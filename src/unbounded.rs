use {
  core::{
    cmp::Ordering,
    marker::PhantomData,
    ops::{Bound, ControlFlow, RangeBounds},
  },
  crossbeam_skiplist_mvcc::{
    nested::{Entry as MapEntry, SkipMap},
    Comparable, Equivalent,
  },
  iter::*,
  ref_cast::RefCast,
  std::sync::Arc,
};

pub use entry::*;

mod entry;

/// Iterators for the memtable.
pub mod iter;

/// Operation to be performed on the batch
#[derive(Debug, Clone)]
pub enum Operation<K, V> {
  /// Insert
  Insert {
    /// The key
    key: K,
    /// The value
    value: V,
  },
  /// Remove
  Remove(K),
  /// Remove deletions
  RemoveRange {
    /// The start bound
    start_bound: Bound<K>,
    /// The end bound
    end_bound: Bound<K>,
  },
  /// Range update
  UpdateRange {
    /// The start bound
    start_bound: Bound<K>,
    /// The end bound
    end_bound: Bound<K>,
    /// The new value
    value: V,
  },
}

#[derive(PartialEq, Eq, PartialOrd, Ord, ref_cast::RefCast)]
#[repr(transparent)]
struct Query<K: ?Sized, Q: ?Sized> {
  _m: PhantomData<K>,
  key: Q,
}

struct QueryRange<K: ?Sized, Q: ?Sized, R>
where
  R: RangeBounds<Q>,
{
  r: R,
  _q: PhantomData<(fn() -> K, fn() -> Q)>,
}

impl<K: ?Sized, Q: ?Sized, R> QueryRange<K, Q, R>
where
  R: RangeBounds<Q>,
{
  #[inline]
  pub(super) const fn new(r: R) -> Self {
    Self { r, _q: PhantomData }
  }
}

impl<K: ?Sized, Q: ?Sized, R> RangeBounds<Query<K, Q>> for QueryRange<K, Q, R>
where
  R: RangeBounds<Q>,
{
  #[inline]
  fn start_bound(&self) -> Bound<&Query<K, Q>> {
    self.r.start_bound().map(RefCast::ref_cast)
  }

  fn end_bound(&self) -> Bound<&Query<K, Q>> {
    self.r.end_bound().map(RefCast::ref_cast)
  }
}

#[non_exhaustive]
enum RangeKind<V> {
  Set(V),
  Deletion,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
enum StartKey<K> {
  Minimum,
  Key(K),
}

impl<K> StartKey<K> {
  #[inline]
  fn new(key: Bound<K>) -> Self {
    match key {
      Bound::Included(k) => Self::Key(k),
      Bound::Excluded(k) => Self::Key(k),
      Bound::Unbounded => Self::Minimum,
    }
  }
}

impl<K: Ord> PartialOrd for StartKey<K> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<K: Ord> Ord for StartKey<K> {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {
      (Self::Minimum, Self::Minimum) => Ordering::Equal,
      (Self::Minimum, _) => Ordering::Less,
      (_, Self::Minimum) => Ordering::Greater,
      (Self::Key(k1), Self::Key(k2)) => k1.cmp(k2),
    }
  }
}

impl<K, Q> Equivalent<StartKey<K>> for Query<K, Q>
where
  Q: ?Sized + Equivalent<K>,
{
  #[inline]
  fn equivalent(&self, key: &StartKey<K>) -> bool {
    match key {
      StartKey::Minimum => false,
      StartKey::Key(k) => self.key.equivalent(k),
    }
  }
}

impl<K, Q> Comparable<StartKey<K>> for Query<K, Q>
where
  Q: ?Sized + Comparable<K>,
{
  #[inline]
  fn compare(&self, key: &StartKey<K>) -> Ordering {
    match key {
      StartKey::Minimum => Ordering::Greater,
      StartKey::Key(k) => self.key.compare(k),
    }
  }
}

struct KeySpan<K, V> {
  start_bound: Bound<()>,
  /// only store the bound information, the key will be stored in the SkipMap as key.
  end_bound: Bound<K>,
  value: RangeKind<V>,
}

impl<K, V> KeySpan<K, V> {
  #[inline]
  const fn new(start_bound: Bound<()>, end_bound: Bound<K>, value: RangeKind<V>) -> Self {
    Self {
      start_bound,
      end_bound,
      value,
    }
  }

  #[inline]
  fn range<'a>(&'a self, start_key: &'a StartKey<K>) -> impl RangeBounds<K> + 'a {
    let start_bound = match start_key {
      StartKey::Key(k) => match self.start_bound {
        Bound::Included(_) => Bound::Included(k),
        Bound::Excluded(_) => Bound::Excluded(k),
        Bound::Unbounded => Bound::Unbounded,
      },
      StartKey::Minimum => Bound::Unbounded,
    };

    (start_bound, self.end_bound.as_ref())
  }

  #[inline]
  const fn unwrap_value(&self) -> &V {
    match &self.value {
      RangeKind::Set(v) => v,
      RangeKind::Deletion => panic!("invoke unwrap value on deletion span"),
    }
  }
}

struct Inner<K, V> {
  skl: SkipMap<K, V>,
  // key is the start bound
  range_del_skl: SkipMap<StartKey<K>, KeySpan<K, V>>,
  range_key_skl: SkipMap<StartKey<K>, KeySpan<K, V>>,
}

/// Memtable based on unbounded `SkipList`.
///
/// All APIs are designed to be lock-free, but it is the user's responsibility to ensure that the
/// `version` is monotonically increasing to promise linear and avoid ABA problems.
///
/// ## Entry Priority
///
/// If the point entry has the same version as the range entry, the point entry will be shadowed by
/// the range entry, which means range entry has higher priority.
///
/// Besides, range remove entry has higher priority than range set entry.
///
/// ```rust
/// use memorable::unbounded::Memtable;
/// use core::ops::Bound;
///
/// let memtable = Memtable::<&str, &str>::new();
///
/// memtable.insert(0, "1", "v1");
/// memtable.insert(0, "2", "v2");
/// memtable.insert(0, "3", "v3");
///
/// memtable.remove_range(0, Bound::Included("2"), Bound::Unbounded);
///
/// memtable.update_range(0, Bound::Included("1"), Bound::Unbounded, "updated");
///
/// assert_eq!(*memtable.get(0, &"1").unwrap().value(), "updated");
/// assert!(memtable.get(0, &"2").is_none());
/// assert!(memtable.get(0, &"3").is_none());
/// ```
///
/// In the above example, if we invoke get(1) at version 0, the result will be "updated" because the
/// range set entry has higher priority than the point entry and shadowed its value.
///
/// If we invoke get(2) at version 0, the result will be None because the range remove entry has
/// higher priority than the point entry and shadowed its value.
pub struct Memtable<K, V> {
  // has an inner here because of the `mem::size_of::<Inner<K, V>>() == 1980`, which is too large
  // to be stored in the stack. So we store it in the heap through `Arc`.
  inner: Arc<Inner<K, V>>,
}

impl<K, V> Clone for Memtable<K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      inner: self.inner.clone(),
    }
  }
}

impl<K, V> Default for Memtable<K, V> {
  fn default() -> Self {
    Self::new()
  }
}

impl<K, V> Memtable<K, V> {
  /// Returns a new, empty memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable: Memtable<i32, i32> = Memtable::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self {
      inner: Arc::new(Inner {
        skl: SkipMap::new(),
        range_del_skl: SkipMap::new(),
        range_key_skl: SkipMap::new(),
      }),
    }
  }
}

impl<K, V> Memtable<K, V>
where
  K: Ord,
{
  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let ages = Memtable::new();
  /// ages.insert(0, "Bill Gates", 64);
  ///
  /// assert!(ages.contains_key(0, &"Bill Gates"));
  /// assert!(!ages.contains_key(0, &"Steve Jobs"));
  /// ```
  #[inline]
  pub fn contains_key<Q>(&self, version: u64, key: &Q) -> bool
  where
    Q: ?Sized + Comparable<K>,
  {
    self.get(version, key).is_some()
  }

  /// Returns an entry with the specified `key`.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable: Memtable<i32, i32> = Memtable::new();
  ///
  /// memtable.insert(0, 1, 1);
  /// assert_eq!(*memtable.get(0, &1).unwrap().value(), 1);
  /// ```
  #[inline]
  pub fn get<Q>(&self, version: u64, key: &Q) -> Option<Entry<'_, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    let ent = self.inner.skl.get(version, key)?;
    match self.validate(version, ent) {
      ControlFlow::Break(entry) => entry,
      ControlFlow::Continue(_) => None,
    }
  }

  /// Returns the first entry in the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  ///
  /// let first = memtable.first(0).unwrap();
  /// assert_eq!(*first.value(), "one");
  /// ```
  #[inline]
  pub fn first(&self, version: u64) -> Option<Entry<'_, K, V>> {
    self.iter(version).next()
  }

  /// Returns the last entry in the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  ///
  /// let last = memtable.last(0).unwrap();
  /// assert_eq!(*last.value(), "two");
  /// ```
  #[inline]
  pub fn last(&self, version: u64) -> Option<Entry<'_, K, V>> {
    self.iter(version).next_back()
  }

  /// Returns an [`Entry`] pointing to the highest element whose key is below
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = Memtable::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let less_than_eight = numbers.upper_bound(0, Excluded(&8)).unwrap();
  /// assert_eq!(*less_than_eight.value(), "seven");
  ///
  /// let less_than_six = numbers.upper_bound(0, Excluded(&6));
  /// assert!(less_than_six.is_none());
  /// ```
  #[inline]
  pub fn upper_bound<Q>(&self, version: u64, key: Bound<&Q>) -> Option<Entry<'_, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    self
      .range::<Q, _>(version, (Bound::Unbounded, key))
      .next_back()
  }

  /// Returns an [`Entry`] pointing to the lowest element whose key is above
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = Memtable::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let greater_than_five = numbers.lower_bound(0, Excluded(&5)).unwrap();
  /// assert_eq!(*greater_than_five.value(), "six");
  ///
  /// let greater_than_six = numbers.lower_bound(0, Excluded(&6)).unwrap();
  /// assert_eq!(*greater_than_six.value(), "seven");
  ///
  /// let greater_than_thirteen = numbers.lower_bound(0, Excluded(&13));
  /// assert!(greater_than_thirteen.is_none());
  /// ```
  #[inline]
  pub fn lower_bound<Q>(&self, version: u64, key: Bound<&Q>) -> Option<Entry<'_, K, V>>
  where
    Q: ?Sized + Comparable<K>,
  {
    self.range::<Q, _>(version, (key, Bound::Unbounded)).next()
  }

  /// Returns an iterator over the entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  /// memtable.insert(0, 3, "three");
  /// memtable.insert(0, 4, "four");
  ///
  /// memtable.remove_range(1, Bound::Excluded(1), Bound::Unbounded);
  ///
  /// memtable.update_range(2, Bound::Unbounded, Bound::Included(2), "updated");
  ///
  /// // At view 0, the memtable contains 4 entries.
  /// let mut num = 0;
  /// for (idx, entry) in memtable.iter(0).enumerate() {
  ///   assert_eq!(entry.key(), &(idx + 1));
  ///   num += 1;
  /// }
  /// assert_eq!(num, 4);
  ///
  /// // At view 1, the memtable contains 1 entry because of remove_range..
  /// let mut num = 0;
  /// for entry in memtable.iter(1) {
  ///   assert_eq!(entry.key(), &1);
  ///   assert_eq!(*entry.value(), "one");
  ///   num += 1;
  /// }
  /// assert_eq!(num, 1);
  ///
  /// // At view 2, the memtable contains 1 entry because of update_range, and the value is updated because of the update_range.
  /// let mut num = 0;
  /// for (idx, entry) in memtable.iter(2).enumerate() {
  ///   assert_eq!(entry.key(), &(idx + 1));
  ///   assert_eq!(*entry.value(), "updated");
  ///   num += 1;
  /// }
  /// assert_eq!(num, 1);
  /// ```
  #[inline]
  pub fn iter(&self, version: u64) -> Iter<'_, K, V> {
    Iter::new(version, self)
  }

  /// Returns an iterator over the point entries of the memtable.
  /// Bulk-deletion and bulk-update operations will be ignored.
  ///
  /// This method is useful when you implementing flush and compaction logic to build LSM tree.
  ///
  /// ## Example
  ///
  /// In this example, you can see that the value yield by point iter is not shadowed by the range entries.
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  /// memtable.insert(1, 3, "three");
  /// memtable.insert(2, 4, "four");
  ///
  /// memtable.remove_range(1, Bound::Excluded(1), Bound::Unbounded);
  ///
  /// memtable.update_range(2, Bound::Unbounded, Bound::Included(2), "updated");
  ///
  /// let mut num = 0;
  /// for (idx, entry) in memtable.iter_points(0).enumerate() {
  ///   assert_eq!(entry.key(), &(idx + 1));
  ///   assert_eq!(entry.version(), 0);
  ///   num += 1;
  /// }
  /// assert_eq!(num, 2);
  ///
  /// let mut num = 0;
  /// for (idx, entry) in memtable.iter_points(1).enumerate() {
  ///   assert_eq!(entry.key(), &(idx + 1));
  ///   num += 1;
  /// }
  /// assert_eq!(num, 3);
  ///
  /// let mut num = 0;
  /// for (idx, entry) in memtable.iter_points(2).enumerate() {
  ///   assert_eq!(entry.key(), &(idx + 1));
  ///   num += 1;
  /// }
  /// assert_eq!(num, 4);
  /// ```
  #[inline]
  pub fn iter_points(&self, version: u64) -> PointIter<'_, K, V> {
    PointIter::new(version, self)
  }

  /// Returns an iterator over all point entries (with all versions) of the memtable.
  /// Bulk-deletion and bulk-update operations will be ignored.
  ///
  /// This method is useful when you implementing flush and compaction logic to build LSM tree.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one-v0");
  /// memtable.insert(1, 1, "one-v1");
  /// memtable.insert(1, 2, "two-v1");
  /// memtable.insert(2, 3, "three-v2");
  ///
  /// let mut iter = memtable.iter_points_all_versions(0);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.key(), &1);
  /// assert_eq!(*first.value().unwrap(), "one-v0");
  /// assert_eq!(first.version(), 0);
  /// assert!(iter.next().is_none());
  ///
  /// let mut iter = memtable.iter_points_all_versions(1);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.key(), &1);
  /// assert_eq!(*first.value().unwrap(), "one-v1");
  /// assert_eq!(first.version(), 1);
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.key(), &1);
  /// assert_eq!(*second.value().unwrap(), "one-v0");
  /// assert_eq!(second.version(), 0);
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.key(), &2);
  /// assert_eq!(*third.value().unwrap(), "two-v1");
  /// assert_eq!(third.version(), 1);
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn iter_points_all_versions(&self, version: u64) -> IterAllPoints<'_, K, V> {
    self.inner.skl.iter_all_versions(version)
  }

  /// Returns an iterator over the bulk deletion entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.remove_range(0, Bound::Included(1), Bound::Excluded(3));
  /// memtable.remove_range(0, Bound::Included(4), Bound::Included(7));
  /// memtable.remove_range(0, Bound::Excluded(6), Bound::Unbounded);
  ///
  /// let mut iter = memtable.iter_bulk_deletions(0);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Excluded(&3));
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&4));
  /// assert_eq!(second.end_bound(), Bound::Included(&7));
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Excluded(&6));
  /// assert_eq!(third.end_bound(), Bound::Unbounded);
  /// ```
  #[inline]
  pub fn iter_bulk_deletions(&self, version: u64) -> BulkDeletionIter<'_, K, V> {
    BulkDeletionIter::new(version, self)
  }

  /// Returns an iterator over the bulk deletion entries (all versions) of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.remove_range(0, Bound::Included(1), Bound::Excluded(3));
  /// memtable.remove_range(1, Bound::Included(1), Bound::Included(7));
  /// memtable.remove_range(0, Bound::Included(4), Bound::Included(7));
  /// memtable.remove_range(0, Bound::Excluded(6), Bound::Unbounded);
  ///
  /// let mut iter = memtable.iter_bulk_deletions_all_versions(0);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Excluded(&3));
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&4));
  /// assert_eq!(second.end_bound(), Bound::Included(&7));
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Excluded(&6));
  /// assert_eq!(third.end_bound(), Bound::Unbounded);
  ///
  /// let mut iter = memtable.iter_bulk_deletions_all_versions(1);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Included(&7));
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&1));
  /// assert_eq!(second.end_bound(), Bound::Excluded(&3));
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Included(&4));
  /// assert_eq!(third.end_bound(), Bound::Included(&7));
  ///
  /// let fourth = iter.next().unwrap();
  /// assert_eq!(fourth.start_bound(), Bound::Excluded(&6));
  /// assert_eq!(fourth.end_bound(), Bound::Unbounded);
  /// ```
  #[inline]
  pub fn iter_bulk_deletions_all_versions(&self, version: u64) -> BulkDeletionIterAll<'_, K, V> {
    BulkDeletionIterAll::new(version, self)
  }

  /// Returns an iterator over the bulk update entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.update_range(0, Bound::Included(1), Bound::Excluded(3), "[1, 3)");
  /// memtable.update_range(1, Bound::Included(4), Bound::Included(7), "[4, 7]");
  /// memtable.update_range(2, Bound::Excluded(6), Bound::Unbounded, "(6, +∞)");
  ///
  /// let mut iter = memtable.iter_bulk_updates(2);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Excluded(&3));
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&4));
  /// assert_eq!(second.end_bound(), Bound::Included(&7));
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Excluded(&6));
  /// assert_eq!(third.end_bound(), Bound::Unbounded);
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn iter_bulk_updates(&self, version: u64) -> BulkUpdateIter<'_, K, V> {
    BulkUpdateIter::new(version, self)
  }

  /// Returns an iterator over the bulk update entries (all versions) of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.update_range(0, Bound::Included(1), Bound::Excluded(3), "[1, 3)");
  /// memtable.update_range(1, Bound::Included(1), Bound::Included(7), "[1, 7]");
  /// memtable.update_range(1, Bound::Included(4), Bound::Included(7), "[4, 7]");
  /// memtable.update_range(2, Bound::Excluded(6), Bound::Unbounded, "(6, +∞)");
  ///
  /// let mut iter = memtable.iter_bulk_updates_all_versions(2);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Included(&7));
  /// assert_eq!(first.version(), 1);
  /// assert_eq!(*first.value(), "[1, 7]");
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&1));
  /// assert_eq!(second.end_bound(), Bound::Excluded(&3));
  /// assert_eq!(second.version(), 0);
  /// assert_eq!(*second.value(), "[1, 3)");
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Included(&4));
  /// assert_eq!(third.end_bound(), Bound::Included(&7));
  /// assert_eq!(third.version(), 1);
  /// assert_eq!(*third.value(), "[4, 7]");
  ///
  /// let fourth = iter.next().unwrap();
  /// assert_eq!(fourth.start_bound(), Bound::Excluded(&6));
  /// assert_eq!(fourth.end_bound(), Bound::Unbounded);
  /// assert_eq!(fourth.version(), 2);
  /// assert_eq!(*fourth.value(), "(6, +∞)");
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn iter_bulk_updates_all_versions(&self, version: u64) -> BulkUpdateIterAll<'_, K, V> {
    BulkUpdateIterAll::new(version, self)
  }

  /// Returns an iterator over a subset of the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  /// memtable.insert(0, 3, "three");
  /// memtable.insert(0, 4, "four");
  /// memtable.insert(0, 5, "five");
  /// memtable.insert(0, 6, "six");
  ///
  /// for entry in memtable.range(0, 2..=4) {
  ///   assert!(entry.key() >= &2 && entry.key() <= &4);
  /// }
  /// ```
  #[inline]
  pub fn range<Q, R>(&self, version: u64, r: R) -> Range<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    Range::new(version, self, r)
  }

  /// Returns an iterator over a subset of point entries in the memtable within the specified range.
  /// The yield value will not be shadowed by the range operation entries.
  ///
  /// ## Example
  ///
  /// In this example, you can see that the value yield by point range is not shadowed by the range operation entries.
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  /// memtable.insert(0, 3, "three");
  /// memtable.insert(0, 4, "four");
  ///
  /// memtable.remove_range(0, Bound::Excluded(1), Bound::Unbounded);
  ///
  /// let mut iter = memtable.range_points(0, 2..=4);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.key(), &2);
  /// assert_eq!(*first.value(), "two");
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.key(), &3);
  /// assert_eq!(*second.value(), "three");
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.key(), &4);
  /// assert_eq!(*third.value(), "four");
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn range_points<Q, R>(&self, version: u64, r: R) -> PointRange<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    PointRange::new(version, self, r)
  }

  /// Returns an iterator over a subset of point entries (all of versions) in the memtable within the specified range.
  /// The yield value will not be shadowed by the range operation entries.
  ///
  /// ## Example
  ///
  /// In this example, you can see that the value yield by point range is not shadowed by the range operation entries.
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one-v0");
  /// memtable.insert(1, 1, "one-v1");
  /// memtable.insert(1, 2, "two-v1");
  /// memtable.insert(2, 3, "three-v2");
  ///
  /// let mut iter = memtable.range_all_points(0, 1..=3);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.key(), &1);
  /// assert_eq!(*first.value().unwrap(), "one-v0");
  /// assert_eq!(first.version(), 0);
  /// assert!(iter.next().is_none());
  ///
  /// let mut iter = memtable.range_all_points(1, 1..=3);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.key(), &1);
  /// assert_eq!(*first.value().unwrap(), "one-v1");
  /// assert_eq!(first.version(), 1);
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.key(), &1);
  /// assert_eq!(*second.value().unwrap(), "one-v0");
  /// assert_eq!(second.version(), 0);
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.key(), &2);
  /// assert_eq!(*third.value().unwrap(), "two-v1");
  /// assert_eq!(third.version(), 1);
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn range_all_points<Q, R>(&self, version: u64, r: R) -> RangeAllPoints<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    self.inner.skl.range_all_versions(version, r)
  }

  /// Returns an iterator over a subset of range deletions entries in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.remove_range(0, Bound::Included(1), Bound::Excluded(3));
  /// memtable.remove_range(0, Bound::Included(4), Bound::Included(7));
  /// memtable.remove_range(0, Bound::Excluded(6), Bound::Unbounded);
  ///
  /// let mut iter = memtable.range_bulk_deletions(0, 1..=5);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Excluded(&3));
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&4));
  /// assert_eq!(second.end_bound(), Bound::Included(&7));
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn range_bulk_deletions<Q, R>(&self, version: u64, r: R) -> BulkDeletionRange<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    BulkDeletionRange::new(version, self, r)
  }

  /// Returns an iterator over a subset of range key entries (all versions) in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.remove_range(0, Bound::Included(1), Bound::Excluded(3));
  /// memtable.remove_range(1, Bound::Included(1), Bound::Included(7));
  /// memtable.remove_range(1, Bound::Included(4), Bound::Included(7));
  ///
  /// let mut iter = memtable.range_bulk_deletions_all_versions(2, 1..=5);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Included(&7));
  /// assert_eq!(first.version(), 1);
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&1));
  /// assert_eq!(second.end_bound(), Bound::Excluded(&3));
  /// assert_eq!(second.version(), 0);
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Included(&4));
  /// assert_eq!(third.end_bound(), Bound::Included(&7));
  /// assert_eq!(third.version(), 1);
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn range_bulk_deletions_all_versions<Q, R>(
    &self,
    version: u64,
    r: R,
  ) -> BulkDeletionRangeAll<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    BulkDeletionRangeAll::new(version, self, r)
  }

  /// Returns an iterator over a subset of range key entries in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  ///
  /// memtable.update_range(0, Bound::Included(1), Bound::Excluded(3), "[1, 3)");
  /// memtable.update_range(1, Bound::Included(4), Bound::Included(7), "[4, 7]");
  /// memtable.update_range(2, Bound::Excluded(6), Bound::Unbounded, "(6, +∞)");
  ///
  /// let mut iter = memtable.range_bulk_updates(2, 1..=5);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Excluded(&3));
  /// assert_eq!(*first.value(), "[1, 3)");
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&4));
  /// assert_eq!(second.end_bound(), Bound::Included(&7));
  /// assert_eq!(*second.value(), "[4, 7]");
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn range_bulk_updates<Q, R>(&self, version: u64, r: R) -> BulkUpdateRange<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    BulkUpdateRange::new(version, self, r)
  }

  /// Returns an iterator over a subset of range key entries (all versions) in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.update_range(0, Bound::Included(1), Bound::Excluded(3), "1v0");
  /// memtable.update_range(1, Bound::Included(1), Bound::Included(7), "1v1");
  /// memtable.update_range(1, Bound::Included(4), Bound::Included(7), "4v1");
  ///
  /// let mut iter = memtable.range_bulk_updates_all_versions(2, 1..=5);
  ///
  /// let first = iter.next().unwrap();
  /// assert_eq!(first.start_bound(), Bound::Included(&1));
  /// assert_eq!(first.end_bound(), Bound::Included(&7));
  /// assert_eq!(first.version(), 1);
  /// assert_eq!(*first.value(), "1v1");
  ///
  /// let second = iter.next().unwrap();
  /// assert_eq!(second.start_bound(), Bound::Included(&1));
  /// assert_eq!(second.end_bound(), Bound::Excluded(&3));
  /// assert_eq!(second.version(), 0);
  /// assert_eq!(*second.value(), "1v0");
  ///
  /// let third = iter.next().unwrap();
  /// assert_eq!(third.start_bound(), Bound::Included(&4));
  /// assert_eq!(third.end_bound(), Bound::Included(&7));
  /// assert_eq!(third.version(), 1);
  /// assert_eq!(*third.value(), "4v1");
  ///
  /// assert!(iter.next().is_none());
  /// ```
  #[inline]
  pub fn range_bulk_updates_all_versions<Q, R>(
    &self,
    version: u64,
    r: R,
  ) -> BulkUpdateRangeAll<'_, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K>,
  {
    BulkUpdateRangeAll::new(version, self, r)
  }

  fn validate<'a>(
    &'a self,
    query_version: u64,
    ent: MapEntry<'a, K, V>,
  ) -> ControlFlow<Option<Entry<'a, K, V>>, MapEntry<'a, K, V>> {
    let key = ent.key();
    let version = ent.version();
    let bound = Query::ref_cast(key);

    // check if the next entry is visible.
    // As the range_del_skl is sorted by the end key, we can use the lower_bound to find the first
    // deletion range that may cover the next entry.
    let shadow = self
      .inner
      .range_del_skl
      .range::<Query<K, K>, _>(query_version, ..=bound)
      .any(|ent| {
        let del_ent_version = ent.version();
        (version <= del_ent_version && del_ent_version <= query_version)
          && ent.value().range(ent.key()).contains(key)
      });

    if shadow {
      return ControlFlow::Continue(ent);
    }

    // find the range key entry with maximum version that shadow the next entry.
    let range_ent = self
      .inner
      .range_key_skl
      .range::<Query<K, K>, _>(query_version, ..=bound)
      .filter(|ent| {
        let range_ent_version = ent.version();
        (version <= range_ent_version && range_ent_version <= query_version)
          && ent.value().range(ent.key()).contains(key)
      })
      .max_by_key(|e| e.version());

    // check if the next entry's value should be shadowed by the range key entries.
    if let Some(range_ent) = range_ent {
      let value = EntryValue::<K, V>::Range(range_ent);
      ControlFlow::Break(Some(Entry::new(self, query_version, ent, value)))
    } else {
      let value = EntryValue::<K, V>::Point(ent.value());
      ControlFlow::Break(Some(Entry::new(self, query_version, ent, value)))
    }
  }
}

impl<K, V> Memtable<K, V>
where
  K: Ord + Send + 'static,
  V: Send + 'static,
{
  /// Applies a batch of operations to the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::{Memtable, Operation};
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::new();
  ///
  /// let batch = vec![
  ///   Operation::Insert { key: "key1", value: "value1" },
  ///   Operation::Insert { key: "key2", value: "value2" },
  ///   Operation::Remove("key3"),
  ///   Operation::RemoveRange { start_bound: Bound::Included("key15"), end_bound: Bound::Unbounded },
  ///   Operation::UpdateRange { start_bound: Bound::Included("key6"), end_bound: Bound::Included("key10"), value: "updated" },
  /// ];
  ///
  /// memtable.apply(0, batch.into_iter());
  /// ```
  pub fn apply<B>(&self, version: u64, batch: B)
  where
    B: Iterator<Item = Operation<K, V>>,
  {
    for op in batch {
      match op {
        Operation::Insert { key, value } => self.insert(version, key, value),
        Operation::Remove(key) => self.remove(version, key),
        Operation::RemoveRange {
          start_bound,
          end_bound,
        } => self.remove_range(version, start_bound, end_bound),
        Operation::UpdateRange {
          start_bound,
          end_bound,
          value,
        } => self.update_range(version, start_bound, end_bound, value),
      }
    }
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable = Memtable::new();
  /// memtable.insert(1, "key", "value");
  ///
  /// assert_eq!(*memtable.get(1, "key").unwrap().value(), "value");
  /// ```
  pub fn insert(&self, version: u64, key: K, value: V) {
    self.inner.skl.insert_unchecked(version, key, value);
  }

  /// Insert a tombstone entry for the specified `key` from the memtable and returns it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  ///
  /// let memtable: Memtable<&str, &str> = Memtable::new();
  /// memtable.insert(0, "key", "value");
  /// memtable.remove(1, "key");
  /// assert!(memtable.get(0, "key").is_some());
  /// assert!(memtable.get(1, "key").is_none());
  /// ```
  pub fn remove(&self, version: u64, key: K) {
    self.inner.skl.remove_unchecked(version, key);
  }

  /// Inserts a range deletion entry into the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable: Memtable<i32, i32> = Memtable::new();
  ///
  /// memtable.insert(0, 1, 1);
  /// memtable.insert(0, 2, 2);
  /// memtable.insert(0, 3, 3);
  /// memtable.insert(0, 4, 4);
  ///
  /// memtable.remove_range(1, Bound::Included(2), Bound::Unbounded);
  ///
  /// assert_eq!(*memtable.get(1, &1).unwrap().value(), 1);
  /// assert!(memtable.get(1, &2).is_none());
  /// assert!(memtable.get(1, &3).is_none());
  /// assert!(memtable.get(1, &4).is_none());
  /// ```
  pub fn remove_range(&self, version: u64, start: Bound<K>, end: Bound<K>) {
    let start_bound = start.as_ref().map(|_| ());
    let start = StartKey::new(start);

    let span = KeySpan::new(start_bound, end, RangeKind::Deletion);
    self
      .inner
      .range_del_skl
      .insert_unchecked(version, start, span);
  }

  /// Update entries within a range to the given value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::unbounded::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable: Memtable<i32, i32> = Memtable::new();
  ///
  /// memtable.insert(0, 1, 1);
  /// memtable.insert(0, 2, 2);
  /// memtable.insert(0, 3, 3);
  /// memtable.insert(0, 4, 4);
  ///
  /// memtable.update_range(1, Bound::Included(2), Bound::Unbounded, 5);
  ///
  /// assert_eq!(*memtable.get(1, &1).unwrap().value(), 1);
  /// assert_eq!(*memtable.get(1, &2).unwrap().value(), 5);
  /// assert_eq!(*memtable.get(1, &3).unwrap().value(), 5);
  /// assert_eq!(*memtable.get(1, &4).unwrap().value(), 5);
  /// ```
  pub fn update_range(&self, version: u64, start: Bound<K>, end: Bound<K>, value: V) {
    let start_bound = start.as_ref().map(|_| ());
    let start = StartKey::new(start);
    let span = KeySpan::new(start_bound, end, RangeKind::Set(value));
    self
      .inner
      .range_key_skl
      .insert_unchecked(version, start, span);
  }
}
