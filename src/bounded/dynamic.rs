use core::ops::{Bound, RangeBounds};

use dbutils::equivalent::Comparable;
use either::Either;
use iter::*;
use ref_cast::RefCast;
use skl::{among::Among, KeyBuilder, VacantBuffer, ValueBuilder};

use super::{generic::Memtable as GenericMemtable, sealed::Constructable};

mod entry;

/// Iterators for the memtable.
pub mod iter;

pub use dbutils::{
  equivalentor::{Ascend, Descend, StaticComparator, StaticEquivalentor, StaticRangeComparator},
  types::SliceRef,
};
pub use entry::*;

use sealed::Key;

mod sealed {
  use core::marker::PhantomData;

  use super::{StaticComparator, StaticEquivalentor};

  use dbutils::{
    buffer::VacantBuffer,
    equivalent::{Comparable, Equivalent},
    types::{SliceRef, Type},
  };

  /// The actual key type used in the [`Memtable`](super::Memtable).
  #[derive(ref_cast::RefCast)]
  #[repr(transparent)]
  #[doc(hidden)]
  pub struct Key<C: ?Sized> {
    _marker: PhantomData<C>,
    data: [u8],
  }

  impl<C: ?Sized> core::fmt::Debug for Key<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      core::fmt::Debug::fmt(&self.data, f)
    }
  }

  impl<C> PartialEq for Key<C>
  where
    C: StaticEquivalentor + ?Sized,
  {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
      C::equivalent(&self.data, &other.data)
    }
  }

  impl<C: ?Sized> Eq for Key<C> where C: StaticComparator {}

  impl<C> PartialOrd for Key<C>
  where
    C: StaticComparator + ?Sized,
  {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
      Some(self.cmp(other))
    }
  }

  impl<C> Ord for Key<C>
  where
    C: StaticComparator + ?Sized,
  {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
      C::compare(&self.data, &other.data)
    }
  }

  impl<C: ?Sized> Type for Key<C> {
    type Ref<'a> = <[u8] as Type>::Ref<'a>;

    type Error = <[u8] as Type>::Error;

    #[inline]
    fn encoded_len(&self) -> usize {
      <[u8] as Type>::encoded_len(&self.data)
    }

    #[inline]
    fn encode_to_buffer(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
      <[u8] as Type>::encode_to_buffer(&self.data, buf)
    }
  }

  impl<C> Equivalent<Key<C>> for SliceRef<'_>
  where
    C: ?Sized + StaticEquivalentor,
  {
    #[inline]
    fn equivalent(&self, other: &Key<C>) -> bool {
      C::equivalent(self, &other.data)
    }
  }

  impl<C> Comparable<Key<C>> for SliceRef<'_>
  where
    C: ?Sized + StaticComparator,
  {
    #[inline]
    fn compare(&self, other: &Key<C>) -> core::cmp::Ordering {
      C::compare(self, &other.data)
    }
  }
}

/// Memtable based on bounded ARENA-style `SkipList`.
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
/// use memorable::bounded::{dynamic::Memtable, Options};
/// use core::ops::Bound;
///
/// let memtable = Options::new().alloc::<Memtable>().unwrap();
///
/// memtable.insert(0, b"1", b"v1").unwrap();
/// memtable.insert(0, b"2", b"v2").unwrap();
/// memtable.insert(0, b"3", b"v3").unwrap();
///
/// memtable.remove_range(0, "2"..).unwrap();
///
/// memtable.update_range(0, "1".., "updated").unwrap();
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
pub struct Memtable<C: ?Sized = Ascend>(GenericMemtable<Key<C>, [u8]>);

impl<C: ?Sized> Clone for Memtable<C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<C> Constructable for Memtable<C>
where
  C: ?Sized + 'static,
{
  #[inline]
  fn construct(opts: super::Options) -> Result<Self, super::Error> {
    GenericMemtable::construct(opts).map(Self)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_anon(opts: super::Options) -> std::io::Result<Self> {
    GenericMemtable::map_anon(opts).map(Self)
  }
}

impl<C> Memtable<C>
where
  C: ?Sized + 'static,
{
  /// Returns the maximum version of the memtable.
  #[inline]
  pub fn maximum_version(&self) -> u64 {
    self.0.maximum_version()
  }

  /// Returns the minimum version of the memtable.
  #[inline]
  pub fn minimum_version(&self) -> u64 {
    self.0.minimum_version()
  }
}

impl<C> Memtable<C>
where
  C: StaticComparator + ?Sized + 'static,
{
  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let ages = Options::new().alloc::<Memtable>().unwrap();
  /// ages.insert(0, "Bill Gates", "64").unwrap();
  ///
  /// assert!(ages.contains_key(0, &"Bill Gates"));
  /// assert!(!ages.contains_key(0, &"Steve Jobs"));
  /// ```
  pub fn contains_key<'a, Q>(&'a self, version: u64, k: &Q) -> bool
  where
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.contains_key(version, k)
  }

  /// Returns an entry with the specified `key`.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  ///
  /// memtable.insert(0, b"1", b"1").unwrap();
  /// assert_eq!(*memtable.get(0, b"1").unwrap().value(), b"1");
  /// ```
  #[inline]
  pub fn get<'a, Q>(&'a self, version: u64, k: &Q) -> Option<Entry<'a, C>>
  where
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.get(version, k)
  }

  /// Returns the first entry in the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
  ///
  /// let first = memtable.first(0).unwrap();
  /// assert_eq!(*first.value(), "one");
  /// ```
  #[inline]
  pub fn first(&self, version: u64) -> Option<Entry<'_, C>> {
    self.iter(version).next()
  }

  /// Returns the last entry in the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
  ///
  /// let last = memtable.last(0).unwrap();
  /// assert_eq!(*last.value(), "two");
  /// ```
  #[inline]
  pub fn last(&self, version: u64) -> Option<Entry<'_, C>> {
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
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use std::ops::Bound::*;
  ///
  /// let numbers: Memtable<usize, str> = Options::new().alloc().unwrap();
  /// numbers.insert(0, &6, "six");
  /// numbers.insert(0, &7, "seven");
  /// numbers.insert(0, &12, "twelve");
  ///
  /// let less_than_eight = numbers.upper_bound(0, Excluded(&8)).unwrap();
  /// assert_eq!(*less_than_eight.value(), "seven");
  ///
  /// let less_than_six = numbers.upper_bound(0, Excluded(&6));
  /// assert!(less_than_six.is_none());
  /// ```
  #[inline]
  pub fn upper_bound<'a, Q>(&'a self, version: u64, key: Bound<&Q>) -> Option<Entry<'a, C>>
  where
    Q: ?Sized + Comparable<SliceRef<'a>>,
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
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use std::ops::Bound::*;
  ///
  /// let numbers: Memtable<usize, str> = Options::new().alloc().unwrap();
  /// numbers.insert(0, &6, "six");
  /// numbers.insert(0, &7, "seven");
  /// numbers.insert(0, &12, "twelve");
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
  pub fn lower_bound<'a, Q>(&'a self, version: u64, key: Bound<&Q>) -> Option<Entry<'a, C>>
  where
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.range::<Q, _>(version, (key, Bound::Unbounded)).next()
  }

  /// Returns an iterator over the entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
  /// memtable.insert(0, &3, "three").unwrap();
  /// memtable.insert(0, &4, "four").unwrap();
  ///
  /// memtable.remove_range::<usize, _>(1, (Bound::Excluded(&1), Bound::Unbounded));
  ///
  /// memtable.update_range::<usize, _>(2, (Bound::Unbounded, Bound::Included(&2)), "updated");
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
  pub fn iter(&self, version: u64) -> Iter<'_, C> {
    self.0.iter(version)
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
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
  /// memtable.insert(1, &3, "three").unwrap();
  /// memtable.insert(2, &4, "four").unwrap();
  ///
  /// memtable.remove_range::<usize, _>(1, (Bound::Excluded(&1), Bound::Unbounded)).unwrap();
  ///
  /// memtable.update_range::<usize, _>(2, (Bound::Unbounded, Bound::Included(&2)), "updated").unwrap();
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
  pub fn iter_points(&self, version: u64) -> PointIter<'_, C> {
    self.0.iter_points(version)
  }

  /// Returns an iterator over all point entries (with all versions) of the memtable.
  /// Bulk-deletion and bulk-update operations will be ignored.
  ///
  /// This method is useful when you implementing flush and compaction logic to build LSM tree.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one-v0");
  /// memtable.insert(1, &1, "one-v1");
  /// memtable.insert(1, &2, "two-v1");
  /// memtable.insert(2, &3, "three-v2");
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
  pub fn iter_points_all_versions(&self, version: u64) -> IterAllPoints<'_, C> {
    self.0.iter_points_all_versions(version)
  }

  /// Returns an iterator over the bulk deletion entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::{Memtable, MaybeStructured}, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.remove_range(0, 1..3).unwrap();
  /// memtable.remove_range(0, 4..=7).unwrap();
  /// memtable.remove_range(0, (Bound::Excluded(6), Bound::Unbounded)).unwrap();
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
  pub fn iter_bulk_deletions(&self, version: u64) -> BulkDeletionIter<'_, C> {
    self.0.iter_bulk_deletions(version)
  }

  /// Returns an iterator over the bulk deletion entries (all versions) of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.remove_range(0, 1..3).unwrap();
  /// memtable.remove_range(1, 1..=7).unwrap();
  /// memtable.remove_range(0, 4..=7).unwrap();
  /// memtable.remove_range(0, (Bound::Excluded(6), Bound::Unbounded)).unwrap();
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
  pub fn iter_bulk_deletions_all_versions(&self, version: u64) -> BulkDeletionIterAll<'_, C> {
    self.0.iter_bulk_deletions_all_versions(version)
  }

  /// Returns an iterator over the bulk update entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.update_range(0, 1..3, "[1, 3)").unwrap();
  /// memtable.update_range(1, 4..=7, "[4, 7]").unwrap();
  /// memtable.update_range(2, (Bound::Excluded(6), Bound::Unbounded), "(6, +∞)").unwrap();
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
  pub fn iter_bulk_updates(&self, version: u64) -> BulkUpdateIter<'_, C> {
    self.0.iter_bulk_updates(version)
  }

  /// Returns an iterator over the bulk update entries (all versions) of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.update_range(0, 1..3, "[1, 3)");
  /// memtable.update_range(1, 1..=7, "[1, 7]");
  /// memtable.update_range(1, 4..=7, "[4, 7]");
  /// memtable.update_range(2, (Bound::Excluded(6), Bound::Unbounded), "(6, +∞)");
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
  pub fn iter_bulk_updates_all_versions(&self, version: u64) -> BulkUpdateIterAll<'_, C> {
    self.0.iter_bulk_updates_all_versions(version)
  }

  /// Returns an iterator over a subset of the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
  /// memtable.insert(0, &3, "three").unwrap();
  /// memtable.insert(0, &4, "four").unwrap();
  /// memtable.insert(0, &5, "five");
  /// memtable.insert(0, &6, "six");
  ///
  /// for entry in memtable.range(0, 2..=4) {
  ///   assert!(entry.key() >= &2 && entry.key() <= &4);
  /// }
  /// ```
  #[inline]
  pub fn range<'a, Q, R>(&'a self, version: u64, r: R) -> Range<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range(version, r)
  }

  /// Returns an iterator over a subset of point entries in the memtable within the specified range.
  /// The yield value will not be shadowed by the range operation entries.
  ///
  /// ## Example
  ///
  /// In this example, you can see that the value yield by point range is not shadowed by the range operation entries.
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
  /// memtable.insert(0, &3, "three").unwrap();
  /// memtable.insert(0, &4, "four").unwrap();
  ///
  /// memtable.remove_range(0, 2..).unwrap();
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
  pub fn range_points<'a, Q, R>(&'a self, version: u64, r: R) -> PointRange<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range_points(version, r)
  }

  /// Returns an iterator over a subset of point entries (all of versions) in the memtable within the specified range.
  /// The yield value will not be shadowed by the range operation entries.
  ///
  /// ## Example
  ///
  /// In this example, you can see that the value yield by point range is not shadowed by the range operation entries.
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one-v0");
  /// memtable.insert(1, &1, "one-v1");
  /// memtable.insert(1, &2, "two-v1");
  /// memtable.insert(2, &3, "three-v2");
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
  pub fn range_all_points<'a, Q, R>(&'a self, version: u64, r: R) -> RangeAllPoints<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range_all_points(version, r)
  }

  /// Returns an iterator over a subset of range deletions entries in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.remove_range(0, 1..3);
  /// memtable.remove_range(0, 4..=7);
  /// memtable.remove_range(0, 7..);
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
  pub fn range_bulk_deletions<'a, Q, R>(
    &'a self,
    version: u64,
    r: R,
  ) -> BulkDeletionRange<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range_bulk_deletions(version, r)
  }

  /// Returns an iterator over a subset of range key entries (all versions) in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.remove_range(0, 1..3);
  /// memtable.remove_range(1, 1..=7);
  /// memtable.remove_range(1, 4..=7);
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
  pub fn range_bulk_deletions_all_versions<'a, Q, R>(
    &'a self,
    version: u64,
    r: R,
  ) -> BulkDeletionRangeAll<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range_bulk_deletions_all_versions(version, r)
  }

  /// Returns an iterator over a subset of range key entries in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  ///
  /// memtable.update_range(0, 1..3, "[1, 3)").unwrap();
  /// memtable.update_range(1, 4..=7, "[4, 7]").unwrap();
  /// memtable.update_range(2, (Bound::Excluded(6), Bound::Unbounded), "(6, +∞)").unwrap();
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
  pub fn range_bulk_updates<'a, Q, R>(&'a self, version: u64, r: R) -> BulkUpdateRange<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range_bulk_updates(version, r)
  }

  /// Returns an iterator over a subset of range key entries (all versions) in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable>().unwrap();
  ///
  /// memtable.update_range(0, 1..3, "1v0").unwrap();
  /// memtable.update_range(1, 1..=7, "1v1").unwrap();
  /// memtable.update_range(1, 4..=7, "4v1").unwrap();
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
  pub fn range_bulk_updates_all_versions<'a, Q, R>(
    &'a self,
    version: u64,
    r: R,
  ) -> BulkUpdateRangeAll<'a, C, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.range_bulk_updates_all_versions(version, r)
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  /// memtable.insert(1, "key".as_bytes(), "value".as_bytes()).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, b"key").unwrap().value(), b"value");
  /// ```
  #[inline]
  pub fn insert(&self, version: u64, key: &[u8], value: &[u8]) -> Result<(), super::Error> {
    self
      .0
      .insert(version, Key::ref_cast(key), value)
      .map_err(Among::unwrap_right)
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options, ValueBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  /// memtable.insert_with_value_builder(1, b"key", ValueBuilder::new(5, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"value"))).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, b"key").unwrap().value(), b"value");
  /// ```
  pub fn insert_with_value_builder<'a, E>(
    &'a self,
    version: u64,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<(), Either<E, skl::error::Error>> {
    self
      .0
      .insert_with_value_builder(version, Key::ref_cast(key), value_builder)
      .map(|_| ())
      .map_err(Among::into_middle_right)
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options, KeyBuilder, ValueBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  /// memtable.insert_with_builders(1, KeyBuilder::new(3, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"key")), ValueBuilder::new(5, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"value"))).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, b"key").unwrap().value(), b"value");
  /// ```
  #[allow(single_use_lifetimes)]
  pub fn insert_with_builders<'a, KE, VE>(
    &'a self,
    version: u64,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<(), Among<KE, VE, skl::error::Error>> {
    self
      .0
      .insert_with_builders(version, key_builder, value_builder)
      .map(|_| ())
  }
}
