use core::ops::{Bound, ControlFlow, RangeBounds};

use super::{sealed::Constructable, Error};

use bulk::*;
use either::Either;
use iter::*;
use ref_cast::RefCast;
use skl::{
  among::Among, generic::{
    multiple_version::{
      sync::{Entry as MapEntry, SkipMap},
      Map,
    },
    Builder, Comparable, KeyRef, Type,
  }, Allocator as _, Arena, KeyBuilder, VacantBuffer, ValueBuilder
};
use std::sync::Arc;

pub use dbutils::types::MaybeStructured;
pub use entry::*;

mod bulk;
mod entry;

/// Iterators for the memtable.
pub mod iter;

const UNBOUNDED: u8 = 0;
const INCLUDED: u8 = 1;
const EXCLUDED: u8 = 2;

struct Inner<K: ?Sized, V: ?Sized> {
  skl: SkipMap<K, V>,
  // key is the start bound
  range_del_skl: SkipMap<PhantomRangeKey<K>, PhantomRangeDeletionSpan<K>>,
  range_key_skl: SkipMap<PhantomRangeKey<K>, PhantomRangeUpdateSpan<K, V>>,
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
/// use memorable::bounded::{generic::Memtable, Options};
/// use core::ops::Bound;
///
/// let memtable = Options::new().alloc::<Memtable::<str, str>>().unwrap();
///
/// memtable.insert(0, "1", "v1").unwrap();
/// memtable.insert(0, "2", "v2").unwrap();
/// memtable.insert(0, "3", "v3").unwrap();
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
pub struct Memtable<K: ?Sized, V: ?Sized> {
  // has an inner here because of the `mem::size_of::<Inner<K, V>>() == 1980`, which is too large
  // to be stored in the stack. So we store it in the heap through `Arc`.
  inner: Arc<Inner<K, V>>,
}

impl<K: ?Sized, V: ?Sized> Clone for Memtable<K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      inner: self.inner.clone(),
    }
  }
}

impl<K, V> Constructable for Memtable<K, V>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
{
  #[inline]
  fn construct(opts: super::Options) -> Result<Self, super::Error> {
    let skl_opts = opts.to_skl_options();
    let skl = Builder::new()
      .with_options(skl_opts)
      .alloc::<SkipMap<K, V>>()?;
    let allocator = skl.allocator().clone();
    let range_del_skl =
      SkipMap::<PhantomRangeKey<K>, PhantomRangeDeletionSpan<K>>::create_from_allocator(
        allocator.clone(),
      )?;
    let range_key_skl =
      SkipMap::<PhantomRangeKey<K>, PhantomRangeUpdateSpan<K, V>>::create_from_allocator(
        allocator,
      )?;

    Ok(Self {
      inner: Arc::new(Inner {
        skl,
        range_del_skl,
        range_key_skl,
      }),
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_anon(opts: super::Options) -> std::io::Result<Self> {
    fn io_err(e: skl::error::Error) -> std::io::Error {
      std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
    }

    let skl_opts = opts.to_skl_options();
    let skl = Builder::new()
      .with_options(skl_opts)
      .map_anon::<SkipMap<K, V>>()?;
    let allocator = skl.allocator().clone();
    let range_del_skl =
      SkipMap::<PhantomRangeKey<K>, PhantomRangeDeletionSpan<K>>::create_from_allocator(
        allocator.clone(),
      )
      .map_err(io_err)?;
    let range_key_skl =
      SkipMap::<PhantomRangeKey<K>, PhantomRangeUpdateSpan<K, V>>::create_from_allocator(allocator)
        .map_err(io_err)?;

    Ok(Self {
      inner: Arc::new(Inner {
        skl,
        range_del_skl,
        range_key_skl,
      }),
    })
  }
}

impl<K, V> Memtable<K, V>
where
  K: ?Sized + 'static,
  V: ?Sized + 'static,
{
  /// Returns the maximum version of the memtable.
  #[inline]
  pub fn maximum_version(&self) -> u64 {
    self
      .inner
      .skl
      .maximum_version()
      .max(self.inner.range_del_skl.maximum_version())
      .max(self.inner.range_key_skl.maximum_version())
  }

  /// Returns the minimum version of the memtable.
  #[inline]
  pub fn minimum_version(&self) -> u64 {
    self
      .inner
      .skl
      .minimum_version()
      .min(self.inner.range_del_skl.minimum_version())
      .min(self.inner.range_key_skl.minimum_version())
  }

  /// Returns the reserved slice of the memtable by users.
  #[inline]
  pub fn reserved_slice(&self) -> &[u8] {
    self.inner.skl.allocator().reserved_slice()
  }

  /// Returns the mutable reserved slice of the memtable by users.
  /// 
  /// ## Safety
  /// - The caller need to make sure there is no data-race
  ///
  /// # Panic
  /// - If in read-only mode, and num of reserved bytes is greater than 0, this method will panic.
  #[allow(clippy::mut_from_ref)]
  #[inline]
  pub unsafe fn reserved_slice_mut(&self) -> &mut [u8] {
    self.inner.skl.allocator().reserved_slice_mut()
  }
}

impl<K, V> Memtable<K, V>
where
  K: ?Sized + Type + 'static,
  for<'a> K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type + 'static,
{
  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let ages = Options::new().alloc::<Memtable<str, u8>>().unwrap();
  /// ages.insert(0, "Bill Gates", &64).unwrap();
  ///
  /// assert!(ages.contains_key(0, &"Bill Gates"));
  /// assert!(!ages.contains_key(0, &"Steve Jobs"));
  /// ```
  #[inline]
  pub fn contains_key<'a, Q>(&'a self, version: u64, key: &Q) -> bool
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
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
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable: Memtable<i32, i32> = Options::new().alloc().unwrap();
  ///
  /// memtable.insert(0, &1, &1).unwrap();
  /// assert_eq!(*memtable.get(0, &1).unwrap().value(), 1);
  /// ```
  #[inline]
  pub fn get<'a, Q>(&'a self, version: u64, key: &Q) -> Option<Entry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
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
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
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
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
  ///
  /// memtable.insert(0, &1, "one").unwrap();
  /// memtable.insert(0, &2, "two").unwrap();
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
  /// use memorable::bounded::{generic::Memtable, Options};
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
  pub fn upper_bound<'a, Q>(&'a self, version: u64, key: Bound<&Q>) -> Option<Entry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
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
  /// use memorable::bounded::{generic::Memtable, Options};
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
  pub fn lower_bound<'a, Q>(&'a self, version: u64, key: Bound<&Q>) -> Option<Entry<'a, K, V>>
  where
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.range::<Q, _>(version, (key, Bound::Unbounded)).next()
  }

  /// Returns an iterator over the entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  pub fn iter_points_all_versions(&self, version: u64) -> IterAllPoints<'_, K, V> {
    self.inner.skl.iter_all_versions(version)
  }

  /// Returns an iterator over the bulk deletion entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::{Memtable, MaybeStructured}, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<u32, str>>().unwrap();
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
  pub fn iter_bulk_deletions(&self, version: u64) -> BulkDeletionIter<'_, K, V> {
    BulkDeletionIter::new(version, self)
  }

  /// Returns an iterator over the bulk deletion entries (all versions) of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable<u32, str>>().unwrap();
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
  pub fn iter_bulk_deletions_all_versions(&self, version: u64) -> BulkDeletionIterAll<'_, K, V> {
    BulkDeletionIterAll::new(version, self)
  }

  /// Returns an iterator over the bulk update entries of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  pub fn iter_bulk_updates(&self, version: u64) -> BulkUpdateIter<'_, K, V> {
    BulkUpdateIter::new(version, self)
  }

  /// Returns an iterator over the bulk update entries (all versions) of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  pub fn iter_bulk_updates_all_versions(&self, version: u64) -> BulkUpdateIterAll<'_, K, V> {
    BulkUpdateIterAll::new(version, self)
  }

  /// Returns an iterator over a subset of the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  pub fn range<'a, Q, R>(&'a self, version: u64, r: R) -> Range<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
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
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<u32, str>>().unwrap();
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
  pub fn range_points<'a, Q, R>(&'a self, version: u64, r: R) -> PointRange<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
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
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable = Options::new().alloc::<Memtable::<u32, str>>().unwrap();
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
  pub fn range_all_points<'a, Q, R>(&'a self, version: u64, r: R) -> RangeAllPoints<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    self.inner.skl.range_all_versions(version, r)
  }

  /// Returns an iterator over a subset of range deletions entries in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<u32, str>>().unwrap();
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
  ) -> BulkDeletionRange<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    BulkDeletionRange::new(version, self, r)
  }

  /// Returns an iterator over a subset of range key entries (all versions) in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<u32, str>>().unwrap();
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
  ) -> BulkDeletionRangeAll<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    BulkDeletionRangeAll::new(version, self, r)
  }

  /// Returns an iterator over a subset of range key entries in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  pub fn range_bulk_updates<'a, Q, R>(
    &'a self,
    version: u64,
    r: R,
  ) -> BulkUpdateRange<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    BulkUpdateRange::new(version, self, r)
  }

  /// Returns an iterator over a subset of range key entries (all versions) in the memtable within the specified range.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable = Options::new().alloc::<Memtable::<usize, str>>().unwrap();
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
  ) -> BulkUpdateRangeAll<'a, K, V, Q, R>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Comparable<K::Ref<'a>>,
  {
    BulkUpdateRangeAll::new(version, self, r)
  }
}

impl<K, V> Memtable<K, V>
where
  K: ?Sized + Type + 'static,
  for<'a> K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type + 'static,
{
  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable: Memtable<str, str> = Options::new().alloc().unwrap();
  /// memtable.insert(1, "key", "value").unwrap();
  ///
  /// assert_eq!(*memtable.get(1, "key").unwrap().value(), "value");
  /// ```
  pub fn insert<'a, 'b: 'a>(
    &'a self,
    version: u64,
    key: impl Into<MaybeStructured<'b, K>>,
    value: impl Into<MaybeStructured<'b, V>>,
  ) -> Result<(), Among<K::Error, V::Error, skl::error::Error>> {
    self.inner.skl.insert(version, key, value).map(|_| ())
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options, ValueBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable<str, str> = Options::new().alloc().unwrap();
  /// memtable.insert_with_value_builder(1, "key", ValueBuilder::new(5, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"value"))).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, "key").unwrap().value(), "value");
  /// ```
  pub fn insert_with_value_builder<'a, E>(
    &'a self,
    version: u64,
    key: impl Into<MaybeStructured<'a, K>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<(), Among<K::Error, E, skl::error::Error>> {
    self
      .inner
      .skl
      .insert_with_value_builder(version, key, value_builder)
      .map(|_| ())
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options, KeyBuilder, ValueBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable<str, str> = Options::new().alloc().unwrap();
  /// memtable.insert_with_builders(1, KeyBuilder::new(3, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"key")), ValueBuilder::new(5, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"value"))).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, "key").unwrap().value(), "value");
  /// ```
  #[allow(single_use_lifetimes)]
  pub fn insert_with_builders<'a, KE, VE>(
    &'a self,
    version: u64,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<(), Among<KE, VE, skl::error::Error>> {
    self
      .inner
      .skl
      .insert_with_builders(version, key_builder, value_builder)
      .map(|_| ())
  }

  /// Insert a tombstone entry for the specified `key` from the memtable and returns it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  ///
  /// let memtable: Memtable<str, str> = Options::new().alloc().unwrap();
  /// memtable.insert(0, "key", "value").unwrap();
  /// memtable.remove(1, "key").unwrap();
  /// assert!(memtable.get(0, "key").is_some());
  /// assert!(memtable.get(1, "key").is_none());
  /// ```
  pub fn remove<'a>(
    &'a self,
    version: u64,
    key: impl Into<MaybeStructured<'a, K>>,
  ) -> Result<(), Either<K::Error, Error>> {
    self.inner.skl.get_or_remove(version, key).map(|_| ())
  }

  /// Insert a tombstone entry for the specified `key` from the memtable and returns it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options, KeyBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable<str, str> = Options::new().alloc().unwrap();
  /// memtable.insert(0, "key", "value").unwrap();
  /// memtable.remove_with_builder(1, KeyBuilder::new(3, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"key"))).unwrap();
  /// assert!(memtable.get(0, "key").is_some());
  /// assert!(memtable.get(1, "key").is_none());
  /// ```
  #[inline]
  pub fn remove_with_builder<'a, E>(
    &'a self,
    version: u64,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<(), Either<E, Error>> {
    self
      .inner
      .skl
      .get_or_remove_with_builder(version, key_builder)
      .map(|_| ())
  }

  /// Inserts a range deletion entry into the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable: Memtable<i32, i32> = Options::new().alloc().unwrap();
  ///
  /// memtable.insert(0, &1, &1).unwrap();
  /// memtable.insert(0, &2, &2).unwrap();
  /// memtable.insert(0, &3, &3).unwrap();
  /// memtable.insert(0, &4, &4).unwrap();
  ///
  /// memtable.remove_range(1, 2..).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, &1).unwrap().value(), 1);
  /// assert!(memtable.get(1, &2).is_none());
  /// assert!(memtable.get(1, &3).is_none());
  /// assert!(memtable.get(1, &4).is_none());
  /// ```
  pub fn remove_range<'a, Q, R>(
    &'a self,
    version: u64,
    range: R,
  ) -> Result<(), Either<K::Error, Error>>
  where
    R: RangeBounds<Q> + 'a,
    Q: ?Sized + IntoMaybeStructured<K> + 'a,
  {
    let range = {
      let start = range.start_bound().map(IntoMaybeStructured::to_maybe);
      let end = range.end_bound().map(IntoMaybeStructured::to_maybe);
      (start, end)
    };

    let start = RangeKeyEncoder::new(range.start_bound().map(|k| *k));
    let span = RangeDeletionSpan::new(range.end_bound().map(|k| *k));
    let kb = |buf: &mut VacantBuffer<'_>| start.encode(buf);
    let vb = |buf: &mut VacantBuffer<'_>| span.encode(buf);
    self
      .inner
      .range_del_skl
      .insert_with_builders(
        version,
        KeyBuilder::new(start.encoded_len, kb),
        ValueBuilder::new(span.encoded_len, vb),
      )
      .map(|_| ())
      .map_err(|e| match e {
        Among::Left(e) => Either::Left(e),
        Among::Middle(e) => Either::Left(e),
        Among::Right(e) => Either::Right(e),
      })
  }

  /// Update entries within a range to the given value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{generic::Memtable, Options};
  /// use core::ops::Bound;
  ///
  /// let memtable: Memtable<i32, i32> = Options::new().alloc().unwrap();
  ///
  /// memtable.insert(0, &1, &1).unwrap();
  /// memtable.insert(0, &2, &2).unwrap();
  /// memtable.insert(0, &3, &3).unwrap();
  /// memtable.insert(0, &4, &4).unwrap();
  ///
  /// memtable.update_range(1, 2.., &5).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, &1).unwrap().value(), 1);
  /// assert_eq!(*memtable.get(1, &2).unwrap().value(), 5);
  /// assert_eq!(*memtable.get(1, &3).unwrap().value(), 5);
  /// assert_eq!(*memtable.get(1, &4).unwrap().value(), 5);
  /// ```
  pub fn update_range<'a, Q, R>(
    &self,
    version: u64,
    range: R,
    value: impl Into<MaybeStructured<'a, V>>,
  ) -> Result<(), Among<K::Error, V::Error, Error>>
  where
    R: RangeBounds<Q> + 'a,
    Q: ?Sized + IntoMaybeStructured<K> + 'a,
  {
    let range = {
      let start = range.start_bound().map(IntoMaybeStructured::to_maybe);
      let end = range.end_bound().map(IntoMaybeStructured::to_maybe);
      (start, end)
    };
    let start = RangeKeyEncoder::new(range.start_bound().map(|k| *k));
    let span = RangeUpdateSpan::new(range.end_bound().map(|k| *k), value.into());
    let kb = |buf: &mut VacantBuffer<'_>| start.encode(buf);
    let vb = |buf: &mut VacantBuffer<'_>| span.encode(buf);
    self
      .inner
      .range_key_skl
      .insert_with_builders(
        version,
        KeyBuilder::new(start.encoded_len, kb),
        ValueBuilder::new(span.encoded_len, vb),
      )
      .map(|_| ())
      .map_err(|e| match e {
        Among::Middle(e) => Among::from_either_to_left_middle(e),
        Among::Left(e) => Among::Left(e),
        Among::Right(e) => Among::Right(e),
      })
  }
}

impl<K, V> Memtable<K, V>
where
  K: ?Sized + Type + 'static,
  for<'a> K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type + 'static,
{
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
      .range::<Query<K::Ref<'_>>, _>(query_version, ..=bound)
      .any(|ent| {
        let del_ent_version = ent.version();
        let span = ent.value();
        (version <= del_ent_version && del_ent_version <= query_version)
          && span.contains(ent.key(), key)
      });

    if shadow {
      return ControlFlow::Continue(ent);
    }

    // find the range key entry with maximum version that shadow the next entry.
    let range_ent = self
      .inner
      .range_key_skl
      .range::<Query<K::Ref<'_>>, _>(query_version, ..=bound)
      .filter(|ent| {
        let range_ent_version = ent.version();
        let span = ent.value();
        (version <= range_ent_version && range_ent_version <= query_version)
          && span.contains(ent.key(), key)
      })
      .max_by_key(|e| e.version());

    // check if the next entry's value should be shadowed by the range key entries.
    if let Some(range_ent) = range_ent {
      let value = EntryValue::<K, V>::Range(range_ent);
      ControlFlow::Break(Some(Entry::new(self, query_version, ent, value)))
    } else {
      let value = EntryValue::<K, V>::Point(*ent.value());
      ControlFlow::Break(Some(Entry::new(self, query_version, ent, value)))
    }
  }
}

use sealed::IntoMaybeStructured;
mod sealed {
  use super::MaybeStructured;

  pub trait IntoMaybeStructured<T: ?Sized> {
    fn to_maybe(&self) -> MaybeStructured<'_, T>;
  }

  impl<T: ?Sized> IntoMaybeStructured<T> for T {
    #[inline]
    fn to_maybe(&self) -> MaybeStructured<'_, T> {
      MaybeStructured::from(self)
    }
  }

  impl<T: ?Sized> IntoMaybeStructured<T> for &T {
    #[inline]
    fn to_maybe(&self) -> MaybeStructured<'_, T> {
      MaybeStructured::from(*self)
    }
  }

  impl<T: ?Sized> IntoMaybeStructured<T> for MaybeStructured<'_, T> {
    #[inline]
    fn to_maybe(&self) -> MaybeStructured<'_, T> {
      *self
    }
  }
}
