use super::{
  BulkDeletionEntry, BulkUpdateEntry, Entry, EntryValue, KeySpan, Memtable, Query, QueryRange,
  StartKey,
};
use core::ops::{ControlFlow, RangeBounds};
use crossbeam_skiplist_mvcc::{
  nested::{Iter as MapIter, IterAll, Range as MapRange, RangeAll},
  Comparable,
};

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of a `Memtable`.
pub type IterAllPoints<'a, K, V> = IterAll<'a, K, V>;

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of a `Memtable` within the specified range.
pub type RangeAllPoints<'a, K, V, Q, R> = RangeAll<'a, Q, R, K, V>;

/// An iterator over the entries of a `Memtable`.
pub struct Iter<'a, K, V> {
  table: &'a Memtable<K, V>,
  iter: MapIter<'a, K, V>,
  query_version: u64,
}

impl<'a, K, V> Iter<'a, K, V>
where
  K: Ord,
{
  pub(super) fn new(version: u64, table: &'a Memtable<K, V>) -> Self {
    Self {
      iter: table.inner.skl.iter(version),
      query_version: version,
      table,
    }
  }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
  K: Ord,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let next = self.iter.next()?;
      match self.table.validate(self.query_version, next) {
        ControlFlow::Break(entry) => return entry,
        ControlFlow::Continue(_) => continue,
      }
    }
  }
}

impl<K, V> DoubleEndedIterator for Iter<'_, K, V>
where
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    loop {
      let prev = self.iter.next_back()?;
      match self.table.validate(self.query_version, prev) {
        ControlFlow::Break(entry) => return entry,
        ControlFlow::Continue(_) => continue,
      }
    }
  }
}

/// An iterator over the entries of a `Memtable`.
pub struct Range<'a, K, V, Q, R>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  table: &'a Memtable<K, V>,
  iter: MapRange<'a, Q, R, K, V>,
  query_version: u64,
}

impl<'a, K, V, Q, R> Range<'a, K, V, Q, R>
where
  K: Ord,
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  pub(super) fn new(version: u64, table: &'a Memtable<K, V>, r: R) -> Self {
    Self {
      iter: table.inner.skl.range(version, r),
      query_version: version,
      table,
    }
  }
}

impl<'a, K, V, Q, R> Iterator for Range<'a, K, V, Q, R>
where
  K: Ord,
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let next = self.iter.next()?;
      match self.table.validate(self.query_version, next) {
        ControlFlow::Break(entry) => return entry,
        ControlFlow::Continue(_) => continue,
      }
    }
  }
}

impl<K, V, Q, R> DoubleEndedIterator for Range<'_, K, V, Q, R>
where
  K: Ord,
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    loop {
      let prev = self.iter.next_back()?;
      match self.table.validate(self.query_version, prev) {
        ControlFlow::Break(entry) => return entry,
        ControlFlow::Continue(_) => continue,
      }
    }
  }
}

macro_rules! bulk_iter {
  (
    $(
      $(#[$meta:meta])*
      $name:ident::$new:ident($iter:ident, $entry:ident).$iterator:ident.$method:ident
    ), +$(,)?
  ) => {
    $(
      $(#[$meta])*
      pub struct $name<'a, K, V> {
        table: &'a Memtable<K, V>,
        iter: $iter<'a, StartKey<K>, KeySpan<K, V>>,
        query_version: u64,
      }

      impl<'a, K, V> $name<'a, K, V>
      where
        K: Ord,
      {
        #[inline]
        pub(super) fn new(version: u64, table: &'a Memtable<K, V>) -> Self {
          Self {
            iter: table.inner.$iterator.$method(version),
            query_version: version,
            table,
          }
        }
      }

      impl<'a, K, V> Iterator for $name<'a, K, V>
      where
        K: Ord,
      {
        type Item = $entry<'a, K, V>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
          self
            .iter
            .next()
            .map(|ent| $entry::$new(self.table, self.query_version, ent))
        }
      }

      impl<K, V> DoubleEndedIterator for $name<'_, K, V>
      where
        K: Ord,
      {
        #[inline]
        fn next_back(&mut self) -> Option<Self::Item> {
          self
            .iter
            .next_back()
            .map(|ent| $entry::$new(self.table, self.query_version, ent))
        }
      }
    )*
  };
}

bulk_iter!(
  /// An iterator over the range deletion entries of a `Memtable`.
  BulkDeletionIter::new(MapIter, BulkDeletionEntry).range_del_skl.iter,
  /// An iterator over the range update entries of a `Memtable`.
  BulkUpdateIter::new(MapIter, BulkUpdateEntry).range_key_skl.iter,
  /// An iterator over the range deletion entries of a `Memtable`.
  BulkDeletionIterAll::versioned(IterAll, BulkDeletionEntry).range_del_skl.iter_all_versions,
  /// An iterator over the range update entries of a `Memtable`.
  BulkUpdateIterAll::versioned(IterAll, BulkUpdateEntry).range_key_skl.iter_all_versions,
);

macro_rules! bulk_range {
  (
    $(
      $(#[$meta:meta])*
      $name:ident::$new:ident($iter:ident, $entry:ident).$iterator:ident.$method:ident
    ), +$(,)?
  ) => {
    $(
      $(#[$meta])*
      pub struct $name<'a, K, V, Q, R>
      where
        K: Ord,
        R: RangeBounds<Q>,
        Q: ?Sized + Comparable<K>,
      {
        table: &'a Memtable<K, V>,
        iter: $iter<'a, Query<K, Q>, QueryRange<K, Q, R>, StartKey<K>, KeySpan<K, V>>,
        query_version: u64,
      }

      impl<'a, K, V, Q, R> $name<'a, K, V, Q, R>
      where
        K: Ord,
        R: RangeBounds<Q>,
        Q: ?Sized + Comparable<K>,
      {
        pub(super) fn new(version: u64, table: &'a Memtable<K, V>, range: R) -> Self {
          Self {
            iter: table
              .inner
              .$iterator
              .$method(version, QueryRange::new(range)),
            query_version: version,
            table,
          }
        }
      }

      impl<'a, K, V, Q, R> Iterator for $name<'a, K, V, Q, R>
      where
        K: Ord,
        R: RangeBounds<Q>,
        Q: ?Sized + Comparable<K>,
      {
        type Item = $entry<'a, K, V>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
          self
            .iter
            .next()
            .map(|ent| $entry::$new(self.table, self.query_version, ent))
        }
      }

      impl<K, V, Q, R> DoubleEndedIterator for $name<'_, K, V, Q, R>
      where
        K: Ord,
        R: RangeBounds<Q>,
        Q: ?Sized + Comparable<K>,
      {
        #[inline]
        fn next_back(&mut self) -> Option<Self::Item> {
          self
            .iter
            .next_back()
            .map(|ent| $entry::$new(self.table, self.query_version, ent))
        }
      }
    )*
  }
}

bulk_range!(
  /// An iterator over the range deletion entries of a `Memtable`.
  BulkDeletionRange::new(MapRange, BulkDeletionEntry).range_del_skl.range,
  /// An iterator over the range update entries of a `Memtable`.
  BulkUpdateRange::new(MapRange, BulkUpdateEntry).range_key_skl.range,
  /// An iterator over the range deletion entries (all versions) of a `Memtable`.
  BulkDeletionRangeAll::versioned(RangeAll, BulkDeletionEntry).range_del_skl.range_all_versions,
  /// An iterator over the range update entries (all versions) of a `Memtable`.
  BulkUpdateRangeAll::versioned(RangeAll, BulkUpdateEntry).range_key_skl.range_all_versions,
);

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of a `Memtable`.
pub struct PointIter<'a, K, V> {
  table: &'a Memtable<K, V>,
  iter: MapIter<'a, K, V>,
  query_version: u64,
}

impl<'a, K, V> PointIter<'a, K, V>
where
  K: Ord,
{
  pub(super) fn new(version: u64, table: &'a Memtable<K, V>) -> Self {
    Self {
      iter: table.inner.skl.iter(version),
      query_version: version,
      table,
    }
  }
}

impl<'a, K, V> Iterator for PointIter<'a, K, V>
where
  K: Ord,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.iter.next().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}

impl<K, V> DoubleEndedIterator for PointIter<'_, K, V>
where
  K: Ord,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.iter.next_back().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of a `Memtable`.
pub struct PointRange<'a, K, V, Q, R>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  table: &'a Memtable<K, V>,
  iter: MapRange<'a, Q, R, K, V>,
  query_version: u64,
}

impl<'a, K, V, Q, R> PointRange<'a, K, V, Q, R>
where
  K: Ord,
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  pub(super) fn new(version: u64, table: &'a Memtable<K, V>, r: R) -> Self {
    Self {
      iter: table.inner.skl.range(version, r),
      query_version: version,
      table,
    }
  }
}

impl<'a, K, V, Q, R> Iterator for PointRange<'a, K, V, Q, R>
where
  K: Ord,
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  type Item = Entry<'a, K, V>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.iter.next().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}

impl<K, V, Q, R> DoubleEndedIterator for PointRange<'_, K, V, Q, R>
where
  K: Ord,
  R: RangeBounds<Q>,
  Q: ?Sized + Comparable<K>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.iter.next_back().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}
