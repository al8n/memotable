use {
  super::{BulkDeletionEntry, BulkUpdateEntry, Entry, EntryValue, Memtable, StartKey, RangeKeyComparator},
  core::{
    borrow::Borrow,
    ops::{ControlFlow, RangeBounds},
  },
  skl::dynamic::{
    multiple_version::{sync::{Iter as MapIter, IterAll, Range as MapRange, RangeAll}, Map},
    Comparator,
  },
  std::sync::Arc,
};

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of a `Memtable`.
pub type IterAllPoints<'a, C> = IterAll<'a, C>;

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of a `Memtable` within the specified range.
pub type RangeAllPoints<'a, C, Q, R> = RangeAll<'a, Q, R, C>;

/// An iterator over the entries of a `Memtable`.
pub struct Iter<'a, C> {
  table: &'a Memtable<C>,
  iter: MapIter<'a, Arc<C>>,
  query_version: u64,
}

impl<'a, C> Iter<'a, C>
where
  C: Comparator,
{
  pub(super) fn new(version: u64, table: &'a Memtable<C>) -> Self {
    Self {
      iter: table.inner.skl.iter(version),
      query_version: version,
      table,
    }
  }
}

impl<'a, C> Iterator for Iter<'a, C>
where
  C: Comparator,
{
  type Item = Entry<'a, C>;

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

impl<C> DoubleEndedIterator for Iter<'_, C>
where
  C: Comparator,
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
pub struct Range<'a, C, Q, R>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  table: &'a Memtable<C>,
  iter: MapRange<'a, Arc<C>, Q, R>,
  query_version: u64,
}

impl<'a, C, Q, R> Range<'a, C, Q, R>
where
  C: Comparator,
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  pub(super) fn new(version: u64, table: &'a Memtable<C>, r: R) -> Self {
    Self {
      iter: table.inner.skl.range(version, r),
      query_version: version,
      table,
    }
  }
}

impl<'a, C, Q, R> Iterator for Range<'a, C, Q, R>
where
  C: Comparator,
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  type Item = Entry<'a, C>;

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

impl<C, Q, R> DoubleEndedIterator for Range<'_, C, Q, R>
where
  C: Comparator,
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
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
      pub struct $name<'a, C> {
        table: &'a Memtable<C>,
        iter: $iter<'a, RangeKeyComparator<C>>,
        query_version: u64,
      }

      impl<'a, C> $name<'a, C>
      where
        C: Comparator
      {
        #[inline]
        pub(super) fn new(version: u64, table: &'a Memtable<C>) -> Self {
          Self {
            iter: table.inner.$iterator.$method(version),
            query_version: version,
            table,
          }
        }
      }

      impl<'a, C> Iterator for $name<'a, C>
      where
        C: Comparator
      {
        type Item = $entry<'a, C>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
          self
            .iter
            .next()
            .map(|ent| $entry::$new(self.table, self.query_version, ent))
        }
      }

      impl<C> DoubleEndedIterator for $name<'_, C>
      where
        C: Comparator
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
      pub struct $name<'a, C, Q, R>
      where
        C: Comparator,
        R: RangeBounds<Q>,
        Q: ?Sized + Borrow<[u8]>,
      {
        table: &'a Memtable<C>,
        iter: $iter<'a, RangeKeyComparator<C>, Q, R>,
        query_version: u64,
      }

      impl<'a, C, Q, R> $name<'a, C, Q, R>
      where
        C: Comparator,
        R: RangeBounds<Q>,
        Q: ?Sized + Borrow<[u8]>,
      {
        pub(super) fn new(version: u64, table: &'a Memtable<C>, range: R) -> Self {
          Self {
            iter: table
              .inner
              .$iterator
              .$method(version, range),
            query_version: version,
            table,
          }
        }
      }

      impl<'a, C, Q, R> Iterator for $name<'a, C, Q, R>
      where
        C: Comparator,
        R: RangeBounds<Q>,
        Q: ?Sized + Borrow<[u8]>,
      {
        type Item = $entry<'a, C>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
          self
            .iter
            .next()
            .map(|ent| $entry::$new(self.table, self.query_version, ent))
        }
      }

      impl<C, Q, R> DoubleEndedIterator for $name<'_, C, Q, R>
      where
        C: Comparator,
        R: RangeBounds<Q>,
        Q: ?Sized + Borrow<[u8]>,
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
pub struct PointIter<'a, C> {
  table: &'a Memtable<C>,
  iter: MapIter<'a, Arc<C>>,
  query_version: u64,
}

impl<'a, C> PointIter<'a, C>
where
  C: Comparator,
{
  pub(super) fn new(version: u64, table: &'a Memtable<C>) -> Self {
    Self {
      iter: table.inner.skl.iter(version),
      query_version: version,
      table,
    }
  }
}

impl<'a, C> Iterator for PointIter<'a, C>
where
  C: Comparator,
{
  type Item = Entry<'a, C>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.iter.next().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}

impl<C> DoubleEndedIterator for PointIter<'_, C>
where
  C: Comparator,
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
pub struct PointRange<'a, C, Q, R>
where
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  table: &'a Memtable<C>,
  iter: MapRange<'a, Arc<C>, Q, R>,
  query_version: u64,
}

impl<'a, C, Q, R> PointRange<'a, C, Q, R>
where
  C: Comparator,
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  pub(super) fn new(version: u64, table: &'a Memtable<C>, r: R) -> Self {
    Self {
      iter: table.inner.skl.range(version, r),
      query_version: version,
      table,
    }
  }
}

impl<'a, C, Q, R> Iterator for PointRange<'a, C, Q, R>
where
  C: Comparator,
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  type Item = Entry<'a, C>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.iter.next().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}

impl<C, Q, R> DoubleEndedIterator for PointRange<'_, C, Q, R>
where
  C: Comparator,
  R: RangeBounds<Q>,
  Q: ?Sized + Borrow<[u8]>,
{
  #[inline]
  fn next_back(&mut self) -> Option<Self::Item> {
    self.iter.next_back().map(|ent| {
      let val = ent.value();
      Entry::new(self.table, self.query_version, ent, EntryValue::Point(val))
    })
  }
}
