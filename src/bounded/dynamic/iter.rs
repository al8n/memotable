use crate::bounded::generic::iter::{
  BulkDeletionIter as GenericBulkDeletionIter, BulkDeletionIterAll as GenericBulkDeletionIterAll,
  BulkDeletionRange as GenericBulkDeletionRange,
  BulkDeletionRangeAll as GenericBulkDeletionRangeAll, BulkUpdateIter as GenericBulkUpdateIter,
  BulkUpdateIterAll as GenericBulkUpdateIterAll, BulkUpdateRange as GenericBulkUpdateRange,
  BulkUpdateRangeAll as GenericBulkUpdateRangeAll, Iter as GenericIter,
  IterAllPoints as GenericIterAllPoints, PointIter as GenericPointIter,
  PointRange as GenericPointRange, Range as GenericRange, RangeAllPoints as GenericRangeAllPoints,
};

use super::Key;

/// An iterator in the [`Memtable`](super::Memtable).
pub type Iter<'a, C> = GenericIter<'a, Key<C>, [u8]>;

/// A point iterator in the [`Memtable`](super::Memtable).
pub type PointIter<'a, C> = GenericPointIter<'a, Key<C>, [u8]>;

/// An iterator over all points in the [`Memtable`](super::Memtable).
pub type IterAllPoints<'a, C> = GenericIterAllPoints<'a, Key<C>, [u8]>;

/// A bulk deletion iterator in the [`Memtable`](super::Memtable).
pub type BulkDeletionIter<'a, C> = GenericBulkDeletionIter<'a, Key<C>, [u8]>;

/// An iterator over all bulk deletions in the [`Memtable`](super::Memtable).
pub type BulkDeletionIterAll<'a, C> = GenericBulkDeletionIterAll<'a, Key<C>, [u8]>;

/// A bulk update iterator in the [`Memtable`](super::Memtable).
pub type BulkUpdateIter<'a, C> = GenericBulkUpdateIter<'a, Key<C>, [u8]>;

/// An iterator over all bulk updates in the [`Memtable`](super::Memtable).
pub type BulkUpdateIterAll<'a, C> = GenericBulkUpdateIterAll<'a, Key<C>, [u8]>;

/// A range in the [`Memtable`](super::Memtable).
pub type Range<'a, C, Q, R> = GenericRange<'a, Key<C>, [u8], Q, R>;

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of
/// a [`Memtable`](super::Memtable) with in a specified range.
pub type PointRange<'a, C, Q, R> = GenericPointRange<'a, Key<C>, [u8], Q, R>;

/// An iterator over the point entries (bulk-deletion and bulk-update operations will be ignored) of
/// a [`Memtable`](super::Memtable) with in a specified range.
pub type RangeAllPoints<'a, C, Q, R> = GenericRangeAllPoints<'a, Key<C>, [u8], Q, R>;

/// A bulk deletion range in the [`Memtable`](super::Memtable).
pub type BulkDeletionRange<'a, C, Q, R> = GenericBulkDeletionRange<'a, Key<C>, [u8], Q, R>;

/// A range over all bulk deletions in the [`Memtable`](super::Memtable).
pub type BulkDeletionRangeAll<'a, C, Q, R> = GenericBulkDeletionRangeAll<'a, Key<C>, [u8], Q, R>;

/// A bulk update range in the [`Memtable`](super::Memtable).
pub type BulkUpdateRange<'a, C, Q, R> = GenericBulkUpdateRange<'a, Key<C>, [u8], Q, R>;

/// A range over all bulk updates in the [`Memtable`](super::Memtable).
pub type BulkUpdateRangeAll<'a, C, Q, R> = GenericBulkUpdateRangeAll<'a, Key<C>, [u8], Q, R>;
