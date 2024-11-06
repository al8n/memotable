use {
  super::{Entry, Memtable},
  core::ops::{ControlFlow, RangeBounds},
  crossbeam_skiplist_mvcc::{
    nested::{Iter as MapIter, Range as MapRange},
    Comparable,
  },
};

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
