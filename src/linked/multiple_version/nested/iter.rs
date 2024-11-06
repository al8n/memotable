use {
  super::{Entry, Memtable},
  crossbeam_skiplist_mvcc::nested::Iter as MapIter,
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
      iter: table.skl.iter(version),
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
      self.table.validate(self.query_version, next)?;
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
      self.table.validate(self.query_version, prev)?;
    }
  }
}
