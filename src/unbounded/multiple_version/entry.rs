use {
  super::{KeySpan, Memtable},
  crate::unbounded::StartKey,
  crossbeam_skiplist_mvcc::nested::Entry as MapEntry,
};

pub(super) enum EntryValue<'a, K, V> {
  Range(MapEntry<'a, StartKey<K>, KeySpan<K, V>>),
  Point(&'a V),
}

impl<K, V> Clone for EntryValue<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    match self {
      Self::Range(entry) => Self::Range(entry.clone()),
      Self::Point(entry) => Self::Point(entry),
    }
  }
}

impl<'a, K, V> EntryValue<'a, K, V> {
  #[inline]
  fn value(&self) -> &'a V {
    match self {
      Self::Range(entry) => entry.value().unwrap_value(),
      Self::Point(entry) => entry,
    }
  }
}

/// An entry in the `Memtable`.
pub struct Entry<'a, K, V> {
  table: &'a Memtable<K, V>,
  key: MapEntry<'a, K, V>,
  value: EntryValue<'a, K, V>,
  version: u64,
  query_version: u64,
}

impl<K, V> core::fmt::Debug for Entry<'_, K, V>
where
  K: core::fmt::Debug,
  V: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("key", self.key())
      .field("value", self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<K, V> Clone for Entry<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      table: self.table,
      key: self.key.clone(),
      value: self.value.clone(),
      version: self.version,
      query_version: self.query_version,
    }
  }
}

impl<'a, K, V> Entry<'a, K, V> {
  #[inline]
  pub(super) fn new(
    table: &'a Memtable<K, V>,
    query_version: u64,
    key: MapEntry<'a, K, V>,
    value: EntryValue<'a, K, V>,
  ) -> Self {
    Self {
      table,
      version: key.version(),
      key,
      value,
      query_version,
    }
  }

  /// Returns the key of the entry.
  #[inline]
  pub fn key(&self) -> &'a K {
    self.key.key()
  }

  /// Returns the value of the entry.
  #[inline]
  pub fn value(&self) -> &'a V {
    self.value.value()
  }

  /// Returns the version of the entry.
  #[inline]
  pub const fn version(&self) -> u64 {
    self.version
  }
}
