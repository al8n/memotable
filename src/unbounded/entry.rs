use {
  super::{KeySpan, Memtable, StartKey},
  core::ops::{Bound, ControlFlow},
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

impl<K, V> Entry<'_, K, V>
where
  K: Ord,
{
  /// Returns the next entry in the `Memtable`.
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
  /// let mut ent = memtable.first(0);
  /// while let Some(entry) = ent {
  ///   assert_eq!(entry.key(), &(num + 1));
  ///   num += 1;
  ///   ent = entry.next();
  /// }
  /// assert_eq!(num, 4);
  ///
  /// // At view 1, the memtable contains 1 entry because of remove_range..
  /// let mut num = 0;
  /// let mut ent = memtable.first(1);
  /// while let Some(entry) = ent {
  ///   assert_eq!(entry.key(), &(num + 1));
  ///   assert_eq!(*entry.value(), "one");
  ///   ent = entry.next();
  ///   num += 1;
  /// }
  /// assert_eq!(num, 1);
  ///
  /// // At view 2, the memtable contains 1 entry because of update_range, and the value is updated because of the update_range.
  /// let mut num = 0;
  /// let mut ent = memtable.first(2);
  /// while let Some(entry) = ent {
  ///   assert_eq!(entry.key(), &(num + 1));
  ///   assert_eq!(*entry.value(), "updated");
  ///   ent = entry.next();
  ///   num += 1;
  /// }
  /// assert_eq!(num, 1);
  /// ```
  #[inline]
  pub fn next(&self) -> Option<Self> {
    let mut next = self.key.next();
    while let Some(ent) = next {
      match self.table.validate(self.query_version, ent) {
        ControlFlow::Break(entry) => return entry,
        ControlFlow::Continue(ent) => next = ent.next(),
      }
    }
    None
  }

  /// Returns the previous entry in the `Memtable`.
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
  /// memtable.remove_range(1, Bound::Unbounded, Bound::Included(3));
  ///
  /// memtable.update_range(2, Bound::Included(2), Bound::Unbounded, "updated");
  ///
  /// // At view 0, the memtable contains 4 entries.
  /// let mut num = 4;
  /// let mut ent = memtable.last(0);
  /// while let Some(entry) = ent {
  ///   assert_eq!(entry.key(), &num);
  ///   ent = entry.prev();
  ///   num -= 1;
  /// }
  /// assert_eq!(num, 0);
  ///
  /// // At view 1, the memtable only contains 4 because of remove_range.
  /// let mut num = 0;
  /// let mut ent = memtable.last(1);
  /// while let Some(entry) = ent {
  ///   assert_eq!(entry.key(), &4);
  ///   assert_eq!(*entry.value(), "four");
  ///   ent = entry.prev();
  ///   num += 1;
  /// }
  /// assert_eq!(num, 1);
  ///
  /// // At view 2, the memtable only contains 4 because of update_range, and the value is updated because of the update_range.
  /// let mut num = 0;
  /// let mut ent = memtable.last(2);
  /// while let Some(entry) = ent {
  ///   assert_eq!(entry.key(), &4);
  ///   assert_eq!(*entry.value(), "updated");
  ///   ent = entry.prev();
  ///   num += 1;
  /// }
  /// assert_eq!(num, 1);
  /// ```
  #[inline]
  pub fn prev(&self) -> Option<Self> {
    let mut prev = self.key.prev();
    while let Some(ent) = prev {
      match self.table.validate(self.query_version, ent) {
        ControlFlow::Break(entry) => return entry,
        ControlFlow::Continue(ent) => prev = ent.prev(),
      }
    }
    None
  }
}

/// A range entry in the `Memtable`.
pub struct RangeEntry<'a, K, V> {
  table: &'a Memtable<K, V>,
  ent: MapEntry<'a, StartKey<K>, KeySpan<K, V>>,
  query_version: u64,
}

impl<K, V> core::fmt::Debug for RangeEntry<'_, K, V>
where
  K: core::fmt::Debug,
  V: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("RangeEntry")
      .field("version", &self.version())
      .field("start", &self.start())
      .field("end", &self.end())
      .field("value", self.value())
      .finish()
  }
}

impl<K, V> Clone for RangeEntry<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      table: self.table,
      ent: self.ent.clone(),
      query_version: self.query_version,
    }
  }
}

impl<'a, K, V> RangeEntry<'a, K, V> {
  /// Returns the start bound of the range entry.
  #[inline]
  pub fn start(&self) -> Bound<&'a K> {
    let k = self.ent.key();
    let v = self.ent.value();
    match k {
      StartKey::Key(k) => v.start_bound.as_ref().map(|_| k),
      StartKey::Minimum => Bound::Unbounded,
    }
  }

  /// Returns the end bound of the range entry.
  #[inline]
  pub fn end(&self) -> Bound<&'a K> {
    self.ent.value().end_bound.as_ref()
  }

  /// Returns the value of the range entry.
  #[inline]
  pub fn value(&self) -> &'a V {
    self.ent.value().unwrap_value()
  }

  /// Returns the version of the range entry.
  #[inline]
  pub fn version(&self) -> u64 {
    self.ent.version()
  }
}

/// A range deletion entry in the `Memtable`.
pub struct BulkDeletionEntry<'a, K, V> {
  table: &'a Memtable<K, V>,
  ent: MapEntry<'a, StartKey<K>, KeySpan<K, V>>,
  version: u64,
  query_version: u64,
}

impl<K, V> core::fmt::Debug for BulkDeletionEntry<'_, K, V>
where
  K: core::fmt::Debug,
  V: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("BulkDeletionEntry")
      .field("version", &self.version())
      .field("start_bound", &self.start_bound())
      .field("end_bound", &self.end_bound())
      .finish()
  }
}

impl<K, V> Clone for BulkDeletionEntry<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      table: self.table,
      ent: self.ent.clone(),
      version: self.version,
      query_version: self.query_version,
    }
  }
}

impl<'a, K, V> BulkDeletionEntry<'a, K, V> {
  pub(super) fn new(
    table: &'a Memtable<K, V>,
    query_version: u64,
    ent: MapEntry<'a, StartKey<K>, KeySpan<K, V>>,
  ) -> Self {
    Self {
      version: ent.version(),
      table,
      ent,
      query_version,
    }
  }

  /// Returns the bounds of the range deletion entry.
  #[inline]
  pub fn bounds(&self) -> (Bound<&'a K>, Bound<&'a K>) {
    (self.start_bound(), self.end_bound())
  }

  /// Returns the start bound of the range deletion entry.
  #[inline]
  pub fn start_bound(&self) -> Bound<&'a K> {
    let k = self.ent.key();
    let v = self.ent.value();
    match k {
      StartKey::Key(k) => v.start_bound.as_ref().map(|_| k),
      StartKey::Minimum => Bound::Unbounded,
    }
  }

  /// Returns the end bound of the range deletion entry.
  #[inline]
  pub fn end_bound(&self) -> Bound<&'a K> {
    self.ent.value().end_bound.as_ref()
  }

  /// Returns the version of the range deletion entry.
  #[inline]
  pub const fn version(&self) -> u64 {
    self.version
  }
}

impl<K, V> core::ops::RangeBounds<K> for BulkDeletionEntry<'_, K, V> {
  #[inline]
  fn start_bound(&self) -> Bound<&K> {
    self.start_bound()
  }

  #[inline]
  fn end_bound(&self) -> Bound<&K> {
    self.end_bound()
  }
}

/// A range deletion entry in the `Memtable`.
pub struct BulkUpdateEntry<'a, K, V> {
  table: &'a Memtable<K, V>,
  ent: MapEntry<'a, StartKey<K>, KeySpan<K, V>>,
  version: u64,
  query_version: u64,
}

impl<K, V> core::fmt::Debug for BulkUpdateEntry<'_, K, V>
where
  K: core::fmt::Debug,
  V: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("BulkUpdateEntry")
      .field("version", &self.version())
      .field("start_bound", &self.start_bound())
      .field("end_bound", &self.end_bound())
      .field("value", self.value())
      .finish()
  }
}

impl<K, V> Clone for BulkUpdateEntry<'_, K, V> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      table: self.table,
      ent: self.ent.clone(),
      version: self.version,
      query_version: self.query_version,
    }
  }
}

impl<'a, K, V> BulkUpdateEntry<'a, K, V> {
  pub(super) fn new(
    table: &'a Memtable<K, V>,
    query_version: u64,
    ent: MapEntry<'a, StartKey<K>, KeySpan<K, V>>,
  ) -> Self {
    Self {
      version: ent.version(),
      table,
      ent,
      query_version,
    }
  }

  /// Returns the bounds of the range update entry.
  #[inline]
  pub fn bounds(&self) -> (Bound<&'a K>, Bound<&'a K>) {
    (self.start_bound(), self.end_bound())
  }

  /// Returns the start bound of the range update entry.
  #[inline]
  pub fn start_bound(&self) -> Bound<&'a K> {
    let k = self.ent.key();
    let v = self.ent.value();
    match k {
      StartKey::Key(k) => v.start_bound.as_ref().map(|_| k),
      StartKey::Minimum => Bound::Unbounded,
    }
  }

  /// Returns the end bound of the range update entry.
  #[inline]
  pub fn end_bound(&self) -> Bound<&'a K> {
    self.ent.value().end_bound.as_ref()
  }

  /// Returns the version of the range update entry.
  #[inline]
  pub const fn version(&self) -> u64 {
    self.version
  }

  /// Returns the value of the range update entry.
  #[inline]
  pub fn value(&self) -> &'a V {
    self.ent.value().unwrap_value()
  }
}

impl<K, V> core::ops::RangeBounds<K> for BulkUpdateEntry<'_, K, V> {
  #[inline]
  fn start_bound(&self) -> Bound<&K> {
    self.start_bound()
  }

  #[inline]
  fn end_bound(&self) -> Bound<&K> {
    self.end_bound()
  }
}
