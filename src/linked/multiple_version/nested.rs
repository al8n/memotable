use {
  super::super::{KeyRange, KeySpan, RangeKind, StartKey}, crate::linked::Query, core::ops::Bound, crossbeam_skiplist::Comparable, crossbeam_skiplist_mvcc::nested::{Entry as MapEntry, SkipMap}, ref_cast::RefCast
};

pub use {entry::*, iter::Iter};

mod entry;
mod iter;

/// Memtable based on [`SkipMap`].
pub struct Memtable<K, V> {
  skl: SkipMap<K, V>,
  // key is the start bound
  range_del_skl: SkipMap<StartKey<K>, KeySpan<K, V>>,
  range_key_skl: SkipMap<StartKey<K>, KeySpan<K, V>>,
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
  /// use memtable::linked::nested::Memtable;
  ///
  /// let memtable: Memtable<i32, i32> = Memtable::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self {
      skl: SkipMap::new(),
      range_del_skl: SkipMap::new(),
      range_key_skl: SkipMap::new(),
    }
  }
}

impl<K, V> Memtable<K, V>
where
  K: Ord,
{
  /// Returns an entry with the specified `key`.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  /// 
  /// ## Example
  /// 
  /// ```rust
  /// use memorable::linked::multiple_version::nested::Memtable;
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
    let ent = self.skl.get(version, key)?;
    self.validate(version, ent)
  }

  /// Returns an iterator over the entries of the memtable.
  #[inline]
  pub fn iter(&self, version: u64) -> Iter<'_, K, V> {
    Iter::new(version, self)
  }

  fn validate<'a>(&'a self, query_version: u64, ent: MapEntry<'a, K, V>) -> Option<Entry<'a, K, V>> {
    let key = ent.key();
    let version = ent.version();

    let bound = Query::ref_cast(key);

    // check if the next entry is visible.
    // As the range_del_skl is sorted by the end key, we can use the lower_bound to find the first
    // deletion range that may cover the next entry.
    let shadow = self
      .range_del_skl
      .range::<Query<K>, _>(query_version, ..=bound)
      .any(|ent| ent.version() >= version && ent.value().within_end_bound(key));

    if shadow {
      return None;
    }

    // find the range key entry with maximum version that shadow the next entry.
    let range_ent = self
      .range_key_skl
      .range::<Query<K>, _>(query_version, ..=bound)
      .filter(|ent| ent.version() >= version && ent.value().within_end_bound(key))
      .max_by_key(|e| e.version());

    // check if the next entry's value should be shadowed by the range key entries.
    if let Some(range_ent) = range_ent {
      let value = EntryValue::<K, V>::Range(range_ent);
      Some(Entry::new(self, query_version, ent, value))
    } else {
      let value = EntryValue::<K, V>::Point(ent.value());
      Some(Entry::new(self, query_version, ent, value))
    }
  }
}

impl<K, V> Memtable<K, V>
where
  K: Ord + Send + 'static,
  V: Send + 'static,
{
  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::linked::multiple_version::nested::Memtable;
  ///
  /// let memtable = Memtable::new();
  /// memtable.insert(1, "key", "value");
  ///
  /// assert_eq!(*memtable.get(1, "key").unwrap().value(), "value");
  /// ```
  pub fn insert(&self, version: u64, key: K, value: V) {
    self.skl.insert_unchecked(version, key, value);
  }

  /// Insert a tombstone entry for the specified `key` from the memtable and returns it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::linked::multiple_version::nested::Memtable;
  ///
  /// let memtable: Memtable<&str, &str> = Memtable::new();
  /// assert!(memtable.remove(1, "invalid key").is_none());
  ///
  /// memtable.insert(0, "key", "value");
  /// assert_eq!(*memtable.remove(1, "key"), "value");
  /// ```
  pub fn remove(&self, version: u64, key: K) {
    self.skl.remove_unchecked(version, key);
  }

  /// Inserts a range deletion entry into the memtable.
  /// 
  /// ## Example
  /// 
  /// ```rust
  /// use memorable::linked::multiple_version::nested::Memtable;
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
    let span = KeySpan::new(start_bound, end, RangeKind::Deletion);
    self
      .range_del_skl
      .insert_unchecked(version, StartKey::new(start), span);
  }

  /// Update entries within a range to the given value.
  /// 
  /// ## Example
  /// 
  /// ```rust
  /// use memorable::linked::multiple_version::nested::Memtable;
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
    let span = KeySpan::new(start_bound, end, RangeKind::Set(value));
    self
      .range_key_skl
      .insert_unchecked(version, StartKey::new(start), span);
  }
}
