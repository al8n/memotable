use super::{KeySpan, Memtable, StartKey};
use core::{
  cmp::Ordering,
  ops::{Bound, ControlFlow},
};
use crossbeam_skiplist_mvcc::{
  nested::{Entry as MapEntry, VersionedEntry as MapVersionedEntry},
  Comparable,
};
use either::Either;

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

macro_rules! bulk_entry {
  ($(
    $(#[$meta:meta])*
    $name:ident($ent:ident, $versioned_ent:ident) $( => $value:ident)?
  ),+$(,)?) => {
    $(
      $(#[$meta])*
      pub struct $name<'a, K, V> {
        table: &'a Memtable<K, V>,
        ent: Either<$ent<'a, StartKey<K>, KeySpan<K, V>>, $versioned_ent<'a, StartKey<K>, KeySpan<K, V>>>,
        version: u64,
        query_version: u64,
      }

      impl<K, V> core::fmt::Debug for $name<'_, K, V>
      where
        K: core::fmt::Debug,
        V: core::fmt::Debug,
      {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          f.debug_struct(stringify!($name))
            .field("version", &self.version())
            .field("start_bound", &self.start_bound())
            .field("end_bound", &self.end_bound())
            $(.field("value", self.$value()))?
            .finish()
        }
      }

      impl<K, V> Clone for $name<'_, K, V> {
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

      impl<'a, K, V> $name<'a, K, V> {
        #[inline]
        pub(super) fn new(
          table: &'a Memtable<K, V>,
          query_version: u64,
          ent: $ent<'a, StartKey<K>, KeySpan<K, V>>,
        ) -> Self {
          Self {
            version: ent.version(),
            table,
            ent: Either::Left(ent),
            query_version,
          }
        }

        #[inline]
        pub(super) fn versioned(
          table: &'a Memtable<K, V>,
          query_version: u64,
          ent: $versioned_ent<'a, StartKey<K>, KeySpan<K, V>>,
        ) -> Self {
          Self {
            version: ent.version(),
            table,
            ent: Either::Right(ent),
            query_version,
          }
        }

        /// Returns `true` if the entry contains the key.
        #[inline]
        pub fn contains<Q>(&self, key: &Q) -> bool
        where
          Q: ?Sized + Comparable<K>,
        {
          (match self.start_bound() {
            Bound::Included(start) => key.compare(start) != Ordering::Less,
            Bound::Excluded(start) => key.compare(start) == Ordering::Greater,
            Bound::Unbounded => true,
          }) && (match self.end_bound() {
            Bound::Included(end) => key.compare(end) != Ordering::Greater,
            Bound::Excluded(end) => key.compare(end) == Ordering::Less,
            Bound::Unbounded => true,
          })
        }

        /// Returns the bounds of the entry.
        #[inline]
        pub fn bounds(&self) -> (Bound<&'a K>, Bound<&'a K>) {
          (self.start_bound(), self.end_bound())
        }

        /// Returns the start bound of the entry.
        #[inline]
        pub fn start_bound(&self) -> Bound<&'a K> {
          let (k, v) = match &self.ent {
            Either::Left(ent) => (ent.key(), ent.value()),
            Either::Right(ent) => (ent.key(), ent.value().unwrap()),
          };

          match k {
            StartKey::Key(k) => v.start_bound.as_ref().map(|_| k),
            StartKey::Minimum => Bound::Unbounded,
          }
        }

        /// Returns the end bound of the entry.
        #[inline]
        pub fn end_bound(&self) -> Bound<&'a K> {
          match &self.ent {
            Either::Left(ent) => ent.value().end_bound.as_ref(),
            Either::Right(ent) => ent.value().unwrap().end_bound.as_ref(),
          }
        }

        /// Returns the version of the entry.
        #[inline]
        pub const fn version(&self) -> u64 {
          self.version
        }

        /// Moves to the next entry.
        #[inline]
        pub fn next(&self) -> Option<Self>
        where
          K: Ord,
        {
          match &self.ent {
            Either::Left(ent) => {
              ent.next().map(|ent| $name::new(self.table, self.query_version, ent))
            },
            Either::Right(ent) => {
              ent.next().map(|ent| $name::versioned(self.table, self.query_version, ent))
            },
          }
        }

        /// Moves to the previous entry.
        #[inline]
        pub fn prev(&self) -> Option<Self>
        where
          K: Ord,
        {
          match &self.ent {
            Either::Left(ent) => {
              ent.prev().map(|ent| $name::new(self.table, self.query_version, ent))
            },
            Either::Right(ent) => {
              ent.prev().map(|ent| $name::versioned(self.table, self.query_version, ent))
            },
          }
        }

        $(
          /// Returns the value of the entry.
          #[inline]
          pub fn $value(&self) -> &'a V {
            match &self.ent {
              Either::Left(ent) => ent.value().unwrap_value(),
              Either::Right(ent) => ent.value().unwrap().unwrap_value(),
            }
          }
        )?
      }

      impl<K, V> core::ops::RangeBounds<K> for $name<'_, K, V> {
        #[inline]
        fn start_bound(&self) -> Bound<&K> {
          self.start_bound()
        }

        #[inline]
        fn end_bound(&self) -> Bound<&K> {
          self.end_bound()
        }
      }
    )*
  };
}

bulk_entry!(
  /// A range deletion entry in the `Memtable`.
  BulkDeletionEntry(MapEntry, MapVersionedEntry),
);

bulk_entry!(
  /// A range update entry in the `Memtable`.
  BulkUpdateEntry(MapEntry, MapVersionedEntry) => value,
);
