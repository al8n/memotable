use super::{Memtable, PhantomRangeDeletionSpan, PhantomRangeKey, PhantomRangeUpdateSpan};
use core::{
  cmp::Ordering,
  ops::{Bound, ControlFlow},
};
use either::Either;
use skl::generic::{
  multiple_version::sync::{Entry as MapEntry, VersionedEntry as MapVersionedEntry},
  Comparable, KeyRef, Type,
};

pub(super) enum EntryValue<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  Range(MapEntry<'a, PhantomRangeKey<K>, PhantomRangeUpdateSpan<K, V>>),
  Point(V::Ref<'a>),
}

impl<K, V> Clone for EntryValue<'_, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  #[inline]
  fn clone(&self) -> Self {
    match self {
      Self::Range(ent) => Self::Range(ent.clone()),
      Self::Point(ent) => Self::Point(*ent),
    }
  }
}

impl<'a, K, V> EntryValue<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  #[inline]
  fn value(&self) -> &V::Ref<'a> {
    match self {
      Self::Range(ent) => ent.value().value(),
      Self::Point(ent) => ent,
    }
  }
}

/// An entry in the `Memtable`.
pub struct Entry<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  table: &'a Memtable<K, V>,
  key: MapEntry<'a, K, V>,
  value: EntryValue<'a, K, V>,
  version: u64,
  query_version: u64,
}

impl<K, V> core::fmt::Debug for Entry<'_, K, V>
where
  K: core::fmt::Debug + Type + ?Sized,
  V: core::fmt::Debug + Type + ?Sized,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("key", self.key())
      .field("value", self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<K, V> Clone for Entry<'_, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
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

impl<'a, K, V> Entry<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
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
  pub fn key(&self) -> &K::Ref<'a> {
    self.key.key()
  }

  /// Returns the value of the entry.
  #[inline]
  pub fn value(&self) -> &V::Ref<'a> {
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
  K: ?Sized + Type + 'static,
  for<'a> K::Ref<'a>: KeyRef<'a, K>,
  V: ?Sized + Type + 'static,
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
    $name:ident($span:ty)($ent:ident, $versioned_ent:ident) $( => $value:ident)?
  ),+$(,)?) => {
    $(
      $(#[$meta])*
      pub struct $name<'a, K, V>
      where
        K: ?Sized + Type,
        V: ?Sized + Type,
      {
        table: &'a Memtable<K, V>,
        ent: Either<$ent<'a, PhantomRangeKey<K>, $span>, $versioned_ent<'a, PhantomRangeKey<K>, $span>>,
        version: u64,
        query_version: u64,
      }

      impl<K, V> core::fmt::Debug for $name<'_, K, V>
      where
        K: core::fmt::Debug + Type + ?Sized,
        V: core::fmt::Debug + Type + ?Sized,
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

      impl<K, V> Clone for $name<'_, K, V>
      where
        K: ?Sized + Type,
        V: ?Sized + Type,
      {
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

      impl<'a, K, V> $name<'a, K, V>
      where
        K: ?Sized + Type,
        V: ?Sized + Type,
      {
        #[inline]
        pub(super) fn new(
          table: &'a Memtable<K, V>,
          query_version: u64,
          ent: $ent<'a, PhantomRangeKey<K>, $span>,
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
          ent: $versioned_ent<'a, PhantomRangeKey<K>, $span>,
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
          Q: ?Sized + Comparable<K::Ref<'a>>,
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
        pub fn bounds(&self) -> (Bound<&K::Ref<'a>>, Bound<&K::Ref<'a>>) {
          (self.start_bound(), self.end_bound())
        }

        /// Returns the start bound of the entry.
        #[inline]
        pub fn start_bound(&self) -> Bound<&K::Ref<'a>> {
          let k = match &self.ent {
            Either::Left(ent) => ent.key(),
            Either::Right(ent) => ent.key(),
          };

          k.bound()
        }

        /// Returns the end bound of the entry.
        #[inline]
        pub fn end_bound(&self) -> Bound<&K::Ref<'a>> {
          match &self.ent {
            Either::Left(ent) => ent.value().bound(),
            Either::Right(ent) => ent.value().unwrap().bound(),
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
          for<'b> K::Ref<'b>: KeyRef<'b, K>,
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
          for<'b> K::Ref<'b>: KeyRef<'b, K>,
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
          pub fn $value(&self) -> &V::Ref<'a> {
            match &self.ent {
              Either::Left(ent) => ent.value().value(),
              Either::Right(ent) => ent.value().unwrap().value(),
            }
          }
        )?
      }

      impl<'a, K, V> core::ops::RangeBounds<K::Ref<'a>> for $name<'a, K, V>
      where
        K: ?Sized + Type,
        V: ?Sized + Type,
      {
        #[inline]
        fn start_bound(&self) -> Bound<&K::Ref<'a>> {
          self.start_bound()
        }

        #[inline]
        fn end_bound(&self) -> Bound<&K::Ref<'a>> {
          self.end_bound()
        }
      }
    )*
  };
}

bulk_entry!(
  /// A range deletion entry in the `Memtable`.
  BulkDeletionEntry(PhantomRangeDeletionSpan<K>)(MapEntry, MapVersionedEntry),
);

bulk_entry!(
  /// A range update entry in the `Memtable`.
  BulkUpdateEntry(PhantomRangeUpdateSpan<K, V>)(MapEntry, MapVersionedEntry) => value,
);
