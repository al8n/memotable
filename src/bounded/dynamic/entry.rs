use {
  super::{
    Memtable, RangeDeletionSpan, RangeKeyComparator, RangeKeyEncoder, RangeUpdateSpan, StartKey,
  },
  core::{
    borrow::Borrow,
    cmp::Ordering,
    ops::{Bound, ControlFlow},
  },
  either::Either,
  skl::dynamic::{
    multiple_version::sync::{Entry as MapEntry, VersionedEntry as MapVersionedEntry},
    Comparator,
  },
  std::sync::Arc,
};

pub(super) enum EntryValue<'a, C> {
  Range(MapEntry<'a, RangeKeyComparator<C>>),
  Point(&'a [u8]),
}

impl<C> Clone for EntryValue<'_, C> {
  #[inline]
  fn clone(&self) -> Self {
    match self {
      Self::Range(entry) => Self::Range(entry.clone()),
      Self::Point(entry) => Self::Point(entry),
    }
  }
}

impl<'a, C> EntryValue<'a, C> {
  #[inline]
  fn value(&self) -> &'a [u8] {
    match self {
      Self::Range(entry) => entry.value(),
      Self::Point(entry) => entry,
    }
  }
}

/// An entry in the `Memtable`.
pub struct Entry<'a, C> {
  table: &'a Memtable<C>,
  key: MapEntry<'a, Arc<C>>,
  value: EntryValue<'a, C>,
  version: u64,
  query_version: u64,
}

impl<C> core::fmt::Debug for Entry<'_, C> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Entry")
      .field("key", &self.key())
      .field("value", &self.value())
      .field("version", &self.version)
      .finish()
  }
}

impl<C> Clone for Entry<'_, C> {
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

impl<'a, C> Entry<'a, C> {
  #[inline]
  pub(super) fn new(
    table: &'a Memtable<C>,
    query_version: u64,
    key: MapEntry<'a, Arc<C>>,
    value: EntryValue<'a, C>,
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
  pub fn key(&self) -> &'a [u8] {
    self.key.key()
  }

  /// Returns the value of the entry.
  #[inline]
  pub fn value(&self) -> &'a [u8] {
    self.value.value()
  }

  /// Returns the version of the entry.
  #[inline]
  pub const fn version(&self) -> u64 {
    self.version
  }
}

impl<C> Entry<'_, C>
where
  C: Comparator,
{
  /// Returns the next entry in the `Memtable`.
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  /// use core::ops::Bound;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, b"1", b"one");
  /// memtable.insert(0, b"2", b"two");
  /// memtable.insert(0, b"3", b"three");
  /// memtable.insert(0, b"4", b"four");
  ///
  /// memtable.remove_range(1, Bound::Excluded(b"1"), Bound::Unbounded);
  ///
  /// memtable.update_range(2, Bound::Unbounded, Bound::Included(b"2"), "updated");
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
  /// use memorable::bounded::dynamic::Memtable;
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
    $name:ident($span:ident)($ent:ident, $versioned_ent:ident) $( => $value:ident)?
  ),+$(,)?) => {
    $(
      $(#[$meta])*
      pub struct $name<'a, C> {
        table: &'a Memtable<C>,
        ent: Either<$ent<'a, RangeKeyComparator<C>>, $versioned_ent<'a, RangeKeyComparator<C>>>,
        key: StartKey<'a>,
        span: $span<'a>,
        version: u64,
        query_version: u64,
      }

      impl<C> core::fmt::Debug for $name<'_, C>
      {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          f.debug_struct(stringify!($name))
            .field("version", &self.version())
            .field("start_bound", &self.start_bound())
            .field("end_bound", &self.end_bound())
            $(.field("value", &self.$value()))?
            .finish()
        }
      }

      impl<C> Clone for $name<'_, C> {
        #[inline]
        fn clone(&self) -> Self {
          Self {
            table: self.table,
            ent: self.ent.clone(),
            key: self.key,
            span: self.span,
            version: self.version,
            query_version: self.query_version,
          }
        }
      }

      impl<'a, C> $name<'a, C> {
        #[inline]
        pub(super) fn new(
          table: &'a Memtable<C>,
          query_version: u64,
          ent: $ent<'a, RangeKeyComparator<C>>,
        ) -> Self {
          Self {
            version: ent.version(),
            table,
            key: RangeKeyEncoder::decode(ent.key()),
            span: $span::decode(ent.value()),
            ent: Either::Left(ent),
            query_version,
          }
        }

        #[inline]
        pub(super) fn versioned(
          table: &'a Memtable<C>,
          query_version: u64,
          ent: $versioned_ent<'a, RangeKeyComparator<C>>,
        ) -> Self {
          Self {
            version: ent.version(),
            table,
            key: RangeKeyEncoder::decode(ent.key()),
            span: $span::decode(ent.value().unwrap()),
            ent: Either::Right(ent),
            query_version,
          }
        }

        /// Returns `true` if the entry contains the key.
        #[inline]
        pub fn contains<Q>(&self, key: &Q) -> bool
        where
          Q: ?Sized + Borrow<[u8]>,
          C: Comparator,
        {
          let cmp = self.table.comparator();
          let key = key.borrow();
          (match self.start_bound() {
            Bound::Included(start) => cmp.compare(key, start) != Ordering::Less,
            Bound::Excluded(start) => cmp.compare(key, start) == Ordering::Greater,
            Bound::Unbounded => true,
          }) && (match self.end_bound() {
            Bound::Included(end) => cmp.compare(key, end) != Ordering::Greater,
            Bound::Excluded(end) => cmp.compare(key, end) == Ordering::Less,
            Bound::Unbounded => true,
          })
        }

        /// Returns the bounds of the entry.
        #[inline]
        pub fn bounds(&self) -> (Bound<&'a [u8]>, Bound<&'a [u8]>) {
          (self.start_bound(), self.end_bound())
        }

        /// Returns the start bound of the entry.
        #[inline]
        pub fn start_bound(&self) -> Bound<&'a [u8]> {
          self.key.0
        }

        /// Returns the end bound of the entry.
        #[inline]
        pub fn end_bound(&self) -> Bound<&'a [u8]> {
          self.span.end_bound
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
          C: Comparator,
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
          C: Comparator,
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
          pub const fn $value(&self) -> &'a [u8] {
            self.span.value
          }
        )?
      }

      impl<C> core::ops::RangeBounds<[u8]> for $name<'_, C> {
        #[inline]
        fn start_bound(&self) -> Bound<&[u8]> {
          self.start_bound()
        }

        #[inline]
        fn end_bound(&self) -> Bound<&[u8]> {
          self.end_bound()
        }
      }
    )*
  };
}

bulk_entry!(
  /// A range deletion entry in the `Memtable`.
  BulkDeletionEntry(RangeDeletionSpan)(MapEntry, MapVersionedEntry),
);

bulk_entry!(
  /// A range update entry in the `Memtable`.
  BulkUpdateEntry(RangeUpdateSpan)(MapEntry, MapVersionedEntry) => value,
);
