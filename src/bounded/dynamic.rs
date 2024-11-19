use core::{
  borrow::Borrow,
  cmp,
  ops::{Bound, ControlFlow, RangeBounds},
};
use std::sync::Arc;

use super::Error;

use dbutils::error::InsufficientBuffer;
use skl::{
  among::Among,
  dynamic::{
    multiple_version::{
      sync::{Entry as MapEntry, SkipMap},
      Map,
    },
    Ascend, Comparator, Equivalentor,
  },
  Allocator, Arena, KeyBuilder, VacantBuffer, ValueBuilder,
};

mod entry;
pub use entry::*;

mod iter;
pub use iter::*;

const UNBOUNDED: u8 = 0;
const INCLUDED: u8 = 1;
const EXCLUDED: u8 = 2;

struct RangeKeyComparator<C = Ascend> {
  cmp: Arc<C>,
}

impl<C> Clone for RangeKeyComparator<C> {
  #[inline]
  fn clone(&self) -> Self {
    Self {
      cmp: self.cmp.clone(),
    }
  }
}

impl<C: core::fmt::Debug> core::fmt::Debug for RangeKeyComparator<C> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("RangeKeyComparator")
      .field(&*self.cmp)
      .finish()
  }
}

impl<C: Equivalentor> Equivalentor for RangeKeyComparator<C> {
  #[inline]
  fn equivalent(&self, a: &[u8], b: &[u8]) -> bool {
    let a = RangeKeyEncoder::decode(a);
    let b = RangeKeyEncoder::decode(b);

    match (a.0, b.0) {
      (Bound::Included(a), Bound::Included(b)) => self.cmp.equivalent(a, b),
      (Bound::Included(a), Bound::Excluded(b)) => self.cmp.equivalent(a, b),
      (Bound::Included(_), Bound::Unbounded) => false,
      (Bound::Excluded(a), Bound::Included(b)) => self.cmp.equivalent(a, b),
      (Bound::Excluded(a), Bound::Excluded(b)) => self.cmp.equivalent(a, b),
      (Bound::Excluded(_), Bound::Unbounded) => false,
      (Bound::Unbounded, Bound::Included(_)) => false,
      (Bound::Unbounded, Bound::Excluded(_)) => false,
      (Bound::Unbounded, Bound::Unbounded) => true,
    }
  }
}

impl<C: Comparator> Comparator for RangeKeyComparator<C> {
  #[inline]
  fn compare(&self, a: &[u8], b: &[u8]) -> core::cmp::Ordering {
    let a = RangeKeyEncoder::decode(a);
    let b = RangeKeyEncoder::decode(b);

    match (a.0, b.0) {
      (Bound::Included(a), Bound::Included(b)) => self.cmp.compare(a, b),
      (Bound::Included(a), Bound::Excluded(b)) => self.cmp.compare(a, b),
      (Bound::Included(_), Bound::Unbounded) => cmp::Ordering::Greater,
      (Bound::Excluded(a), Bound::Included(b)) => self.cmp.compare(a, b),
      (Bound::Excluded(a), Bound::Excluded(b)) => self.cmp.compare(a, b),
      (Bound::Excluded(_), Bound::Unbounded) => cmp::Ordering::Greater,
      (Bound::Unbounded, Bound::Included(_)) => cmp::Ordering::Less,
      (Bound::Unbounded, Bound::Excluded(_)) => cmp::Ordering::Less,
      (Bound::Unbounded, Bound::Unbounded) => cmp::Ordering::Equal,
    }
  }
}

#[derive(Copy, Clone)]
struct StartKey<'a>(Bound<&'a [u8]>);

impl StartKey<'_> {
  #[inline]
  fn len(&self) -> usize {
    match self.0 {
      Bound::Included(key) | Bound::Excluded(key) => key.len() + 1,
      Bound::Unbounded => 1,
    }
  }
}

struct RawKeySpan<'a>(&'a [u8]);

impl<'a> RawKeySpan<'a> {
  #[inline]
  fn range(&self, start_key: &'a [u8]) -> impl RangeBounds<[u8]> + 'a {
    let (bound, key) = start_key.split_at(1);
    let (start_bound, remaining) = self.0.split_at(1);
    let start_bound = match bound[0] {
      UNBOUNDED => Bound::Unbounded,
      _ => match start_bound[0] {
        UNBOUNDED => Bound::Unbounded,
        INCLUDED => Bound::Included(key),
        EXCLUDED => Bound::Excluded(key),
        _ => unreachable!("invalid bound byte"),
      },
    };

    let (end_bound, value) = remaining.split_at(1);
    let end_bound = match end_bound[0] {
      UNBOUNDED => Bound::Unbounded,
      INCLUDED => Bound::Included(value),
      EXCLUDED => Bound::Excluded(value),
      _ => unreachable!("invalid bound byte"),
    };

    (start_bound, end_bound)
  }
}

struct Inner<C = Ascend> {
  skl: SkipMap<Arc<C>>,
  // key is the start bound
  range_del_skl: SkipMap<RangeKeyComparator<C>>,
  range_key_skl: SkipMap<RangeKeyComparator<C>>,
  cmp: Arc<C>,
}

/// Memtable with dynamic key-value types based on bounded `SkipList`.
///
/// All APIs are designed to be lock-free, but it is the user's responsibility to ensure that the
/// `version` is monotonically increasing to promise linear and avoid ABA problems.
///
/// ## Entry Priority
///
/// If the point entry has the same version as the range entry, the point entry will be shadowed by
/// the range entry, which means range entry has higher priority.
///
/// Besides, range remove entry has higher priority than range set entry.
///
/// ```rust
/// use memorable::bounded::dynamic::Memtable;
/// use core::ops::Bound;
///
/// let memtable = Memtable::new();
///
/// memtable.insert(0, b"1", b"v1");
/// memtable.insert(0, b"2", b"v2");
/// memtable.insert(0, b"3", b"v3");
///
/// memtable.remove_range(0, Bound::Included(b"2"), Bound::Unbounded);
///
/// memtable.update_range(0, Bound::Included(b"1"), Bound::Unbounded, "updated");
///
/// assert_eq!(*memtable.get(0, b"1").unwrap().value(), b"updated");
/// assert!(memtable.get(0, b"2").is_none());
/// assert!(memtable.get(0, b"3").is_none());
/// ```
///
/// In the above example, if we invoke get(1) at version 0, the result will be "updated" because the
/// range set entry has higher priority than the point entry and shadowed its value.
///
/// If we invoke get(2) at version 0, the result will be None because the range remove entry has
/// higher priority than the point entry and shadowed its value.
pub struct Memtable<C = Ascend> {
  inner: Arc<Inner<C>>,
}

impl<C> Memtable<C> {
  /// Returns the active reference count of the memtable.
  #[inline]
  pub fn refs(&self) -> usize {
    // `skl`, `range_del_skl`, and `range_key_skl` are sharing the same underlying allocator.
    // So we only need to check one of them.
    self.inner.skl.allocator().refs()
  }

  #[inline]
  fn comparator(&self) -> &C {
    &self.inner.cmp
  }
}

impl<C> Memtable<C>
where
  C: Comparator,
{
  /// Returns `true` if the map contains a value for the specified key.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  ///
  /// let ages = Memtable::new();
  /// ages.insert(0, "Bill Gates", 64);
  ///
  /// assert!(ages.contains_key(0, &"Bill Gates"));
  /// assert!(!ages.contains_key(0, &"Steve Jobs"));
  /// ```
  #[inline]
  pub fn contains_key<Q>(&self, version: u64, key: &Q) -> bool
  where
    Q: ?Sized + Borrow<[u8]>,
  {
    self.get(version, key).is_some()
  }

  /// Returns an entry with the specified `key`.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  ///
  /// let memtable: Memtable<i32, i32> = Memtable::new();
  ///
  /// memtable.insert(0, 1, 1);
  /// assert_eq!(*memtable.get(0, &1).unwrap().value(), 1);
  /// ```
  #[inline]
  pub fn get<Q>(&self, version: u64, key: &Q) -> Option<Entry<'_, C>>
  where
    Q: ?Sized + Borrow<[u8]>,
  {
    let ent = self.inner.skl.get(version, key)?;
    match self.validate(version, ent) {
      ControlFlow::Break(entry) => entry,
      ControlFlow::Continue(_) => None,
    }
  }

  /// Returns the first entry in the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  ///
  /// let first = memtable.first(0).unwrap();
  /// assert_eq!(*first.value(), "one");
  /// ```
  #[inline]
  pub fn first(&self, version: u64) -> Option<Entry<'_, C>> {
    // self.iter(version).next()
    todo!()
  }

  /// Returns the last entry in the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  ///
  /// let memtable = Memtable::<usize, &'static str>::new();
  ///
  /// memtable.insert(0, 1, "one");
  /// memtable.insert(0, 2, "two");
  ///
  /// let last = memtable.last(0).unwrap();
  /// assert_eq!(*last.value(), "two");
  /// ```
  #[inline]
  pub fn last(&self, version: u64) -> Option<Entry<'_, C>> {
    // self.iter(version).next_back()
    todo!()
  }

  /// Returns an [`Entry`] pointing to the highest element whose key is below
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = Memtable::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let less_than_eight = numbers.upper_bound(0, Excluded(&8)).unwrap();
  /// assert_eq!(*less_than_eight.value(), "seven");
  ///
  /// let less_than_six = numbers.upper_bound(0, Excluded(&6));
  /// assert!(less_than_six.is_none());
  /// ```
  #[inline]
  pub fn upper_bound<Q>(&self, version: u64, key: Bound<&Q>) -> Option<Entry<'_, C>>
  where
    Q: ?Sized + Borrow<[u8]>,
  {
    // self
    //   .range::<Q, _>(version, (Bound::Unbounded, key))
    //   .next_back()
    todo!()
  }

  /// Returns an [`Entry`] pointing to the lowest element whose key is above
  /// the given bound. If no such element is found then `None` is
  /// returned.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  /// use std::ops::Bound::*;
  ///
  /// let numbers = Memtable::new();
  /// numbers.insert(0, 6, "six");
  /// numbers.insert(0, 7, "seven");
  /// numbers.insert(0, 12, "twelve");
  ///
  /// let greater_than_five = numbers.lower_bound(0, Excluded(&5)).unwrap();
  /// assert_eq!(*greater_than_five.value(), "six");
  ///
  /// let greater_than_six = numbers.lower_bound(0, Excluded(&6)).unwrap();
  /// assert_eq!(*greater_than_six.value(), "seven");
  ///
  /// let greater_than_thirteen = numbers.lower_bound(0, Excluded(&13));
  /// assert!(greater_than_thirteen.is_none());
  /// ```
  #[inline]
  pub fn lower_bound<Q>(&self, version: u64, key: Bound<&Q>) -> Option<Entry<'_, C>>
  where
    Q: ?Sized + Borrow<[u8]>,
  {
    // self.range::<Q, _>(version, (key, Bound::Unbounded)).next()
    todo!()
  }
}

impl<C> Memtable<C>
where
  C: Comparator,
{
  fn validate<'a>(
    &'a self,
    query_version: u64,
    ent: MapEntry<'a, Arc<C>>,
  ) -> ControlFlow<Option<Entry<'a, C>>, MapEntry<'a, Arc<C>>> {
    let key = ent.key();
    let version = ent.version();
    let bound = key;

    // check if the next entry is visible.
    // As the range_del_skl is sorted by the end key, we can use the lower_bound to find the first
    // deletion range that may cover the next entry.
    let shadow = self
      .inner
      .range_del_skl
      .range(query_version, ..=bound)
      .any(|ent| {
        let del_ent_version = ent.version();
        (version <= del_ent_version && del_ent_version <= query_version)
          && RawKeySpan(ent.value()).range(ent.key()).contains(key)
      });

    if shadow {
      return ControlFlow::Continue(ent);
    }

    // find the range key entry with maximum version that shadow the next entry.
    let range_ent = self
      .inner
      .range_key_skl
      .range(query_version, ..=bound)
      .filter(|ent| {
        let range_ent_version = ent.version();
        (version <= range_ent_version && range_ent_version <= query_version)
          && RawKeySpan(ent.value()).range(ent.key()).contains(key)
      })
      .max_by_key(|e| e.version());

    // check if the next entry's value should be shadowed by the range key entries.
    if let Some(range_ent) = range_ent {
      let value = EntryValue::<C>::Range(range_ent);
      ControlFlow::Break(Some(Entry::new(self, query_version, ent, value)))
    } else {
      let value = EntryValue::<C>::Point(ent.value());
      ControlFlow::Break(Some(Entry::new(self, query_version, ent, value)))
    }
  }
}

impl<C> Memtable<C>
where
  C: Comparator,
{
  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  ///
  /// let memtable = Memtable::new();
  /// memtable.insert(1, "key", "value");
  ///
  /// assert_eq!(*memtable.get(1, "key").unwrap().value(), "value");
  /// ```
  pub fn insert(
    &self,
    version: u64,
    key: impl Borrow<[u8]>,
    value: impl Borrow<[u8]>,
  ) -> Result<(), skl::error::Error> {
    self
      .inner
      .skl
      .insert(version, key.borrow(), value.borrow())
      .map(|_| ())
  }

  /// Insert a tombstone entry for the specified `key` from the memtable and returns it.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
  ///
  /// let memtable: Memtable<&str, &str> = Memtable::new();
  /// memtable.insert(0, "key", "value");
  /// memtable.remove(1, "key");
  /// assert!(memtable.get(0, "key").is_some());
  /// assert!(memtable.get(1, "key").is_none());
  /// ```
  pub fn remove(&self, version: u64, key: impl Borrow<[u8]>) -> Result<(), Error> {
    self
      .inner
      .skl
      .get_or_remove(version, key.borrow())
      .map(|_| ())
  }

  /// Inserts a range deletion entry into the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
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
  pub fn remove_range<R, Q>(&self, version: u64, range: R) -> Result<(), Error>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Borrow<[u8]>,
  {
    let start = StartKey(range.start_bound().map(Borrow::borrow));
    let kenc = RangeKeyEncoder::new(start);
    let span_enc = RangeDeletionSpan::new(range.end_bound().map(Borrow::borrow));
    let kb = |buf: &mut VacantBuffer<'_>| kenc.encode(buf);
    let vb = |buf: &mut VacantBuffer<'_>| span_enc.encode(buf);
    self
      .inner
      .range_del_skl
      .insert_with_builders(
        version,
        KeyBuilder::new(kenc.encoded_len, kb),
        ValueBuilder::new(span_enc.encoded_len, vb),
      )
      .map(|_| ())
      .map_err(Among::unwrap_right)
  }

  /// Update entries within a range to the given value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::dynamic::Memtable;
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
  pub fn update_range<R, Q>(&self, version: u64, range: R, value: &Q) -> Result<(), Error>
  where
    R: RangeBounds<Q>,
    Q: ?Sized + Borrow<[u8]>,
  {
    let start = StartKey(range.start_bound().map(Borrow::borrow));
    let kenc = RangeKeyEncoder::new(start);
    let span_enc = RangeUpdateSpan::new(
      range.end_bound().map(Borrow::borrow),
      value.borrow(),
    );
    let kb = |buf: &mut VacantBuffer<'_>| kenc.encode(buf);
    let vb = |buf: &mut VacantBuffer<'_>| span_enc.encode(buf);
    self
      .inner
      .range_key_skl
      .insert_with_builders(
        version,
        KeyBuilder::new(kenc.encoded_len, kb),
        ValueBuilder::new(span_enc.encoded_len, vb),
      )
      .map(|_| ())
      .map_err(Among::unwrap_right)
  }
}

struct RangeKeyEncoder<'a> {
  kind: u8,
  key: &'a [u8],
  encoded_len: usize,
}

impl<'a> RangeKeyEncoder<'a> {
  #[inline]
  const fn new(key: StartKey<'a>) -> Self {
    match key.0 {
      Bound::Included(key) => {
        let len = 1 + key.len();
        Self {
          kind: INCLUDED,
          key,
          encoded_len: len,
        }
      }
      Bound::Excluded(key) => {
        let len = 1 + key.len();
        Self {
          kind: EXCLUDED,
          key,
          encoded_len: len,
        }
      }
      Bound::Unbounded => Self {
        kind: UNBOUNDED,
        key: &[],
        encoded_len: 1,
      },
    }
  }

  #[inline]
  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, InsufficientBuffer> {
    match self.kind {
      INCLUDED => buf
        .put_u8(INCLUDED)
        .and_then(|_| buf.put_slice(self.key))
        .map(|_| self.encoded_len),
      EXCLUDED => buf
        .put_u8(EXCLUDED)
        .and_then(|_| buf.put_slice(self.key))
        .map(|_| self.encoded_len),
      UNBOUNDED => buf.put_u8(UNBOUNDED).map(|_| 1),
      _ => unreachable!("invalid bound kind"),
    }
  }

  #[inline]
  fn decode<'b>(buf: &'b [u8]) -> StartKey<'b> {
    let (kind, key) = buf.split_at(1);
    StartKey(match kind[0] {
      INCLUDED => Bound::Included(key),
      EXCLUDED => Bound::Excluded(key),
      UNBOUNDED => Bound::Unbounded,
      _ => unreachable!("invalid bound kind"),
    })
  }
}

#[derive(Copy, Clone)]
struct RangeDeletionSpan<'a> {
  end_bound: Bound<&'a [u8]>,
  encoded_len: usize,
}

impl<'a> RangeDeletionSpan<'a> {
  #[inline]
  const fn new(end_bound: Bound<&'a [u8]>) -> Self {
    let end_len = match end_bound {
      Bound::Included(key) | Bound::Excluded(key) => 1 + key.len(),
      Bound::Unbounded => 1,
    };

    Self {
      end_bound,
      encoded_len: 1 + end_len, // start bound byte + end bound byte + end key
    }
  }

  #[inline]
  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, InsufficientBuffer> {
    macro_rules! encode_deletion_end_key {
      ($this:ident($end_bound:ident, $buf:ident $(, $k:ident)?)) => {{
        $buf.put_u8($end_bound) $(.and_then(|_| $buf.put_slice($k)))? .map(|_| $this.encoded_len)
      }};
    }

    match self.end_bound {
      Bound::Included(k) => encode_deletion_end_key!(self(INCLUDED, buf, k)),
      Bound::Excluded(k) => encode_deletion_end_key!(self(EXCLUDED, buf, k)),
      Bound::Unbounded => encode_deletion_end_key!(self(UNBOUNDED, buf)),
    }
  }

  #[inline]
  fn decode(buf: &'a [u8]) -> Self {
    let (bound, remaining) = buf.split_at(1);

    let end_bound = match bound[0] {
      INCLUDED => Bound::Included(remaining),
      EXCLUDED => Bound::Excluded(remaining),
      UNBOUNDED => Bound::Unbounded,
      _ => unreachable!("invalid bound kind"),
    };

    Self {
      end_bound,
      encoded_len: buf.len(),
    }
  }
}

#[derive(Copy, Clone)]
struct RangeUpdateSpan<'a> {
  end_bound: Bound<&'a [u8]>,
  end_key_len: u32,
  encoded_len: usize,
  value: &'a [u8],
}

impl<'a> RangeUpdateSpan<'a> {
  #[inline]
  const fn new(end_bound: Bound<&'a [u8]>, value: &'a [u8]) -> Self {
    const END_KEY_LEN_SIZE: usize = core::mem::size_of::<u32>();

    let (end_len, end_key_len) = match end_bound {
      Bound::Included(key) | Bound::Excluded(key) => {
        let len = key.len();
        (1 + END_KEY_LEN_SIZE + len, len as u32)
      }
      Bound::Unbounded => (1 + END_KEY_LEN_SIZE, 0),
    };

    Self {
      end_bound,
      end_key_len,
      encoded_len: end_len + value.len(), // end bound byte + end key len size + end key + value
      value,
    }
  }

  const UNBOUNDED_SLICE: [u8; 5] = {
    let zero = 0u32.to_le_bytes();
    [UNBOUNDED, zero[0], zero[1], zero[2], zero[3]]
  };

  #[inline]
  fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, InsufficientBuffer> {
    macro_rules! encode_end_key {
      ($this:ident($end_bound:ident, $buf:ident, $k:ident)) => {{
        $buf
          .put_u8($end_bound)
          .and_then(|_| $buf.put_u32_le($this.end_key_len))
          .and_then(|_| $buf.put_slice($k))
          .and_then(|_| $buf.put_slice($this.value))
          .map(|_| $this.encoded_len)
      }};
    }

    match self.end_bound {
      Bound::Included(k) => encode_end_key!(self(INCLUDED, buf, k)),
      Bound::Excluded(k) => encode_end_key!(self(EXCLUDED, buf, k)),
      Bound::Unbounded => buf
        .put_slice(&Self::UNBOUNDED_SLICE)
        .map(|_| Self::UNBOUNDED_SLICE.len()),
    }
  }

  #[inline]
  fn decode(buf: &'a [u8]) -> Self {
    let (bound, key) = buf.split_at(1);

    let end_key_len = u32::from_le_bytes(key[..4].try_into().unwrap());
    let (end_key, value) = key[4..].split_at(end_key_len as usize);
    let end_bound = match bound[0] {
      INCLUDED => Bound::Included(end_key),
      EXCLUDED => Bound::Excluded(end_key),
      UNBOUNDED => Bound::Unbounded,
      _ => unreachable!("invalid bound kind"),
    };

    Self {
      end_bound,
      end_key_len,
      value,
      encoded_len: buf.len(),
    }
  }
}
