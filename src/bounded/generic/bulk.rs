use core::{
  cmp,
  marker::PhantomData,
  ops::{Bound, RangeBounds},
};

use either::Either;
use ref_cast::RefCast;
use skl::{
  generic::{Comparable, Equivalent, KeyRef, MaybeStructured, Type, TypeRef},
  VacantBuffer,
};

use super::{EXCLUDED, INCLUDED, UNBOUNDED};

#[repr(transparent)]
pub(super) struct PhantomRangeKey<K: ?Sized>(PhantomData<K>);

impl<K: ?Sized> core::fmt::Debug for PhantomRangeKey<K> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("PhantomRangeKey").field(&self.0).finish()
  }
}

impl<K> Type for PhantomRangeKey<K>
where
  K: ?Sized + Type,
{
  type Ref<'a> = RangeKeyRef<'a, K>;

  type Error = core::convert::Infallible;

  #[inline(never)]
  #[cold]
  fn encoded_len(&self) -> usize {
    0
  }

  #[inline(never)]
  #[cold]
  fn encode_to_buffer(&self, _: &mut skl::VacantBuffer<'_>) -> Result<usize, Self::Error> {
    Ok(0)
  }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, ref_cast::RefCast)]
#[repr(transparent)]
pub(super) struct Query<Q: ?Sized> {
  key: Q,
}

impl<'a, K, Q> Equivalent<RangeKeyRef<'a, K>> for Query<Q>
where
  K: ?Sized + Type,
  Q: ?Sized + Equivalent<K::Ref<'a>>,
{
  fn equivalent(&self, key: &RangeKeyRef<'a, K>) -> bool {
    self.key.equivalent(&key.key)
  }
}

impl<'a, K, Q> Comparable<RangeKeyRef<'a, K>> for Query<Q>
where
  K: ?Sized + Type,
  Q: ?Sized + Comparable<K::Ref<'a>>,
{
  fn compare(&self, key: &RangeKeyRef<'a, K>) -> cmp::Ordering {
    self.key.compare(&key.key)
  }
}

pub(super) struct QueryRange<Q: ?Sized, R>
where
  R: RangeBounds<Q>,
{
  r: R,
  _q: PhantomData<Q>,
}

impl<Q: ?Sized, R> QueryRange<Q, R>
where
  R: RangeBounds<Q>,
{
  #[inline]
  pub(super) const fn new(r: R) -> Self {
    Self { r, _q: PhantomData }
  }
}

impl<Q: ?Sized, R> RangeBounds<Query<Q>> for QueryRange<Q, R>
where
  R: RangeBounds<Q>,
{
  #[inline]
  fn start_bound(&self) -> Bound<&Query<Q>> {
    self.r.start_bound().map(RefCast::ref_cast)
  }

  fn end_bound(&self) -> Bound<&Query<Q>> {
    self.r.end_bound().map(RefCast::ref_cast)
  }
}

pub(super) struct RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
{
  bound: Bound<()>,
  raw: &'a [u8],
  key: K::Ref<'a>,
}

impl<'a, K> PartialEq for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
  K::Ref<'a>: PartialEq,
{
  #[inline]
  fn eq(&self, other: &Self) -> bool {
    match (self.bound, other.bound) {
      (Bound::Unbounded, Bound::Unbounded) => true,
      (Bound::Included(_), Bound::Unbounded) => false,
      (Bound::Excluded(_), Bound::Unbounded) => false,
      (Bound::Unbounded, Bound::Included(_)) => false,
      (Bound::Unbounded, Bound::Excluded(_)) => false,
      _ => self.key == other.key,
    }
  }
}

impl<'a, K> Eq for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
  K::Ref<'a>: Eq,
{
}

impl<'a, K> PartialOrd for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
  K::Ref<'a>: Ord,
{
  #[inline]
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl<'a, K> Ord for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
  K::Ref<'a>: Ord,
{
  #[inline]
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    match (self.bound, other.bound) {
      (Bound::Included(_), Bound::Unbounded) => cmp::Ordering::Greater,
      (Bound::Excluded(_), Bound::Unbounded) => cmp::Ordering::Greater,
      (Bound::Unbounded, Bound::Included(_)) => cmp::Ordering::Less,
      (Bound::Unbounded, Bound::Excluded(_)) => cmp::Ordering::Less,
      (Bound::Unbounded, Bound::Unbounded) => cmp::Ordering::Equal,
      _ => self.key.cmp(&other.key),
    }
  }
}

impl<'a, K> core::fmt::Debug for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
  K::Ref<'a>: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let kr = self.bound.as_ref().map(|_| &self.key);

    f.debug_tuple("RangeKeyRef").field(&kr).finish()
  }
}

impl<K> Clone for RangeKeyRef<'_, K>
where
  K: ?Sized + Type,
{
  fn clone(&self) -> Self {
    *self
  }
}

impl<K> Copy for RangeKeyRef<'_, K> where K: ?Sized + Type {}

impl<'a, K> TypeRef<'a> for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
{
  #[inline]
  unsafe fn from_slice(src: &'a [u8]) -> Self {
    println!("decode src {src:?}");
    let (bound, key) = src.split_at(1);
    let bound = match bound[0] {
      UNBOUNDED => Bound::Unbounded,
      INCLUDED => Bound::Included(()),
      EXCLUDED => Bound::Excluded(()),
      _ => unreachable!(),
    };

    Self {
      bound,
      raw: src,
      key: K::Ref::from_slice(key),
    }
  }

  #[inline]
  fn as_raw(&self) -> Option<&'a [u8]> {
    Some(self.raw)
  }
}

impl<K> Equivalent<PhantomRangeKey<K>> for RangeKeyRef<'_, K>
where
  K: ?Sized + Type,
{
  #[inline(never)]
  #[cold]
  fn equivalent(&self, _: &PhantomRangeKey<K>) -> bool {
    unreachable!()
  }
}

impl<K> Comparable<PhantomRangeKey<K>> for RangeKeyRef<'_, K>
where
  K: ?Sized + Type,
{
  #[inline(never)]
  #[cold]
  fn compare(&self, _: &PhantomRangeKey<K>) -> cmp::Ordering {
    unreachable!()
  }
}

impl<'a, K> KeyRef<'a, PhantomRangeKey<K>> for RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
  for<'b> K::Ref<'b>: Ord,
{
  #[inline]
  fn compare<Q>(&self, a: &Q) -> cmp::Ordering
  where
    Q: ?Sized + Ord + Comparable<Self>,
  {
    a.compare(self).reverse()
  }

  #[inline]
  unsafe fn compare_binary(a: &[u8], b: &[u8]) -> cmp::Ordering {
    let ak = <RangeKeyRef<'_, K> as TypeRef<'_>>::from_slice(a);
    let bk = <RangeKeyRef<'_, K> as TypeRef<'_>>::from_slice(b);

    ak.cmp(&bk)
  }
}

impl<'a, K> RangeKeyRef<'a, K>
where
  K: ?Sized + Type,
{
  #[inline]
  pub(super) fn bound(&self) -> Bound<&K::Ref<'a>> {
    self.bound.map(|_| &self.key)
  }
}

#[repr(transparent)]
pub(super) struct PhantomRangeDeletionSpan<K: ?Sized> {
  _k: PhantomData<K>,
}

impl<K> core::fmt::Debug for PhantomRangeDeletionSpan<K>
where
  K: ?Sized,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("PhantomRangeDeletionSpan")
      .field(&self._k)
      .finish()
  }
}

impl<K> Type for PhantomRangeDeletionSpan<K>
where
  K: ?Sized + Type,
{
  type Ref<'a> = RangeDeletionSpanRef<'a, K>;

  type Error = core::convert::Infallible;

  #[inline(never)]
  #[cold]
  fn encoded_len(&self) -> usize {
    0
  }

  #[inline(never)]
  #[cold]
  fn encode_to_buffer(&self, _: &mut skl::VacantBuffer<'_>) -> Result<usize, Self::Error> {
    Ok(0)
  }
}

pub(super) struct RangeDeletionSpanRef<'a, K>
where
  K: ?Sized + Type,
{
  // end key bound
  key: Bound<K::Ref<'a>>,
  raw: &'a [u8],
}

impl<K> core::fmt::Debug for RangeDeletionSpanRef<'_, K>
where
  K: ?Sized + Type,
  for<'a> K::Ref<'a>: core::fmt::Debug,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("RangeDeletionSpanRef")
      .field(&self.key)
      .finish()
  }
}

impl<K> Clone for RangeDeletionSpanRef<'_, K>
where
  K: ?Sized + Type,
{
  fn clone(&self) -> Self {
    *self
  }
}

impl<K> Copy for RangeDeletionSpanRef<'_, K> where K: ?Sized + Type {}

impl<'a, K> TypeRef<'a> for RangeDeletionSpanRef<'a, K>
where
  K: ?Sized + Type,
{
  #[inline]
  unsafe fn from_slice(src: &'a [u8]) -> Self {
    let (bound, key) = src.split_at(1);
    let bound = match bound[0] {
      UNBOUNDED => Bound::Unbounded,
      INCLUDED => Bound::Included(K::Ref::from_slice(key)),
      EXCLUDED => Bound::Excluded(K::Ref::from_slice(key)),
      _ => panic!("invalid bound type"),
    };

    Self {
      key: bound,
      raw: src,
    }
  }

  #[inline]
  fn as_raw(&self) -> Option<&'a [u8]> {
    Some(self.raw)
  }
}

impl<'a, K> RangeDeletionSpanRef<'a, K>
where
  K: ?Sized + Type,
{
  #[inline]
  pub(super) fn bound(&self) -> Bound<&K::Ref<'a>> {
    self.key.as_ref()
  }
}

impl<'a, K> RangeDeletionSpanRef<'a, K>
where
  K: ?Sized + Type,
  for<'b> K::Ref<'b>: KeyRef<'b, K>,
{
  #[inline]
  pub(super) fn contains(&self, start: &RangeKeyRef<'a, K>, k: &K::Ref<'a>) -> bool {
    (start.bound(), self.key.as_ref()).contains(k)
  }
}

#[repr(transparent)]
pub(super) struct PhantomRangeUpdateSpan<K, V>
where
  K: ?Sized,
  V: ?Sized,
{
  _k: PhantomData<K>,
  _v: PhantomData<V>,
}

impl<K, V> core::fmt::Debug for PhantomRangeUpdateSpan<K, V>
where
  K: ?Sized,
  V: ?Sized,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("PhantomRangeUpdateSpan")
      .field("key", &self._k)
      .field("value", &self._v)
      .finish()
  }
}

impl<K, V> Type for PhantomRangeUpdateSpan<K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  type Ref<'a> = RangeUpdateSpanRef<'a, K, V>;

  type Error = core::convert::Infallible;

  #[inline(never)]
  #[cold]
  fn encoded_len(&self) -> usize {
    0
  }

  #[inline(never)]
  #[cold]
  fn encode_to_buffer(&self, _: &mut skl::VacantBuffer<'_>) -> Result<usize, Self::Error> {
    Ok(0)
  }
}

pub(super) struct RangeUpdateSpanRef<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  // end key bound
  key: Bound<K::Ref<'a>>,
  value: V::Ref<'a>,
  raw: &'a [u8],
}

impl<K, V> core::fmt::Debug for RangeUpdateSpanRef<'_, K, V>
where
  K: ?Sized + Type,
  for<'a> K::Ref<'a>: core::fmt::Debug,
  V: ?Sized + Type,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("RangeUpdateSpanRef")
      .field("key", &self.key)
      .field("value", &self.value)
      .finish()
  }
}

impl<K, V> Clone for RangeUpdateSpanRef<'_, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  fn clone(&self) -> Self {
    *self
  }
}

impl<K, V> Copy for RangeUpdateSpanRef<'_, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
}

impl<'a, K, V> TypeRef<'a> for RangeUpdateSpanRef<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  #[inline]
  unsafe fn from_slice(src: &'a [u8]) -> Self {
    let (bound, remaining) = src.split_at(1);
    let (key, value) = match bound[0] {
      UNBOUNDED => (Bound::Unbounded, V::Ref::from_slice(remaining)),
      INCLUDED => {
        let (len_buf, remaining) = remaining.split_at(4);
        let klen = u32::from_le_bytes(len_buf.try_into().unwrap()) as usize;
        let (key, value) = remaining.split_at(klen);
        (
          Bound::Included(K::Ref::from_slice(key)),
          V::Ref::from_slice(value),
        )
      }
      EXCLUDED => {
        let (len_buf, remaining) = remaining.split_at(4);
        let klen = u32::from_le_bytes(len_buf.try_into().unwrap()) as usize;
        let (key, value) = remaining.split_at(klen);
        (
          Bound::Excluded(K::Ref::from_slice(key)),
          V::Ref::from_slice(value),
        )
      }
      _ => panic!("invalid bound type"),
    };

    Self {
      key,
      value,
      raw: src,
    }
  }

  #[inline]
  fn as_raw(&self) -> Option<&'a [u8]> {
    Some(self.raw)
  }
}

impl<'a, K, V> RangeUpdateSpanRef<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  #[inline]
  pub(super) fn value(&self) -> &V::Ref<'a> {
    &self.value
  }

  #[inline]
  pub(super) fn bound(&self) -> Bound<&K::Ref<'a>> {
    self.key.as_ref()
  }
}

impl<'a, K, V> RangeUpdateSpanRef<'a, K, V>
where
  K: ?Sized + Type,
  for<'b> K::Ref<'b>: KeyRef<'b, K>,
  V: ?Sized + Type,
{
  #[inline]
  pub(super) fn contains(&self, start: &RangeKeyRef<'a, K>, k: &K::Ref<'a>) -> bool {
    (start.bound(), self.key.as_ref()).contains(k)
  }
}

pub(super) struct RangeKeyEncoder<'a, K>
where
  K: ?Sized,
{
  key: Bound<MaybeStructured<'a, K>>,
  pub(super) encoded_len: usize,
}

impl<'a, K> RangeKeyEncoder<'a, K>
where
  K: ?Sized + Type,
{
  #[inline]
  pub(super) fn new(key: Bound<MaybeStructured<'a, K>>) -> Self {
    let len = match key {
      Bound::Included(key) => 1 + key.encoded_len(),
      Bound::Excluded(key) => 1 + key.encoded_len(),
      Bound::Unbounded => 1,
    };

    Self {
      key,
      encoded_len: len,
    }
  }

  #[inline]
  pub(super) fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, K::Error> {
    println!("buf len {}", buf.len());
    match self.key.as_ref() {
      Bound::Excluded(key) => {
        buf.put_u8_unchecked(u8::MAX);
        println!("buf len included {}", buf.len());
        key.encode_to_buffer(buf).map(|_| {
          println!("encoded buf {:?}", buf.as_ref());
          self.encoded_len
        })
      }
      Bound::Included(key) => {
        buf.put_u8_unchecked(0);
        println!("buf len excluded {}", buf.len());
        key.encode_to_buffer(buf).map(|_| {
          println!("encoded buf {:?}", buf.as_ref());
          self.encoded_len
        })
      }
      Bound::Unbounded => {
        buf.put_u8_unchecked(1);
        println!("buf len unbounded {}", buf.len());
        Ok(1)
      }
    }
  }
}

pub(super) struct RangeDeletionSpan<'a, K: ?Sized> {
  end_bound: Bound<MaybeStructured<'a, K>>,
  pub(super) encoded_len: usize,
}

impl<K: ?Sized> Clone for RangeDeletionSpan<'_, K> {
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<K: ?Sized> Copy for RangeDeletionSpan<'_, K> {}

impl<'a, K> RangeDeletionSpan<'a, K>
where
  K: ?Sized + Type,
{
  #[inline]
  pub(super) fn new(end_bound: Bound<MaybeStructured<'a, K>>) -> Self {
    let end_len = match end_bound {
      Bound::Included(key) | Bound::Excluded(key) => 1 + key.encoded_len(),
      Bound::Unbounded => 1,
    };

    Self {
      end_bound,
      encoded_len: 1 + end_len, // end bound byte + end key
    }
  }

  #[inline]
  pub(super) fn encode(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, K::Error> {
    macro_rules! encode_deletion_end_key {
      ($this:ident($end_bound:ident, $buf:ident $(, $k:ident)?)) => {{
        $buf.put_u8_unchecked($end_bound);
        $($k.encode_to_buffer($buf).map(|_| $this.encoded_len))?
      }};
    }

    match self.end_bound {
      Bound::Included(k) => encode_deletion_end_key!(self(INCLUDED, buf, k)),
      Bound::Excluded(k) => encode_deletion_end_key!(self(EXCLUDED, buf, k)),
      Bound::Unbounded => {
        encode_deletion_end_key!(self(UNBOUNDED, buf));
        Ok(self.encoded_len)
      }
    }
  }
}

pub(super) struct RangeUpdateSpan<'a, K, V>
where
  K: ?Sized,
  V: ?Sized,
{
  end_bound: Bound<MaybeStructured<'a, K>>,
  end_key_len: u32,
  pub(super) encoded_len: usize,
  value: MaybeStructured<'a, V>,
}

impl<K, V> Clone for RangeUpdateSpan<'_, K, V>
where
  K: ?Sized,
  V: ?Sized,
{
  #[inline]
  fn clone(&self) -> Self {
    *self
  }
}

impl<K, V> Copy for RangeUpdateSpan<'_, K, V>
where
  K: ?Sized,
  V: ?Sized,
{
}

impl<'a, K, V> RangeUpdateSpan<'a, K, V>
where
  K: ?Sized + Type,
  V: ?Sized + Type,
{
  #[inline]
  pub(super) fn new(
    end_bound: Bound<MaybeStructured<'a, K>>,
    value: MaybeStructured<'a, V>,
  ) -> Self {
    const END_KEY_LEN_SIZE: usize = core::mem::size_of::<u32>();

    let (end_len, end_key_len) = match end_bound {
      Bound::Included(key) | Bound::Excluded(key) => {
        let len = key.encoded_len();
        (1 + END_KEY_LEN_SIZE + len, len as u32)
      }
      Bound::Unbounded => (1, 0),
    };

    Self {
      end_bound,
      end_key_len,
      encoded_len: end_len + value.encoded_len(), // end bound byte + end key len size + end key + value
      value,
    }
  }

  #[inline]
  pub(super) fn encode(
    &self,
    buf: &mut VacantBuffer<'_>,
  ) -> Result<usize, Either<K::Error, V::Error>> {
    macro_rules! encode_update_end_key {
      ($this:ident($end_bound:ident, $buf:ident, $k:ident)) => {{
        $buf.put_u8_unchecked($end_bound);
        $buf.put_u32_le_unchecked($this.end_key_len);
        $k.encode_to_buffer($buf).map_err(Either::Left)?;
        $this
          .value
          .encode_to_buffer($buf)
          .map_err(Either::Right)
          .map(|_| self.encoded_len)
      }};
    }

    match self.end_bound {
      Bound::Included(k) => encode_update_end_key!(self(INCLUDED, buf, k)),
      Bound::Excluded(k) => encode_update_end_key!(self(EXCLUDED, buf, k)),
      Bound::Unbounded => {
        buf.put_u8_unchecked(UNBOUNDED);
        self
          .value
          .encode_to_buffer(buf)
          .map_err(Either::Right)
          .map(|_| self.encoded_len)
      }
    }
  }
}
