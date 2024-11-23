use dbutils::equivalent::Comparable;
use either::Either;
use ref_cast::RefCast;
use skl::{among::Among, KeyBuilder, VacantBuffer, ValueBuilder};

use super::{generic::Memtable as GenericMemtable, sealed::Constructable};

mod entry;

/// Iterators for the memtable.
pub mod iter;

pub use dbutils::{
  equivalentor::{Ascend, Descend, StaticComparator, StaticEquivalentor, StaticRangeComparator},
  types::SliceRef,
};
pub use entry::*;

use sealed::Key;

mod sealed {
  use core::marker::PhantomData;

  use super::{StaticComparator, StaticEquivalentor};

  use dbutils::{
    buffer::VacantBuffer,
    equivalent::{Comparable, Equivalent},
    types::{SliceRef, Type},
  };

  /// The actual key type used in the [`Memtable`](super::Memtable).
  #[derive(ref_cast::RefCast)]
  #[repr(transparent)]
  #[doc(hidden)]
  pub struct Key<C: ?Sized> {
    _marker: PhantomData<C>,
    data: [u8],
  }

  impl<C: ?Sized> core::fmt::Debug for Key<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      core::fmt::Debug::fmt(&self.data, f)
    }
  }

  impl<C> PartialEq for Key<C>
  where
    C: StaticEquivalentor + ?Sized,
  {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
      C::equivalent(&self.data, &other.data)
    }
  }

  impl<C: ?Sized> Eq for Key<C> where C: StaticComparator {}

  impl<C> PartialOrd for Key<C>
  where
    C: StaticComparator + ?Sized,
  {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
      Some(self.cmp(other))
    }
  }

  impl<C> Ord for Key<C>
  where
    C: StaticComparator + ?Sized,
  {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
      C::compare(&self.data, &other.data)
    }
  }

  impl<C: ?Sized> Type for Key<C> {
    type Ref<'a> = <[u8] as Type>::Ref<'a>;

    type Error = <[u8] as Type>::Error;

    #[inline]
    fn encoded_len(&self) -> usize {
      <[u8] as Type>::encoded_len(&self.data)
    }

    #[inline]
    fn encode_to_buffer(&self, buf: &mut VacantBuffer<'_>) -> Result<usize, Self::Error> {
      <[u8] as Type>::encode_to_buffer(&self.data, buf)
    }
  }

  impl<C> Equivalent<Key<C>> for SliceRef<'_>
  where
    C: ?Sized + StaticEquivalentor,
  {
    #[inline]
    fn equivalent(&self, other: &Key<C>) -> bool {
      C::equivalent(self, &other.data)
    }
  }

  impl<C> Comparable<Key<C>> for SliceRef<'_>
  where
    C: ?Sized + StaticComparator,
  {
    #[inline]
    fn compare(&self, other: &Key<C>) -> core::cmp::Ordering {
      C::compare(self, &other.data)
    }
  }
}

/// Memtable based on bounded ARENA-style `SkipList`.
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
/// use memorable::bounded::{dynamic::Memtable, Options};
/// use core::ops::Bound;
///
/// let memtable = Options::new().alloc::<Memtable>().unwrap();
///
/// memtable.insert(0, b"1", b"v1").unwrap();
/// memtable.insert(0, b"2", b"v2").unwrap();
/// memtable.insert(0, b"3", b"v3").unwrap();
///
/// memtable.remove_range(0, "2"..).unwrap();
///
/// memtable.update_range(0, "1".., "updated").unwrap();
///
/// assert_eq!(*memtable.get(0, &"1").unwrap().value(), "updated");
/// assert!(memtable.get(0, &"2").is_none());
/// assert!(memtable.get(0, &"3").is_none());
/// ```
///
/// In the above example, if we invoke get(1) at version 0, the result will be "updated" because the
/// range set entry has higher priority than the point entry and shadowed its value.
///
/// If we invoke get(2) at version 0, the result will be None because the range remove entry has
/// higher priority than the point entry and shadowed its value.
pub struct Memtable<C: ?Sized = Ascend>(GenericMemtable<Key<C>, [u8]>);

impl<C: ?Sized> Clone for Memtable<C> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<C> Constructable for Memtable<C>
where
  C: ?Sized + 'static,
{
  #[inline]
  fn construct(opts: super::Options) -> Result<Self, super::Error> {
    GenericMemtable::construct(opts).map(Self)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_anon(opts: super::Options) -> std::io::Result<Self> {
    GenericMemtable::map_anon(opts).map(Self)
  }
}

impl<C> Memtable<C>
where
  C: ?Sized + 'static,
{
  /// Returns the maximum version of the memtable.
  #[inline]
  pub fn maximum_version(&self) -> u64 {
    self.0.maximum_version()
  }

  /// Returns the minimum version of the memtable.
  #[inline]
  pub fn minimum_version(&self) -> u64 {
    self.0.minimum_version()
  }
}

impl<C> Memtable<C>
where
  C: StaticComparator + ?Sized + 'static,
{
  /// Returns an entry with the specified `key`.
  ///
  /// This function returns an [`Entry`] which
  /// can be used to access the key's associated value.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  ///
  /// memtable.insert(0, b"1", b"1").unwrap();
  /// assert_eq!(*memtable.get(0, b"1").unwrap().value(), b"1");
  /// ```
  #[inline]
  pub fn get<'a, Q>(&'a self, version: u64, k: &Q) -> Option<Entry<'a, C>>
  where
    Q: ?Sized + Comparable<SliceRef<'a>>,
  {
    self.0.get(version, k)
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  /// memtable.insert(1, "key".as_bytes(), "value".as_bytes()).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, b"key").unwrap().value(), b"value");
  /// ```
  #[inline]
  pub fn insert(&self, version: u64, key: &[u8], value: &[u8]) -> Result<(), super::Error> {
    self
      .0
      .insert(version, Key::ref_cast(key), value)
      .map_err(Among::unwrap_right)
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options, ValueBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  /// memtable.insert_with_value_builder(1, b"key", ValueBuilder::new(5, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"value"))).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, b"key").unwrap().value(), b"value");
  /// ```
  pub fn insert_with_value_builder<'a, E>(
    &'a self,
    version: u64,
    key: &'a [u8],
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, E>>,
  ) -> Result<(), Either<E, skl::error::Error>> {
    self
      .0
      .insert_with_value_builder(version, Key::ref_cast(key), value_builder)
      .map(|_| ())
      .map_err(Among::into_middle_right)
  }

  /// Inserts a `key`-`value` pair into the memtable and returns the new entry.
  ///
  /// If there is an existing entry with this key, it will be removed before inserting the new
  /// one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{dynamic::Memtable, Options, KeyBuilder, ValueBuilder, VacantBuffer};
  ///
  /// let memtable: Memtable = Options::new().alloc().unwrap();
  /// memtable.insert_with_builders(1, KeyBuilder::new(3, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"key")), ValueBuilder::new(5, |buf: &mut VacantBuffer<'_>| buf.put_slice(b"value"))).unwrap();
  ///
  /// assert_eq!(*memtable.get(1, b"key").unwrap().value(), b"value");
  /// ```
  #[allow(single_use_lifetimes)]
  pub fn insert_with_builders<'a, KE, VE>(
    &'a self,
    version: u64,
    key_builder: KeyBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, KE>>,
    value_builder: ValueBuilder<impl FnOnce(&mut VacantBuffer<'a>) -> Result<usize, VE>>,
  ) -> Result<(), Among<KE, VE, skl::error::Error>> {
    self
      .0
      .insert_with_builders(version, key_builder, value_builder)
      .map(|_| ())
  }
}
