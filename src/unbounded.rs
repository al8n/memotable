use {
  core::{
    cmp::Ordering,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
  },
  crossbeam_skiplist_mvcc::{Comparable, Equivalent},
};

#[derive(PartialEq, Eq, PartialOrd, Ord, ref_cast::RefCast)]
#[repr(transparent)]
struct Query<K: ?Sized, Q: ?Sized> {
  _m: PhantomData<K>,
  key: Q,
}

enum RangeKind<V> {
  Set(V),
  Deletion,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum StartKey<K> {
  Minimum,
  Key(K),
}

impl<K> StartKey<K> {
  #[inline]
  fn new(key: Bound<K>) -> Self {
    match key {
      Bound::Included(k) => Self::Key(k),
      Bound::Excluded(k) => Self::Key(k),
      Bound::Unbounded => Self::Minimum,
    }
  }
}

impl<K: Ord> PartialOrd for StartKey<K> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<K: Ord> Ord for StartKey<K> {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {
      (Self::Minimum, Self::Minimum) => Ordering::Equal,
      (Self::Minimum, _) => Ordering::Less,
      (_, Self::Minimum) => Ordering::Greater,
      (Self::Key(k1), Self::Key(k2)) => k1.cmp(k2),
    }
  }
}

impl<K, Q> Equivalent<StartKey<K>> for Query<K, Q>
where
  Q: ?Sized + Equivalent<K>,
{
  #[inline]
  fn equivalent(&self, key: &StartKey<K>) -> bool {
    match key {
      StartKey::Minimum => false,
      StartKey::Key(k) => self.key.equivalent(k),
    }
  }
}

impl<K, Q> Comparable<StartKey<K>> for Query<K, Q>
where
  Q: ?Sized + Comparable<K>,
{
  #[inline]
  fn compare(&self, key: &StartKey<K>) -> Ordering {
    match key {
      StartKey::Minimum => Ordering::Greater,
      StartKey::Key(k) => self.key.compare(k),
    }
  }
}

impl<K, Q> Equivalent<Query<K, Q>> for StartKey<K>
where
  Q: ?Sized + Equivalent<K>,
{
  #[inline]
  fn equivalent(&self, key: &Query<K, Q>) -> bool {
    match self {
      Self::Minimum => false,
      Self::Key(k) => key.key.equivalent(k),
    }
  }
}

impl<K, Q> Comparable<Query<K, Q>> for StartKey<K>
where
  Q: ?Sized + Comparable<K>,
{
  #[inline]
  fn compare(&self, key: &Query<K, Q>) -> Ordering {
    match self {
      Self::Minimum => Ordering::Less,
      Self::Key(k) => key.key.compare(k).reverse(),
    }
  }
}

struct KeySpan<K, V> {
  start_bound: Bound<()>,
  /// only store the bound information, the key will be stored in the SkipMap as key.
  end_bound: Bound<K>,
  value: RangeKind<V>,
}

impl<K, V> KeySpan<K, V> {
  #[inline]
  const fn new(start_bound: Bound<()>, end_bound: Bound<K>, value: RangeKind<V>) -> Self {
    Self {
      start_bound,
      end_bound,
      value,
    }
  }

  #[inline]
  fn range<'a>(&'a self, start_key: &'a StartKey<K>) -> impl RangeBounds<K> + 'a {
    let start_bound = match start_key {
      StartKey::Key(k) => match self.start_bound {
        Bound::Included(_) => Bound::Included(k),
        Bound::Excluded(_) => Bound::Excluded(k),
        Bound::Unbounded => Bound::Unbounded,
      },
      StartKey::Minimum => Bound::Unbounded,
    };

    (start_bound, self.end_bound.as_ref())
  }

  #[inline]
  const fn unwrap_value(&self) -> &V {
    match &self.value {
      RangeKind::Set(v) => v,
      RangeKind::Deletion => panic!("invoke unwrap value on deletion span"),
    }
  }
}

/// Memtable supports multiple version of the same key.
pub mod multiple_version;

/// Memtable without support for multiple version of the same key.
pub mod base;
