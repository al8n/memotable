use {
  core::{
    borrow::Borrow,
    cmp::Ordering,
    ops::{Bound, RangeBounds},
  },
  crossbeam_skiplist_mvcc::{Comparable, ComparableRangeBounds, Equivalent},
};

/// Memtable supports multiple version of the same key.
pub mod multiple_version;

/// Memtable without support for multiple version of the same key.
pub mod base;

#[derive(PartialEq, Eq, PartialOrd, Ord, ref_cast::RefCast)]
#[repr(transparent)]
struct Query<K>(K);

enum RangeKind<V> {
  Set(V),
  Unset,
  Deletion,
}

struct KeyRangeContainsResult {
  left: bool,
  right: bool,
  contained: bool,
}

/// The key range is ordered by start bound first, then end bound.
///
/// Here is an example of how the key range is ordered and how it works when iterating over the memtable.
///
/// ```text
/// point_skl (version 1):
///   a: 1,
///   b: 2,
///   c: 3,
///   d: 4,
///   e: 5,
///   f: 6,
///   g: 7,
///   h: 8,
///   i: 9,
///   j: 10,
///   k: 11,
///   l: 12,
///   m: 13,
///   n: 14,
///   o: 15,
///   p: 16,
///   q: 17,
///   r: 18,
///   s: 19,
///   t: 20,
///   u: 21,
///   v: 22,
///   w: 23,
///   x: 24,
///   y: 25,
///   z: 26,
///
/// range_del_skl (version 2):
///   rd0: a---e
///   rd1:  b---------l
///   rd2:    d---h
///   rd3:       g---k
///   rd4:          j---n
///   rd5:             m---q
///   rd6:                    t--w
///
/// range_key_skl (version 3):
///   rk1: x-z: 100
/// ```
///
/// Let's say we inserted a-z to the memtable at version 1, then we inserted range deletions `a---e`, `b---------l`, `d---h`, `g---k`, `j---n`, `m---q`, `t--w` at version 2, then we inserted range key `x-z: 100` at version 3.
///
/// When a new iterator is created and moving forward,
///
/// 1. we try to yield an entry from `point_skl`, which should be `a: 1`.
///
/// 2. we try to yield an entry from `range_del_skl`, which should be `rd0: a---e`.
///
/// 3. we check if the key `a` is within `rd0: a---e`, and find yes, so we keep the current `rd0`,
///     and then continue to yield the next entry from `point_skl`, which should be `b: 2`, until we find `f: 6`.
///
/// 4. we found `f: 6` is not within `rd0: a---e`, so we try to yield the next entry from `range_del_skl`,
///     which should be `rd1: b---------l`. Again, we continue find tombstone entries until we find `m: 13`.
///
/// 5. we found `m: 13` is not within `rd1: b---------l`, so we try to yield the next entry from `range_del_skl`,
///     which should be `rd2: d---h`, and we find `m: 13` is not within `rd2: d---h`,
///     so we try to yield the next entry from `range_del_skl`, until we find `rd4: j---n`.
///
/// 6. we found `m: 13` is within `rd4: j---n`, so we keep the current `rd4`, and then continue to yield the next entry from `point_skl`,
///     until we find `o: 15`, which is not within `rd4: j---n`. Again, we try to yield the next entry from `range_del_skl`,
///     until we find `rd5: m---q`.
///
/// 7. we found `o: 15` is within `rd5: m---q`, so we keep the current `rd5`, and then continue to yield the next entry from `point_skl`,
///     until we find `r: 18`, which is not within `rd5: m---q`. Again, we try to yield the next entry from `range_del_skl`,
///     we get `rd6: t--w`, and yes, `r: 18` is not within `rd6: t--w`, so we can return `r: 18` to the caller.
///
/// 8. Based on the above, the first entry yield from memtable iterator should be `r: 18`.
///
/// 9. The second entry yield from memtable iterator should be `s: 19`.
///
/// 10. Then, we will reach `t: 20`, which is within `rd6: t--w`, so we should skip `t: 20`, and until we find `x: 24`.
///
/// 11. We found `x: 24` is not within `rd6: t--w`, so we try to yield the next entry from `range_key_skl`, which is none.
///
/// the first entry for `range_del_skl` is `rd0: a---e`, the first entry for range_key_skl is `r1`.
#[derive(Clone, Debug, Eq, PartialEq)]
struct KeyRange<K> {
  start_bound: Bound<K>,
  end_bound: Bound<K>,
}

impl<K> KeyRange<K> {
  #[inline]
  const fn new(start_bound: Bound<K>, end_bound: Bound<K>) -> Self {
    Self {
      start_bound,
      end_bound,
    }
  }
}

impl<K> KeyRange<K>
where
  K: Ord,
{
  #[inline]
  fn contains(&self, item: &K) -> KeyRangeContainsResult {
    let left = match self.start_bound.as_ref() {
      Bound::Included(start) => start <= item,
      Bound::Excluded(start) => start < item,
      Bound::Unbounded => true,
    };

    let right = match self.end_bound.as_ref() {
      Bound::Included(end) => item <= end,
      Bound::Excluded(end) => item < end,
      Bound::Unbounded => true,
    };

    KeyRangeContainsResult {
      left,
      right,
      contained: left && right,
    }
  }
}

impl<K: Ord> PartialOrd for KeyRange<K> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl<K: Ord> Ord for KeyRange<K> {
  fn cmp(&self, other: &Self) -> Ordering {
    let this_start = self.start_bound.as_ref();
    let other_start = other.start_bound.as_ref();

    compare_bound(this_start, other_start).then_with(|| {
      let this_end = self.end_bound.as_ref();
      let other_end = other.end_bound.as_ref();
      compare_bound(this_end, other_end)
    })
  }
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

  #[inline]
  fn compare(&self, other: &K) -> Ordering
  where
    K: Ord,
  {
    match self {
      Self::Minimum => Ordering::Less,
      Self::Key(k) => k.cmp(other),
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

impl<K> Equivalent<StartKey<K>> for Query<K>
where
  K: Eq,
{
  #[inline]
  fn equivalent(&self, key: &StartKey<K>) -> bool {
    match key {
      StartKey::Minimum => false,
      StartKey::Key(k) => self.0 == *k,
    }
  }
}

impl<K> Comparable<StartKey<K>> for Query<K>
where
  K: Ord,
{
  #[inline]
  fn compare(&self, key: &StartKey<K>) -> Ordering {
    match key {
      StartKey::Minimum => Ordering::Greater,
      StartKey::Key(k) => self.0.cmp(k),
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
      StartKey::Key(k) => match self.end_bound {
        Bound::Included(_) => Bound::Included(k),
        Bound::Excluded(_) => Bound::Excluded(k),
        Bound::Unbounded => Bound::Unbounded,
      },
      StartKey::Minimum => Bound::Unbounded,
    };

    (start_bound, self.end_bound.as_ref())
  }

  /// Returns `true` if the end bound of the span is less than the given key.
  #[inline]
  fn within_end_bound(&self, item: &K) -> bool
  where
    K: Ord,
  {
    match self.end_bound.as_ref() {
      Bound::Included(end) => item <= end,
      Bound::Excluded(end) => item < end,
      Bound::Unbounded => true,
    }
  }

  #[inline]
  const fn unwrap_value(&self) -> &V {
    match &self.value {
      RangeKind::Set(v) => v,
      RangeKind::Deletion => panic!("invoke unwrap value on deletion span"),
      RangeKind::Unset => panic!("invoke unwrap value on unset span"),
    }
  }
}

#[inline]
fn compare_bound<K: Ord>(a: Bound<&K>, b: Bound<&K>) -> Ordering {
  match (a, b) {
    (Bound::Unbounded, Bound::Unbounded) => Ordering::Equal,
    (Bound::Unbounded, _) => Ordering::Less,
    (_, Bound::Unbounded) => Ordering::Greater,
    (Bound::Included(k1), Bound::Included(k2)) | (Bound::Excluded(k1), Bound::Excluded(k2)) => {
      k1.cmp(k2)
    }
    (Bound::Included(k1), Bound::Excluded(k2)) => match k1.cmp(k2) {
      Ordering::Less => Ordering::Less,
      Ordering::Equal => Ordering::Greater,
      Ordering::Greater => Ordering::Greater,
    },
    (Bound::Excluded(k1), Bound::Included(k2)) => match k1.cmp(k2) {
      Ordering::Less => Ordering::Less,
      Ordering::Equal => Ordering::Less,
      Ordering::Greater => Ordering::Greater,
    },
  }
}
