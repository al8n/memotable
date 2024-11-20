pub use skl::{
  options::{CompressionPolicy, Freelist},
  Height, KeySize,
};

use skl::Options as SklOptions;

use super::sealed::Constructable;

/// The options for the `Memtable`.
#[derive(Debug, Clone, Copy)]
pub struct Options {
  capacity: u32,
  maximum_height: Height,
  maximum_key_size: KeySize,
  maximum_value_size: u32,
  freelist: Freelist,
  policy: CompressionPolicy,
  reserved: u32,
}

impl Default for Options {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Creates a new `Options` with default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      capacity: 8 * 1024 * 1024, // 8MB
      maximum_height: Height::new(),
      maximum_key_size: KeySize::new(),
      maximum_value_size: u32::MAX,
      freelist: Freelist::None,
      policy: CompressionPolicy::Fast,
      reserved: 0,
    }
  }

  /// Sets the capacity of the memtable.
  ///
  /// The default value is `8MB`.
  ///
  /// The capacity is the maximum size in bytes of the memtable.
  #[inline]
  pub fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }

  /// Sets the maximum height of the node of the skiplist.
  ///
  /// The default value is `20`.
  #[inline]
  pub fn with_maximum_height(mut self, maximum_height: Height) -> Self {
    self.maximum_height = maximum_height;
    self
  }

  /// Sets the maximum key size of the memtable.
  ///
  /// The default value is `u16::MAX`.
  #[inline]
  pub fn with_maximum_key_size(mut self, maximum_key_size: KeySize) -> Self {
    self.maximum_key_size = maximum_key_size;
    self
  }

  /// Sets the maximum value size of the memtable.
  ///
  /// The default value is `u32::MAX`.
  #[inline]
  pub fn with_maximum_value_size(mut self, maximum_value_size: u32) -> Self {
    self.maximum_value_size = maximum_value_size;
    self
  }

  /// Sets the freelist policy of the underlying ARENA allocator.
  #[inline]
  pub fn with_freelist(mut self, freelist: Freelist) -> Self {
    self.freelist = freelist;
    self
  }

  /// Sets the compression policy of the memtable.
  #[inline]
  pub fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.policy = policy;
    self
  }

  /// Sets the reserved space of the memtable.
  #[inline]
  pub fn with_reserved(mut self, reserved: u32) -> Self {
    self.reserved = reserved;
    self
  }

  /// Allocates a new bounded memtable with the options.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, generic::Memtable};
  ///
  /// let table = Options::new().alloc::<Memtable<String, String>>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<M>(self) -> Result<M, skl::error::Error>
  where
    M: Constructable,
  {
    M::construct(self)
  }

  /// Converts the options to the `SklOptions`.
  #[inline]
  pub(super) fn to_skl_options(&self) -> SklOptions {
    SklOptions::new()
      .with_capacity(self.capacity)
      .with_max_height(self.maximum_height)
      .with_max_key_size(self.maximum_key_size)
      .with_max_value_size(self.maximum_value_size)
      .with_freelist(self.freelist)
      .with_compression_policy(self.policy)
      .with_reserved(self.reserved)
  }
}
