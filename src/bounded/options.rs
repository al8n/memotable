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
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::Options;
  ///
  /// let options = Options::new().with_capacity(1024 * 1024);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }

  /// Returns the capacity of the memtable.
  ///
  /// The default value is `8MB`.
  ///
  /// The capacity is the maximum size in bytes of the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::Options;
  ///
  /// let options = Options::new().with_capacity(1024 * 1024);
  /// assert_eq!(options.capacity(), 1024 * 1024);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.capacity
  }

  /// Sets the maximum height of the node of the skiplist.
  ///
  /// The default value is `20`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, Height};
  ///
  /// let options = Options::new().with_maximum_height(Height::with(10));
  /// ```
  #[inline]
  pub const fn with_maximum_height(mut self, maximum_height: Height) -> Self {
    self.maximum_height = maximum_height;
    self
  }

  /// Returns the maximum height of the node of the skiplist.
  ///
  /// The default value is `20`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, Height};
  ///
  /// let options = Options::new().with_maximum_height(Height::with(10));
  /// assert_eq!(options.maximum_height(), Height::with(10));
  /// ```
  #[inline]
  pub const fn maximum_height(&self) -> Height {
    self.maximum_height
  }

  /// Sets the maximum key size of the memtable.
  ///
  /// The default value is `u16::MAX`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, KeySize};
  ///
  /// let options = Options::new().with_maximum_key_size(KeySize::with(1024));
  /// ```
  #[inline]
  pub const fn with_maximum_key_size(mut self, maximum_key_size: KeySize) -> Self {
    self.maximum_key_size = maximum_key_size;
    self
  }

  /// Returns the maximum key size of the memtable.
  ///
  /// The default value is `u16::MAX`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, KeySize};
  ///
  /// let options = Options::new().with_maximum_key_size(KeySize::with(1024));
  /// assert_eq!(options.maximum_key_size(), KeySize::with(1024));
  /// ```
  #[inline]
  pub const fn maximum_key_size(&self) -> KeySize {
    self.maximum_key_size
  }

  /// Sets the maximum value size of the memtable.
  ///
  /// The default value is `u32::MAX`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::Options;
  ///
  /// let options = Options::new().with_maximum_value_size(1024 * 1024);
  /// assert_eq!(options.maximum_value_size(), 1024 * 1024);
  /// ```
  #[inline]
  pub const fn with_maximum_value_size(mut self, maximum_value_size: u32) -> Self {
    self.maximum_value_size = maximum_value_size;
    self
  }

  /// Returns the maximum value size of the memtable.
  ///
  /// The default value is `u32::MAX`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::Options;
  ///
  /// let options = Options::new().with_maximum_value_size(1024 * 1024);
  /// assert_eq!(options.maximum_value_size(), 1024 * 1024);
  /// ```
  #[inline]
  pub const fn maximum_value_size(&self) -> u32 {
    self.maximum_value_size
  }

  /// Sets the freelist policy of the underlying ARENA allocator.
  ///
  /// Default is `Freelist::None`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, Freelist};
  ///
  /// let options = Options::new().with_freelist(Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn with_freelist(mut self, freelist: Freelist) -> Self {
    self.freelist = freelist;
    self
  }

  /// Returns the freelist policy of the underlying ARENA allocator.
  ///
  /// Default is `Freelist::None`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, Freelist};
  ///
  /// let options = Options::new().with_freelist(Freelist::Optimistic);
  /// assert_eq!(options.freelist(), Freelist::Optimistic);
  /// ```
  #[inline]
  pub const fn freelist(&self) -> Freelist {
    self.freelist
  }

  /// Sets the compression policy of the memtable.
  ///
  /// Default is `CompressionPolicy::Fast`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, CompressionPolicy};
  ///
  /// let options = Options::new().with_compression_policy(CompressionPolicy::Fast);
  /// ```
  #[inline]
  pub const fn with_compression_policy(mut self, policy: CompressionPolicy) -> Self {
    self.policy = policy;
    self
  }

  /// Returns the compression policy of the memtable.
  ///
  /// Default is `CompressionPolicy::Fast`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, CompressionPolicy};
  ///
  /// let options = Options::new().with_compression_policy(CompressionPolicy::Fast);
  /// assert_eq!(options.compression_policy(), CompressionPolicy::Fast);
  /// ```
  #[inline]
  pub const fn compression_policy(&self) -> CompressionPolicy {
    self.policy
  }

  /// Sets the reserved space of the memtable.
  ///
  /// Default is `0`.
  ///
  /// The reserved space is the space that is allocated for users to store some metadata,
  /// and will not be used by the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::Options;
  ///
  /// let options = Options::new().with_reserved(1024);
  /// ```
  #[inline]
  pub const fn with_reserved(mut self, reserved: u32) -> Self {
    self.reserved = reserved;
    self
  }

  /// Returns the reserved space of the memtable.
  ///
  /// Default is `0`.
  ///
  /// The reserved space is the space that is allocated for users to store some metadata,
  /// and will not be used by the memtable.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::Options;
  ///
  /// let options = Options::new().with_reserved(1024);
  /// assert_eq!(options.reserved(), 1024);
  /// ```
  #[inline]
  pub const fn reserved(&self) -> u32 {
    self.reserved
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

  /// Allocates a new bounded memtable with the options, the backing memory is anonymous.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use memorable::bounded::{Options, generic::Memtable};
  ///
  /// let table = Options::new().map_anon::<Memtable<String, String>>().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn map_anon<M>(self) -> std::io::Result<M>
  where
    M: Constructable,
  {
    M::map_anon(self)
  }

  /// Converts the options to the `SklOptions`.
  #[allow(clippy::wrong_self_convention)]
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
