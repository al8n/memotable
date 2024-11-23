/// The dynamic key-value type `Memtable`s.
pub mod dynamic;

/// The generic key-value type `Memtable`s.
pub mod generic;

mod options;
pub use options::*;

pub use dbutils::buffer::VacantBuffer;
pub use skl::{
  error::{ArenaError, Error},
  KeyBuilder, ValueBuilder,
};

mod sealed {
  pub trait Constructable: Sized {
    fn construct(opts: super::Options) -> Result<Self, super::Error>;

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn map_anon(opts: super::Options) -> std::io::Result<Self>;
  }
}
