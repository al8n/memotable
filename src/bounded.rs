// /// The dynamic key-value type `Memtable`s.
// pub mod dynamic;

/// The generic key-value type `Memtable`s.
pub mod generic;

mod options;
pub use options::Options;

pub use skl::error::{ArenaError, Error};

mod sealed {
  pub trait Constructable: Sized {
    fn construct(opts: super::Options) -> Result<Self, super::Error>;
  }
}
