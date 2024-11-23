use crate::bounded::generic::{
  BulkDeletionEntry as GenericBulkDeletionEntry, BulkUpdateEntry as GenericBulkUpdateEntry,
  Entry as GenericEntry,
};

use super::Key;

/// An entry in the [`Memtable`](super::Memtable).
pub type Entry<'a, C> = GenericEntry<'a, Key<C>, [u8]>;

/// A bulk deletion entry in the [`Memtable`](super::Memtable).
pub type BulkDeletionEntry<'a, C> = GenericBulkDeletionEntry<'a, Key<C>, [u8]>;

/// A bulk update entry in the [`Memtable`](super::Memtable).
pub type BulkUpdateEntry<'a, C> = GenericBulkUpdateEntry<'a, Key<C>, [u8]>;
