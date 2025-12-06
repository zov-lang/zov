//! ZIR - Universal Mid-level Intermediate Representation
//!
//! A language-independent MIR designed for:
//! - Arena-based memory management
//! - Arbitrary precision integer types
//! - Multiple codegen backends
//! - Incremental compilation via Salsa

pub mod arena;
pub mod idx;
pub mod intern;
pub mod list;
pub mod mir;
pub mod query;
pub mod ty;

pub use arena::{Arena, DroplessArena, TypedArena};
pub use idx::{Idx, IndexVec};
pub use intern::Interned;
pub use list::List;
pub use mir::{BasicBlock, Body, Local, Place, Statement, Terminator};
pub use query::{CompilerDatabase, MirDatabase, SourceDatabase, SourceFileId, TypeDatabase};
pub use ty::{IntWidth, Mutability, Ty, TyKind};

#[cfg(test)]
mod tests;
