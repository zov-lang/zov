//! ZIR - Middle-level Intermediate Representation
//!
//! A language-independent MIR designed for:
//! - Arena-based memory management
//! - Arbitrary precision integer types
//! - Multiple codegen backends
//! - Incremental compilation via Salsa 0.24

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
pub use query::{
    CompilerError, FunctionDef, MirResult, Severity, SourceFile, TypeCheckResult, mir_body,
    parse_definitions, type_check,
};
pub use ty::{IntWidth, Mutability, Ty, TyKind};

/// The main database trait for the ZIR compiler.
///
/// This trait combines all query capabilities and is implemented by
/// `CompilerDatabase`.
#[salsa::db]
pub trait Db: salsa::Database {}

/// The main compiler database.
///
/// This struct implements the `Db` trait and serves as the central
/// point for incremental compilation using Salsa 0.24.
#[salsa::db]
#[derive(Default, Clone)]
pub struct CompilerDatabase {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
impl salsa::Database for CompilerDatabase {}

#[salsa::db]
impl Db for CompilerDatabase {}

impl CompilerDatabase {
    /// Creates a new compiler database.
    pub fn new() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests;
