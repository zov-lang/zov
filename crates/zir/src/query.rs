//! Salsa-based incremental compilation database
//!
//! This module provides the foundation for incremental compilation using Salsa.
//! It defines the query interfaces for the ZIR compiler that enable efficient
//! recomputation when sources change.

use std::sync::Arc;

use crate::mir::DefId;

/// Query group for source inputs
#[salsa::query_group(SourceDatabaseStorage)]
pub trait SourceDatabase {
    /// Returns the source text for a given source file.
    #[salsa::input]
    fn source_text(&self, file_id: SourceFileId) -> Arc<String>;

    /// Returns all source files in the compilation.
    #[salsa::input]
    fn source_files(&self) -> Arc<Vec<SourceFileId>>;
}

/// Query group for type checking
#[salsa::query_group(TypeDatabaseStorage)]
pub trait TypeDatabase: SourceDatabase {
    /// Returns the type-checked body for a definition.
    fn type_check(&self, def_id: DefId) -> Arc<TypeCheckResult>;
}

fn type_check(_db: &dyn TypeDatabase, _def_id: DefId) -> Arc<TypeCheckResult> {
    // Placeholder implementation
    Arc::new(TypeCheckResult { errors: vec![] })
}

/// Query group for MIR lowering
#[salsa::query_group(MirDatabaseStorage)]
pub trait MirDatabase: TypeDatabase {
    /// Returns the MIR body for a definition.
    fn mir_body(&self, def_id: DefId) -> Arc<MirResult>;

    /// Returns all definitions in a source file.
    fn definitions(&self, file_id: SourceFileId) -> Arc<Vec<DefId>>;
}

fn mir_body(_db: &dyn MirDatabase, _def_id: DefId) -> Arc<MirResult> {
    // Placeholder implementation
    Arc::new(MirResult { body: None, errors: vec![] })
}

fn definitions(_db: &dyn MirDatabase, _file_id: SourceFileId) -> Arc<Vec<DefId>> {
    // Placeholder implementation
    Arc::new(vec![])
}

/// Unique identifier for source files
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceFileId(pub u32);

impl SourceFileId {
    /// Creates a new source file ID.
    pub fn new(id: u32) -> Self {
        Self(id)
    }
}

/// Result of type checking
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypeCheckResult {
    /// Type checking errors
    pub errors: Vec<CompilerError>,
}

/// Result of MIR lowering
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MirResult {
    /// The MIR body if successful
    pub body: Option<MirBodyRef>,
    /// Any errors encountered during lowering
    pub errors: Vec<CompilerError>,
}

/// Reference to a MIR body (placeholder, actual body would be stored in arena)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirBodyRef {
    /// The definition this body belongs to
    pub def_id: DefId,
}

/// A compiler error or diagnostic
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilerError {
    /// Error message
    pub message: String,
    /// Source location
    pub span: Option<crate::mir::Span>,
    /// Error severity
    pub severity: Severity,
}

/// Error severity level
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// A fatal error that prevents compilation
    Error,
    /// A warning that doesn't prevent compilation
    Warning,
    /// An informational note
    Note,
}

/// The main compiler database
///
/// This struct implements all the query traits and serves as the central
/// point for incremental compilation.
#[salsa::database(SourceDatabaseStorage, TypeDatabaseStorage, MirDatabaseStorage)]
#[derive(Default)]
pub struct CompilerDatabase {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for CompilerDatabase {}

impl CompilerDatabase {
    /// Creates a new compiler database.
    pub fn new() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_database_creation() {
        let db = CompilerDatabase::new();
        // Just verify the database can be created
        let _ = db;
    }

    #[test]
    fn test_source_input() {
        let mut db = CompilerDatabase::new();
        let file_id = SourceFileId::new(0);

        // Set source text
        db.set_source_text(file_id, Arc::new("fn main() {}".to_string()));
        db.set_source_files(Arc::new(vec![file_id]));

        // Query source text
        let text = db.source_text(file_id);
        assert_eq!(&*text, "fn main() {}");

        // Query source files
        let files = db.source_files();
        assert_eq!(files.len(), 1);
        assert_eq!(files[0], file_id);
    }

    #[test]
    fn test_incremental_update() {
        let mut db = CompilerDatabase::new();
        let file_id = SourceFileId::new(0);

        // Set initial source
        db.set_source_text(file_id, Arc::new("fn foo() {}".to_string()));

        // Query and cache
        let text1 = db.source_text(file_id);
        assert_eq!(&*text1, "fn foo() {}");

        // Update source
        db.set_source_text(file_id, Arc::new("fn bar() {}".to_string()));

        // Query again - should return updated value
        let text2 = db.source_text(file_id);
        assert_eq!(&*text2, "fn bar() {}");
    }
}
