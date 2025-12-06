//! Salsa 0.24 incremental compilation database
//!
//! This module provides the foundation for incremental compilation using Salsa 0.24.
//! It defines the database and query interfaces for the ZIR compiler that enable
//! efficient recomputation when sources change.

use std::sync::Arc;

use crate::mir::DefId;

/// Unique identifier for source files (Salsa input).
#[salsa::input]
pub struct SourceFile {
    /// The source text content.
    #[returns(ref)]
    pub text: String,

    /// The file path or name (for diagnostics).
    #[returns(ref)]
    pub path: String,
}

/// A function definition tracked by Salsa.
///
/// This struct represents a function in the compilation and is used
/// as input to tracked functions.
#[salsa::tracked]
pub struct FunctionDef<'db> {
    /// The source file this function belongs to.
    pub source_file: SourceFile,

    /// The definition ID (index within the crate).
    pub def_id: DefId,

    /// The function name.
    #[returns(ref)]
    pub name: String,
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

/// Tracked function: type check a function definition.
#[salsa::tracked]
pub fn type_check<'db>(db: &'db dyn crate::Db, func: FunctionDef<'db>) -> Arc<TypeCheckResult> {
    let _ = (db, func);
    // Placeholder implementation
    Arc::new(TypeCheckResult { errors: vec![] })
}

/// Tracked function: lower a function to MIR.
#[salsa::tracked]
pub fn mir_body<'db>(db: &'db dyn crate::Db, func: FunctionDef<'db>) -> Arc<MirResult> {
    let def_id = func.def_id(db);
    // Placeholder implementation - just return a reference to the body
    Arc::new(MirResult { body: Some(MirBodyRef { def_id }), errors: vec![] })
}

/// Tracked function: get all function definitions from a source file.
#[salsa::tracked]
pub fn parse_definitions<'db>(
    db: &'db dyn crate::Db,
    file: SourceFile,
) -> Arc<Vec<FunctionDef<'db>>> {
    let _ = file.text(db); // Depend on source text
    // Placeholder implementation - returns empty list
    Arc::new(vec![])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CompilerDatabase;
    use salsa::Setter;

    #[test]
    fn test_database_creation() {
        let db = CompilerDatabase::new();
        let _ = db;
    }

    #[test]
    fn test_source_input() {
        let db = CompilerDatabase::new();

        // Create a source file input
        let file = SourceFile::new(&db, "fn main() {}".to_string(), "test.zov".to_string());

        // Query source text
        let text = file.text(&db);
        assert_eq!(text, "fn main() {}");

        // Query path
        let path = file.path(&db);
        assert_eq!(path, "test.zov");
    }

    #[test]
    fn test_incremental_update() {
        let mut db = CompilerDatabase::new();

        // Create initial source
        let file = SourceFile::new(&db, "fn foo() {}".to_string(), "test.zov".to_string());

        // Query and verify
        let text1 = file.text(&db);
        assert_eq!(text1, "fn foo() {}");

        // Update source using setter
        file.set_text(&mut db).to("fn bar() {}".to_string());

        // Query again - should return updated value
        let text2 = file.text(&db);
        assert_eq!(text2, "fn bar() {}");
    }

    #[test]
    fn test_parse_definitions() {
        let db = CompilerDatabase::new();

        // Create a source file
        let file = SourceFile::new(
            &db,
            "fn add(a: i64, b: i64) -> i64 { a + b }".to_string(),
            "add.zov".to_string(),
        );

        // Parse definitions returns tracked structs via the tracked function
        let defs = parse_definitions(&db, file);
        // Placeholder implementation returns empty list
        assert!(defs.is_empty());
    }
}
