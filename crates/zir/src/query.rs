//! Incremental compilation database
//!
//! This module provides the foundation for incremental compilation using Salsa.
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
