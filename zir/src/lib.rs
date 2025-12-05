//! ZIR - Universal MIR Library for ZoV Language
//!
//! Context-free, arena-based, serializable intermediate representation.

pub mod idx;
pub mod scalar;
pub mod ty;
pub mod mir;
pub mod module;

pub use idx::{BasicBlock, Local, TyId, FuncId, GlobalId};
pub use scalar::Scalar;
pub use ty::{Ty, TyKind, IntWidth, FnSig};
pub use mir::{
    Body, BasicBlockData, Statement, StatementKind,
    Terminator, TerminatorKind, Place, PlaceElem,
    Operand, Rvalue, BinOp, UnOp, CastKind, ConstValue,
    SwitchTargets, Mutability, LocalDecl, SourceInfo,
};
pub use module::Module;
