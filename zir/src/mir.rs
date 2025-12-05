//! MIR (Mid-level Intermediate Representation) structures.

use std::fmt;
use index_vec::IndexVec;
use smallvec::SmallVec;
use serde::{Serialize, Deserialize};

use crate::idx::{BasicBlock, Local, TyId};
use crate::scalar::Scalar;
pub use crate::ty::Mutability;

/// Source location information.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceInfo {
    /// Byte offset in source file.
    pub offset: u32,
    /// Length in bytes.
    pub len: u32,
}

impl SourceInfo {
    pub const DUMMY: Self = Self { offset: 0, len: 0 };

    pub fn new(offset: u32, len: u32) -> Self {
        Self { offset, len }
    }
}

/// A location within a function body.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    pub block: BasicBlock,
    pub statement_index: usize,
}

impl Location {
    pub const START: Self = Self {
        block: BasicBlock::START,
        statement_index: 0,
    };

    pub fn successor_within_block(&self) -> Location {
        Location {
            block: self.block,
            statement_index: self.statement_index + 1,
        }
    }
}

impl fmt::Debug for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}[{}]", self.block, self.statement_index)
    }
}

/// A projection element for a place.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum PlaceElem {
    /// Dereference a pointer/reference.
    Deref,
    /// Access a tuple field by index.
    Field(u32),
    /// Subtype cast (non-transmuting).
    Subtype(TyId),
}

impl PlaceElem {
    pub fn is_indirect(&self) -> bool {
        matches!(self, PlaceElem::Deref)
    }
}

/// A place in memory (lvalue).
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Place {
    pub local: Local,
    pub projection: SmallVec<[PlaceElem; 2]>,
}

impl Place {
    /// Create a place for just a local variable.
    pub fn local(local: Local) -> Self {
        Self {
            local,
            projection: SmallVec::new(),
        }
    }

    /// The return place.
    pub fn return_place() -> Self {
        Self::local(Local::RETURN_PLACE)
    }

    /// Check if this is just a local (no projection).
    pub fn as_local(&self) -> Option<Local> {
        if self.projection.is_empty() {
            Some(self.local)
        } else {
            None
        }
    }

    /// Check if this place involves any indirection.
    pub fn is_indirect(&self) -> bool {
        self.projection.iter().any(|e| e.is_indirect())
    }

    /// Add a projection element.
    pub fn project(mut self, elem: PlaceElem) -> Self {
        self.projection.push(elem);
        self
    }

    /// Dereference this place.
    pub fn deref(self) -> Self {
        self.project(PlaceElem::Deref)
    }

    /// Access a field of this place.
    pub fn field(self, index: u32) -> Self {
        self.project(PlaceElem::Field(index))
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.local)?;
        for elem in &self.projection {
            match elem {
                PlaceElem::Deref => write!(f, ".*")?,
                PlaceElem::Field(idx) => write!(f, ".{}", idx)?,
                PlaceElem::Subtype(ty) => write!(f, " as {:?}", ty)?,
            }
        }
        Ok(())
    }
}

impl From<Local> for Place {
    fn from(local: Local) -> Self {
        Self::local(local)
    }
}

/// A constant value.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ConstValue {
    /// A scalar value.
    Scalar(Scalar),
    /// Zero-sized value.
    Zst,
}

impl ConstValue {
    pub fn try_to_scalar(&self) -> Option<&Scalar> {
        match self {
            ConstValue::Scalar(s) => Some(s),
            ConstValue::Zst => None,
        }
    }

    pub fn try_to_bool(&self) -> Option<bool> {
        self.try_to_scalar()?.to_bool()
    }
}

/// An operand (rvalue that can be used in expressions).
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Operand {
    /// Copy the value from a place.
    Copy(Place),
    /// Move the value from a place.
    Move(Place),
    /// A constant value with its type.
    Const(ConstValue, TyId),
}

impl Operand {
    pub fn place(&self) -> Option<&Place> {
        match self {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            Operand::Const(_, _) => None,
        }
    }

    pub fn constant(&self) -> Option<(&ConstValue, TyId)> {
        match self {
            Operand::Const(c, ty) => Some((c, *ty)),
            _ => None,
        }
    }
}

impl fmt::Debug for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Copy(p) => write!(f, "copy {:?}", p),
            Operand::Move(p) => write!(f, "move {:?}", p),
            Operand::Const(c, ty) => write!(f, "const {:?}: {:?}", c, ty),
        }
    }
}

/// Binary operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum BinOp {
    Add,
    AddUnchecked,
    Sub,
    SubUnchecked,
    Mul,
    MulUnchecked,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    ShlUnchecked,
    Shr,
    ShrUnchecked,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Offset,
}

impl BinOp {
    /// Check if this is a comparison operation.
    pub fn is_comparison(&self) -> bool {
        matches!(
            self,
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
        )
    }

    /// Get the operator as a string.
    pub fn as_str(&self) -> &'static str {
        match self {
            BinOp::Add | BinOp::AddUnchecked => "+",
            BinOp::Sub | BinOp::SubUnchecked => "-",
            BinOp::Mul | BinOp::MulUnchecked => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::BitXor => "^",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::Shl | BinOp::ShlUnchecked => "<<",
            BinOp::Shr | BinOp::ShrUnchecked => ">>",
            BinOp::Eq => "==",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Ne => "!=",
            BinOp::Ge => ">=",
            BinOp::Gt => ">",
            BinOp::Offset => "offset",
        }
    }
}

/// Unary operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum UnOp {
    /// Logical/bitwise NOT.
    Not,
    /// Arithmetic negation.
    Neg,
}

impl UnOp {
    pub fn as_str(&self) -> &'static str {
        match self {
            UnOp::Not => "!",
            UnOp::Neg => "-",
        }
    }
}

/// Kind of cast operation.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum CastKind {
    /// Integer to integer conversion.
    IntToInt,
    /// Pointer to pointer conversion.
    PtrToPtr,
    /// Pointer to address (integer).
    PtrToAddr,
    /// Address (integer) to pointer.
    AddrToPtr,
}

/// An rvalue expression.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Rvalue {
    /// Use an operand directly.
    Use(Operand),
    /// Take a reference to a place.
    Ref(Mutability, Place),
    /// Take the address of a place.
    AddrOf(Mutability, Place),
    /// Unary operation.
    UnaryOp(UnOp, Operand),
    /// Binary operation.
    BinaryOp(BinOp, Operand, Operand),
    /// Cast operation.
    Cast(CastKind, Operand, TyId),
}

impl fmt::Debug for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(op) => write!(f, "{:?}", op),
            Rvalue::Ref(m, p) => write!(f, "&{}{:?}", m.prefix_str(), p),
            Rvalue::AddrOf(m, p) => {
                let q = if m.is_mut() { "mut" } else { "const" };
                write!(f, "addr_of!(*{} {:?})", q, p)
            }
            Rvalue::UnaryOp(op, operand) => write!(f, "{}{:?}", op.as_str(), operand),
            Rvalue::BinaryOp(op, lhs, rhs) => {
                write!(f, "{:?} {} {:?}", lhs, op.as_str(), rhs)
            }
            Rvalue::Cast(kind, op, ty) => {
                write!(f, "{:?} as {:?} ({:?})", op, ty, kind)
            }
        }
    }
}

/// A statement in a basic block.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Statement {
    pub source_info: SourceInfo,
    pub kind: StatementKind,
}

impl Statement {
    pub fn new(source_info: SourceInfo, kind: StatementKind) -> Self {
        Self { source_info, kind }
    }

    pub fn nop() -> Self {
        Self::new(SourceInfo::DUMMY, StatementKind::Nop)
    }

    pub fn assign(source_info: SourceInfo, place: Place, rvalue: Rvalue) -> Self {
        Self::new(source_info, StatementKind::Assign(place, rvalue))
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

/// Kind of statement.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum StatementKind {
    /// Assignment: place = rvalue.
    Assign(Place, Rvalue),
    /// No operation.
    Nop,
}

impl fmt::Debug for StatementKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StatementKind::Assign(place, rvalue) => {
                write!(f, "{:?} = {:?}", place, rvalue)
            }
            StatementKind::Nop => write!(f, "nop"),
        }
    }
}

/// Switch targets for conditional branching.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct SwitchTargets {
    pub values: SmallVec<[Scalar; 2]>,
    pub targets: SmallVec<[BasicBlock; 3]>,
}

impl SwitchTargets {
    /// Create switch targets from value-target pairs and an otherwise target.
    pub fn new<I>(branches: I, otherwise: BasicBlock) -> Self
    where
        I: IntoIterator<Item = (Scalar, BasicBlock)>,
    {
        let (values, mut targets): (SmallVec<[Scalar; 2]>, SmallVec<[BasicBlock; 3]>) = branches.into_iter().unzip();
        targets.push(otherwise);
        Self { values, targets }
    }

    /// Create an if-else style switch (single value test).
    pub fn if_else(value: Scalar, then_bb: BasicBlock, else_bb: BasicBlock) -> Self {
        Self {
            values: smallvec::smallvec![value],
            targets: smallvec::smallvec![then_bb, else_bb],
        }
    }

    /// Get the otherwise (fallback) target.
    pub fn otherwise(&self) -> BasicBlock {
        *self.targets.last().expect("SwitchTargets must have at least one target")
    }

    /// Iterate over (value, target) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&Scalar, BasicBlock)> + '_ {
        self.values.iter().zip(self.targets.iter().copied())
    }

    /// Find the target for a given value.
    pub fn target_for_value(&self, value: &Scalar) -> BasicBlock {
        for (v, t) in self.iter() {
            if v == value {
                return t;
            }
        }
        self.otherwise()
    }
}

/// Kind of terminator.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TerminatorKind {
    /// Unconditional jump.
    Goto { target: BasicBlock },
    /// Conditional switch on an integer value.
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    /// Return from the function.
    Return,
    /// Unreachable code.
    Unreachable,
    /// Function call.
    Call {
        func: Operand,
        args: Vec<Operand>,
        dest: Place,
        target: Option<BasicBlock>,
    },
}

impl TerminatorKind {
    /// Get all successor basic blocks.
    pub fn successors(&self) -> impl Iterator<Item = BasicBlock> + '_ {
        let mut single = None;
        let multi: &[BasicBlock] = match self {
            TerminatorKind::Goto { target } => {
                single = Some(*target);
                &[]
            }
            TerminatorKind::SwitchInt { targets, .. } => &targets.targets,
            TerminatorKind::Return | TerminatorKind::Unreachable => &[],
            TerminatorKind::Call { target, .. } => {
                single = *target;
                &[]
            }
        };
        single.into_iter().chain(multi.iter().copied())
    }
}

impl fmt::Debug for TerminatorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TerminatorKind::Goto { target } => write!(f, "goto {:?}", target),
            TerminatorKind::SwitchInt { discr, targets } => {
                write!(f, "switchInt({:?}) -> [", discr)?;
                for (i, (val, bb)) in targets.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {:?}", val, bb)?;
                }
                write!(f, ", otherwise: {:?}]", targets.otherwise())
            }
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Unreachable => write!(f, "unreachable"),
            TerminatorKind::Call {
                func,
                args,
                dest,
                target,
            } => {
                write!(f, "{:?} = call {:?}(", dest, func)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", arg)?;
                }
                write!(f, ")")?;
                if let Some(t) = target {
                    write!(f, " -> {:?}", t)?;
                }
                Ok(())
            }
        }
    }
}

/// A terminator at the end of a basic block.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Terminator {
    pub source_info: SourceInfo,
    pub kind: TerminatorKind,
}

impl Terminator {
    pub fn new(source_info: SourceInfo, kind: TerminatorKind) -> Self {
        Self { source_info, kind }
    }

    pub fn successors(&self) -> impl Iterator<Item = BasicBlock> + '_ {
        self.kind.successors()
    }
}

impl fmt::Debug for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

/// A local variable declaration.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct LocalDecl {
    pub mutability: Mutability,
    pub ty: TyId,
}

impl LocalDecl {
    pub fn new(mutability: Mutability, ty: TyId) -> Self {
        Self { mutability, ty }
    }

    pub fn immut(ty: TyId) -> Self {
        Self::new(Mutability::Not, ty)
    }

    pub fn mutable(ty: TyId) -> Self {
        Self::new(Mutability::Mut, ty)
    }
}

/// Data for a basic block.
#[derive(Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

impl BasicBlockData {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn terminator(&self) -> &Terminator {
        self.terminator.as_ref().expect("basic block has no terminator")
    }

    pub fn terminator_mut(&mut self) -> &mut Terminator {
        self.terminator.as_mut().expect("basic block has no terminator")
    }

    pub fn is_empty_unreachable(&self) -> bool {
        self.statements.is_empty()
            && matches!(
                self.terminator.as_ref().map(|t| &t.kind),
                Some(TerminatorKind::Unreachable)
            )
    }
}

impl fmt::Debug for BasicBlockData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{{")?;
        for stmt in &self.statements {
            writeln!(f, "    {:?};", stmt)?;
        }
        if let Some(term) = &self.terminator {
            writeln!(f, "    {:?}", term)?;
        }
        write!(f, "}}")
    }
}

/// The body of a function.
#[derive(Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Body {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
    pub local_decls: IndexVec<Local, LocalDecl>,
    /// Number of arguments (excluding return place).
    pub arg_count: usize,
}

impl Body {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get an iterator over argument locals (1..=arg_count).
    pub fn args_iter(&self) -> impl Iterator<Item = Local> {
        (1..=self.arg_count).map(Local::new)
    }

    /// Get an iterator over non-argument locals.
    pub fn vars_and_temps_iter(&self) -> impl Iterator<Item = Local> {
        (self.arg_count + 1..self.local_decls.len()).map(Local::new)
    }

    /// Get the return type.
    pub fn return_ty(&self) -> TyId {
        self.local_decls[Local::RETURN_PLACE].ty
    }

    /// Get the start block.
    pub fn start_block(&self) -> &BasicBlockData {
        &self.basic_blocks[BasicBlock::START]
    }
}

impl fmt::Debug for Body {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "fn(...) -> {:?} {{", self.return_ty())?;

        // Print locals
        for (local, decl) in self.local_decls.iter_enumerated() {
            let kind = if local == Local::RETURN_PLACE {
                "return"
            } else if local.index() <= self.arg_count {
                "arg"
            } else {
                "let"
            };
            writeln!(f, "    {} {:?}: {:?};", kind, local, decl.ty)?;
        }

        writeln!(f)?;

        // Print basic blocks
        for (bb, data) in self.basic_blocks.iter_enumerated() {
            writeln!(f, "    {:?}: {{", bb)?;
            for stmt in &data.statements {
                writeln!(f, "        {:?};", stmt)?;
            }
            if let Some(term) = &data.terminator {
                writeln!(f, "        {:?}", term)?;
            }
            writeln!(f, "    }}")?;
        }

        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_place_local() {
        let p = Place::local(Local::new(5));
        assert_eq!(p.as_local(), Some(Local::new(5)));
        assert!(!p.is_indirect());
    }

    #[test]
    fn test_place_deref() {
        let p = Place::local(Local::new(1)).deref();
        assert_eq!(p.as_local(), None);
        assert!(p.is_indirect());
    }

    #[test]
    fn test_switch_targets() {
        let t = SwitchTargets::if_else(
            Scalar::from(1u8),
            BasicBlock::new(1),
            BasicBlock::new(2),
        );
        assert_eq!(t.otherwise(), BasicBlock::new(2));
        assert_eq!(
            t.target_for_value(&Scalar::from(1u8)),
            BasicBlock::new(1)
        );
        assert_eq!(
            t.target_for_value(&Scalar::from(0u8)),
            BasicBlock::new(2)
        );
    }
}
