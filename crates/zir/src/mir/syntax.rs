//! MIR syntax definitions

use smallvec::SmallVec;

use super::{BasicBlock, Local, Place};
use crate::ty::{ScalarRepr, Ty};

/// Source information for diagnostics.
#[derive(Clone, Copy, Debug, Default)]
pub struct SourceInfo {
    /// Byte offset in source file.
    pub span: Span,
}

/// A span in the source code.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    /// Start byte offset.
    pub start: u32,
    /// End byte offset.
    pub end: u32,
}

impl Span {
    /// Creates a dummy span.
    pub const DUMMY: Span = Span { start: 0, end: 0 };

    /// Creates a new span.
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
}

/// Data for a single basic block.
#[derive(Clone, Debug, Default)]
pub struct BasicBlockData<'zir> {
    /// Statements in this block.
    pub statements: Vec<Statement<'zir>>,
    /// The terminator of this block.
    pub terminator: Option<Terminator<'zir>>,
}

impl<'zir> BasicBlockData<'zir> {
    /// Creates a new empty basic block.
    pub fn new() -> Self {
        Self { statements: Vec::new(), terminator: None }
    }

    /// Returns the terminator, panicking if not set.
    pub fn terminator(&self) -> &Terminator<'zir> {
        self.terminator.as_ref().expect("block has no terminator")
    }

    /// Returns mutable reference to terminator.
    pub fn terminator_mut(&mut self) -> &mut Terminator<'zir> {
        self.terminator.as_mut().expect("block has no terminator")
    }
}

/// A statement in a basic block.
#[derive(Clone, Debug)]
pub struct Statement<'zir> {
    /// Source information.
    pub source_info: SourceInfo,
    /// The kind of statement.
    pub kind: StatementKind<'zir>,
}

/// Kinds of statements.
#[derive(Clone, Debug)]
pub enum StatementKind<'zir> {
    /// Assign an rvalue to a place.
    Assign(Place<'zir>, Rvalue<'zir>),
    /// No operation.
    Nop,
    /// Storage live marker.
    StorageLive(Local),
    /// Storage dead marker.
    StorageDead(Local),
}

/// An rvalue (right-hand side of assignment).
#[derive(Clone, Debug)]
pub enum Rvalue<'zir> {
    /// Use an operand directly.
    Use(Operand<'zir>),
    /// Dereference a place and use the value.
    UseDeref(Place<'zir>),
    /// Create a reference to a place.
    Ref(super::super::ty::Mutability, Place<'zir>),
    /// Unary operation.
    UnaryOp(UnOp, Operand<'zir>),
    /// Binary operation.
    BinaryOp(BinOp, Operand<'zir>, Operand<'zir>),
    /// Type cast.
    Cast(CastKind, Operand<'zir>, Ty<'zir>),
    /// Take address of a place.
    AddrOf(super::super::ty::Mutability, Place<'zir>),
    /// Aggregate construction (tuple, struct, etc.).
    Aggregate(AggregateKind<'zir>, Vec<Operand<'zir>>),
}

/// Kinds of aggregates.
#[derive(Clone, Debug)]
pub enum AggregateKind<'zir> {
    /// Tuple construction.
    Tuple,
    /// Array construction.
    Array(Ty<'zir>),
}

/// An operand in an expression.
#[derive(Clone, Debug)]
pub enum Operand<'zir> {
    /// Copy from a place.
    Copy(Place<'zir>),
    /// Move from a place.
    Move(Place<'zir>),
    /// A constant value.
    Const(ConstValue, Ty<'zir>),
}

impl<'zir> Operand<'zir> {
    /// Returns the place if this is a Copy or Move.
    pub fn place(&self) -> Option<&Place<'zir>> {
        match self {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            Operand::Const(..) => None,
        }
    }

    /// Creates a constant operand.
    pub fn const_val(value: ConstValue, ty: Ty<'zir>) -> Self {
        Operand::Const(value, ty)
    }
}

/// A constant value.
#[derive(Clone, Debug)]
pub enum ConstValue {
    /// A scalar value.
    Scalar(ScalarRepr),
    /// A zero-sized type.
    Zst,
}

impl ConstValue {
    /// Creates a scalar constant.
    pub fn scalar(repr: ScalarRepr) -> Self {
        ConstValue::Scalar(repr)
    }

    /// Returns the scalar if this is a scalar constant.
    pub fn as_scalar(&self) -> Option<&ScalarRepr> {
        match self {
            ConstValue::Scalar(s) => Some(s),
            ConstValue::Zst => None,
        }
    }
}

/// Unary operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// Logical/bitwise NOT.
    Not,
    /// Arithmetic negation.
    Neg,
}

/// Binary operators for arithmetic, bitwise, and comparison operations.
///
/// Used in `Rvalue::BinaryOp` to represent two-operand operations.
/// Comparison operators return `bool`, arithmetic/bitwise operators return
/// a value of the same type as their operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// Integer addition: `a + b`
    Add,
    /// Integer subtraction: `a - b`
    Sub,
    /// Integer multiplication: `a * b`
    Mul,
    /// Integer division: `a / b` (truncates toward zero)
    Div,
    /// Integer remainder: `a % b` (sign follows dividend)
    Rem,
    /// Bitwise XOR: `a ^ b`
    BitXor,
    /// Bitwise AND: `a & b`
    BitAnd,
    /// Bitwise OR: `a | b`
    BitOr,
    /// Left shift: `a << b`
    Shl,
    /// Right shift: `a >> b` (arithmetic for signed, logical for unsigned)
    Shr,
    /// Equality comparison: `a == b`
    Eq,
    /// Less than comparison: `a < b`
    Lt,
    /// Less than or equal comparison: `a <= b`
    Le,
    /// Not equal comparison: `a != b`
    Ne,
    /// Greater than or equal comparison: `a >= b`
    Ge,
    /// Greater than comparison: `a > b`
    Gt,
}

impl BinOp {
    /// Returns true if this is a comparison operator.
    pub fn is_comparison(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt)
    }
}

/// Cast kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastKind {
    /// Integer to integer cast.
    IntToInt,
    /// Pointer to integer cast.
    PtrToInt,
    /// Integer to pointer cast.
    IntToPtr,
    /// Pointer to pointer cast.
    PtrToPtr,
}

/// A block terminator.
#[derive(Clone, Debug)]
pub struct Terminator<'zir> {
    /// Source information.
    pub source_info: SourceInfo,
    /// The kind of terminator.
    pub kind: TerminatorKind<'zir>,
}

/// Kinds of terminators that end a basic block.
#[derive(Clone, Debug)]
pub enum TerminatorKind<'zir> {
    /// Unconditional jump to target block.
    Goto { target: BasicBlock },
    /// Conditional switch on an integer value.
    SwitchInt { discr: Operand<'zir>, targets: SwitchTargets },
    /// Return from function.
    Return,
    /// Unreachable code marker.
    Unreachable,
    /// Function call with destination and optional continuation block.
    Call {
        func: Operand<'zir>,
        args: Vec<Operand<'zir>>,
        dest: Place<'zir>,
        target: Option<BasicBlock>,
        fn_span: Span,
    },
}

impl<'zir> TerminatorKind<'zir> {
    /// Returns the successor blocks of this terminator.
    pub fn successors(&self) -> Vec<BasicBlock> {
        match self {
            TerminatorKind::Goto { target } => vec![*target],
            TerminatorKind::SwitchInt { targets, .. } => targets.all_targets(),
            TerminatorKind::Return | TerminatorKind::Unreachable => vec![],
            TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
        }
    }
}

/// Switch targets for conditional branches.
#[derive(Clone, Debug, PartialEq)]
pub struct SwitchTargets {
    /// Values to match against.
    pub values: SmallVec<[u128; 1]>,
    /// Target blocks (last one is the "otherwise" block).
    pub targets: SmallVec<[BasicBlock; 2]>,
}

impl SwitchTargets {
    /// Creates a new switch with the given value-target pairs and otherwise target.
    pub fn new(iter: impl Iterator<Item = (u128, BasicBlock)>, otherwise: BasicBlock) -> Self {
        let (values, mut targets): (SmallVec<_>, SmallVec<_>) = iter.unzip();
        targets.push(otherwise);
        Self { values, targets }
    }

    /// Creates a simple if-else switch.
    pub fn if_else(value: u128, then_bb: BasicBlock, else_bb: BasicBlock) -> Self {
        Self { values: smallvec::smallvec![value], targets: smallvec::smallvec![then_bb, else_bb] }
    }

    /// Returns the otherwise target.
    pub fn otherwise(&self) -> BasicBlock {
        *self.targets.last().expect("switch must have otherwise target")
    }

    /// Returns all target blocks.
    pub fn all_targets(&self) -> Vec<BasicBlock> {
        self.targets.to_vec()
    }

    /// Returns iterator over value-target pairs.
    pub fn iter(&self) -> impl Iterator<Item = (u128, BasicBlock)> + '_ {
        self.values.iter().copied().zip(self.targets.iter().copied())
    }
}
