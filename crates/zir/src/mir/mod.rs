//! Mid-level Intermediate Representation

mod pretty;
mod syntax;
mod visit;

pub use pretty::PrettyPrinter;
pub use syntax::*;
pub use visit::{MutVisitor, PlaceContext, Visitor};

use index_vec::IndexVec;

use crate::define_index;
use crate::idx::Idx;
use crate::list::List;
use crate::ty::{Mutability, Ty};

define_index! {
    /// Index for basic blocks.
    pub struct BasicBlock = u32;
}

define_index! {
    /// Index for local variables.
    pub struct Local = u32;
}

define_index! {
    /// Index for definitions (functions, globals, etc.).
    pub struct DefId = u32;
}

/// The starting basic block.
pub const START_BLOCK: BasicBlock = BasicBlock(0);

impl Local {
    /// The return place is always local 0.
    pub const RETURN_PLACE: Self = Self(0);
}

/// A location in the MIR.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Location {
    /// The basic block containing this location.
    pub block: BasicBlock,
    /// The statement index within the block.
    pub statement_index: usize,
}

impl Location {
    /// The start of the function.
    pub const START: Location = Location {
        block: START_BLOCK,
        statement_index: 0,
    };

    /// Returns the next statement location.
    pub fn successor_within_block(&self) -> Location {
        Location {
            block: self.block,
            statement_index: self.statement_index + 1,
        }
    }
}

/// Declaration of a local variable.
#[derive(Clone, Copy, Debug)]
pub struct LocalDecl<'zir> {
    /// Mutability of the local.
    pub mutability: Mutability,
    /// Type of the local.
    pub ty: Ty<'zir>,
}

/// The collection of local declarations.
pub type LocalDecls<'zir> = IndexVec<Local, LocalDecl<'zir>>;

/// A place in memory (an lvalue).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Place<'zir> {
    /// The base local variable.
    pub local: Local,
    /// Projection elements applied to the local.
    pub projection: &'zir List<PlaceElem<'zir>>,
}

impl<'zir> Place<'zir> {
    /// Creates a place referring to a local with no projection.
    pub fn from_local(local: Local) -> Self {
        Place {
            local,
            projection: List::empty(),
        }
    }

    /// Returns true if this place refers to a local with no projection.
    pub fn is_local(&self) -> bool {
        self.projection.is_empty()
    }

    /// Returns the local if this place is just a local reference.
    pub fn as_local(&self) -> Option<Local> {
        if self.is_local() {
            Some(self.local)
        } else {
            None
        }
    }
}

/// A reference to a place (borrowed view).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PlaceRef<'a, 'zir> {
    pub local: Local,
    pub projection: &'a [PlaceElem<'zir>],
}

impl<'a, 'zir> From<&'a Place<'zir>> for PlaceRef<'a, 'zir> {
    fn from(place: &'a Place<'zir>) -> Self {
        PlaceRef {
            local: place.local,
            projection: place.projection.as_slice(),
        }
    }
}

/// Projection elements for places.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PlaceElem<'zir> {
    /// Dereference a pointer or reference.
    Deref,
    /// Subtype coercion (reinterpret as different type).
    Subtype(Ty<'zir>),
    /// Field access by index.
    Field(u32),
    /// Array/slice indexing.
    Index(Local),
}

/// Basic blocks in a function body.
#[derive(Clone, Debug, Default)]
pub struct BasicBlocks<'zir> {
    blocks: IndexVec<BasicBlock, BasicBlockData<'zir>>,
}

impl<'zir> BasicBlocks<'zir> {
    /// Creates empty basic blocks.
    pub fn new() -> Self {
        Self {
            blocks: IndexVec::new(),
        }
    }

    /// Returns an iterator over the basic blocks.
    pub fn iter(&self) -> impl Iterator<Item = &BasicBlockData<'zir>> {
        self.blocks.iter()
    }

    /// Returns an iterator with indices.
    pub fn iter_enumerated(&self) -> impl Iterator<Item = (BasicBlock, &BasicBlockData<'zir>)> {
        self.blocks.iter_enumerated()
    }

    /// Returns the number of basic blocks.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Returns true if there are no basic blocks.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Adds a new basic block and returns its index.
    pub fn push(&mut self, data: BasicBlockData<'zir>) -> BasicBlock {
        self.blocks.push(data)
    }
}

impl<'zir> std::ops::Index<BasicBlock> for BasicBlocks<'zir> {
    type Output = BasicBlockData<'zir>;

    fn index(&self, bb: BasicBlock) -> &Self::Output {
        &self.blocks[bb]
    }
}

impl<'zir> std::ops::IndexMut<BasicBlock> for BasicBlocks<'zir> {
    fn index_mut(&mut self, bb: BasicBlock) -> &mut Self::Output {
        &mut self.blocks[bb]
    }
}

/// A function body.
#[derive(Clone, Debug, Default)]
pub struct Body<'zir> {
    /// The basic blocks in this function.
    pub basic_blocks: BasicBlocks<'zir>,
    /// Local variable declarations.
    pub local_decls: LocalDecls<'zir>,
    /// Number of function arguments (first N locals after return place).
    pub arg_count: usize,
    /// Pass count for debugging.
    pub pass_count: usize,
}

impl<'zir> Body<'zir> {
    /// Creates a new empty body.
    pub fn new(local_decls: LocalDecls<'zir>, arg_count: usize) -> Self {
        Self {
            basic_blocks: BasicBlocks::new(),
            local_decls,
            arg_count,
            pass_count: 0,
        }
    }

    /// Returns the return type of the function.
    pub fn return_ty(&self) -> Ty<'zir> {
        self.local_decls[Local::RETURN_PLACE].ty
    }

    /// Returns iterator over argument locals.
    pub fn args_iter(&self) -> impl Iterator<Item = Local> {
        (1..=self.arg_count).map(Local::new)
    }

    /// Returns iterator over all locals.
    pub fn local_iter(&self) -> impl Iterator<Item = Local> {
        (0..self.local_decls.len()).map(Local::new)
    }
}
