//! MIR visitor traits

use super::*;
use crate::ty::Ty;

/// A visitor for traversing MIR structures immutably.
pub trait Visitor<'zir>: Sized {
    fn visit_body(&mut self, body: &Body<'zir>) {
        self.super_body(body);
    }

    fn visit_basic_block_data(&mut self, bb: BasicBlock, data: &BasicBlockData<'zir>) {
        self.super_basic_block_data(bb, data);
    }

    fn visit_statement(&mut self, stmt: &Statement<'zir>, location: Location) {
        self.super_statement(stmt, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'zir>, location: Location) {
        self.super_terminator(terminator, location);
    }

    fn visit_place(&mut self, place: &Place<'zir>, context: PlaceContext, location: Location) {
        self.super_place(place, context, location);
    }

    fn visit_operand(&mut self, operand: &Operand<'zir>, location: Location) {
        self.super_operand(operand, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'zir>, location: Location) {
        self.super_rvalue(rvalue, location);
    }

    fn visit_local(&mut self, _local: Local, _context: PlaceContext, _location: Location) {}

    fn visit_ty(&mut self, _ty: Ty<'zir>, _location: Location) {}

    fn visit_constant(&mut self, _const_val: &ConstValue, _ty: Ty<'zir>, _location: Location) {}

    // Super methods for default traversal

    fn super_body(&mut self, body: &Body<'zir>) {
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            self.visit_basic_block_data(bb, data);
        }
    }

    fn super_basic_block_data(&mut self, bb: BasicBlock, data: &BasicBlockData<'zir>) {
        for (i, stmt) in data.statements.iter().enumerate() {
            let location = Location { block: bb, statement_index: i };
            self.visit_statement(stmt, location);
        }

        if let Some(ref terminator) = data.terminator {
            let location = Location { block: bb, statement_index: data.statements.len() };
            self.visit_terminator(terminator, location);
        }
    }

    fn super_statement(&mut self, stmt: &Statement<'zir>, location: Location) {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.visit_place(place, PlaceContext::Store, location);
                self.visit_rvalue(rvalue, location);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                self.visit_local(*local, PlaceContext::StorageLive, location);
            }
            StatementKind::Nop => {}
        }
    }

    fn super_terminator(&mut self, terminator: &Terminator<'zir>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Goto { .. } => {}
            TerminatorKind::SwitchInt { discr, .. } => {
                self.visit_operand(discr, location);
            }
            TerminatorKind::Return | TerminatorKind::Unreachable => {}
            TerminatorKind::Call { func, args, dest, .. } => {
                self.visit_operand(func, location);
                for arg in args {
                    self.visit_operand(arg, location);
                }
                self.visit_place(dest, PlaceContext::Store, location);
            }
        }
    }

    fn super_place(&mut self, place: &Place<'zir>, context: PlaceContext, location: Location) {
        self.visit_local(place.local, context, location);
    }

    fn super_operand(&mut self, operand: &Operand<'zir>, location: Location) {
        match operand {
            Operand::Copy(place) => {
                self.visit_place(place, PlaceContext::Copy, location);
            }
            Operand::Move(place) => {
                self.visit_place(place, PlaceContext::Move, location);
            }
            Operand::Const(val, ty) => {
                self.visit_constant(val, *ty, location);
            }
        }
    }

    fn super_rvalue(&mut self, rvalue: &Rvalue<'zir>, location: Location) {
        match rvalue {
            Rvalue::Use(op) => {
                self.visit_operand(op, location);
            }
            Rvalue::UseDeref(place) => {
                self.visit_place(place, PlaceContext::Copy, location);
            }
            Rvalue::Ref(_, place) | Rvalue::AddrOf(_, place) => {
                self.visit_place(place, PlaceContext::Borrow, location);
            }
            Rvalue::UnaryOp(_, op) => {
                self.visit_operand(op, location);
            }
            Rvalue::BinaryOp(_, lhs, rhs) => {
                self.visit_operand(lhs, location);
                self.visit_operand(rhs, location);
            }
            Rvalue::Cast(_, op, ty) => {
                self.visit_operand(op, location);
                self.visit_ty(*ty, location);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    self.visit_operand(op, location);
                }
            }
        }
    }
}

/// A mutable visitor for transforming MIR structures.
pub trait MutVisitor<'zir>: Sized {
    fn visit_body(&mut self, body: &mut Body<'zir>) {
        self.super_body(body);
    }

    fn visit_basic_block_data(&mut self, bb: BasicBlock, data: &mut BasicBlockData<'zir>) {
        self.super_basic_block_data(bb, data);
    }

    fn visit_statement(&mut self, stmt: &mut Statement<'zir>, location: Location) {
        self.super_statement(stmt, location);
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'zir>, location: Location) {
        self.super_terminator(terminator, location);
    }

    fn visit_place(&mut self, place: &mut Place<'zir>, context: PlaceContext, location: Location) {
        self.super_place(place, context, location);
    }

    fn visit_operand(&mut self, operand: &mut Operand<'zir>, location: Location) {
        self.super_operand(operand, location);
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'zir>, location: Location) {
        self.super_rvalue(rvalue, location);
    }

    fn visit_local(&mut self, _local: &mut Local, _context: PlaceContext, _location: Location) {}

    // Super methods for default traversal

    fn super_body(&mut self, body: &mut Body<'zir>) {
        for bb in 0..body.basic_blocks.len() {
            let bb = BasicBlock::new(bb);
            let data = &mut body.basic_blocks[bb];
            // Need to borrow mutably, but we can use indices
            let statements_len = data.statements.len();
            for i in 0..statements_len {
                let location = Location { block: bb, statement_index: i };
                let stmt = &mut body.basic_blocks[bb].statements[i];
                self.visit_statement(stmt, location);
            }

            if body.basic_blocks[bb].terminator.is_some() {
                let location = Location { block: bb, statement_index: statements_len };
                let terminator = body.basic_blocks[bb].terminator.as_mut().unwrap();
                self.visit_terminator(terminator, location);
            }
        }
    }

    fn super_basic_block_data(&mut self, bb: BasicBlock, data: &mut BasicBlockData<'zir>) {
        for (i, stmt) in data.statements.iter_mut().enumerate() {
            let location = Location { block: bb, statement_index: i };
            self.visit_statement(stmt, location);
        }

        if let Some(ref mut terminator) = data.terminator {
            let location = Location { block: bb, statement_index: data.statements.len() };
            self.visit_terminator(terminator, location);
        }
    }

    fn super_statement(&mut self, stmt: &mut Statement<'zir>, location: Location) {
        match &mut stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.visit_place(place, PlaceContext::Store, location);
                self.visit_rvalue(rvalue, location);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                self.visit_local(local, PlaceContext::StorageLive, location);
            }
            StatementKind::Nop => {}
        }
    }

    fn super_terminator(&mut self, terminator: &mut Terminator<'zir>, location: Location) {
        match &mut terminator.kind {
            TerminatorKind::Goto { .. } => {}
            TerminatorKind::SwitchInt { discr, .. } => {
                self.visit_operand(discr, location);
            }
            TerminatorKind::Return | TerminatorKind::Unreachable => {}
            TerminatorKind::Call { func, args, dest, .. } => {
                self.visit_operand(func, location);
                for arg in args {
                    self.visit_operand(arg, location);
                }
                self.visit_place(dest, PlaceContext::Store, location);
            }
        }
    }

    fn super_place(&mut self, place: &mut Place<'zir>, context: PlaceContext, location: Location) {
        self.visit_local(&mut place.local, context, location);
    }

    fn super_operand(&mut self, operand: &mut Operand<'zir>, location: Location) {
        match operand {
            Operand::Copy(place) => {
                self.visit_place(place, PlaceContext::Copy, location);
            }
            Operand::Move(place) => {
                self.visit_place(place, PlaceContext::Move, location);
            }
            Operand::Const(..) => {}
        }
    }

    fn super_rvalue(&mut self, rvalue: &mut Rvalue<'zir>, location: Location) {
        match rvalue {
            Rvalue::Use(op) => {
                self.visit_operand(op, location);
            }
            Rvalue::UseDeref(place) => {
                self.visit_place(place, PlaceContext::Copy, location);
            }
            Rvalue::Ref(_, place) | Rvalue::AddrOf(_, place) => {
                self.visit_place(place, PlaceContext::Borrow, location);
            }
            Rvalue::UnaryOp(_, op) => {
                self.visit_operand(op, location);
            }
            Rvalue::BinaryOp(_, lhs, rhs) => {
                self.visit_operand(lhs, location);
                self.visit_operand(rhs, location);
            }
            Rvalue::Cast(_, op, _) => {
                self.visit_operand(op, location);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    self.visit_operand(op, location);
                }
            }
        }
    }
}

/// Context in which a place is used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlaceContext {
    /// Place is being copied.
    Copy,
    /// Place is being moved.
    Move,
    /// Place is being stored to.
    Store,
    /// Place is being borrowed.
    Borrow,
    /// Storage marker.
    StorageLive,
}

impl PlaceContext {
    /// Returns true if this is a use of the value.
    pub fn is_use(self) -> bool {
        matches!(self, PlaceContext::Copy | PlaceContext::Move)
    }

    /// Returns true if this mutates the place.
    pub fn is_mutating(self) -> bool {
        matches!(self, PlaceContext::Store)
    }
}
