//! Pretty printing for MIR structures

use std::fmt::{self, Display};

use super::*;

/// Pretty printer for MIR bodies
pub struct PrettyPrinter<'a, 'zir> {
    body: &'a Body<'zir>,
    name: Option<&'a str>,
}

impl<'a, 'zir> PrettyPrinter<'a, 'zir> {
    pub fn new(body: &'a Body<'zir>) -> Self {
        Self { body, name: None }
    }

    pub fn with_name(mut self, name: &'a str) -> Self {
        self.name = Some(name);
        self
    }
}

impl<'a, 'zir> Display for PrettyPrinter<'a, 'zir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let body = self.body;
        let name = self.name.unwrap_or("_");

        // Handle empty body (no locals)
        if body.local_decls.is_empty() {
            write!(f, "fn {}() {{}}", name)?;
            return Ok(());
        }

        // Function signature
        write!(f, "fn {}(", name)?;
        for (i, local) in body.args_iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "_{}: {:?}", local.index(), body.local_decls[local].ty)?;
        }
        write!(f, ") -> {:?}", body.return_ty())?;
        writeln!(f, " {{")?;

        // Local declarations (excluding args and return)
        let first_local = body.arg_count + 1;
        if first_local < body.local_decls.len() {
            for i in first_local..body.local_decls.len() {
                let local = Local::new(i);
                let decl = &body.local_decls[local];
                let mutability = if decl.mutability.is_mut() { "mut " } else { "" };
                writeln!(f, "    let {}_{}: {:?};", mutability, i, decl.ty)?;
            }
            writeln!(f)?;
        }

        // Return place
        writeln!(f, "    let mut _0: {:?};", body.return_ty())?;
        writeln!(f)?;

        // Basic blocks
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            writeln!(f, "    bb{}: {{", bb.index())?;

            for stmt in &data.statements {
                write!(f, "        ")?;
                write_statement(f, stmt)?;
                writeln!(f)?;
            }

            if let Some(term) = &data.terminator {
                write!(f, "        ")?;
                write_terminator(f, term)?;
                writeln!(f)?;
            }

            writeln!(f, "    }}")?;
        }

        write!(f, "}}")
    }
}

fn write_statement(f: &mut fmt::Formatter<'_>, stmt: &Statement<'_>) -> fmt::Result {
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            write_place(f, place)?;
            write!(f, " = ")?;
            write_rvalue(f, rvalue)?;
            write!(f, ";")
        }
        StatementKind::Nop => write!(f, "nop;"),
        StatementKind::StorageLive(local) => write!(f, "StorageLive(_{});", local.index()),
        StatementKind::StorageDead(local) => write!(f, "StorageDead(_{});", local.index()),
    }
}

fn write_place(f: &mut fmt::Formatter<'_>, place: &Place<'_>) -> fmt::Result {
    write!(f, "_{}", place.local.index())?;
    for elem in place.projection.iter() {
        match elem {
            PlaceElem::Deref => write!(f, ".deref")?,
            PlaceElem::Subtype(ty) => write!(f, ".subtype({:?})", ty)?,
            PlaceElem::Field(idx) => write!(f, ".{}", idx)?,
            PlaceElem::Index(local) => write!(f, "[_{}]", local.index())?,
        }
    }
    Ok(())
}

fn write_rvalue(f: &mut fmt::Formatter<'_>, rvalue: &Rvalue<'_>) -> fmt::Result {
    match rvalue {
        Rvalue::Use(op) => write_operand(f, op),
        Rvalue::UseDeref(place) => {
            write!(f, "deref(")?;
            write_place(f, place)?;
            write!(f, ")")
        }
        Rvalue::Ref(mutability, place) => {
            let prefix = if mutability.is_mut() { "&mut " } else { "&" };
            write!(f, "{}", prefix)?;
            write_place(f, place)
        }
        Rvalue::UnaryOp(op, operand) => {
            write!(f, "{:?}(", op)?;
            write_operand(f, operand)?;
            write!(f, ")")
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            write!(f, "{:?}(", op)?;
            write_operand(f, lhs)?;
            write!(f, ", ")?;
            write_operand(f, rhs)?;
            write!(f, ")")
        }
        Rvalue::Cast(kind, operand, ty) => {
            write!(f, "{:?}(", kind)?;
            write_operand(f, operand)?;
            write!(f, " as {:?})", ty)
        }
        Rvalue::AddrOf(mutability, place) => {
            let prefix = if mutability.is_mut() { "addr_of_mut!" } else { "addr_of!" };
            write!(f, "{}(", prefix)?;
            write_place(f, place)?;
            write!(f, ")")
        }
        Rvalue::Aggregate(kind, operands) => {
            match kind {
                AggregateKind::Tuple => write!(f, "(")?,
                AggregateKind::Array(ty) => write!(f, "[{:?}; ", ty)?,
            }
            for (i, op) in operands.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_operand(f, op)?;
            }
            match kind {
                AggregateKind::Tuple => write!(f, ")"),
                AggregateKind::Array(_) => write!(f, "]"),
            }
        }
    }
}

fn write_operand(f: &mut fmt::Formatter<'_>, operand: &Operand<'_>) -> fmt::Result {
    match operand {
        Operand::Copy(place) => {
            write!(f, "copy ")?;
            write_place(f, place)
        }
        Operand::Move(place) => {
            write!(f, "move ")?;
            write_place(f, place)
        }
        Operand::Const(value, ty) => {
            write_const_value(f, value)?;
            write!(f, ": {:?}", ty)
        }
    }
}

fn write_const_value(f: &mut fmt::Formatter<'_>, value: &ConstValue) -> fmt::Result {
    match value {
        ConstValue::Scalar(repr) => write!(f, "{}", repr),
        ConstValue::Zst => write!(f, "{{zst}}"),
    }
}

fn write_terminator(f: &mut fmt::Formatter<'_>, term: &Terminator<'_>) -> fmt::Result {
    match &term.kind {
        TerminatorKind::Goto { target } => write!(f, "goto -> bb{};", target.index()),
        TerminatorKind::SwitchInt { discr, targets } => {
            write!(f, "switchInt(")?;
            write_operand(f, discr)?;
            write!(f, ") -> [")?;
            for (i, (val, bb)) in targets.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}: bb{}", val, bb.index())?;
            }
            if !targets.values.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "otherwise: bb{}];", targets.otherwise().index())
        }
        TerminatorKind::Return => write!(f, "return;"),
        TerminatorKind::Unreachable => write!(f, "unreachable;"),
        TerminatorKind::Call { func, args, dest, target, .. } => {
            write_place(f, dest)?;
            write!(f, " = ")?;
            write_operand(f, func)?;
            write!(f, "(")?;
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_operand(f, arg)?;
            }
            write!(f, ")")?;
            if let Some(target) = target {
                write!(f, " -> bb{}", target.index())?;
            }
            write!(f, ";")
        }
    }
}

impl<'zir> Body<'zir> {
    /// Returns a pretty printer for this body.
    pub fn pretty<'a>(&'a self) -> PrettyPrinter<'a, 'zir> {
        PrettyPrinter::new(self)
    }

    /// Returns a pretty printer with a name.
    pub fn pretty_with_name<'a>(&'a self, name: &'a str) -> PrettyPrinter<'a, 'zir> {
        PrettyPrinter::new(self).with_name(name)
    }
}
