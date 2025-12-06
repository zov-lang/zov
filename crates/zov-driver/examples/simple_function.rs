//! Example: Creating and compiling a simple function

use zir::arena::Arena;
use zir::idx::Idx;
use zir::intern::InternSet;
use zir::mir::*;
use zir::ty::*;

fn main() {
    // Create arena for allocations
    let arena = Arena::new();

    // Create type intern set
    let types = InternSet::new();

    // Create types
    let i64_ty = types.intern(TyKind::Int(IntWidth::I64), |kind| {
        arena.dropless.alloc(kind)
    });

    // Create a simple function: fn add(a: i64, b: i64) -> i64 { a + b }

    // Local declarations:
    // _0: return place (i64)
    // _1: arg a (i64)
    // _2: arg b (i64)
    let mut local_decls = zir::IndexVec::new();
    local_decls.push(LocalDecl {
        mutability: Mutability::Mut,
        ty: i64_ty,
    });
    local_decls.push(LocalDecl {
        mutability: Mutability::Not,
        ty: i64_ty,
    });
    local_decls.push(LocalDecl {
        mutability: Mutability::Not,
        ty: i64_ty,
    });

    let mut body = Body::new(local_decls, 2);

    // Create basic block: bb0
    let mut bb0 = BasicBlockData::new();

    // Statement: _0 = Add(_1, _2)
    let place_0 = Place::from_local(Local::new(0));
    let place_1 = Place::from_local(Local::new(1));
    let place_2 = Place::from_local(Local::new(2));

    bb0.statements.push(Statement {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: StatementKind::Assign(
            place_0,
            Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(place_1),
                Operand::Copy(place_2),
            ),
        ),
    });

    // Terminator: return
    bb0.terminator = Some(Terminator {
        source_info: SourceInfo { span: Span::DUMMY },
        kind: TerminatorKind::Return,
    });

    body.basic_blocks.push(bb0);

    // Print MIR
    println!("Generated MIR for fn add(a: i64, b: i64) -> i64:");
    println!();
    println!("fn add(_1: i64, _2: i64) -> i64 {{");
    println!("    let mut _0: i64;");
    println!();
    println!("    bb0: {{");
    println!("        _0 = Add(copy _1, copy _2);");
    println!("        return;");
    println!("    }}");
    println!("}}");
    println!();
    println!("Body has {} basic blocks", body.basic_blocks.len());
    println!("Body has {} locals", body.local_decls.len());
    println!("Body has {} arguments", body.arg_count);
}
