//! SSA analysis for Cranelift codegen

use index_vec::IndexVec;
use zir::mir::{Body, Local, Location, PlaceContext, Rvalue, Visitor};

/// SSA kind for a local variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SsaKind {
    /// Cannot be represented as SSA (address taken, etc.).
    NotSsa,
    /// May be representable as SSA.
    MaybeSsa,
}

/// Analyzes which locals can be represented as SSA variables.
pub fn analyze_ssa<'zir>(body: &Body<'zir>) -> IndexVec<Local, SsaKind> {
    let mut analyzer =
        SsaAnalyzer { kinds: body.local_decls.iter().map(|_| SsaKind::MaybeSsa).collect() };

    analyzer.visit_body(body);
    analyzer.kinds
}

struct SsaAnalyzer {
    kinds: IndexVec<Local, SsaKind>,
}

impl<'zir> Visitor<'zir> for SsaAnalyzer {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'zir>, location: Location) {
        match rvalue {
            // Taking a reference means the local cannot be SSA
            Rvalue::Ref(_, place) | Rvalue::AddrOf(_, place) => {
                self.kinds[place.local] = SsaKind::NotSsa;
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        // If the place is used in a borrowing context, it cannot be SSA
        if matches!(context, PlaceContext::Borrow) {
            self.kinds[local] = SsaKind::NotSsa;
        }
    }
}

#[cfg(test)]
mod tests {
    use zir::mir::LocalDecls;

    use super::*;

    #[test]
    fn test_empty_body() {
        let body = Body::new(LocalDecls::new(), 0);
        let ssa = analyze_ssa(&body);
        assert!(ssa.is_empty());
    }
}
