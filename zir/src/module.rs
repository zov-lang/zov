//! Module struct holding all arenas for types, functions, and globals.

use std::fmt;
use index_vec::IndexVec;
use serde::{Serialize, Deserialize};

use crate::idx::{TyId, FuncId, GlobalId};
use crate::ty::{TyKind, FnSig, Mutability};
use crate::mir::Body;

/// A global variable.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct Global {
    pub name: String,
    pub ty: TyId,
    pub mutability: Mutability,
}

/// A function definition.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Function {
    pub name: String,
    pub sig: FnSig,
    pub body: Option<Body>,
}

impl Function {
    pub fn new(name: String, sig: FnSig) -> Self {
        Self {
            name,
            sig,
            body: None,
        }
    }

    pub fn with_body(name: String, sig: FnSig, body: Body) -> Self {
        Self {
            name,
            sig,
            body: Some(body),
        }
    }
}

/// A module containing types, functions, and globals.
///
/// This is the top-level container for a ZIR program or library.
/// It owns all the arenas and provides methods to create and look up items.
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Module {
    /// Type arena.
    types: IndexVec<TyId, TyKind>,
    /// Function arena.
    functions: IndexVec<FuncId, Function>,
    /// Global variable arena.
    globals: IndexVec<GlobalId, Global>,
    /// Cached common types.
    #[serde(skip)]
    common_types: Option<CommonTypes>,
}

/// Cached IDs for common types.
#[derive(Clone, Copy)]
struct CommonTypes {
    bool_ty: TyId,
    unit_ty: TyId,
    never_ty: TyId,
    i8_ty: TyId,
    i16_ty: TyId,
    i32_ty: TyId,
    i64_ty: TyId,
    i128_ty: TyId,
    isize_ty: TyId,
    u8_ty: TyId,
    u16_ty: TyId,
    u32_ty: TyId,
    u64_ty: TyId,
    u128_ty: TyId,
    usize_ty: TyId,
}

impl Module {
    /// Create a new empty module.
    pub fn new() -> Self {
        let mut module = Self::default();
        module.init_common_types();
        module
    }

    /// Initialize common types and cache their IDs.
    fn init_common_types(&mut self) {
        use crate::ty::IntWidth;

        let bool_ty = self.intern_type(TyKind::Bool);
        let unit_ty = self.intern_type(TyKind::Unit);
        let never_ty = self.intern_type(TyKind::Never);

        let i8_ty = self.intern_type(TyKind::Int(IntWidth::I8));
        let i16_ty = self.intern_type(TyKind::Int(IntWidth::I16));
        let i32_ty = self.intern_type(TyKind::Int(IntWidth::I32));
        let i64_ty = self.intern_type(TyKind::Int(IntWidth::I64));
        let i128_ty = self.intern_type(TyKind::Int(IntWidth::I128));
        let isize_ty = self.intern_type(TyKind::Int(IntWidth::ISIZE));

        let u8_ty = self.intern_type(TyKind::Uint(IntWidth::I8));
        let u16_ty = self.intern_type(TyKind::Uint(IntWidth::I16));
        let u32_ty = self.intern_type(TyKind::Uint(IntWidth::I32));
        let u64_ty = self.intern_type(TyKind::Uint(IntWidth::I64));
        let u128_ty = self.intern_type(TyKind::Uint(IntWidth::I128));
        let usize_ty = self.intern_type(TyKind::Uint(IntWidth::ISIZE));

        self.common_types = Some(CommonTypes {
            bool_ty,
            unit_ty,
            never_ty,
            i8_ty,
            i16_ty,
            i32_ty,
            i64_ty,
            i128_ty,
            isize_ty,
            u8_ty,
            u16_ty,
            u32_ty,
            u64_ty,
            u128_ty,
            usize_ty,
        });
    }

    fn common(&self) -> &CommonTypes {
        self.common_types
            .as_ref()
            .expect("Module not initialized with common types")
    }

    // Type accessors

    pub fn bool_ty(&self) -> TyId {
        self.common().bool_ty
    }

    pub fn unit_ty(&self) -> TyId {
        self.common().unit_ty
    }

    pub fn never_ty(&self) -> TyId {
        self.common().never_ty
    }

    pub fn i8_ty(&self) -> TyId {
        self.common().i8_ty
    }

    pub fn i16_ty(&self) -> TyId {
        self.common().i16_ty
    }

    pub fn i32_ty(&self) -> TyId {
        self.common().i32_ty
    }

    pub fn i64_ty(&self) -> TyId {
        self.common().i64_ty
    }

    pub fn i128_ty(&self) -> TyId {
        self.common().i128_ty
    }

    pub fn isize_ty(&self) -> TyId {
        self.common().isize_ty
    }

    pub fn u8_ty(&self) -> TyId {
        self.common().u8_ty
    }

    pub fn u16_ty(&self) -> TyId {
        self.common().u16_ty
    }

    pub fn u32_ty(&self) -> TyId {
        self.common().u32_ty
    }

    pub fn u64_ty(&self) -> TyId {
        self.common().u64_ty
    }

    pub fn u128_ty(&self) -> TyId {
        self.common().u128_ty
    }

    pub fn usize_ty(&self) -> TyId {
        self.common().usize_ty
    }

    // Type operations

    /// Intern a type, returning its ID. Returns existing ID if already interned.
    pub fn intern_type(&mut self, kind: TyKind) -> TyId {
        // Check if type already exists
        for (id, existing) in self.types.iter_enumerated() {
            if existing == &kind {
                return id;
            }
        }
        self.types.push(kind)
    }

    /// Get a type kind by ID.
    pub fn get_type(&self, id: TyId) -> &TyKind {
        &self.types[id]
    }

    /// Create an arbitrary bit-width unsigned integer type.
    pub fn uint_ty(&mut self, bits: u16) -> TyId {
        self.intern_type(TyKind::uint(bits))
    }

    /// Create an arbitrary bit-width signed integer type.
    pub fn int_ty(&mut self, bits: u16) -> TyId {
        self.intern_type(TyKind::int(bits))
    }

    /// Create a pointer type.
    pub fn ptr_ty(&mut self, mutability: Mutability, pointee: TyId) -> TyId {
        self.intern_type(TyKind::Ptr(mutability, pointee))
    }

    /// Create a reference type.
    pub fn ref_ty(&mut self, mutability: Mutability, pointee: TyId) -> TyId {
        self.intern_type(TyKind::Ref(mutability, pointee))
    }

    /// Create a tuple type.
    pub fn tuple_ty(&mut self, elements: Vec<TyId>) -> TyId {
        if elements.is_empty() {
            self.unit_ty()
        } else {
            self.intern_type(TyKind::Tuple(elements))
        }
    }

    // Function operations

    /// Add a function to the module.
    pub fn add_function(&mut self, function: Function) -> FuncId {
        self.functions.push(function)
    }

    /// Get a function by ID.
    pub fn get_function(&self, id: FuncId) -> &Function {
        &self.functions[id]
    }

    /// Get a mutable reference to a function.
    pub fn get_function_mut(&mut self, id: FuncId) -> &mut Function {
        &mut self.functions[id]
    }

    /// Find a function by name.
    pub fn find_function(&self, name: &str) -> Option<FuncId> {
        self.functions
            .iter_enumerated()
            .find(|(_, f)| f.name == name)
            .map(|(id, _)| id)
    }

    /// Iterate over all functions.
    pub fn functions(&self) -> impl Iterator<Item = (FuncId, &Function)> {
        self.functions.iter_enumerated()
    }

    // Global operations

    /// Add a global variable to the module.
    pub fn add_global(&mut self, global: Global) -> GlobalId {
        self.globals.push(global)
    }

    /// Get a global by ID.
    pub fn get_global(&self, id: GlobalId) -> &Global {
        &self.globals[id]
    }

    /// Find a global by name.
    pub fn find_global(&self, name: &str) -> Option<GlobalId> {
        self.globals
            .iter_enumerated()
            .find(|(_, g)| g.name == name)
            .map(|(id, _)| id)
    }

    /// Iterate over all globals.
    pub fn globals(&self) -> impl Iterator<Item = (GlobalId, &Global)> {
        self.globals.iter_enumerated()
    }

    // Statistics

    /// Number of types in the module.
    pub fn type_count(&self) -> usize {
        self.types.len()
    }

    /// Number of functions in the module.
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Number of globals in the module.
    pub fn global_count(&self) -> usize {
        self.globals.len()
    }
}

impl fmt::Debug for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Module {{")?;
        writeln!(f, "  types: {} entries", self.types.len())?;
        writeln!(f, "  functions: {} entries", self.functions.len())?;
        writeln!(f, "  globals: {} entries", self.globals.len())?;
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::IntWidth;

    #[test]
    fn test_module_common_types() {
        let module = Module::new();
        assert_eq!(module.get_type(module.bool_ty()), &TyKind::Bool);
        assert_eq!(module.get_type(module.unit_ty()), &TyKind::Unit);
        assert_eq!(module.get_type(module.i32_ty()), &TyKind::Int(IntWidth::I32));
        assert_eq!(module.get_type(module.u64_ty()), &TyKind::Uint(IntWidth::I64));
    }

    #[test]
    fn test_module_intern_type() {
        let mut module = Module::new();

        // Interning same type should return same ID
        let ty1 = module.uint_ty(256);
        let ty2 = module.uint_ty(256);
        assert_eq!(ty1, ty2);

        // Different types should have different IDs
        let ty3 = module.uint_ty(512);
        assert_ne!(ty1, ty3);
    }

    #[test]
    fn test_module_add_function() {
        let mut module = Module::new();
        let sig = FnSig::new(vec![module.i32_ty()], module.i32_ty());
        let func = Function::new("square".to_string(), sig);
        let id = module.add_function(func);

        assert_eq!(module.get_function(id).name, "square");
        assert_eq!(module.find_function("square"), Some(id));
        assert_eq!(module.find_function("nonexistent"), None);
    }

    #[test]
    fn test_module_arbitrary_bit_width() {
        let mut module = Module::new();

        // Test u256
        let u256 = module.uint_ty(256);
        assert_eq!(module.get_type(u256), &TyKind::uint(256));

        // Test i512
        let i512 = module.int_ty(512);
        assert_eq!(module.get_type(i512), &TyKind::int(512));
    }
}
