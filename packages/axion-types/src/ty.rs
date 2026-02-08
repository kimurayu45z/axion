use std::fmt;

use axion_resolve::def_id::DefId;

/// Internal representation of types used during type checking.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    /// Primitive type: i64, f64, bool, char, str, never, etc.
    Prim(PrimTy),
    /// Unit type: `{}`
    Unit,
    /// Named struct type: `Point`, `Vec[i64]`
    Struct { def_id: DefId, type_args: Vec<Ty> },
    /// Named enum type: `Shape`, `Option[T]`
    Enum { def_id: DefId, type_args: Vec<Ty> },
    /// Tuple type: `{i64, f64}`
    Tuple(Vec<Ty>),
    /// Function type: `Fn(i64) -> bool`
    Fn { params: Vec<Ty>, ret: Box<Ty> },
    /// Reference type: `&str`
    Ref(Box<Ty>),
    /// Slice type: `&[T]`
    Slice(Box<Ty>),
    /// Type parameter (generic): `T` — indexed by DefId
    Param(DefId),
    /// Inference variable (unresolved) — filled by unification
    Infer(InferVar),
    /// Error (poison) — prevents cascading errors
    Error,
}

/// Primitive types built into the language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    F16,
    F32,
    F64,
    Bf16,
    Bool,
    Char,
    Str,
    Never,
}

/// A unique ID for an inference variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InferVar(pub u32);

impl PrimTy {
    /// Try to parse a primitive type name.
    pub fn from_name(name: &str) -> Option<PrimTy> {
        match name {
            "i8" => Some(PrimTy::I8),
            "i16" => Some(PrimTy::I16),
            "i32" => Some(PrimTy::I32),
            "i64" => Some(PrimTy::I64),
            "i128" => Some(PrimTy::I128),
            "u8" => Some(PrimTy::U8),
            "u16" => Some(PrimTy::U16),
            "u32" => Some(PrimTy::U32),
            "u64" => Some(PrimTy::U64),
            "u128" => Some(PrimTy::U128),
            "usize" => Some(PrimTy::Usize),
            "f16" => Some(PrimTy::F16),
            "f32" => Some(PrimTy::F32),
            "f64" => Some(PrimTy::F64),
            "bf16" => Some(PrimTy::Bf16),
            "bool" => Some(PrimTy::Bool),
            "char" => Some(PrimTy::Char),
            "str" => Some(PrimTy::Str),
            "never" => Some(PrimTy::Never),
            _ => None,
        }
    }

    /// Whether this primitive is a numeric type (integer or float).
    pub fn is_numeric(self) -> bool {
        matches!(
            self,
            PrimTy::I8
                | PrimTy::I16
                | PrimTy::I32
                | PrimTy::I64
                | PrimTy::I128
                | PrimTy::U8
                | PrimTy::U16
                | PrimTy::U32
                | PrimTy::U64
                | PrimTy::U128
                | PrimTy::Usize
                | PrimTy::F16
                | PrimTy::F32
                | PrimTy::F64
                | PrimTy::Bf16
        )
    }

    /// Whether this primitive is an integer type.
    pub fn is_integer(self) -> bool {
        matches!(
            self,
            PrimTy::I8
                | PrimTy::I16
                | PrimTy::I32
                | PrimTy::I64
                | PrimTy::I128
                | PrimTy::U8
                | PrimTy::U16
                | PrimTy::U32
                | PrimTy::U64
                | PrimTy::U128
                | PrimTy::Usize
        )
    }
}

impl fmt::Display for PrimTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            PrimTy::I8 => "i8",
            PrimTy::I16 => "i16",
            PrimTy::I32 => "i32",
            PrimTy::I64 => "i64",
            PrimTy::I128 => "i128",
            PrimTy::U8 => "u8",
            PrimTy::U16 => "u16",
            PrimTy::U32 => "u32",
            PrimTy::U64 => "u64",
            PrimTy::U128 => "u128",
            PrimTy::Usize => "usize",
            PrimTy::F16 => "f16",
            PrimTy::F32 => "f32",
            PrimTy::F64 => "f64",
            PrimTy::Bf16 => "bf16",
            PrimTy::Bool => "bool",
            PrimTy::Char => "char",
            PrimTy::Str => "str",
            PrimTy::Never => "never",
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Prim(p) => write!(f, "{p}"),
            Ty::Unit => write!(f, "{{}}"),
            Ty::Struct { def_id, type_args } => {
                write!(f, "Struct({}", def_id.0)?;
                if !type_args.is_empty() {
                    write!(f, "[")?;
                    for (i, arg) in type_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                    }
                    write!(f, "]")?;
                }
                write!(f, ")")
            }
            Ty::Enum { def_id, type_args } => {
                write!(f, "Enum({}", def_id.0)?;
                if !type_args.is_empty() {
                    write!(f, "[")?;
                    for (i, arg) in type_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                    }
                    write!(f, "]")?;
                }
                write!(f, ")")
            }
            Ty::Tuple(elems) => {
                write!(f, "{{")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, "}}")
            }
            Ty::Fn { params, ret } => {
                write!(f, "Fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, ") -> {ret}")
            }
            Ty::Ref(inner) => write!(f, "&{inner}"),
            Ty::Slice(inner) => write!(f, "&[{inner}]"),
            Ty::Param(def_id) => write!(f, "Param({})", def_id.0),
            Ty::Infer(v) => write!(f, "?{}", v.0),
            Ty::Error => write!(f, "<error>"),
        }
    }
}

impl Ty {
    /// Whether this type is numeric (primitive numeric or inference variable).
    pub fn is_numeric(&self) -> bool {
        matches!(self, Ty::Prim(p) if p.is_numeric())
    }
}
