use anyhow::{anyhow, bail, ensure, Context, Result};
use wasmtime::component::{Component, Func, Instance, Linker, LinkerInstance, Type, Val};
use wasmtime::{AsContext, AsContextMut};

use crate::{
    bad_utf8, declare_vecs, handle_call_error, handle_result, to_str, wasm_byte_vec_t,
    wasm_config_t, wasm_engine_t, wasm_name_t, wasm_trap_t, wasmtime_error_t, CStoreContextMut,
    StoreData,
};
use core::ffi::c_void;
use std::collections::HashMap;
use std::{mem, mem::MaybeUninit, ptr, slice, str};

#[no_mangle]
pub extern "C" fn wasmtime_config_component_model_set(c: &mut wasm_config_t, enable: bool) {
    c.config.wasm_component_model(enable);
}

pub type wasmtime_component_val_string_t = wasm_byte_vec_t;

#[repr(C)]
#[derive(Clone)]
pub struct wasmtime_component_val_record_field_t {
    pub name: wasm_name_t,
    pub val: wasmtime_component_val_t,
}

impl Default for wasmtime_component_val_record_field_t {
    fn default() -> Self {
        Self {
            name: Vec::new().into(),
            val: Default::default(),
        }
    }
}

declare_vecs! {
    (
        name: wasmtime_component_val_vec_t,
        ty: wasmtime_component_val_t,
        new: wasmtime_component_val_vec_new,
        empty: wasmtime_component_val_vec_new_empty,
        uninit: wasmtime_component_val_vec_new_uninitialized,
        copy: wasmtime_component_val_vec_copy,
        delete: wasmtime_component_val_vec_delete,
    )
    (
        name: wasmtime_component_val_record_t,
        ty: wasmtime_component_val_record_field_t,
        new: wasmtime_component_val_record_field_new,
        empty: wasmtime_component_val_record_field_new_empty,
        uninit: wasmtime_component_val_record_field_new_uninitialized,
        copy: wasmtime_component_val_record_field_copy,
        delete: wasmtime_component_val_record_field_delete,
    )
    (
        name: wasmtime_component_val_flags_t,
        ty: u32,
        new: wasmtime_component_val_flags_new,
        empty: wasmtime_component_val_flags_new_empty,
        uninit: wasmtime_component_val_flags_new_uninitialized,
        copy: wasmtime_component_val_flags_copy,
        delete: wasmtime_component_val_flags_delete,
    )
}

#[repr(C)]
#[derive(Clone)]
pub struct wasmtime_component_val_variant_t {
    pub index: u32,
    pub val: Option<Box<wasmtime_component_val_t>>,
}

#[repr(C)]
#[derive(Clone)]
pub struct wasmtime_component_val_result_t {
    pub value: Option<Box<wasmtime_component_val_t>>,
    pub error: bool,
}

#[repr(C)]
#[derive(Clone)]
pub struct wasmtime_component_val_enum_t {
    pub discriminant: u32,
}

#[no_mangle]
pub extern "C" fn wasmtime_component_val_flags_set(
    flags: &mut wasmtime_component_val_flags_t,
    index: u32,
    enabled: bool,
) {
    let mut f = flags.take();
    let (idx, bit) = ((index / u32::BITS) as usize, index % u32::BITS);
    if idx >= f.len() {
        f.resize(idx + 1, Default::default());
    }
    if enabled {
        f[idx] |= 1 << (bit);
    } else {
        f[idx] &= !(1 << (bit));
    }
    flags.set_buffer(f);
}

#[no_mangle]
pub extern "C" fn wasmtime_component_val_flags_test(
    flags: &wasmtime_component_val_flags_t,
    index: u32,
) -> bool {
    let flags = flags.as_slice();
    let (idx, bit) = ((index / u32::BITS) as usize, index % u32::BITS);
    flags.get(idx).map(|v| v & (1 << bit) != 0).unwrap_or(false)
}

#[repr(C, u8)]
#[derive(Clone)]
pub enum wasmtime_component_val_t {
    Bool(bool),
    S8(i8),
    U8(u8),
    S16(i16),
    U16(u16),
    S32(i32),
    U32(u32),
    S64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    Char(char),
    String(wasmtime_component_val_string_t),
    List(wasmtime_component_val_vec_t),
    Record(wasmtime_component_val_record_t),
    Tuple(wasmtime_component_val_vec_t),
    Variant(wasmtime_component_val_variant_t),
    Enum(wasmtime_component_val_enum_t),
    Option(Option<Box<wasmtime_component_val_t>>),
    Result(wasmtime_component_val_result_t),
    Flags(wasmtime_component_val_flags_t),
}

impl wasmtime_component_val_t {
    fn into_val(self, ty: &Type) -> Result<Val> {
        Ok(match self {
            wasmtime_component_val_t::Bool(b) => {
                ensure!(
                    ty == &Type::Bool,
                    "attempted to create a bool for a {}",
                    ty.desc()
                );
                Val::Bool(b)
            }
            wasmtime_component_val_t::S8(v) => {
                ensure!(
                    ty == &Type::S8,
                    "attempted to create a s8 for a {}",
                    ty.desc()
                );
                Val::S8(v)
            }
            wasmtime_component_val_t::U8(v) => {
                ensure!(
                    ty == &Type::U8,
                    "attempted to create a u8 for a {}",
                    ty.desc()
                );
                Val::U8(v)
            }
            wasmtime_component_val_t::S16(v) => {
                ensure!(
                    ty == &Type::S16,
                    "attempted to create a s16 for a {}",
                    ty.desc()
                );
                Val::S16(v)
            }
            wasmtime_component_val_t::U16(v) => {
                ensure!(
                    ty == &Type::U16,
                    "attempted to create a u16 for a {}",
                    ty.desc()
                );
                Val::U16(v)
            }
            wasmtime_component_val_t::S32(v) => {
                ensure!(
                    ty == &Type::S32,
                    "attempted to create a s32 for a {}",
                    ty.desc()
                );
                Val::S32(v)
            }
            wasmtime_component_val_t::U32(v) => {
                ensure!(
                    ty == &Type::U32,
                    "attempted to create a u32 for a {}",
                    ty.desc()
                );
                Val::U32(v)
            }
            wasmtime_component_val_t::S64(v) => {
                ensure!(
                    ty == &Type::S64,
                    "attempted to create a s64 for a {}",
                    ty.desc()
                );
                Val::S64(v)
            }
            wasmtime_component_val_t::U64(v) => {
                ensure!(
                    ty == &Type::U64,
                    "attempted to create a u64 for a {}",
                    ty.desc()
                );
                Val::U64(v)
            }
            wasmtime_component_val_t::F32(v) => {
                ensure!(
                    ty == &Type::Float32,
                    "attempted to create a float32 for a {}",
                    ty.desc()
                );
                Val::Float32(v)
            }
            wasmtime_component_val_t::F64(v) => {
                ensure!(
                    ty == &Type::Float64,
                    "attempted to create a float64 for a {}",
                    ty.desc()
                );
                Val::Float64(v)
            }
            wasmtime_component_val_t::Char(v) => {
                ensure!(
                    ty == &Type::Char,
                    "attempted to create a char for a {}",
                    ty.desc()
                );
                Val::Char(v)
            }
            wasmtime_component_val_t::String(mut v) => {
                ensure!(
                    ty == &Type::String,
                    "attempted to create a string for a {}",
                    ty.desc()
                );
                Val::String(String::from_utf8(v.take())?.into_boxed_str())
            }
            wasmtime_component_val_t::List(mut v) => {
                if let Type::List(ty) = ty {
                    ty.new_val(
                        v.take()
                            .into_iter()
                            .map(|v| v.into_val(&ty.ty()))
                            .collect::<Result<Vec<_>>>()?
                            .into_boxed_slice(),
                    )?
                } else {
                    bail!("attempted to create a list for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Record(mut v) => {
                if let Type::Record(ty) = ty {
                    let mut field_vals: HashMap<Vec<u8>, wasmtime_component_val_t> =
                        HashMap::from_iter(
                            v.take().into_iter().map(|mut f| (f.name.take(), f.val)),
                        );
                    let field_tys = ty.fields();
                    ty.new_val(
                        field_tys
                            .map(|tyf| {
                                if let Some(v) = field_vals.remove(tyf.name.as_bytes()) {
                                    Ok((tyf.name, v.into_val(&tyf.ty)?))
                                } else {
                                    bail!("record missing field: {}", tyf.name);
                                }
                            })
                            .collect::<Result<Vec<_>>>()?,
                    )?
                } else {
                    bail!("attempted to create a record for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Tuple(mut v) => {
                if let Type::Tuple(ty) = ty {
                    ty.new_val(
                        ty.types()
                            .zip(v.take().into_iter())
                            .map(|(ty, v)| v.into_val(&ty))
                            .collect::<Result<Vec<_>>>()?
                            .into_boxed_slice(),
                    )?
                } else {
                    bail!("attempted to create a tuple for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Variant(v) => {
                if let Type::Variant(ty) = ty {
                    let case = ty
                        .cases()
                        .nth(v.index as usize)
                        .with_context(|| format!("missing variant {}", v.index))?;
                    ensure!(
                        case.ty.is_some() == v.val.is_some(),
                        "variant type mismatch: {}",
                        case.ty.map(|ty| ty.desc()).unwrap_or("none")
                    );
                    if let (Some(t), Some(v)) = (case.ty, v.val) {
                        let v = v.into_val(&t)?;
                        ty.new_val(case.name, Some(v))?
                    } else {
                        ty.new_val(case.name, None)?
                    }
                } else {
                    bail!("attempted to create a variant for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Enum(v) => {
                if let Type::Enum(ty) = ty {
                    let name = ty
                        .names()
                        .nth(v.discriminant as usize)
                        .with_context(|| format!("missing enumeration {}", v.discriminant))?;
                    ty.new_val(name)?
                } else {
                    bail!("attempted to create an enum for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Option(v) => {
                if let Type::Option(ty) = ty {
                    ty.new_val({
                        match v {
                            Some(v) => Some(v.into_val(&ty.ty())?),
                            None => None,
                        }
                    })?
                } else {
                    bail!("attempted to create an option for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Result(v) => {
                if let Type::Result(ty) = ty {
                    let v = if v.error {
                        Ok(match v.value {
                            Some(v) => {
                                let ty = ty.err().context("expected err type")?;
                                Some(v.into_val(&ty)?)
                            }
                            None => {
                                ensure!(ty.err().is_none(), "expected no err type");
                                None
                            }
                        })
                    } else {
                        Ok(match v.value {
                            Some(v) => {
                                let ty = ty.ok().context("expected ok type")?;
                                Some(v.into_val(&ty)?)
                            }
                            None => {
                                ensure!(ty.ok().is_none(), "expected no ok type");
                                None
                            }
                        })
                    };
                    ty.new_val(v)?
                } else {
                    bail!("attempted to create a result for a {}", ty.desc());
                }
            }
            wasmtime_component_val_t::Flags(flags) => {
                if let Type::Flags(ty) = ty {
                    let mut set = Vec::new();
                    for (idx, name) in ty.names().enumerate() {
                        if wasmtime_component_val_flags_test(&flags, idx as u32) {
                            set.push(name);
                        }
                    }
                    ty.new_val(&set)?
                } else {
                    bail!("attempted to create a flags for a {}", ty.desc());
                }
            }
        })
    }
}

impl TryFrom<&Val> for wasmtime_component_val_t {
    type Error = anyhow::Error;

    fn try_from(value: &Val) -> Result<Self> {
        Ok(match value {
            Val::Bool(v) => wasmtime_component_val_t::Bool(*v),
            Val::S8(v) => wasmtime_component_val_t::S8(*v),
            Val::U8(v) => wasmtime_component_val_t::U8(*v),
            Val::S16(v) => wasmtime_component_val_t::S16(*v),
            Val::U16(v) => wasmtime_component_val_t::U16(*v),
            Val::S32(v) => wasmtime_component_val_t::S32(*v),
            Val::U32(v) => wasmtime_component_val_t::U32(*v),
            Val::S64(v) => wasmtime_component_val_t::S64(*v),
            Val::U64(v) => wasmtime_component_val_t::U64(*v),
            Val::Float32(v) => wasmtime_component_val_t::F32(*v),
            Val::Float64(v) => wasmtime_component_val_t::F64(*v),
            Val::Char(v) => wasmtime_component_val_t::Char(*v),
            Val::String(v) => {
                let v = v.to_string().into_bytes();
                wasmtime_component_val_t::String(v.into())
            }
            Val::List(v) => {
                let v = v.iter().map(|v| v.try_into()).collect::<Result<Vec<_>>>()?;
                wasmtime_component_val_t::List(v.into())
            }
            Val::Record(v) => {
                let v = v
                    .fields()
                    .map(|(name, v)| {
                        Ok(wasmtime_component_val_record_field_t {
                            name: name.to_string().into_bytes().into(),
                            val: v.try_into()?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                wasmtime_component_val_t::Record(v.into())
            }
            Val::Tuple(v) => {
                let v = v
                    .values()
                    .iter()
                    .map(|v| v.try_into())
                    .collect::<Result<Vec<_>>>()?;
                wasmtime_component_val_t::Tuple(v.into())
            }
            Val::Variant(v) => {
                let val = match v.payload() {
                    Some(v) => Some(Box::new(v.try_into()?)),
                    None => None,
                };
                let discriminant = v.discriminant();
                let index = v
                    .ty()
                    .cases()
                    .enumerate()
                    .find(|(_, v)| v.name == discriminant)
                    .map(|(idx, _)| idx as u32)
                    .context("expected valid discriminant")?;
                wasmtime_component_val_t::Variant(wasmtime_component_val_variant_t { index, val })
            }
            Val::Enum(v) => {
                let discriminant = v.discriminant();
                let index = v
                    .ty()
                    .names()
                    .zip(0u32..)
                    .find(|(n, _)| *n == discriminant)
                    .map(|(_, idx)| idx)
                    .context("expected valid discriminant")?;
                wasmtime_component_val_t::Enum(wasmtime_component_val_enum_t {
                    discriminant: index,
                })
            }
            Val::Option(v) => wasmtime_component_val_t::Option(match v.value() {
                Some(v) => Some(Box::new(v.try_into()?)),
                None => None,
            }),
            Val::Result(v) => {
                let (error, value) = match v.value() {
                    Ok(v) => (false, v),
                    Err(v) => (true, v),
                };
                let value = match value {
                    Some(v) => Some(Box::new(v.try_into()?)),
                    None => None,
                };
                wasmtime_component_val_t::Result(wasmtime_component_val_result_t { value, error })
            }
            Val::Flags(v) => {
                let mapping: HashMap<_, _> = v.ty().names().zip(0u32..).collect();
                let mut flags: wasmtime_component_val_flags_t = Vec::new().into();
                for name in v.flags() {
                    let idx = mapping.get(name).context("expected valid name")?;
                    wasmtime_component_val_flags_set(&mut flags, *idx, true);
                }
                wasmtime_component_val_t::Flags(flags)
            }
            Val::Resource(_) => bail!("resource types are unimplemented"),
        })
    }
}

impl Default for wasmtime_component_val_t {
    fn default() -> Self {
        Self::Bool(false)
    }
}

pub type wasmtime_component_val_kind_t = u8;
pub const WASMTIME_COMPONENT_VAL_KIND_BOOL: wasmtime_component_val_kind_t = 0;
pub const WASMTIME_COMPONENT_VAL_KIND_S8: wasmtime_component_val_kind_t = 1;
pub const WASMTIME_COMPONENT_VAL_KIND_U8: wasmtime_component_val_kind_t = 2;
pub const WASMTIME_COMPONENT_VAL_KIND_S16: wasmtime_component_val_kind_t = 3;
pub const WASMTIME_COMPONENT_VAL_KIND_U16: wasmtime_component_val_kind_t = 4;
pub const WASMTIME_COMPONENT_VAL_KIND_S32: wasmtime_component_val_kind_t = 5;
pub const WASMTIME_COMPONENT_VAL_KIND_U32: wasmtime_component_val_kind_t = 6;
pub const WASMTIME_COMPONENT_VAL_KIND_S64: wasmtime_component_val_kind_t = 7;
pub const WASMTIME_COMPONENT_VAL_KIND_U64: wasmtime_component_val_kind_t = 8;
pub const WASMTIME_COMPONENT_VAL_KIND_FLOAT_32: wasmtime_component_val_kind_t = 9;
pub const WASMTIME_COMPONENT_VAL_KIND_FLOAT_64: wasmtime_component_val_kind_t = 10;
pub const WASMTIME_COMPONENT_VAL_KIND_CHAR: wasmtime_component_val_kind_t = 11;
pub const WASMTIME_COMPONENT_VAL_KIND_STRING: wasmtime_component_val_kind_t = 12;
pub const WASMTIME_COMPONENT_VAL_KIND_LIST: wasmtime_component_val_kind_t = 13;
pub const WASMTIME_COMPONENT_VAL_KIND_RECORD: wasmtime_component_val_kind_t = 14;
pub const WASMTIME_COMPONENT_VAL_KIND_TUPLE: wasmtime_component_val_kind_t = 15;
pub const WASMTIME_COMPONENT_VAL_KIND_VARIANT: wasmtime_component_val_kind_t = 16;
pub const WASMTIME_COMPONENT_VAL_KIND_ENUM: wasmtime_component_val_kind_t = 17;
pub const WASMTIME_COMPONENT_VAL_KIND_OPTION: wasmtime_component_val_kind_t = 18;
pub const WASMTIME_COMPONENT_VAL_KIND_RESULT: wasmtime_component_val_kind_t = 19;
pub const WASMTIME_COMPONENT_VAL_KIND_FLAGS: wasmtime_component_val_kind_t = 20;

#[repr(transparent)]
pub struct wasmtime_component_t {
    component: Component,
}

#[no_mangle]
pub unsafe extern "C" fn wasmtime_component_from_binary(
    engine: &wasm_engine_t,
    bytes: *const u8,
    len: usize,
    out: &mut *mut wasmtime_component_t,
) -> Option<Box<wasmtime_error_t>> {
    let bytes = crate::slice_from_raw_parts(bytes, len);
    handle_result(Component::from_binary(&engine.engine, bytes), |component| {
        *out = Box::into_raw(Box::new(wasmtime_component_t { component }));
    })
}

#[no_mangle]
pub unsafe extern "C" fn wasmtime_component_delete(_: Box<wasmtime_component_t>) {}

pub type wasmtime_component_func_callback_t = extern "C" fn(
    *mut c_void,
    CStoreContextMut<'_>,
    *const wasmtime_component_val_t,
    usize,
    *mut wasmtime_component_val_t,
    usize,
) -> Option<Box<wasm_trap_t>>;

struct HostFuncDefinition {
    path: Vec<String>,
    name: String,
    signature: String,
    callback: wasmtime_component_func_callback_t,
    data: *mut c_void,
    finalizer: Option<extern "C" fn(*mut std::ffi::c_void)>,
}

#[repr(C)]
pub struct wasmtime_component_linker_t {
    linker: Linker<StoreData>,
    is_built: bool,
    functions: Vec<HostFuncDefinition>,
}

#[no_mangle]
pub extern "C" fn wasmtime_component_linker_new(
    engine: &wasm_engine_t,
) -> Box<wasmtime_component_linker_t> {
    Box::new(wasmtime_component_linker_t {
        linker: Linker::new(&engine.engine),
        is_built: false,
        functions: Vec::new(),
    })
}

#[no_mangle]
pub unsafe extern "C" fn wasmtime_component_linker_define_func(
    linker: &mut wasmtime_component_linker_t,
    path_buf: *const u8,
    path_len: usize,
    name_buf: *const u8,
    name_len: usize,
    signature_buf: *const u8,
    signature_len: usize,
    callback: wasmtime_component_func_callback_t,
    data: *mut c_void,
    finalizer: Option<extern "C" fn(*mut std::ffi::c_void)>,
) -> Option<Box<wasmtime_error_t>> {
    if linker.is_built {
        return Some(Box::new(wasmtime_error_t::from(anyhow!(
            "cannot define a function in a linker already built"
        ))));
    }
    let path = to_str!(path_buf, path_len)
        .split('.')
        .filter(|s| s.len() > 0)
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
    let name = to_str!(name_buf, name_len).to_string();
    let signature = to_str!(signature_buf, signature_len).to_string();
    linker.functions.push(HostFuncDefinition {
        path,
        name,
        signature,
        callback,
        data,
        finalizer,
    });
    None
}

macro_rules! sig_to_type {
    (i) => {
        i32
    };
    (f) => {
        f32
    };
    (s) => {
        String
    };
    (v) => {
        Vec<u8>
    };
}

macro_rules! sig_to_wamr {
    (i) => {
        "i"
    };
    (f) => {
        "f"
    };
    (s) => {
        "$"
    };
    (v) => {
        "*~"
    };
}

macro_rules! ret_to_wamr {
    (i) => {
        "i"
    };
    (f) => {
        "f"
    };
    (s) => {
        "$"
    };
    (v) => {
        "v"
    };
    (u) => {
        ""
    };
}

macro_rules! ret_to_type {
    (i) => {
        (i32,)
    };
    (f) => {
        (f32,)
    };
    (s) => {
        (String,)
    };
    (v) => {
        (Vec<u8>,)
    };
    (u) => {
        ()
    };
}

macro_rules! sig_count {
    () => { 0 };
    ($head:ident) => { 1 };
    ($head:ident, $($tail:ident),*) => { 1 + sig_count!($($tail),*) };
}

macro_rules! sig_to_val_t {
    (i $arg:expr) => {
        wasmtime_component_val_t::S32($arg)
    };
    (f $arg:expr) => {
        wasmtime_component_val_t::F32($arg)
    };
    (s $arg:expr) => {{
        let v = $arg.to_string().into_bytes();
        wasmtime_component_val_t::String(v.into())
    }};
    (v $arg:expr) => {{
        let v = $arg.iter().map(|v| wasmtime_component_val_t::U8(*v)).collect::<Vec<_>>();
        wasmtime_component_val_t::List(v.into())
    }};
}

macro_rules! ret_to_val_t {
    ($vars:ident i) => {
        $vars.push(wasmtime_component_val_t::S32(-1))
    };
    ($vars:ident f) => {
        $vars.push(wasmtime_component_val_t::F32(0.0))
    };
    ($vars:ident s) => {
        $vars.push(wasmtime_component_val_t::String(Vec::new().into()))
    };
    ($vars:ident v) => {
        $vars.push(wasmtime_component_val_t::List(Vec::new().into()))
    };
    ($vars:ident u) => {};
}

macro_rules! val_t_to_ret {
    ($output:ident i) => {
        match &$output[0] {
            wasmtime_component_val_t::S32(i) => Ok((*i,)),
            _ => Err(anyhow!("unexpected output type")),
        }
    };
    ($output:ident f) => {
        match &$output[0] {
            wasmtime_component_val_t::F32(f) => Ok((*f,)),
            _ => Err(anyhow!("unexpected output type")),
        }
    };
    ($output:ident s) => {
        match &$output[0] {
            wasmtime_component_val_t::String(s) => match std::str::from_utf8(s.as_slice()) {
                Ok(s) => Ok((s.to_owned(),)),
                Err(err) => Err(anyhow!(err)),
            },
            _ => Err(anyhow!("unexpected output type")),
        }
    };
    ($output:ident v) => {
        match &$output[0] {
            wasmtime_component_val_t::List(v) => {
                // FIXME JJL
                Ok((v.as_slice().iter().map(|val| match val { wasmtime_component_val_t::U8(u) => *u, _ => 0u8 }).collect::<Vec<_>>(),))
            },
            _ => Err(anyhow!("unexpected output type")),
        }
    };
    ($output:ident u) => {
        Ok(())
    };
}

macro_rules! define_c_callback_to_rust_component_fn {
    ( ( $($i:ident $idx:tt),* ) -> $r:ident ) => {
        paste::paste! {
            #[allow(dead_code)]
            #[allow(unused_variables)]
            unsafe fn [< c_callback_to_rust_component_fn_ $($i) _ * _ $r >] (
                callback: wasmtime_component_func_callback_t,
                data: *mut c_void,
                finalizer: Option<extern "C" fn(*mut std::ffi::c_void)>,
            ) -> impl Fn(CStoreContextMut<'_>, ($(sig_to_type!($i),)*)) -> Result<ret_to_type!($r)> {
                let foreign = crate::ForeignData { data, finalizer };
                move |context: CStoreContextMut<'_>, args: ($(sig_to_type!($i),)*)|
                {
                    let _ = &foreign; // move entire foreign into this closure

                    let mut vars = Vec::new();
                    $(
                    vars.push(sig_to_val_t!($i args.$idx));
                    )*
                    ret_to_val_t!(vars $r);
                    // don't use unstable meta-variable expression because later versions of the nightly build
                    // changed to require a '$' : ${count($i)} instead of ${count(i)}, so keep recursive count for now
                    let nb_args = sig_count!($($i),*);
                    let (inputs, outputs) = vars.split_at_mut(nb_args);
                    // Invoke the C function pointer, getting the results.
                    let out = callback(
                        foreign.data,
                        context,
                        inputs.as_ptr(),
                        inputs.len(),
                        outputs.as_mut_ptr(),
                        outputs.len(),
                    );
                    if let Some(trap) = out {
                        return Err(trap.error);
                    }
                    val_t_to_ret!(outputs $r)
                }
            }
        }
    };
}

macro_rules! define_and_use_all_c_callbacks {
    ($(($($i:ident),*) -> $r:ident;)*) => {
        paste::paste! {
            $(define_c_callback_to_rust_component_fn!(($($i ${index()}),*) -> $r);)*
            fn insert_in_instance(instance: &mut LinkerInstance<StoreData>, function: &HostFuncDefinition) -> Result<()> {
                match function.signature.as_str() {
                    $(
                        concat!("(", $(sig_to_wamr!($i),)* ")", ret_to_wamr!($r)) =>
                            instance.func_wrap(&function.name, unsafe { [< c_callback_to_rust_component_fn_ $($i) _ * _ $r >](function.callback, function.data, function.finalizer) }),
                    )*
                    _ => Err(anyhow!("unknown signature {}", function.signature)),
                }
            }
        }
    };
}

define_and_use_all_c_callbacks!(
    (i) -> i;
    (i, i) -> i;
    () -> i;
    () -> u;
    (i) -> u;
    (s) -> u;
    (s) -> i;
    (f, f) -> f;
    (s, s) -> s;
    (s, v, v) -> i;
    (s, s, i, i) -> u;
    (s, s) -> i;
    (s, v) -> i;
    (v, v) -> i;
    (v) -> i;
    (i) -> v;
    (s) -> v;
    (v) -> v;
    (s, v) -> v;
    (s, v, i) -> v;
);

#[no_mangle]
pub extern "C" fn wasmtime_component_linker_build(
    linker: &mut wasmtime_component_linker_t,
) -> Option<Box<wasmtime_error_t>> {
    if linker.is_built {
        return Some(Box::new(wasmtime_error_t::from(anyhow!(
            "cannot build an already built linker"
        ))));
    }

    struct InstanceTree {
        children: HashMap<String, InstanceTree>,
        functions: Vec<HostFuncDefinition>,
    }

    impl InstanceTree {
        fn insert(&mut self, depth: usize, function: HostFuncDefinition) {
            if function.path.len() == depth {
                self.functions.push(function);
            } else {
                let child = self
                    .children
                    .entry(function.path[depth].to_string())
                    .or_insert_with(|| InstanceTree {
                        children: HashMap::new(),
                        functions: Vec::new(),
                    });
                child.insert(depth + 1, function);
            }
        }
        fn build(&self, mut instance: LinkerInstance<StoreData>) -> Result<()> {
            for function in self.functions.iter() {
                insert_in_instance(&mut instance, function)?;
            }
            for (name, child) in self.children.iter() {
                let child_instance = instance.instance(&name)?;
                child.build(child_instance)?;
            }
            Ok(())
        }
    }

    let mut root = InstanceTree {
        children: HashMap::new(),
        functions: Vec::new(),
    };
    for function in linker.functions.drain(..) {
        root.insert(0, function);
    }
    match root.build(linker.linker.root()) {
        Ok(()) => {
            linker.is_built = true;
            None
        }
        Err(err) => Some(Box::new(wasmtime_error_t::from(anyhow!(err)))),
    }
}

#[no_mangle]
pub extern "C" fn wasmtime_component_linker_instantiate(
    linker: &wasmtime_component_linker_t,
    store: CStoreContextMut<'_>,
    component: &wasmtime_component_t,
    out: &mut *mut wasmtime_component_instance_t,
    trap_ret: &mut *mut wasm_trap_t,
) -> Option<Box<wasmtime_error_t>> {
    if !linker.is_built && !linker.functions.is_empty() {
        return Some(Box::new(wasmtime_error_t::from(anyhow!(
            "cannot instantiate with a linker not built"
        ))));
    }
    match linker.linker.instantiate(store, &component.component) {
        Ok(instance) => {
            *out = Box::into_raw(Box::new(wasmtime_component_instance_t { instance }));
            None
        }
        Err(e) => handle_call_error(e, trap_ret),
    }
}

#[repr(transparent)]
pub struct wasmtime_component_instance_t {
    instance: Instance,
}

#[no_mangle]
pub unsafe extern "C" fn wasmtime_component_instance_get_func(
    instance: &wasmtime_component_instance_t,
    context: CStoreContextMut<'_>,
    name: *const u8,
    len: usize,
    item: &mut *mut wasmtime_component_func_t,
) -> bool {
    let name = crate::slice_from_raw_parts(name, len);
    let name = match std::str::from_utf8(name) {
        Ok(name) => name,
        Err(_) => return false,
    };
    let func = instance.instance.get_func(context, name);
    if let Some(func) = func {
        *item = Box::into_raw(Box::new(wasmtime_component_func_t { func }));
    }
    func.is_some()
}

#[repr(transparent)]
pub struct wasmtime_component_func_t {
    func: Func,
}

fn call_func(
    func: &wasmtime_component_func_t,
    mut context: CStoreContextMut<'_>,
    raw_params: &[wasmtime_component_val_t],
    raw_results: &mut [wasmtime_component_val_t],
) -> Result<()> {
    let params = func
        .func
        .params(context.as_context())
        .iter()
        .zip(raw_params.iter())
        .map(|(ty, v)| v.clone().into_val(ty))
        .collect::<Result<Vec<_>>>()?;
    let mut results = vec![Val::Bool(false); raw_results.len()];
    func.func
        .call(context.as_context_mut(), &params, &mut results)?;
    func.func.post_return(context)?;
    for (i, r) in results.iter().enumerate() {
        raw_results[i] = r.try_into()?;
    }
    Ok(())
}

#[no_mangle]
pub unsafe extern "C" fn wasmtime_component_func_call(
    func: &wasmtime_component_func_t,
    context: CStoreContextMut<'_>,
    params: *const wasmtime_component_val_t,
    params_len: usize,
    results: *mut wasmtime_component_val_t,
    results_len: usize,
    out_trap: &mut *mut wasm_trap_t,
) -> Option<Box<wasmtime_error_t>> {
    let raw_params = crate::slice_from_raw_parts(params, params_len);
    let mut raw_results = crate::slice_from_raw_parts_mut(results, results_len);
    match call_func(func, context, &raw_params, &mut raw_results) {
        Ok(_) => None,
        Err(e) => handle_call_error(e, out_trap),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        wasmtime_component_val_flags_set, wasmtime_component_val_flags_t,
        wasmtime_component_val_flags_test,
    };

    #[test]
    fn bit_fiddling() {
        let mut flags: wasmtime_component_val_flags_t = Vec::new().into();
        wasmtime_component_val_flags_set(&mut flags, 1, true);
        assert!(wasmtime_component_val_flags_test(&flags, 1));
        assert!(!wasmtime_component_val_flags_test(&flags, 0));
        wasmtime_component_val_flags_set(&mut flags, 260, true);
        assert!(wasmtime_component_val_flags_test(&flags, 260));
        assert!(!wasmtime_component_val_flags_test(&flags, 261));
        assert!(!wasmtime_component_val_flags_test(&flags, 259));
        assert!(wasmtime_component_val_flags_test(&flags, 1));
        assert!(!wasmtime_component_val_flags_test(&flags, 0));
    }
}
