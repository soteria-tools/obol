#![feature(core_intrinsics)]

use std::any::TypeId;
use std::intrinsics;

pub fn type_id_u32() -> TypeId {
    TypeId::of::<u32>()
}

pub fn type_id_generic<T: 'static>() -> TypeId {
    TypeId::of::<T>()
}

pub fn type_id_intrinsic_u32() -> TypeId {
    intrinsics::type_id::<u32>()
}

pub fn type_id_intrinsic_generic<T: 'static>() -> TypeId {
    intrinsics::type_id::<T>()
}
