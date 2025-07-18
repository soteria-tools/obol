extern crate rustc_smir;
extern crate stable_mir;

use rustc_smir::IndexedVal;
use stable_mir::ty::{self};
use std::hash::Hash;

#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MyGenericArgKind(pub ty::GenericArgKind);

#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MyGenericArgs(pub Vec<MyGenericArgKind>);

impl MyGenericArgKind {
    pub fn sort(&self) -> isize {
        match &self.0 {
            ty::GenericArgKind::Const(tyconst) => (tyconst.id.to_index() as isize) * 4,
            ty::GenericArgKind::Type(ty) => (ty.to_index() as isize) * 4 + 1,
            ty::GenericArgKind::Lifetime(reg) => {
                let v = match &reg.kind {
                    ty::RegionKind::ReErased => 0,
                    ty::RegionKind::ReStatic => -1,
                    ty::RegionKind::RePlaceholder(p) => p.universe as isize, // idk...
                    ty::RegionKind::ReBound(idx, reg) => (idx + reg.var) as isize,
                    ty::RegionKind::ReEarlyParam(eb) => eb.index as isize,
                };
                v * 4 + 2
            }
        }
    }
}

impl Hash for MyGenericArgKind {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.sort().hash(state);
    }
}

impl From<ty::GenericArgs> for MyGenericArgs {
    fn from(args: ty::GenericArgs) -> Self {
        MyGenericArgs(args.0.into_iter().map(MyGenericArgKind).collect())
    }
}

impl Into<ty::GenericArgs> for MyGenericArgs {
    fn into(self) -> ty::GenericArgs {
        ty::GenericArgs(self.0.into_iter().map(|g| g.0).collect())
    }
}

impl MyGenericArgs {
    pub fn sort_key(&self) -> isize {
        let vec = self
            .0
            .iter()
            .map(MyGenericArgKind::sort)
            .collect::<Vec<_>>();
        // hash the sorts
        let mut hash: isize = 0;
        for (i, v) in vec.iter().enumerate() {
            hash = hash.wrapping_add(v.wrapping_mul(31).wrapping_add(i as isize));
        }
        hash
    }

    pub fn empty() -> Self {
        MyGenericArgs(Vec::new())
    }
}
