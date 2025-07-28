//! Translate information about items: name, attributes, etc.

extern crate rustc_span;
extern crate stable_mir;

use super::translate_crate::TransItemSource;
use super::translate_ctx::{ItemTransCtx, TranslateCtx};
use charon_lib::ast::*;
use log::trace;
use stable_mir::{CrateDef, mir, rustc_internal, ty};
use std::cmp::Ord;
use std::path::Component;

// Spans
impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Register a file if it is a "real" file and was not already registered
    /// `span` must be a span from which we obtained that filename.
    fn register_file(&mut self, filename: FileName, _span: ty::Span) -> FileId {
        // Lookup the file if it was already registered
        match self.file_to_id.get(&filename) {
            Some(id) => *id,
            None => {
                let file = File {
                    name: filename.clone(),
                    crate_name: "?".into(),
                    contents: None,
                };
                let id = self.translated.files.push(file);
                self.file_to_id.insert(filename, id);
                id
            }
        }
    }

    pub fn translate_filename(&mut self, name: &rustc_span::FileName) -> meta::FileName {
        match name {
            rustc_span::FileName::Real(name) => {
                use rustc_span::RealFileName;
                match name {
                    RealFileName::LocalPath(path) => FileName::Local(path.clone()),
                    RealFileName::Remapped { virtual_name, .. } => {
                        // We use the virtual name because it is always available.
                        // That name normally starts with `/rustc/<hash>/`. For our purposes we hide
                        // the hash.
                        let mut components_iter = virtual_name.components();
                        if let Some(
                            [
                                Component::RootDir,
                                Component::Normal(rustc),
                                Component::Normal(hash),
                            ],
                        ) = components_iter.by_ref().array_chunks().next()
                            && rustc.to_str() == Some("rustc")
                            && hash.len() == 40
                        {
                            let path_without_hash = [Component::RootDir, Component::Normal(rustc)]
                                .into_iter()
                                .chain(components_iter)
                                .collect();
                            FileName::Virtual(path_without_hash)
                        } else {
                            FileName::Virtual(virtual_name.clone())
                        }
                    }
                }
            }
            // We use the debug formatter to generate a filename.
            // This is not ideal, but filenames are for debugging anyway.
            _ => FileName::NotReal(format!("{name:?}")),
        }
    }

    pub fn translate_raw_span(&mut self, rspan: &ty::Span) -> meta::RawSpan {
        let filename = FileName::Local(rspan.get_filename().into());
        let file_id = match &filename {
            FileName::NotReal(_) => {
                // For now we forbid not real filenames
                unimplemented!();
            }
            FileName::Virtual(_) | FileName::Local(_) => self.register_file(filename, *rspan),
        };

        let lines = rspan.get_lines();
        let beg = Loc {
            line: lines.start_line,
            col: lines.start_col,
        };
        let end = Loc {
            line: lines.end_line,
            col: lines.end_col,
        };

        // Put together
        meta::RawSpan { file_id, beg, end }
    }

    pub(crate) fn translate_span_from_smir(&mut self, span: &ty::Span) -> Span {
        Span {
            span: self.translate_raw_span(span),
            generated_from_span: None,
        }
    }
}

// Names
impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Retrieve the name for this [`mir::DefId`]. Because a given `DefId` may give rise to several
    /// charon items, prefer to use `translate_name` when possible.
    ///
    /// We lookup the path associated to an id, and convert it to a name.
    /// Paths very precisely identify where an item is. There are important
    /// subcases, like the items in an `Impl` block:
    /// ```ignore
    /// impl<T> List<T> {
    ///   fn new() ...
    /// }
    /// ```
    ///
    /// One issue here is that "List" *doesn't appear* in the path, which would
    /// look like the following:
    ///
    ///   `TypeNS("Crate") :: Impl :: ValueNs("new")`
    ///                       ^^^
    ///           This is where "List" should be
    ///
    /// For this reason, whenever we find an `Impl` path element, we actually
    /// lookup the type of the sub-path, from which we can derive a name.
    ///
    /// Besides, as there may be several "impl" blocks for one type, each impl
    /// block is identified by a unique number (rustc calls this a
    /// "disambiguator"), which we grab.
    ///
    /// Example:
    /// ========
    /// For instance, if we write the following code in crate `test` and module
    /// `bla`:
    /// ```ignore
    /// impl<T> Foo<T> {
    ///   fn foo() { ... }
    /// }
    ///
    /// impl<T> Foo<T> {
    ///   fn bar() { ... }
    /// }
    /// ```
    ///
    /// The names we will generate for `foo` and `bar` are:
    /// `[Ident("test"), Ident("bla"), Ident("Foo"), Impl(impl<T> Ty<T>, Disambiguator(0)), Ident("foo")]`
    /// `[Ident("test"), Ident("bla"), Ident("Foo"), Impl(impl<T> Ty<T>, Disambiguator(1)), Ident("bar")]`
    pub fn def_id_to_name(&mut self, def_id: stable_mir::DefId) -> Result<Name, Error> {
        if let Some(name) = self.cached_names.get(&def_id) {
            return Ok(name.clone());
        }
        trace!("Computing name for `{def_id:?}`");

        // let parent_name = if let Some(parent) = &def_id.parent {
        //     self.def_id_to_name(parent)?
        // } else {
        //     Name { name: Vec::new() }
        // };
        let mut name = Name { name: Vec::new() };
        let name_str = def_id.name();
        for elem in name_str.split("::") {
            // We use `Ident` for all names, even if they are not identifiers.
            // This is because we don't have a `PathElem` for these.
            name.name
                .push(PathElem::Ident(elem.to_string(), Disambiguator::ZERO));
        }

        trace!("Computed name for `{def_id:?}`: `{name:?}`");
        self.cached_names.insert(def_id.clone(), name.clone());
        Ok(name)
    }

    /// Retrieve the name for an item.
    pub fn translate_name(&mut self, src: &TransItemSource) -> Result<Name, Error> {
        let def_id = src.as_def_id();
        let mut name = self.def_id_to_name(def_id)?;

        match src {
            TransItemSource::Closure(..) => name
                .name
                .push(PathElem::Ident("closure".into(), Disambiguator::ZERO)),
            TransItemSource::ClosureAsFn(..) => {
                name.name
                    .push(PathElem::Ident("closure_as_fn".into(), Disambiguator::ZERO));
            }
            TransItemSource::Fun(_) | TransItemSource::Type(..) => 'add_generics: {
                let (gargs, span) = match src {
                    TransItemSource::Fun(instance) => (instance.args(), instance.def.span()),
                    TransItemSource::Type(adt, gargs) => (gargs.clone().into(), adt.span()),
                    _ => unreachable!(),
                };
                if gargs.0.is_empty() {
                    break 'add_generics;
                }
                let span = self.translate_span_from_smir(&span);
                let mut item_ctx = ItemTransCtx::new(None, self);
                let generics = item_ctx.translate_generic_args(span, &gargs)?;
                name.name.push(PathElem::Monomorphized(Box::new(generics)));
            }
            _ => {}
        }

        Ok(name)
    }

    // pub(crate) fn opacity_for_name(&self, name: &Name) -> ItemOpacity {
    //     self.options.opacity_for_name(&self.translated, name)
    // }
}

// Attributes
impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    // pub(crate) fn translate_inline(&self, def: &mir::FullDef) -> Option<InlineAttr> {
    //     match def.kind() {
    //         mir::DefKind::Fn { inline, .. } | mir::DefKind::AssocFn { inline, .. } => {
    //             match inline {
    //                 mir::InlineAttr::None => None,
    //                 mir::InlineAttr::Hint => Some(InlineAttr::Hint),
    //                 mir::InlineAttr::Never => Some(InlineAttr::Never),
    //                 mir::InlineAttr::Always => Some(InlineAttr::Always),
    //                 mir::InlineAttr::Force { .. } => Some(InlineAttr::Always),
    //             }
    //         }
    //         _ => None,
    //     }
    // }

    // pub(crate) fn translate_attr_info(&mut self, def: &mir::FullDef) -> AttrInfo {
    //     // Default to `false` for impl blocks and closures.
    //     let public = def.visibility.unwrap_or(false);
    //     let inline = self.translate_inline(def);
    //     let attributes: Vec<Attribute> = vec![];
    //     // def
    //     // .attributes
    //     // .iter()
    //     // .filter_map(|attr| self.translate_attribute(&attr))
    //     // .collect_vec();

    //     let rename = {
    //         let mut renames = attributes.iter().filter_map(|a| a.as_rename()).cloned();
    //         let rename = renames.next();
    //         if renames.next().is_some() {
    //             let span = self.translate_span_from_smir(&def.span);
    //             register_error!(
    //                 self,
    //                 span,
    //                 "There should be at most one `charon::rename(\"...\")` \
    //                 or `aeneas::rename(\"...\")` attribute per declaration",
    //             );
    //         }
    //         rename
    //     };

    //     AttrInfo {
    //         attributes,
    //         inline,
    //         public,
    //         rename,
    //     }
    // }
}

// `ItemMeta`
impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Compute the meta information for a Rust item.
    pub(crate) fn translate_item_meta(
        &mut self,
        item_src: &TransItemSource,
        name: Name,
    ) -> ItemMeta {
        if let Some(item_meta) = self.cached_item_metas.get(&item_src) {
            return item_meta.clone();
        }
        let span = Span::dummy();
        let mut attr_info = AttrInfo::default();

        match item_src {
            TransItemSource::Fun(instance) => {
                if instance.kind == mir::mono::InstanceKind::Intrinsic {
                    attr_info.attributes.push(Attribute::Unknown(RawAttribute {
                        path: "rustc_intrinsic".to_string(),
                        args: None,
                    }));
                }
            }
            _ => {}
        };

        let internal_id = rustc_internal::internal(self.tcx, item_src.as_def_id());
        let lang_item = self
            .tcx
            .as_lang_item(internal_id)
            .map(|l| l.name().to_ident_string());

        let name_opacity = ItemOpacity::Transparent;
        let opacity = if attr_info.attributes.iter().any(|attr| attr.is_opaque()) {
            // Force opaque in these cases.
            ItemOpacity::Opaque.max(name_opacity)
        } else {
            name_opacity
        };

        let item_meta = ItemMeta {
            name,
            span,
            source_text: None,
            attr_info,
            is_local: true,
            opacity,
            lang_item,
        };
        self.cached_item_metas
            .insert(item_src.clone(), item_meta.clone());
        item_meta
    }
}

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub(crate) fn translate_span_from_smir(&mut self, rspan: &ty::Span) -> Span {
        self.t_ctx.translate_span_from_smir(rspan)
    }

    // pub(crate) fn def_span(&mut self, _def_id: stable_mir::DefId) -> Span {
    //     // self.t_ctx.def_span(def_id)
    //     Span::dummy()
    // }
}
