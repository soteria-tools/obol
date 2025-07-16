//! Translate information about items: name, attributes, etc.

extern crate rustc_span;
extern crate stable_mir;

use super::translate_crate::TransItemSource;
use super::translate_ctx::{ItemTransCtx, TranslateCtx};
use charon_lib::ast::*;
use log::trace;
use stable_mir::ty;
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
    fn path_elem_for_def(
        &mut self,
        _span: Span,
        def_id: &stable_mir::DefId,
    ) -> Result<Option<PathElem>, Error> {
        let name = def_id.name();
        Ok(Some(PathElem::Ident(name, Disambiguator::ZERO)))
        // Disambiguator disambiguates identically-named (but distinct) identifiers. This happens
        // notably with macros and inherent impl blocks.
        // let disambiguator = Disambiguator::new(path_elem.disambiguator as usize);
        // // Match over the key data
        // let path_elem = match path_elem.data {
        //     DefPathItem::CrateRoot { name, .. } => {
        //         // Sanity check
        //         error_assert!(self, span, path_elem.disambiguator == 0);
        //         Some(PathElem::Ident(name.clone(), disambiguator))
        //     }
        //     // We map the three namespaces onto a single one. We can always disambiguate by looking
        //     // at the definition.
        //     DefPathItem::TypeNs(symbol)
        //     | DefPathItem::ValueNs(symbol)
        //     | DefPathItem::MacroNs(symbol) => Some(PathElem::Ident(symbol, disambiguator)),
        //     DefPathItem::Impl => {
        //         // let full_def = self.hax_def(def_id)?;
        //         // // Two cases, depending on whether the impl block is
        //         // // a "regular" impl block (`impl Foo { ... }`) or a trait
        //         // // implementation (`impl Bar for Foo { ... }`).
        //         // let impl_elem = match full_def.kind() {
        //         //     // Inherent impl ("regular" impl)
        //         //     mir::DefKind::InherentImpl { ty, .. } => {
        //         //         // We need to convert the type, which may contain quantified
        //         //         // substs and bounds. In order to properly do so, we introduce
        //         //         // a body translation context.
        //         //         let mut bt_ctx = ItemTransCtx::new(def_id.clone(), None, self);
        //         //         bt_ctx.translate_def_generics(span, &full_def)?;
        //         //         let ty = bt_ctx.translate_ty(span, &ty)?;
        //         //         ImplElem::Ty(Binder {
        //         //             kind: BinderKind::InherentImplBlock,
        //         //             params: bt_ctx.into_generics(),
        //         //             skip_binder: ty,
        //         //         })
        //         //     }
        //         //     // Trait implementation
        //         //     mir::DefKind::TraitImpl { .. } => {
        //         //         let impl_id = self.register_trait_impl_id(&None, def_id);
        //         //         ImplElem::Trait(impl_id)
        //         //     }
        //         //     _ => unreachable!(),
        //         // };

        //         // Some(PathElem::Impl(impl_elem))
        //         None
        //     }
        //     // TODO: do nothing for now
        //     DefPathItem::OpaqueTy => None,
        //     // TODO: this is not very satisfactory, but on the other hand
        //     // we should be able to extract closures in local let-bindings
        //     // (i.e., we shouldn't have to introduce top-level let-bindings).
        //     DefPathItem::Closure => Some(PathElem::Ident("closure".to_string(), disambiguator)),
        //     // Do nothing, functions in `extern` blocks are in the same namespace as the
        //     // block.
        //     DefPathItem::ForeignMod => None,
        //     // Do nothing, the constructor of a struct/variant has the same name as the
        //     // struct/variant.
        //     DefPathItem::Ctor => None,
        //     DefPathItem::Use => Some(PathElem::Ident("{use}".to_string(), disambiguator)),
        //     DefPathItem::AnonConst => Some(PathElem::Ident("{const}".to_string(), disambiguator)),
        //     DefPathItem::PromotedConst => Some(PathElem::Ident(
        //         "{promoted_const}".to_string(),
        //         disambiguator,
        //     )),
        //     _ => {
        //         raise_error!(
        //             self,
        //             span,
        //             "Unexpected DefPathItem for `{def_id:?}`: {path_elem:?}"
        //         );
        //     }
        // };
        // Ok(path_elem)
    }

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
        let span = Span::dummy();
        let mut name = Name { name: Vec::new() };
        if let Some(path_elem) = self.path_elem_for_def(span, &def_id)? {
            name.name.push(path_elem);
        }

        trace!("Computed name for `{def_id:?}`: `{name:?}`");
        self.cached_names.insert(def_id.clone(), name.clone());
        Ok(name)
    }

    /// Retrieve the name for an item.
    pub fn translate_name(&mut self, src: &TransItemSource) -> Result<Name, Error> {
        let def_id = src.as_def_id();
        self.def_id_to_name(def_id)
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
        let attr_info = AttrInfo::default();
        // let lang_item = item_src.as_def_id()
        //     .lang_item
        //     .clone()
        //     .or_else(|| def.diagnostic_item.clone());

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
            lang_item: None,
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
