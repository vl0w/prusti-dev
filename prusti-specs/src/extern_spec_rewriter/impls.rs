use super::common::*;
use crate::{span_overrider::SpanOverrider, specifications::common::NameGenerator};
use proc_macro2::TokenStream;
use quote::quote_spanned;
use std::collections::HashMap;
use syn::parse_quote;
use syn::spanned::Spanned;

pub fn rewrite_extern_spec(item_impl: &syn::ItemImpl) -> syn::Result<TokenStream> {
    let rewritten = rewrite_extern_spec_internal(item_impl)?;

    let new_struct = rewritten.generated_struct;
    let new_impl = rewritten.generated_impl;
    let new_trait = rewritten.generated_trait;
    Ok(quote_spanned! {item_impl.span()=>
        #new_trait
        #new_struct
        #new_impl
    })
}

/// Errors that can happen during rewriting of extern impl specs.
/// These are mostly wrong usages of the macro by the user.
#[derive(Debug)]
enum RewriteError {
    CanNotGenerateStructName(proc_macro2::Span, String),
    ImplsWithTraitSupportNoGenerics(proc_macro2::Span),
    TraitObjectWithoutTrait(proc_macro2::Span),
}

impl std::convert::From<RewriteError> for syn::Error {
    fn from(err: RewriteError) -> Self {
        match err {
            RewriteError::CanNotGenerateStructName(span, detailed_message) =>
                syn::Error::new(span, detailed_message),
            RewriteError::ImplsWithTraitSupportNoGenerics(span) =>
                syn::Error::new(span, "Generics for extern trait impls are not supported"),
            RewriteError::TraitObjectWithoutTrait(span) =>
                syn::Error::new(span, "Must specify a trait in an extern spec involving trait objects"),
        }
    }
}

type ExternSpecImplRewriteResult<R> = Result<R, RewriteError>;

#[derive(Debug)]
struct RewrittenExternalSpecs {
    generated_struct: syn::ItemStruct,
    generated_impl: syn::ItemImpl,
    generated_trait: Option<syn::ItemTrait>, // TODO: UGLY!
}

fn rewrite_extern_spec_internal(item_impl: &syn::ItemImpl) -> ExternSpecImplRewriteResult<RewrittenExternalSpecs> {
    let new_struct = generate_new_struct(item_impl)?;
    let struct_ident = &new_struct.ident;
    let generic_args = rewrite_generics(&new_struct.generics);

    let struct_ty: syn::Type = parse_quote_spanned! {item_impl.span()=>
        #struct_ident #generic_args
    };

    if let syn::Type::TraitObject(trait_object) = item_impl.self_ty.as_ref() {
        if item_impl.trait_.is_none() {
            return Err(RewriteError::TraitObjectWithoutTrait(item_impl.span()));
        }

        let (_, trait_path, _) = item_impl.trait_.as_ref().unwrap();
        if has_generic_arguments(trait_path) {
            panic!(); // TODO
        }

        let mut traif_of_impl_assoc_types_map: HashMap<&syn::Ident, &syn::Type> = HashMap::new();
        for item in &item_impl.items {
            if let syn::ImplItem::Type(assoc_type) = item {
                assert!(assoc_type.generics.params.is_empty()); // TODO: Error
                assert!(assoc_type.attrs.is_empty()); // TODO: Error
                assert!(assoc_type.defaultness.is_none()); // TODO: Error
                let ident = &assoc_type.ident;
                let ty = &assoc_type.ty;
                traif_of_impl_assoc_types_map.insert(ident, ty);
            }
        }

        // TODO: Collect associated types

        let a = traif_of_impl_assoc_types_map.keys().clone();
        let b = traif_of_impl_assoc_types_map.values().clone();
        let mut trait_ : syn::ItemTrait = parse_quote!( // TODO: Naming
            #[allow (non_camel_case_types)]
            trait SuperTrait: #trait_path <#(#a = #b),*> {}
        );
        trait_.supertraits.extend(trait_object.bounds.clone());

        let i = &trait_.ident;
        let trait_as_ty: syn::Type = parse_quote!(dyn #i);

        let rewritten_impl = rewrite_dyn_impl(item_impl.clone(), Box::from(struct_ty), Box::from(trait_as_ty))?;


        Ok(RewrittenExternalSpecs{
            generated_struct: new_struct,
            generated_impl: rewritten_impl,
            generated_trait: Some(trait_),
        })
    } else if item_impl.trait_.is_some() {
        let (_, trait_path, _) = item_impl.trait_.as_ref().unwrap();
        if has_generic_arguments(trait_path) {
            return Err(
                RewriteError::ImplsWithTraitSupportNoGenerics(item_impl.generics.params.span())
            );
        }

        let rewritten_impl = rewrite_trait_impl(item_impl.clone(), Box::from(struct_ty))?;

        Ok(RewrittenExternalSpecs {
            generated_struct: new_struct,
            generated_impl: rewritten_impl,
            generated_trait: None,
        })
    } else {
        let mut rewritten_item = item_impl.clone();
        rewrite_plain_impl(&mut rewritten_item, Box::from(struct_ty))?;

        Ok(RewrittenExternalSpecs {
            generated_struct: new_struct,
            generated_impl: rewritten_item,
            generated_trait: None,
        })
    }
}

fn generate_new_struct(item_impl: &syn::ItemImpl) -> ExternSpecImplRewriteResult<syn::ItemStruct> {
    let name_generator = NameGenerator::new();
    let struct_name = match name_generator.generate_struct_name(item_impl) {
        Ok(name) => name,
        Err(msg) => return Err(
            RewriteError::CanNotGenerateStructName(item_impl.span(), msg)
        ),
    };
    let struct_ident = syn::Ident::new(&struct_name, item_impl.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_impl.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident {}
    };
    new_struct.generics = item_impl.generics.clone();

    add_phantom_data_for_generic_params(&mut new_struct);
    Ok(new_struct)
}

/// Rewrite all methods in an impl block to calls to the specified methods.
/// The result of this rewriting is then parsed in `ExternSpecResolver`.
fn rewrite_plain_impl(impl_item: &mut syn::ItemImpl, new_ty: Box<syn::Type>) -> ExternSpecImplRewriteResult<()> {
    let item_ty = &mut impl_item.self_ty;
    if let syn::Type::Path(type_path) = item_ty.as_mut() {
        for seg in type_path.path.segments.iter_mut() {
            if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                genargs.colon2_token = Some(syn::token::Colon2::default());
            }
        }
    }

    for item in impl_item.items.iter_mut() {
        match item {
            syn::ImplItem::Method(method) => {
                rewrite_method(method, item_ty, None);
            }
            syn::ImplItem::Type(_) => {
                // ignore
            }
            _ => {
                unimplemented!("Expected a method when rewriting extern spec");
            }
        }
    }
    impl_item.self_ty = new_ty;

    Ok(())
}

fn rewrite_dyn_impl(
    impl_item: syn::ItemImpl,
    struct_ty: Box<syn::Type>,
    supertrait_ty: Box<syn::Type>,
) -> ExternSpecImplRewriteResult<syn::ItemImpl> {
    if let syn::Type::TraitObject(_) = *supertrait_ty {

    } else {
        todo!();
    }

    let mut new_impl = impl_item.clone();
    new_impl.self_ty = struct_ty;
    new_impl.trait_ = None;
    new_impl.items.clear();

    for item in impl_item.items.iter() {
        if let syn::ImplItem::Method(method) = item {
            let (_, trait_path, _) = &impl_item.trait_.as_ref().unwrap();

            let mut rewritten_method = method.clone();
            rewrite_method(&mut rewritten_method, supertrait_ty.as_ref(), Some(trait_path));

            // Rewrite occurences of associated types in method signature
            // TODO
            // let mut rewriter = AssociatedTypeRewriter::new(&assoc_type_decls);
            // rewriter.rewrite_method_sig(&mut rewritten_method.sig);

            new_impl.items.push(syn::ImplItem::Method(rewritten_method));
        }
    }

    Ok(new_impl)
}

fn rewrite_trait_impl(
    impl_item: syn::ItemImpl,
    new_ty: Box<syn::Type>,
) -> ExternSpecImplRewriteResult<syn::ItemImpl> {
    let item_ty = impl_item.self_ty.clone();

    // Collect declared associated types
    let mut assoc_type_decls = HashMap::<&syn::Ident, syn::TypePath>::new();
    for item in impl_item.items.iter() {
        if let syn::ImplItem::Type(ty) = item {
            if let syn::Type::Path(path) = &ty.ty {
                assoc_type_decls.insert(&ty.ident, path.clone());
            }
        }
    }

    // Create new impl
    let mut new_impl = impl_item.clone();
    new_impl.self_ty = new_ty;
    new_impl.trait_ = None;
    new_impl.items.clear();

    for item in impl_item.items.iter() {
        if let syn::ImplItem::Method(method) = item {
            let (_, trait_path, _) = &impl_item.trait_.as_ref().unwrap();

            let mut rewritten_method = method.clone();
            rewrite_method(&mut rewritten_method, &item_ty, Some(trait_path));

            // Rewrite occurences of associated types in method signature
            let mut rewriter = AssociatedTypeRewriter::new(&assoc_type_decls);
            rewriter.rewrite_method_sig(&mut rewritten_method.sig);

            new_impl.items.push(syn::ImplItem::Method(rewritten_method));
        }
    }

    Ok(new_impl)
}

fn rewrite_method(
    method: &mut syn::ImplItemMethod,
    original_ty: &syn::Type,
    as_ty: Option<&syn::Path>,
) {
    let span = method.span();

    for attr in method.attrs.iter_mut() {
        attr.tokens = rewrite_self(attr.tokens.clone());
    }

    let args = rewrite_method_inputs(original_ty, &mut method.sig.inputs);
    let ident = &method.sig.ident;

    method
        .attrs
        .push(parse_quote_spanned!(span=> #[prusti::extern_spec]));
    method.attrs.push(parse_quote_spanned!(span=> #[trusted]));
    method
        .attrs
        .push(parse_quote_spanned!(span=> #[allow(dead_code)]));

    let mut method_path: syn::ExprPath = match as_ty {
        Some(type_path) => parse_quote_spanned! {ident.span()=>
            < #original_ty as #type_path > :: #ident
        },
        None => parse_quote_spanned! {ident.span()=>
            < #original_ty > :: #ident
        },
    };

    // Fix the span
    syn::visit_mut::visit_expr_path_mut(&mut SpanOverrider::new(ident.span()), &mut method_path);

    method.block = parse_quote_spanned! {span=>
        {
            #method_path (#args);
            unimplemented!()
        }
    };
}

fn has_generic_arguments(path: &syn::Path) -> bool {
    for seg in path.segments.iter() {
        if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
            if !args.args.is_empty() {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::rewrite_extern_spec_internal;
    use quote::ToTokens;
    use syn::parse_quote;

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(actual: T, expected: U) {
        assert_eq!(
            actual.into_token_stream().to_string(),
            expected.into_token_stream().to_string()
        );
    }

    mod trait_object_impl {
        use crate::extern_spec_rewriter::impls::RewriteError;
        use super::*;

        #[test]
        fn trait_object_impl_without_trait_disallowed() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl dyn Bar {}
            );

            let res= rewrite_extern_spec_internal(&inp_impl);
            let err = res.expect_err("Expected error");
            assert!(matches!(err, RewriteError::TraitObjectWithoutTrait(_)))
        }

        #[test]
        fn generated_struct() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl Foo for dyn Bar {}
            );

            let rewritten= rewrite_extern_spec_internal(&inp_impl).unwrap();

            let struct_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemStruct = parse_quote! {
                #[allow (non_camel_case_types)]
                struct #struct_ident (
                );
            };

            assert_eq_tokenizable(rewritten.generated_struct, expected);
        }

        #[test]
        fn generated_trait() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl Foo for dyn Bar + Baz {}
            );

            let rewritten= rewrite_extern_spec_internal(&inp_impl).unwrap();

            let generated_trait = rewritten.generated_trait.expect("Expected generated trait");
            let generated_trait_ident = &generated_trait.ident;
            let expected: syn::ItemTrait = parse_quote! {
                #[allow (non_camel_case_types)]
                trait #generated_trait_ident : Foo <> + Bar + Baz {}
            };

            assert_eq_tokenizable(generated_trait, expected);
        }

        #[test]
        fn generated_trait_assoc_types() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl Foo for dyn Bar<AssocBar=u32> + Baz<AssocBaz=i32> {
                    type AssocFoo = i32;
                }
            );

            let rewritten= rewrite_extern_spec_internal(&inp_impl).unwrap();

            let generated_trait = rewritten.generated_trait.expect("Expected generated trait");
            let generated_trait_ident = &generated_trait.ident;
            let expected: syn::ItemTrait = parse_quote! {
                #[allow (non_camel_case_types)]
                trait #generated_trait_ident : Foo<AssocFoo=i32> + Bar<AssocBar=u32> + Baz<AssocBaz=i32> {}
            };

            assert_eq_tokenizable(generated_trait, expected);
        }

        #[test]
        fn generated_impl_uses_new_supertrait() {
            let inp_impl: syn::ItemImpl = parse_quote!(
                impl Foo for dyn Bar {
                    fn foo(&self) -> i32;
                }
            );

            let rewritten= rewrite_extern_spec_internal(&inp_impl).unwrap();

            let generated_trait = rewritten.generated_trait.expect("Expected generated trait");
            let generated_trait_ident = &generated_trait.ident;
            let generated_struct_ident = &rewritten.generated_struct.ident;

            let expected: syn::ItemImpl = parse_quote!(
                impl #generated_struct_ident <> {
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &dyn #generated_trait_ident) -> i32 {
                        <dyn #generated_trait_ident as Foo>::foo(_self, );
                        unimplemented!()
                    }
                }
            );

            assert_eq_tokenizable(rewritten.generated_impl, expected);
        }
    }

    mod plain_impl {
        use super::*;

        #[test]
        fn generated_struct() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl<'a, const CONST: i32, T> MyStruct<'a, CONST, T> {}
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let struct_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemStruct = parse_quote! {
                #[allow (non_camel_case_types)]
                struct #struct_ident<'a, const CONST: i32, T> (
                    &'a ::core::marker::PhantomData<()>,
                    ::core::marker::PhantomData<T>
                );
            };

            assert_eq_tokenizable(rewritten.generated_struct, expected);
        }

        #[test]
        fn impl_no_generics() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyStruct {
                    fn foo(&self);
                    fn bar(&mut self);
                    fn baz(self);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &MyStruct) {
                        <MyStruct> :: foo(_self,);
                        unimplemented!()
                    }
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn bar(_self: &mut MyStruct) {
                        <MyStruct> :: bar(_self,);
                        unimplemented!()
                    }
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn baz(_self: MyStruct) {
                        <MyStruct> :: baz(_self,);
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }

        #[test]
        fn impl_generics() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl<I, O> MyStruct<I, O, i32> {
                    fn foo(&self, arg1: I, arg2: i32) -> O;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl<I, O> #newtype_ident<I, O> {
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &MyStruct::<I,O, i32>, arg1: I, arg2: i32) -> O {
                        <MyStruct::<I,O,i32>> :: foo(_self, arg1, arg2, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }

        #[test]
        fn impl_specs() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyStruct {
                    #[requires(self.foo > 42 && arg < 50)]
                    #[ensures(self.foo > 50 && result >= 100)]
                    fn foo(&mut self, arg: i32) -> i32;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[requires(_self.foo > 42 && arg < 50)]
                    #[ensures(_self.foo > 50 && result >= 100)]
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected);
        }
    }

    mod trait_impl {
        use super::*;

        #[test]
        fn no_generics_with_specs() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait for MyStruct {
                    #[requires(self.foo > 42 && arg < 50)]
                    #[ensures(self.foo > 50 && result >= 100)]
                    fn foo(&mut self, arg: i32) -> i32;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[requires(_self.foo > 42 && arg < 50)]
                    #[ensures(_self.foo > 50 && result >= 100)]
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct, arg: i32) -> i32 {
                        <MyStruct as MyTrait> :: foo(_self, arg, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }

        #[test]
        fn associated_types() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait for MyStruct {
                    type Result = i32;
                    fn foo(&mut self) -> Self::Result;
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl).unwrap();

            let newtype_ident = &rewritten.generated_struct.ident;
            let expected_impl: syn::ItemImpl = parse_quote! {
                impl #newtype_ident <> {
                    #[prusti::extern_spec]
                    #[trusted]
                    #[allow(dead_code)]
                    fn foo(_self: &mut MyStruct) -> i32 {
                        <MyStruct as MyTrait> :: foo(_self, );
                        unimplemented!()
                    }
                }
            };

            assert_eq_tokenizable(rewritten.generated_impl.clone(), expected_impl);
        }

        #[test]
        fn generics_not_supported() {
            let mut inp_impl: syn::ItemImpl = parse_quote!(
                impl MyTrait<I> for MyStruct {
                    fn foo(&mut self, arg1: I);
                }
            );

            let rewritten = rewrite_extern_spec_internal(&mut inp_impl);

            assert!(rewritten.is_err());
        }
    }
}
