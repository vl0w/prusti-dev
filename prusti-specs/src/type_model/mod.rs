//! Processes `#[model]` attributed types.
//!
//! Usage documentation can be found in the corresponding macro definition.
//!
//! Given a `#[model]` attributed type `T`, this logic creates the following three items:
//! * A struct `M` which holds the model's fields
//! * A trait which provides a `model` method to be used in specifications
//! * An implementation of the aforementioned trait for `T`.
//!   The implementation is `unimplemented!()`, `#[pure]` and `#[trusted]`
//!
//! The model struct `M` must be copyable.
//!
//! # Note
//! This macro always generates a trait with a `model` method on the fly for every modelled type.
//! With this design, one can even model external types which are not present in the local crate.

use super::parse_quote_spanned;
use crate::{
    common::add_phantom_data_for_generic_params,
    user_provided_type_params::{
        UserAnnotatedTypeParam, UserAnnotatedTypeParamParser, UserAnnotatedTypeParamParserError,
    },
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::ToTokens;
use syn::{parse_quote, spanned::Spanned};
use uuid::Uuid;
use crate::common::{HasGenerics, HasIdent};

/// See module level documentation
pub fn rewrite(item_struct: syn::ItemStruct) -> syn::Result<TokenStream> {
    let res = rewrite_internal(item_struct);
    match res {
        Ok(result) => Ok(result.into_token_stream()),
        Err(err) => Err(err.into()),
    }
}

type TypeModelGenerationResult<R> = Result<R, TypeModelGenerationError>;

fn rewrite_internal(item_struct: syn::ItemStruct) -> TypeModelGenerationResult<TypeModel> {
    let idents = GeneratedIdents::generate(&item_struct);

    let model_struct = ModelStruct::create(&item_struct, &idents)?;
    let to_model_trait = ToModelTrait::create(&item_struct, &model_struct, &idents);
    let model_impl = create_model_impl(&item_struct, &model_struct, &to_model_trait)?;

    Ok(TypeModel {
        model_struct,
        to_model_trait,
        model_impl,
    })
}

#[derive(Clone)]
struct ModelStruct {
    input_span: Span,
    item: syn::ItemStruct,
    /// The path to the generated struct, e.g. to be used as a return type
    path: syn::Path,
}

impl ModelStruct {
    fn create(
        item_struct: &syn::ItemStruct,
        idents: &GeneratedIdents,
    ) -> TypeModelGenerationResult<Self> {
        if item_struct.fields.is_empty() {
            return Err(TypeModelGenerationError::MissingStructFields(
                item_struct.span(),
            ));
        }

        let model_struct_ident = &idents.model_struct_ident;
        let mut model_struct: syn::ItemStruct = parse_quote_spanned! {item_struct.span()=>
            #[allow(non_camel_case_types)]
            struct #model_struct_ident {}
        };

        // Attach lifetimes
        for param in item_struct.generics.params.iter() {
            if let syn::GenericParam::Lifetime(lt) = param {
                model_struct.generics.params.push(syn::GenericParam::Lifetime(lt.clone()));
            }
        }

        // Attach type params
        let params = item_struct
            .parse_user_annotated_type_params()
            .map_err(TypeModelGenerationError::NonParsableTypeParam)?;
        model_struct.generics.params.extend(
            params
                .iter()
                .filter_map(UserAnnotatedTypeParam::as_generic_type_param)
                .cloned()
                .map(syn::GenericParam::Type),
        );

        model_struct.fields = item_struct.fields.clone();
        add_phantom_data_for_generic_params(&mut model_struct);

        let path = create_path(&model_struct);

        Ok(Self { input_span: item_struct.span(), item: model_struct, path, })
    }

    fn create_copy_impl(&self) -> syn::ItemImpl {
        let path = &self.path;
        let generics = self.item.generics.params.iter();
        parse_quote_spanned! {self.input_span=>
            impl<#(#generics),*> Copy for #path {}
        }
    }

    fn create_clone_impl(&self) -> syn::ItemImpl {
        let path = &self.path;
        let generics = self.item.generics.params.iter();
        parse_quote_spanned! {self.input_span=>
            impl<#(#generics),*> Clone for #path {
                #[trusted]
                fn clone(&self) -> Self {
                    unimplemented!()
                }
            }
        }
    }
}

#[derive(Clone)]
struct ToModelTrait {
    item: syn::ItemTrait,

    /// The path to the generated trait, e.g. to be used as a return type
    path: syn::Path,
}

impl ToModelTrait {
    fn create(
        item_struct: &syn::ItemStruct,
        model_struct: &ModelStruct,
        idents: &GeneratedIdents,
    ) -> Self {
        let generic_params: Vec<syn::GenericParam> =
            model_struct.item.generics.params.iter().cloned().collect();

        let model_path = &model_struct.path;
        let to_model_trait_ident = &idents.to_model_trait_ident;
        let item: syn::ItemTrait = parse_quote_spanned! {item_struct.span()=>
            #[allow(non_camel_case_types)]
            trait #to_model_trait_ident<#(#generic_params),*> {
                #[pure]
                #[trusted]
                #[prusti::type_models_to_model_fn]
                fn model(&self) -> #model_path;
            }
        };

        let path = create_path(&item);

        Self { item, path }
    }
}

fn create_model_impl(
    item_struct: &syn::ItemStruct,
    model_struct: &ModelStruct,
    to_model_trait: &ToModelTrait,
) -> TypeModelGenerationResult<syn::ItemImpl> {
    for param in &item_struct.generics.params {
        if let syn::GenericParam::Const(const_param) = param {
            return Err(TypeModelGenerationError::ConstParamDisallowed(
                const_param.span(),
            ))
        }
    }

    let generic_params: Vec<syn::GenericParam> =
        model_struct.item.generics.params.iter().cloned().collect();

    let impl_path = create_path(item_struct);

    let to_model_trait_path = &to_model_trait.path;
    let model_struct_path = &model_struct.path;

    Ok(parse_quote_spanned! {item_struct.span()=>
        #[prusti::type_models_to_model_impl]
        impl<#(#generic_params),*> #to_model_trait_path for #impl_path {
            #[trusted]
            #[pure]
            fn model(&self) -> #model_struct_path {
                unimplemented!("Models can only be used in specifications")
            }
        }
    })
}

/// [syn::Ident]s which are used for the generated items
struct GeneratedIdents {
    model_struct_ident: syn::Ident,
    to_model_trait_ident: syn::Ident,
}

impl GeneratedIdents {
    fn generate(item_struct: &syn::ItemStruct) -> Self {
        let mut name = item_struct.ident.to_string();

        for param in item_struct.generics.params.iter() {
            if let syn::GenericParam::Type(ty_param) = param {
                name.push_str(ty_param.ident.to_string().as_str());
            }
        }

        let uuid = Uuid::new_v4().to_simple();

        GeneratedIdents {
            model_struct_ident: Ident::new(
                format!("Prusti{}Model_{}", name, uuid).as_str(),
                item_struct.ident.span(),
            ),
            to_model_trait_ident: Ident::new(
                format!("Prusti{}ToModel_{}", name, uuid).as_str(),
                item_struct.ident.span(),
            ),
        }
    }
}

/// Errors that can happen during model generation.
/// These are mostly wrong usages of the macro by the user.
#[derive(Debug)]
enum TypeModelGenerationError {
    /// Thrown when the model contains no fields
    MissingStructFields(proc_macro2::Span),

    /// Thrown when using a const type param in the model
    ConstParamDisallowed(proc_macro2::Span),

    /// Thrown when user annotated generics could not be parsed
    NonParsableTypeParam(UserAnnotatedTypeParamParserError),
}

impl std::convert::From<TypeModelGenerationError> for syn::Error {
    fn from(err: TypeModelGenerationError) -> Self {
        match err {
            TypeModelGenerationError::MissingStructFields(span) => {
                syn::Error::new(span, "Type model must have at least one field")
            }
            TypeModelGenerationError::ConstParamDisallowed(span) => {
                syn::Error::new(span, "Const generics are disallowed for models")
            }
            TypeModelGenerationError::NonParsableTypeParam(parse_err) => parse_err.into(),
        }
    }
}

/// Type to represent generated code during expansion of the `#[model]` macro
struct TypeModel {
    /// The struct which represents the model
    model_struct: ModelStruct,

    /// A trait which will be implemented on the modelled type
    /// to return the [TypeModel::model_struct]
    to_model_trait: ToModelTrait,

    /// The implementation of the [TypeModel::model_trait] on the modelled type.
    model_impl: syn::ItemImpl,
}

impl ToTokens for TypeModel {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.to_model_trait.item.to_tokens(tokens);
        self.model_struct.item.to_tokens(tokens);
        self.model_struct.create_copy_impl().to_tokens(tokens);
        self.model_struct.create_clone_impl().to_tokens(tokens);
        self.model_impl.to_tokens(tokens);
    }
}

fn create_path<T: HasIdent + HasGenerics>(pathable: &T) -> syn::Path {
    let ident = &pathable.ident();

    let generic_idents = pathable.generics().params.iter()
        .filter_map(|generic_param| match generic_param {
            syn::GenericParam::Lifetime(lt_def) =>
                Some(lt_def.lifetime.to_token_stream()),
            syn::GenericParam::Type(type_param) =>
                Some(type_param.ident.to_token_stream()),
            _ => None,
        });
    parse_quote! {
        #ident < #(#generic_idents),* >
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewritten_model_to_tokens() {
        let to_model_trait = ToModelTrait {
            path: parse_quote!(PrustiFooToModel),
            item: parse_quote!(
                trait PrustiFooToModel {}
            )
        };

        let model_struct = ModelStruct {
            path: parse_quote!(Foo),
            item: parse_quote!(
                struct Foo {}
            ),
            input_span: Span::call_site(),
        };

        let trait_impl: syn::ItemImpl = parse_quote!(impl ToModel for Foo {});

        let rewritten_model = TypeModel {
            to_model_trait: to_model_trait.clone(),
            model_struct: model_struct.clone(),
            model_impl: trait_impl.clone(),
        };
        let actual_ts = rewritten_model.into_token_stream();

        let mut expected_ts = TokenStream::new();
        to_model_trait.item.to_tokens(&mut expected_ts);
        model_struct.item.to_tokens(&mut expected_ts);
        model_struct.create_copy_impl().to_tokens(&mut expected_ts);
        model_struct.create_clone_impl().to_tokens(&mut expected_ts);
        trait_impl.to_tokens(&mut expected_ts);

        assert_eq!(expected_ts.to_string(), actual_ts.to_string());
    }

    #[test]
    fn err_when_no_fields() {
        let input = parse_quote!(
            struct Foo {}
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::MissingStructFields(_))
        ));
    }

    #[test]
    fn ok_generates_model_struct_def_with_named_fields() {
        let input = syn::parse_quote!(
            struct Foo {
                fld1: usize,
                fld2: i32,
            }
        );

        let model = expect_ok(rewrite_internal(input));

        let model_ident = check_model_ident(&model, "PrustiFooModel");
        let expected: syn::ItemStruct = syn::parse_quote!(
            #[allow(non_camel_case_types)]
            struct #model_ident {
                fld1: usize,
                fld2: i32,
            }
        );
        assert_eq_tokenizable(model.model_struct.item, expected);
    }

    #[test]
    fn ok_generates_model_struct_def_with_unnamed_fields() {
        let input = parse_quote!(
            struct Foo(i32, u32, usize);
        );

        let model = expect_ok(rewrite_internal(input));

        let model_ident = check_model_ident(&model, "PrustiFooModel");

        let expected: syn::ItemStruct = parse_quote!(
            #[allow(non_camel_case_types)]
            struct #model_ident(i32, u32, usize);
        );
        assert_eq_tokenizable(model.model_struct.item, expected);
    }

    #[test]
    fn ok_generates_impl_for_to_model_trait() {
        let input = parse_quote!(
            struct Foo(i32, u32, usize);
        );
        let model = expect_ok(rewrite_internal(input));

        let model_ident = check_model_ident(&model, "PrustiFooModel");
        let trait_ident = check_trait_ident(&model, "PrustiFooToModel");
        let expected: syn::ItemImpl = parse_quote!(
            #[prusti::type_models_to_model_impl]
            impl #trait_ident<> for Foo <> {
                #[trusted]
                #[pure]
                fn model(&self) -> #model_ident<> {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(expected, model.model_impl);
    }

    #[test]
    fn ok_uses_defined_lifetime() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<'a, 'b>(i32, u32, usize);
        );
        let model = expect_ok(rewrite_internal(input));

        let model_ident = check_model_ident(&model, "PrustiFooModel");
        let trait_ident = check_trait_ident(&model, "PrustiFooToModel");

        let expected_struct: syn::ItemStruct = parse_quote!(
            #[allow(non_camel_case_types)]
            struct #model_ident<'a, 'b>(
                i32,
                u32,
                usize,
                ::core::marker::PhantomData<&'a()>,
                ::core::marker::PhantomData<&'b()>
            );
        );
        let expected_impl: syn::ItemImpl = parse_quote!(
            #[prusti::type_models_to_model_impl]
            impl<'a, 'b> #trait_ident<'a, 'b> for Foo<'a, 'b> {
                #[trusted]
                #[pure]
                fn model(&self) -> #model_ident<'a, 'b> {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(model.model_struct.item, expected_struct);
        assert_eq_tokenizable(model.model_impl, expected_impl);
    }

    #[test]
    fn ok_with_concrete_and_generic_params() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<#[concrete] i32, #[generic] T, #[concrete] usize, #[generic] U>(i32);
        );
        let model = expect_ok(rewrite_internal(input));

        let model_ident = check_model_ident(&model, "PrustiFooi32TusizeUModel");
        let trait_ident = check_trait_ident(&model, "PrustiFooi32TusizeUToModel");

        let expected_struct: syn::ItemStruct = parse_quote!(
            #[allow(non_camel_case_types)]
            struct #model_ident<T, U> (i32,::core::marker::PhantomData<T> , ::core::marker::PhantomData<U>);
        );

        let expected_trait: syn::ItemTrait = parse_quote!(
            #[allow(non_camel_case_types)]
            trait #trait_ident<T, U> {
                #[pure]
                #[trusted]
                #[prusti::type_models_to_model_fn]
                fn model(&self) -> #model_ident<T, U>;
            }
        );

        let expected_impl: syn::ItemImpl = parse_quote!(
            #[prusti::type_models_to_model_impl]
            impl<T, U> #trait_ident<T, U> for Foo<i32, T, usize, U> {
                #[trusted]
                #[pure]
                fn model(&self) -> #model_ident<T, U> {
                    unimplemented!("Models can only be used in specifications")
                }
            }
        );

        assert_eq_tokenizable(model.model_struct.item, expected_struct);
        assert_eq_tokenizable(model.to_model_trait.item, expected_trait);
        assert_eq_tokenizable(model.model_impl, expected_impl);
    }

    #[test]
    fn ok_defines_to_model_trait() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo(i32, u32, usize);
        );

        let model = expect_ok(rewrite_internal(input));

        let model_ident = check_model_ident(&model, "PrustiFooModel");
        let trait_ident = check_trait_ident(&model, "PrustiFooToModel");

        let actual = model.to_model_trait.item;
        let expected: syn::ItemTrait = parse_quote!(
            #[allow(non_camel_case_types)]
            trait #trait_ident {
                #[pure]
                #[trusted]
                #[prusti::type_models_to_model_fn]
                fn model(&self) -> #model_ident<>;
            }
        );

        assert_eq_tokenizable(actual, expected);
    }

    #[test]
    fn err_const_generics_disallowed() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<const PAR: i32>(i32, u32, usize);
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::ConstParamDisallowed(_))
        ));
    }

    #[test]
    fn err_non_annotated_generic() {
        let input: syn::ItemStruct = parse_quote!(
            struct Foo<T>(i32, u32, usize);
        );
        let result = rewrite_internal(input);
        assert!(matches!(
            result,
            Err(TypeModelGenerationError::NonParsableTypeParam(
                UserAnnotatedTypeParamParserError::InvalidAnnotation(_)
            ))
        ));
    }

    fn expect_ok(result: Result<TypeModel, TypeModelGenerationError>) -> TypeModel {
        result.expect("Expected Ok result")
    }

    fn assert_eq_tokenizable<T: ToTokens, U: ToTokens>(actual: T, expected: U) {
        assert_eq!(
            actual.into_token_stream().to_string(),
            expected.into_token_stream().to_string()
        );
    }

    fn check_model_ident(model: &TypeModel, expected_prefix: &str) -> Ident {
        let ident = &model.model_struct.item.ident;
        assert!(ident.to_string().starts_with(expected_prefix));
        ident.clone()
    }

    fn check_trait_ident(model: &TypeModel, expected_prefix: &str) -> Ident {
        let ident = &model.to_model_trait.item.ident;
        assert!(ident.to_string().starts_with(expected_prefix));
        ident.clone()
    }
}
