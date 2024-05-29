use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DataStruct, DeriveInput, Field, Fields};

#[proc_macro_derive(Base, attributes(ts))]
pub fn transition_system_base(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as DeriveInput);

    let name = &input.ident;
    let field = get_ts_field(&input);
    let field_name = &field.ident;
    let field_type = &field.ty;

    let (ig, tg, w) = input.generics.split_for_impl();

    let out = quote! {
        impl #ig TransitionSystemBase for #name #tg #w {
            type Alphabet = <#field_type as TransitionSystemBase>::Alphabet;
            type StateIndex = <#field_type as TransitionSystemBase>::StateIndex;
            type StateColor = <#field_type as TransitionSystemBase>::StateColor;
            type EdgeColor = <#field_type as TransitionSystemBase>::EdgeColor;
            type StateRef<'this> = <#field_type as TransitionSystemBase>::StateRef<'this>
            where Self: 'this;
            type EdgeRef<'this> = <#field_type as TransitionSystemBase>::StateRef<'this>
            where Self: 'this;

            fn alphabet(&self) -> &Self::Alphabet {
                <#field_type as TransitionSystemBase>::alphabet(&self.#field_name)
            }
        }
    };
    TokenStream::from(out)
}

#[proc_macro_derive(StateIterable, attributes(ts))]
pub fn state_iterable(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as DeriveInput);

    let name = &input.ident;
    let field = get_ts_field(&input);
    let field_name = &field.ident;
    let field_type = &field.ty;

    let (ig, tg, w) = input.generics.split_for_impl();

    let out = quote! {
        impl #ig StateIterable for #name #tg #w {
            type StatesIter<'this> = <#field_type as StateIterable>::StatesIter<'this>
            where Self: 'this;

            fn q(&self, idx: StateIndex<#field_type>) -> Option<Self::StateRef<'_>> {
                <#field_type as StateIterable>::q(&self.#field_name, idx)
            }
            fn states(&self) -> Self::StatesIter<'_> {
                <#field_type as StateIterable>::states(&self.#field_name)
            }
        }
    };
    TokenStream::from(out)
}

#[proc_macro_derive(EdgesFrom, attributes(ts))]
pub fn edges_from(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as DeriveInput);

    let name = &input.ident;
    let field = get_ts_field(&input);
    let field_name = &field.ident;
    let field_type = &field.ty;

    let (ig, tg, w) = input.generics.split_for_impl();

    let out = quote! {
        impl #ig StateIterable for #name #tg #w {
            type EdgesFrom<'this> = <#field_type as EdgesFrom>::StatesIter<'this>
            where Self: 'this;

            fn edges_from(&self, source: StateIndex<#field_type>) -> Option<Self::EdgesFromIter<'_>> {
                <#field_type as EdgesFrom>::edges_from(&self.#field_name, source)
            }
        }
    };
    TokenStream::from(out)
}

#[proc_macro_derive(TransitionSystem, attributes(ts))]
pub fn transition_system(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as DeriveInput);

    let name = &input.ident;
    let field = get_ts_field(&input);
    let field_name = &field.ident;

    let done = quote! {
        impl<T: TransitionSystem> TS<T::Alphabet, T::StateColor, T::EdgeColor> for #name<T> {
            fn ts(&self) -> &T {
                &self.#field_name
            }
        }
    };
    TokenStream::from(done)
}

fn get_ts_field(input: &DeriveInput) -> &Field {
    let field = match input.data {
        Data::Struct(DataStruct {
            fields: Fields::Named(ref fields),
            ..
        }) => fields
            .named
            .iter()
            .find(|field| field.attrs.iter().any(|attr| attr.path().is_ident("ts"))),
        _ => panic!("unsupported type (use struct with named fields)"),
    };

    field.expect("ts attribute is required")
}
