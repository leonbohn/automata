use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DataStruct, DeriveInput, Field, Fields};

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
            .find(|field| field.attrs.iter().any(|attr| attr.path.is_ident("ts"))),
        _ => panic!("unsupported type (use struct with named fields)"),
    };

    field.expect("ts attribute is required")
}
