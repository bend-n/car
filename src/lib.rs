//! provides some ([`map`](array::map) and [`from_fn`](core::array::from_fn)) [`core::array`] fn related functions as const macros.
//! ```
//! const X: [usize; 6] = car::map!(car::from_fn!(|x| x), |x| x * 24);
//! ```
#![forbid(unsafe_code)]
use quote::quote;
use syn::{parse::Parse, punctuated::Punctuated, spanned::Spanned, *};

fn lib() -> proc_macro2::TokenStream {
    quote! {
        // dont worry about this whole area
        const fn uninit_array<T, const N: usize>() -> [::core::mem::MaybeUninit<T>; N] { unsafe { ::core::mem::MaybeUninit::<[::core::mem::MaybeUninit<T>; N]>::uninit().assume_init() } }
        const fn uninit_array_copied<T, U, const N: usize>(/* steal the length */ _len: &[U; N]) -> [::core::mem::MaybeUninit<T>; N] { uninit_array() }
        const unsafe fn aai<T, const N: usize>(array: [::core::mem::MaybeUninit<T>; N]) -> [T; N] { transmute_unchecked(array) }
        const unsafe fn transmute_unchecked<T, U>(value: T) -> U { unsafe { #[repr(C)] union Transmute<T, U> { t: ::core::mem::ManuallyDrop<T>, u: ::core::mem::ManuallyDrop<U> } ::core::mem::ManuallyDrop::into_inner(Transmute { t: ::core::mem::ManuallyDrop::new(value) }.u) } }
    }
}

/// [From fn](std::array::from_fn) in const.
/// ```
/// const OUT: [u8; 8] = car::from_fn!(|x| (x as u32 * 611170012 >> 24) as u8);
/// assert_eq!(OUT, [0, 36, 72, 109, 145, 182, 218, 255]);
/// ```
#[proc_macro]
pub fn from_fn(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ExprClosure { inputs, body, .. } = parse_macro_input!(input as ExprClosure);
    if inputs.len() > 1 {
        let n = inputs.len();
        return Error::new_spanned(inputs, format!("expected one (or 0) inputs, found {n}"))
            .into_compile_error()
            .into();
    };
    let inputs = inputs.into_iter();
    let lib = lib();
    quote! { {
        #lib

        let mut __out = uninit_array();
        let mut i = 0usize;
        while i < __out.len() {
            __out[i] = ::core::mem::MaybeUninit::new({
                // disable mutation (cant shadow)
                let i = i;
                let __out = ();

                #(let #inputs = i)*;

                #body
            });
            i += 1;
        }
        unsafe { aai(__out) }
    } }
    .into()
}

/// [Map](array::map) in const.
/// ```
/// assert_eq!(car::map!([1, 2, 3], |x| x * 2), [2, 4, 6]);
/// ```
#[proc_macro]
pub fn map(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    struct Args {
        array: Expr,
        f: ExprClosure,
    }
    impl Parse for Args {
        fn parse(input: parse::ParseStream) -> Result<Self> {
            let mut args = Punctuated::<Expr, Token![,]>::parse_terminated(input)?;
            if args.len() != 2 {
                return Err(input.error(format!(
                    "arg count mismatch, expected 2 (array expression) found {}",
                    args.len()
                )));
            }
            let f = match args.pop().unwrap().into_value() {
                Expr::Closure(x) => x,
                x => return Err(Error::new_spanned(x, "mismatched types: expected closure")),
            };
            let array = args.pop().unwrap().into_value();

            Ok(Self { array, f })
        }
    }

    let Args {
        array,
        f: ExprClosure { body, inputs, .. },
    } = parse_macro_input!(input as Args);
    let n = inputs.len();
    let ns = inputs.span();
    let mut inputs = inputs.into_iter();
    let Some(binding) = inputs.next() else {
        return Error::new(ns, format!("expected one (or 2) inputs, found {n} inputs"))
            .into_compile_error()
            .into();
    };
    let index = inputs.next().into_iter();
    let lib = lib();
    quote! { {
        #lib

        let __arr = #array;
        let mut __out = uninit_array_copied(&__arr);
        let size = __arr.len();
        let __ap = __arr.as_ptr();
        let __arr = ::core::mem::ManuallyDrop::new(__arr);
        let mut i = 0usize;
        while i < size {
            __out[i] = ::core::mem::MaybeUninit::new({
                let i = i;
                let #binding = unsafe { __ap.add(i).read() };
                let __out = ();
                let __arr = ();
                #(let #index = i;)*

                #body
            });
            i += 1;
        }
        unsafe { aai(__out) }
    }}
    .into()
}

fn try_from_fn(
    input: proc_macro::TokenStream,
    good: proc_macro2::TokenStream,
    pat: proc_macro2::TokenStream,
    then: proc_macro2::TokenStream,
) -> proc_macro::TokenStream {
    let ExprClosure { inputs, body, .. } = parse_macro_input!(input as ExprClosure);
    if inputs.len() > 1 {
        let n = inputs.len();
        return Error::new_spanned(inputs, format!("expected one (or 0) inputs, found {n}"))
            .into_compile_error()
            .into();
    };
    let inputs = inputs.into_iter();
    let lib = lib();
    quote! { {
        #lib
        let mut __out = uninit_array();
        let mut i = 0usize;
        loop {
            if i >= __out.len() {
                break #good(unsafe { aai(__out) })
            }
            __out[i] = ::core::mem::MaybeUninit::new({
                // disable mutation (cant shadow)
                let i = i;
                let __out = __out;

                #(let #inputs = i)*;

                match #body {
                    #good(x) => x,
                    #pat => {
                        let mut j = 0;
                        while j < i {
                            unsafe { __out[j].assume_init() };
                            j += 1;
                        }
                        #then
                    }
                }
            });
            i += 1;
        }
    } }
    .into()
}

#[proc_macro]
/// [Try from fn](std::array::try_from_fn) in const, for options.
/// ```
/// let array: Option<[_; 4]> = car::try_from_fn_option!(|i| i.checked_add(100));
/// assert_eq!(array, Some([100, 101, 102, 103]));
///
/// let array: Option<[_; 4]> = car::try_from_fn_option!(|i| i.checked_sub(100));
/// assert_eq!(array, None);
/// ```
pub fn try_from_fn_option(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    try_from_fn(input, quote!(Some), quote!(None), quote!(break None))
}

#[proc_macro]
/// [Try from fn](std::array::try_from_fn) in const, for results.
/// ```
/// let array: Result<[u8; 5], _> = car::try_from_fn_result!(|i| i.try_into());
/// assert_eq!(array, Ok([0, 1, 2, 3, 4]));
/// let array: Result<[i8; 200], _> = car::try_from_fn_result!(|i| i.try_into());
/// assert!(array.is_err());
/// ```
pub fn try_from_fn_result(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    try_from_fn(
        input,
        quote!(Ok),
        quote!(Err(e)),
        quote!(break Err(e /* .into() */)),
    )
}
