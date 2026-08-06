//! [Lambda terms](https://en.wikipedia.org/wiki/Lambda_calculus#Lambda_terms)

pub use self::Notation::*;
pub use self::Term::*;
use self::TermError::*;
use std::error::Error;
use std::fmt::{self, Write as _};

/// The character used to display lambda abstractions (a backslash).
#[cfg(feature = "backslash_lambda")]
pub const LAMBDA: char = '\\';

/// The character used to display lambda abstractions. The default is the Greek letter 'λ', but it
/// can also be set to a '\' (backslash) using `features = ["backslash_lambda"]`.
#[cfg(not(feature = "backslash_lambda"))]
pub const LAMBDA: char = 'λ';

/// An undefined term that can be used as a value returned by invalid/inapplicable operations, e.g.
/// obtaining an element of an empty list. Since this implementation uses De Bruijn indices greater
/// than zero, `Var(0)` will not occur naturally.
///
/// `fmt::Display` shows it as `undefined`; `fmt::Debug` shows it as `[0]`, which is the form
/// `parse` reads back, so a term holding it still round-trips.
pub const UD: Term = Var(0);

/// The notation used for parsing and displaying purposes.
///
/// # Examples
/// ```
/// use lambda_calculus::combinators::S;
/// use lambda_calculus::term::LAMBDA;
///
/// // `LAMBDA` is `λ` by default, or `\` with the `backslash_lambda` feature; normalising
/// // it keeps these expectations true either way.
/// assert_eq!(format!(  "{}", S()).replace(LAMBDA, "λ"), "λa.λb.λc.a c (b c)"); // Classic
/// assert_eq!(format!("{:?}", S()).replace(LAMBDA, "λ"), "λλλ31(21)");          // DeBruijn
/// ```
///
/// # De Bruijn indices above 15
///
/// De Bruijn notation is concatenative: adjacent indices are an application, so `21` is
/// `App(Var(2), Var(1))` rather than the index 21. A single index is therefore one
/// hexadecimal digit, `1` through `F`, and one that needs more than a digit is wrapped in
/// brackets so it stays distinguishable:
///
/// ```
/// use lambda_calculus::*;
///
/// assert_eq!(format!("{:?}", Var(15)), "F");
/// assert_eq!(format!("{:?}", Var(16)), "[10]");
///
/// // `10` is two indices applied to each other, `[10]` is one index.
/// assert_eq!(parse("10", DeBruijn).unwrap(), app(Var(1), Var(0)));
/// assert_eq!(parse("[10]", DeBruijn).unwrap(), Var(16));
/// ```
///
/// The brackets only delimit; the digits inside them are hexadecimal like all the others,
/// so `[A]` and a bare `A` are the same index. They are accepted around any index,
/// including one that would fit without them, and `fmt::Debug` output always parses back
/// to the term it came from.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Notation {
    /// classic lambda calculus notation; used by `fmt::Display`
    Classic,
    /// De Bruijn indices; used by `fmt::Debug`
    DeBruijn,
}

/// A context holding a list of names for classic notation printing.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Context(Vec<String>);

impl Context {
    /// Creates a new `Context` from a slice of string-like items.
    ///
    /// This is the primary, most flexible constructor. It accepts anything
    /// that can be borrowed as a string slice, like `&[&str]` or `&[String]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use lambda_calculus::term::Context;
    ///
    /// // Create from an array of &str
    /// let context1 = Context::new(&["a", "b", "c"]);
    ///
    /// // Create from a Vec<String>
    /// let names = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    /// let context2 = Context::new(&names);
    ///
    /// assert_eq!(context1, context2);
    /// ```
    pub fn new<S: AsRef<str>>(namings: &[S]) -> Self {
        let owned = namings.iter().map(|s| s.as_ref().to_string()).collect();
        Context(owned)
    }

    /// Creates an empty context.
    pub fn empty() -> Self {
        vec![].into()
    }

    /// Returns an iterator over the names in the context, yielding `&str`.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &str> {
        self.0.iter().map(|s| s.as_str())
    }

    /// Returns the number of names in the context.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the context contains no names.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns `true` if the context contains a name equivalent to the given value.
    ///
    /// This method is generic over `AsRef<str>`, so it can be called with
    /// a string slice (`&str`), a `String`, or other string-like types.
    pub fn contains<S: AsRef<str>>(&self, name: S) -> bool {
        self.iter().any(|item| item == name.as_ref())
    }

    /// Resolves a 1-based index to a free variable name from the context.
    ///
    /// The index is 1-based, where `1` refers to the first name defined in the context.
    /// Returns `None` if the index is 0 or out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lambda_calculus::term::Context;
    /// let ctx = Context::new(&["a", "b", "c"]);
    ///
    /// assert_eq!(ctx.resolve_free_var(1), Some("a"));
    /// assert_eq!(ctx.resolve_free_var(3), Some("c"));
    /// assert_eq!(ctx.resolve_free_var(0), None);
    /// assert_eq!(ctx.resolve_free_var(4), None);
    /// ```
    pub fn resolve_free_var(&self, idx: usize) -> Option<&str> {
        if idx == 0 {
            None
        } else {
            self.0.get(idx - 1).map(|s| s.as_str())
        }
    }
}

impl<S: AsRef<str>> From<&[S]> for Context {
    fn from(namings: &[S]) -> Self {
        Self::new(namings)
    }
}

impl From<Vec<String>> for Context {
    fn from(namings: Vec<String>) -> Self {
        Context(namings)
    }
}

/// A lambda term that is either a variable with a De Bruijn index, an abstraction over a term or
/// an applicaction of one term to another.
#[derive(PartialEq, Clone, Hash, Eq)]
pub enum Term {
    /// a variable
    Var(usize),
    /// an abstraction
    Abs(Box<Term>),
    /// an application
    App(Box<(Term, Term)>),
}

/// An error that can be returned when an inapplicable function is applied to a `Term`.
#[derive(Debug, PartialEq, Eq)]
pub enum TermError {
    /// the term is not a variable
    NotVar,
    /// the term is not an abstraction
    NotAbs,
    /// the term is not an application
    NotApp,
}

impl fmt::Display for TermError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TermError::NotVar => write!(f, "the term is not a variable",),
            TermError::NotAbs => write!(f, "the term is not an abstraction"),
            TermError::NotApp => write!(f, "the term is not an application"),
        }
    }
}

impl Error for TermError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl Term {
    /// Returns a variable's De Bruijn index, consuming it in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Var(1).unvar(), Ok(1));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not a `Var`iable.
    pub fn unvar(self) -> Result<usize, TermError> {
        if let Var(n) = self {
            Ok(n)
        } else {
            Err(NotVar)
        }
    }

    /// Returns a reference to a variable's De Bruijn index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Var(1).unvar_ref(), Ok(&1));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not a `Var`iable.
    pub fn unvar_ref(&self) -> Result<&usize, TermError> {
        if let Var(ref n) = *self {
            Ok(n)
        } else {
            Err(NotVar)
        }
    }

    /// Returns a mutable reference to a variable's De Bruijn index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Var(1).unvar_mut(), Ok(&mut 1));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not a `Var`iable.
    pub fn unvar_mut(&mut self) -> Result<&mut usize, TermError> {
        if let Var(ref mut n) = *self {
            Ok(n)
        } else {
            Err(NotVar)
        }
    }

    /// Returns an abstraction's underlying term, consuming it in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).unabs(), Ok(Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn unabs(self) -> Result<Term, TermError> {
        if let Abs(x) = self {
            Ok(*x)
        } else {
            Err(NotAbs)
        }
    }

    /// Returns a reference to an abstraction's underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).unabs_ref(), Ok(&Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn unabs_ref(&self) -> Result<&Term, TermError> {
        if let Abs(ref x) = *self {
            Ok(x)
        } else {
            Err(NotAbs)
        }
    }

    /// Returns a mutable reference to an abstraction's underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).unabs_mut(), Ok(&mut Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn unabs_mut(&mut self) -> Result<&mut Term, TermError> {
        if let Abs(ref mut x) = *self {
            Ok(x)
        } else {
            Err(NotAbs)
        }
    }

    /// Returns a pair containing an application's underlying terms, consuming it in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).unapp(), Ok((Var(1), Var(2))));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn unapp(self) -> Result<(Term, Term), TermError> {
        if let App(boxed) = self {
            let (lhs, rhs) = *boxed;
            Ok((lhs, rhs))
        } else {
            Err(NotApp)
        }
    }

    /// Returns a pair containing references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).unapp_ref(), Ok((&Var(1), &Var(2))));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn unapp_ref(&self) -> Result<(&Term, &Term), TermError> {
        if let App(boxed) = self {
            let (ref lhs, ref rhs) = **boxed;
            Ok((lhs, rhs))
        } else {
            Err(NotApp)
        }
    }

    /// Returns a pair containing mutable references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).unapp_mut(), Ok((&mut Var(1), &mut Var(2))));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn unapp_mut(&mut self) -> Result<(&mut Term, &mut Term), TermError> {
        if let App(boxed) = self {
            let (ref mut lhs, ref mut rhs) = **boxed;
            Ok((lhs, rhs))
        } else {
            Err(NotApp)
        }
    }

    /// Returns the left-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).lhs(), Ok(Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn lhs(self) -> Result<Term, TermError> {
        if let Ok((lhs, _)) = self.unapp() {
            Ok(lhs)
        } else {
            Err(NotApp)
        }
    }

    /// Returns a reference to the left-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).lhs_ref(), Ok(&Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn lhs_ref(&self) -> Result<&Term, TermError> {
        if let Ok((lhs, _)) = self.unapp_ref() {
            Ok(lhs)
        } else {
            Err(NotApp)
        }
    }

    /// Returns a mutable reference to the left-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).lhs_mut(), Ok(&mut Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn lhs_mut(&mut self) -> Result<&mut Term, TermError> {
        if let Ok((lhs, _)) = self.unapp_mut() {
            Ok(lhs)
        } else {
            Err(NotApp)
        }
    }

    /// Returns the right-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).rhs(), Ok(Var(2)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn rhs(self) -> Result<Term, TermError> {
        if let Ok((_, rhs)) = self.unapp() {
            Ok(rhs)
        } else {
            Err(NotApp)
        }
    }

    /// Returns a reference to the right-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).rhs_ref(), Ok(&Var(2)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn rhs_ref(&self) -> Result<&Term, TermError> {
        if let Ok((_, rhs)) = self.unapp_ref() {
            Ok(rhs)
        } else {
            Err(NotApp)
        }
    }

    /// Returns a mutable reference to the right-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).rhs_mut(), Ok(&mut Var(2)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn rhs_mut(&mut self) -> Result<&mut Term, TermError> {
        if let Ok((_, rhs)) = self.unapp_mut() {
            Ok(rhs)
        } else {
            Err(NotApp)
        }
    }

    /// Returns `true` if `self` is a
    /// [supercombinator](https://en.wikipedia.org/wiki/Supercombinator).
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let term1 = abs(app(Var(1), abs(Var(1)))); // λ 1 (λ 1)
    /// let term2 = app(abs(Var(2)), abs(Var(1))); // (λ 2) (λ 1)
    ///
    /// assert_eq!(term1.is_supercombinator(), true);
    /// assert_eq!(term2.is_supercombinator(), false);
    /// ```
    pub fn is_supercombinator(&self) -> bool {
        let mut stack = vec![(0usize, self)];

        while let Some((depth, term)) = stack.pop() {
            match term {
                Var(i) => {
                    if *i > depth || *i == 0 {
                        return false;
                    }
                }
                Abs(t) => stack.push((depth + 1, t)),
                App(boxed) => {
                    let (ref f, ref a) = **boxed;
                    stack.push((depth, f));
                    stack.push((depth, a))
                }
            }
        }
        true
    }

    /// Returns the maximum depth of lambda abstractions
    /// in the given `Term`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).max_depth(), 1);
    /// ```
    pub fn max_depth(&self) -> u32 {
        match self {
            Var(_) => 0,
            Abs(t) => t.max_depth() + 1,
            App(boxed) => {
                let d0 = boxed.0.max_depth();
                let d1 = boxed.1.max_depth();
                d0.max(d1)
            }
        }
    }

    /// Returns `true` if `self` is structurally isomorphic to `other`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let term1 = abs(Var(1)); // λ 1
    /// let term2 = abs(Var(2)); // λ 2
    /// let term3 = abs(Var(1)); // λ 1
    ///
    /// assert_eq!(term1.is_isomorphic_to(&term2), false);
    /// assert_eq!(term1.is_isomorphic_to(&term3), true);
    ///
    /// ```
    pub fn is_isomorphic_to(&self, other: &Term) -> bool {
        match (self, other) {
            (Var(x), Var(y)) => x == y,
            (Abs(p), Abs(q)) => p.is_isomorphic_to(q),
            (App(p), App(q)) => p.0.is_isomorphic_to(&q.0) && p.1.is_isomorphic_to(&q.1),
            _ => false,
        }
    }

    /// Returns `true` if `self` has any free vairables.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let with_freevar = abs(Var(2));     // λ 2
    /// let without_freevar = abs(Var(1));  // λ 1
    ///
    /// assert!(with_freevar.has_free_variables());
    /// assert!(!without_freevar.has_free_variables());
    pub fn has_free_variables(&self) -> bool {
        self.has_free_variables_helper(0)
    }

    fn has_free_variables_helper(&self, depth: usize) -> bool {
        match self {
            Var(x) => *x > depth || *x == 0,
            Abs(p) => p.has_free_variables_helper(depth + 1),
            App(p) => p.0.has_free_variables_helper(depth) || p.1.has_free_variables_helper(depth),
        }
    }

    /// Calculates the maximum index of any free variable in the term.
    ///
    /// The result corresponds to the number of names `Context` must supply to bind them all.
    pub fn max_free_index(&self) -> usize {
        self.max_free_index_helper(0)
    }

    fn max_free_index_helper(&self, depth: usize) -> usize {
        match self {
            Var(x) => x.saturating_sub(depth),
            Abs(p) => p.max_free_index_helper(depth + 1),
            App(p) => {
                p.0.max_free_index_helper(depth)
                    .max(p.1.max_free_index_helper(depth))
            }
        }
    }

    /// Returns a helper struct that allows displaying the term with a given context.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::{*, term::{Context, LAMBDA}};
    ///
    /// let term = abs(Var(2)); // λa.b
    /// let ctx = Context::new(&["x"]); // Predefine "x" as a free variable
    ///
    /// // The context defines `Var(2)` as "x" instead of the default "b"
    /// // (`LAMBDA` is normalised so this holds under `backslash_lambda` too)
    /// assert_eq!(term.with_context(&ctx).to_string().replace(LAMBDA, "λ"), "λa.x");
    /// ```
    pub fn with_context<'a>(&'a self, ctx: &'a Context) -> impl fmt::Display + 'a {
        DisplayWithContext { term: self, ctx }
    }
}

/// Wraps a `Term` in an `Abs`traction. Consumes its argument.
///
/// # Example
/// ```
/// use lambda_calculus::*;
///
/// assert_eq!(abs(Var(1)), Abs(Box::new(Var(1))));
/// ```
pub fn abs(term: Term) -> Term {
    Abs(Box::new(term))
}

/// Produces an `App`lication of two given `Term`s without any reduction, consuming them in the
/// process.
///
/// # Example
/// ```
/// use lambda_calculus::*;
///
/// assert_eq!(app(Var(1), Var(2)), App(Box::new((Var(1), Var(2)))));
/// ```
pub fn app(lhs: Term, rhs: Term) -> Term {
    App(Box::new((lhs, rhs)))
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let naming = Naming::Auto {
            max_depth: self.max_depth() as usize,
        };
        show_precedence_cla(&naming, self, f, 0, 0)
    }
}

/// A helper struct for displaying a `Term` with an external `Context`.
struct DisplayWithContext<'a> {
    term: &'a Term,
    ctx: &'a Context,
}

impl<'a> fmt::Display for DisplayWithContext<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let binder_names = generate_binder_names(self.ctx, self.term.max_depth());
        let naming = Naming::Provided {
            ctx: self.ctx,
            binder_names: &binder_names,
        };
        show_precedence_cla(&naming, self.term, f, 0, 0)
    }
}

/// How a rendering pass names the variables it meets.
enum Naming<'a> {
    /// Names derived from the term itself: the binder at depth `d` takes the `d`th
    /// generated name, and a free variable continues the same sequence past the last
    /// binder.
    ///
    /// Nothing is precomputed. A name is produced only when a variable is actually
    /// reached, so rendering costs what the output costs rather than what the largest
    /// index happens to be - naming free variables up front made displaying the single
    /// term `Var(4_000_000)` allocate four million strings to print five characters.
    Auto { max_depth: usize },
    /// Names from a caller-supplied context, with the binder names precomputed because
    /// they have to be checked against it for clashes.
    Provided {
        ctx: &'a Context,
        binder_names: &'a [String],
    },
}

impl Naming<'_> {
    /// Writes the name of the binder introduced at `depth`, counted from the outside in.
    fn write_binder(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        match self {
            Self::Auto { .. } => {
                let mut buf = [0; MAX_BASE26_LEN];
                f.write_str(base26_into(depth, &mut buf))
            }
            Self::Provided { binder_names, .. } => f.write_str(
                binder_names
                    .get(depth)
                    .expect("[BUG] binder_names are insufficient"),
            ),
        }
    }

    /// Writes the name of the free variable at 1-based `idx`.
    fn write_free(&self, f: &mut fmt::Formatter, idx: usize) -> fmt::Result {
        match self {
            Self::Auto { max_depth } => {
                // `idx` is at least 1, so the decrement cannot underflow; the saturating
                // add keeps an absurd index from wrapping instead of naming itself.
                let mut buf = [0; MAX_BASE26_LEN];
                f.write_str(base26_into(max_depth.saturating_add(idx) - 1, &mut buf))
            }
            Self::Provided { ctx, .. } => match ctx.resolve_free_var(idx) {
                Some(name) => f.write_str(name),
                None => write!(f, "<unknown{idx}>"),
            },
        }
    }
}

/// Generates a list of fresh names for binders, avoiding clashes with the given context.
///
/// Only the context-supplied naming needs this: the clash check is what forces the names
/// to be produced in order and up front, and `number` is a nesting depth, so the list is
/// bounded by the size of the term being displayed.
fn generate_binder_names(ctx: &Context, number: u32) -> Vec<String> {
    (0..)
        .map(base26_encode)
        .filter(|name| !ctx.contains(name))
        .take(number as usize)
        .collect()
}

/// Enough room for the longest bijective base-26 name a `usize` can produce, which is
/// 14 characters; the slack costs nothing on the stack and keeps the bound obvious.
const MAX_BASE26_LEN: usize = 16;

/// Encodes `n` as a bijective base-26 name - `a`, `b`, .., `z`, `aa`, `ab`, .. - into
/// `buf`, returning the part of it that was written.
///
/// Taking the buffer from the caller lets the formatting paths name a variable without
/// allocating. The digits are peeled off without the `n + 1` a more direct transcription
/// would use, because that addition overflows for an index near `usize::MAX`.
fn base26_into(mut n: usize, buf: &mut [u8; MAX_BASE26_LEN]) -> &str {
    let mut len = 0;
    loop {
        buf[len] = b'a' + (n % 26) as u8;
        len += 1;
        if n < 26 {
            break;
        }
        n = n / 26 - 1;
    }
    buf[..len].reverse();

    // Every byte written above lies in `b'a'..=b'z'`.
    std::str::from_utf8(&buf[..len]).expect("[BUG] base26 produced non-UTF-8")
}

fn base26_encode(n: usize) -> String {
    let mut buf = [0; MAX_BASE26_LEN];
    base26_into(n, &mut buf).to_owned()
}

/// Writes the classic representation of `term` straight into `f`.
///
/// This recurses once per nesting level, so the frame is kept deliberately small.
/// Returning a `String` per subterm instead - which is what this used to do - made
/// the frame large enough to bound how deep a term could be printed at all, and made
/// the whole traversal quadratic, since every level copied its subtree's rendering
/// into a fresh allocation.
fn show_precedence_cla(
    naming: &Naming,
    term: &Term,
    f: &mut fmt::Formatter,
    context_precedence: usize,
    depth: usize,
) -> fmt::Result {
    match term {
        Var(0) => f.write_str("undefined"),
        // Indices stay `usize` the whole way down. Narrowing them to `u32` used to make
        // an index past `u32::MAX` name a different variable, or panic outright.
        Var(i) if *i <= depth => naming.write_binder(f, depth - *i),
        Var(i) => naming.write_free(f, *i - depth),
        Abs(t) => {
            let parenthesize = context_precedence > 1;
            if parenthesize {
                f.write_char('(')?;
            }
            f.write_char(LAMBDA)?;
            naming.write_binder(f, depth)?;
            f.write_char('.')?;
            show_precedence_cla(naming, t, f, 0, depth + 1)?;
            if parenthesize {
                f.write_char(')')?;
            }
            Ok(())
        }
        App(boxed) => {
            let (ref t1, ref t2) = **boxed;
            let parenthesize = context_precedence == 3;
            if parenthesize {
                f.write_char('(')?;
            }
            show_precedence_cla(naming, t1, f, 2, depth)?;
            f.write_char(' ')?;
            show_precedence_cla(naming, t2, f, 3, depth)?;
            if parenthesize {
                f.write_char(')')?;
            }
            Ok(())
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        show_precedence_dbr(self, f, 0)
    }
}

/// Writes the De Bruijn representation of `term` straight into `f`.
///
/// Small-frame for the same reason as [`show_precedence_cla`], and for one more: this
/// is the path `assert_eq!` takes when it fails, so its depth limit decided how deep a
/// term a test could compare without aborting instead of reporting the mismatch.
fn show_precedence_dbr(
    term: &Term,
    f: &mut fmt::Formatter,
    context_precedence: usize,
) -> fmt::Result {
    match term {
        // Adjacent digits mean application, not a multi-digit number, so an index that
        // does not fit in one digit has to be delimited or it reads back as something else
        // entirely: bare `10` parses as `1 0`, not as 16. The brackets are purely a
        // delimiter - the digits inside are hexadecimal like everywhere else - and this is
        // the only form that round-trips at every index.
        Var(i) if *i <= 0xF && *i != 0 => write!(f, "{i:X}"),
        Var(i) => write!(f, "[{i:X}]"),
        Abs(t) => {
            let parenthesize = context_precedence > 1;
            if parenthesize {
                f.write_char('(')?;
            }
            f.write_char(LAMBDA)?;
            show_precedence_dbr(t, f, 0)?;
            if parenthesize {
                f.write_char(')')?;
            }
            Ok(())
        }
        App(boxed) => {
            let (ref t1, ref t2) = **boxed;
            let parenthesize = context_precedence == 3;
            if parenthesize {
                f.write_char('(')?;
            }
            show_precedence_dbr(t1, f, 2)?;
            show_precedence_dbr(t2, f, 3)?;
            if parenthesize {
                f.write_char(')')?;
            }
            Ok(())
        }
    }
}

/// A macro for chain application of `Term`s.
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::*;
///
/// assert_eq!(app!(Var(1), Var(2), Var(3)), app(app(Var(1), Var(2)), Var(3)));
/// # }
/// ```
#[macro_export]
macro_rules! app {
    ($term1:expr, $($term2:expr),+) => {
        {
            let mut term = $term1;
            $(term = app(term, $term2);)*
            term
        }
    };
}

/// A macro for multiple abstraction of `Term`s.
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::*;
///
/// assert_eq!(abs!(3, Var(1)), abs(abs(abs(Var(1)))));
/// # }
/// ```
#[macro_export]
macro_rules! abs {
    ($n:expr, $term:expr) => {{
        let mut term = $term;

        for _ in 0..$n {
            term = abs(term);
        }

        term
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Rewrites the `λ` in an expected rendering to whatever `LAMBDA` currently is.
    ///
    /// Lets the expectations below stay readable while still holding under the
    /// `backslash_lambda` feature, which used to break every one of them.
    fn lam(expected: &str) -> String {
        expected.replace('λ', &LAMBDA.to_string())
    }

    #[test]
    fn app_macro() {
        assert_eq!(
            app!(Var(4), app!(Var(1), Var(2), Var(3))),
            app(Var(4), app(app(Var(1), Var(2)), Var(3)))
        );
    }

    #[test]
    fn context_methods() {
        let ctx = Context::new(&["a", "b", "c"]);
        let empty_ctx = Context::empty();

        // len & is_empty
        assert_eq!(ctx.len(), 3);
        assert!(!ctx.is_empty());
        assert_eq!(empty_ctx.len(), 0);
        assert!(empty_ctx.is_empty());

        // contains
        assert!(ctx.contains("b"));
        assert!(!ctx.contains("d"));

        // iter
        let names: Vec<&str> = ctx.iter().collect();
        assert_eq!(names, vec!["a", "b", "c"]);
    }

    #[test]
    fn context_resolve_free_var() {
        let ctx = Context::new(&["a", "b", "c"]);

        // 1-based index, forward lookup
        assert_eq!(ctx.resolve_free_var(1), Some("a"));
        assert_eq!(ctx.resolve_free_var(3), Some("c"));

        // Invalid cases
        assert_eq!(ctx.resolve_free_var(0), None); // 0 is invalid
        assert_eq!(ctx.resolve_free_var(4), None); // Out of bounds
    }

    #[test]
    fn abs_macro() {
        assert_eq!(abs!(4, Var(1)), abs(abs(abs(abs(Var(1))))));

        assert_eq!(abs!(2, app(Var(1), Var(2))), abs(abs(app(Var(1), Var(2)))));
    }

    #[test]
    fn open_term_display() {
        assert_eq!(abs(Var(2)).to_string(), lam("λa.b"));
        assert_eq!(abs(Var(3)).to_string(), lam("λa.c"));
        assert_eq!(abs!(2, Var(3)).to_string(), lam("λa.λb.c"));
        assert_eq!(abs!(2, Var(4)).to_string(), lam("λa.λb.d"));
        assert_eq!(
            app!(
                Var(3),
                Var(4),
                abs(app(Var(4), Var(5))),
                abs!(2, app(Var(5), Var(6)))
            )
            .to_string(),
            lam("e f (λa.e f) (λa.λb.e f)")
        );
        assert_eq!(
            app!(
                abs!(2, app(Var(3), Var(4))),
                Var(1),
                Var(2),
                abs(app(Var(2), Var(3)))
            )
            .to_string(),
            lam("(λa.λb.c d) c d (λa.c d)")
        );
        assert_eq!(
            app(abs(Var(1)), app(abs(app(Var(10), Var(1))), Var(10))).to_string(),
            lam("(λa.a) ((λa.j a) k)")
        );

        assert_eq!(
            abs!(
                27,
                app!(Var(28), Var(29), Var(30), Var(50), Var(702), Var(703))
            )
            .to_string(),
            lam(
                "λa.λb.λc.λd.λe.λf.λg.λh.λi.λj.λk.λl.λm.λn.λo.λp.λq.λr.λs.λt.λu.λv.λw.λx.λy.λz.λaa.ab ac ad ax zz aaa"
            )
        );
        assert_eq!(
            abs!(3, app!(Var(2), Var(3), Var(4))).to_string(),
            lam("λa.λb.λc.b a d")
        );
        assert_eq!(Var(26).to_string(), "z");
        assert_eq!(Var(27).to_string(), "aa");
    }

    #[test]
    fn display_modes() {
        let zero = abs!(2, Var(1));
        let succ = abs!(3, app(Var(2), app!(Var(3), Var(2), Var(1))));
        let pred = abs!(
            3,
            app!(
                Var(3),
                abs!(2, app(Var(1), app(Var(2), Var(4)))),
                abs(Var(2)),
                abs(Var(1))
            )
        );

        assert_eq!(zero.to_string(), lam("λa.λb.b"));
        assert_eq!(succ.to_string(), lam("λa.λb.λc.b (a b c)"));
        assert_eq!(
            pred.to_string(),
            lam("λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)")
        );

        assert_eq!(format!("{:?}", zero), lam("λλ1"));
        assert_eq!(format!("{:?}", succ), lam("λλλ2(321)"));
        assert_eq!(format!("{:?}", pred), lam("λλλ3(λλ1(24))(λ2)(λ1)"));
    }

    #[test]
    fn term_display_with_context() {
        let ctx = Context::new(&["x", "y"]);

        // Term with only free variables: Var(1) -> x, Var(2) -> y
        let term1 = app(Var(1), Var(2));
        assert_eq!(term1.with_context(&ctx).to_string(), "x y");

        // Term with bound and free variables
        // λa. a y  (y is Var(2) from context)
        let term2 = abs(app(Var(1), Var(3)));
        assert_eq!(term2.with_context(&ctx).to_string(), lam("λa.a y"));

        let term3 = abs(Var(2));
        assert_eq!(term3.with_context(&ctx).to_string(), lam("λa.x"));
    }

    #[test]
    fn term_display_with_clashing_context() {
        let ctx = Context::new(&["a", "c"]);

        let term1 = app(Var(1), Var(2));
        assert_eq!(term1.with_context(&ctx).to_string(), "a c");

        let term2 = abs(app(Var(1), Var(3)));
        assert_eq!(term2.with_context(&ctx).to_string(), lam("λb.b c"));

        let term3 = abs(Var(2));
        assert_eq!(term3.with_context(&ctx).to_string(), lam("λb.a"));
    }

    #[test]
    fn term_display_without_context() {
        let term1 = app(Var(1), Var(2));
        assert_eq!(term1.to_string(), "a b");
        assert_eq!(
            term1.with_context(&Context::empty()).to_string(),
            "<unknown1> <unknown2>"
        );

        let term2 = abs(app(Var(1), Var(3)));
        assert_eq!(term2.to_string(), lam("λa.a c"));
        assert_eq!(
            term2.with_context(&Context::empty()).to_string(),
            lam("λa.a <unknown2>")
        );

        let term3 = abs(Var(2));
        assert_eq!(term3.to_string(), lam("λa.b"));
        assert_eq!(
            term3.with_context(&Context::empty()).to_string(),
            lam("λa.<unknown1>")
        );
    }

    #[test]
    fn is_supercombinator() {
        assert!(abs(Var(1)).is_supercombinator());
        assert!(app(abs(Var(1)), abs(Var(1))).is_supercombinator());
        assert!(abs!(10, Var(10)).is_supercombinator());
        assert!(abs!(10, app(Var(10), Var(10))).is_supercombinator());

        assert!(!Var(0).is_supercombinator());
        assert!(!Var(1).is_supercombinator());
        assert!(!abs(Var(2)).is_supercombinator());
        assert!(!app(abs(Var(1)), Var(1)).is_supercombinator());
        assert!(!abs!(10, Var(11)).is_supercombinator());
        assert!(!abs!(10, app(Var(10), Var(11))).is_supercombinator());
    }

    #[test]
    fn max_depth() {
        assert_eq!(Var(1).max_depth(), 0);
        assert_eq!(abs(Var(1)).max_depth(), 1);
        assert_eq!(abs!(10, Var(5)).max_depth(), 10);
        assert_eq!(
            app!(abs!(5, Var(2)), abs!(9, Var(4)), abs!(7, Var(6))).max_depth(),
            9
        );
    }

    #[test]
    fn is_isomorphic_to() {
        assert!(abs(Var(1)).is_isomorphic_to(&abs(Var(1))));
        assert!(!abs(Var(1)).is_isomorphic_to(&abs(Var(2))));
        assert!(!app(abs(Var(1)), Var(1)).is_isomorphic_to(&app(abs(Var(1)), Var(2))));
        assert!(app(abs(Var(1)), Var(1)).is_isomorphic_to(&app(abs(Var(1)), Var(1))));
        assert!(!app(abs(Var(1)), Var(1)).is_isomorphic_to(&app(Var(2), abs(Var(1)))));
    }

    #[test]
    fn has_free_variables() {
        assert!(!(abs(Var(1)).has_free_variables()));
        assert!(abs(Var(2)).has_free_variables());
        assert!(app(abs(Var(2)), Var(1)).has_free_variables());
        assert!(app(abs(Var(2)), abs(Var(1))).has_free_variables());
        assert!(app(abs(Var(1)), abs(Var(2))).has_free_variables());
        assert!(!app(abs(Var(1)), abs(Var(1))).has_free_variables());
        assert!(
            !(abs(app(
                abs(app(Var(2), app(Var(1), Var(1)))),
                abs(app(Var(2), app(Var(1), Var(1)))),
            )))
            .has_free_variables()
        );
        assert!((Var(0)).has_free_variables());
    }
}
