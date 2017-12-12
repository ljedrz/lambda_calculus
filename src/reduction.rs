//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

use term::{Term, TermError, show_precedence_cla};
use term::Term::*;
use std::fmt;
use std::io::{Write, BufWriter, stdout};
use std::mem;
pub use self::Order::*;

/// The [evaluation order](http://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf) of
/// β-reductions. The default is `NOR` (normal order).
///
/// They don't always yield the same result:
///
/// - The `NOR`, `HNO`, `APP` and `HAP` orders reduce expressions to their normal forms
/// - The `APP` order will fail to fully reduce expressions containing functions without a normal
/// form, e.g. the `Y` combinator (they will expand forever)
/// - The `CBN` order reduces to weak head normal form
/// - The `CBV` order reduces to weak normal form
/// - The `HSP` order reduces to head normal form
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Order {
    /// Normal - leftmost outermost; the most popular lambda calculus reduction strategy
    NOR,
    /// Call-by-name - leftmost outermost, but no reductions inside abstractions
    CBN,
    /// Head spine - leftmost outermost, but abstractions reduced only in head position
    HSP,
    /// Hybrid normal - a hybrid between `HSP` (head spine) and `NOR` (normal) strategies
    HNO,
    /// Applicative - leftmost innermost; the most eager strategy; unfit for recursion combinators
    APP,
    /// Call-by-value - leftmost innermost, but no reductions inside abstractions
    CBV,
    /// Hybrid applicative - a hybrid between `CBV` (call-by-value) and `APP` (applicative)
    /// strategies; usually the fastest-reducing normalizing strategy
    HAP
}

/// Applies two `Term`s with substitution and variable update, consuming the first one in the
/// process.
///
/// # Example
/// ```
/// use lambda_calculus::reduction::apply;
/// use lambda_calculus::*;
///
/// // these are valid terms, but be careful with unwraps in your code
/// let lhs    = parse(&"λλ42(λ13)", DeBruijn).unwrap();
/// let rhs    = parse(&"λ51", DeBruijn).unwrap();
/// let result = parse(&"λ3(λ61)(λ1(λ71))", DeBruijn).unwrap();
///
/// assert_eq!(apply(lhs, &rhs), Ok(result));
/// ```
/// # Errors
///
/// The function will return an error if the `lhs` term is not an `Abs`traction.
pub fn apply(mut lhs: Term, rhs: &Term) -> Result<Term, TermError> {
    if lhs.unabs_ref().is_err() { return Err(TermError::NotAnAbs) }

    _apply(&mut lhs, rhs, 0);

    lhs.unabs()
}

fn _apply(lhs: &mut Term, rhs: &Term, depth: usize) {
    match *lhs {
        Var(i) => if i == depth {
            *lhs = rhs.to_owned(); // substitute a top-level variable from lhs with rhs
            update_free_variables(lhs, depth - 1, 0); // update indices of free variables from rhs
        } else if i > depth {
            *lhs = Var(i - 1) // decrement a free variable's index
        },
        Abs(ref mut abstracted) => {
            _apply(abstracted, rhs, depth + 1)
        },
        App(ref mut lhs_lhs, ref mut lhs_rhs) => {
            _apply(lhs_lhs, rhs, depth);
            _apply(lhs_rhs, rhs, depth)
        }
    }
}

fn update_free_variables(term: &mut Term, added_depth: usize, own_depth: usize) {
    match *term {
        Var(ref mut i) => if *i > own_depth {
            *i += added_depth
        },
        Abs(ref mut abstracted) => {
            update_free_variables(abstracted, added_depth, own_depth + 1)
        },
        App(ref mut lhs, ref mut rhs) => {
            update_free_variables(lhs, added_depth, own_depth);
            update_free_variables(rhs, added_depth, own_depth)
        }
    }
}

/// Performs β-reduction on a `Term` with the specified evaluation `Order`, an optional limit on
/// number of reductions (`0` means no limit) and optional display of reduction steps; it returns
/// the `Term` after reductions.
///
/// # Example
///
/// ```
/// use lambda_calculus::*;
///
/// let expression = parse(&"(λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)) (λa.λb.a b)", Classic);
/// let reduced    = parse(&"λa.λb.b", Classic);
///
/// assert!(expression.is_ok());
/// assert!(reduced.is_ok());
/// assert_eq!(beta(expression.unwrap(), NOR, 0, false), reduced.unwrap());
/// ```
pub fn beta(mut term: Term, order: Order, limit: usize, verbose: bool) -> Term {
    term.beta(order, limit, verbose);
    term
}

/// Prints the number of reductions required for a `Term` to reach the final form with the given
/// reduction strategies and optionally displaying the applicable reduction steps.
///
/// # Example
///
/// ```
/// use lambda_calculus::reduction::compare;
/// use lambda_calculus::*;
///
/// let expression = parse(&"(λa.a (λb.λc.λd.b (λe.c (d e)) (λe.λf.e (d e f))) (λb.λc.b)\
///     (λb.λc.b c) (λb.λc.b c)) (λa.λb.a (a (a b)))", Classic); // Church-encoded factorial of 3
///
/// assert!(expression.is_ok());
/// compare(&expression.unwrap(), &[NOR, APP, HNO, HAP], false); // compare normalizing strategies
///
/// // stdout:
///
/// // normal:             35
/// // applicative:        36
/// // hybrid normal:      35
/// // hybrid applicative: 30
/// ```
pub fn compare(term: &Term, orders: &[Order], verbose: bool) {
    let stdout = stdout();
    let mut buf = BufWriter::new(stdout.lock());

    writeln!(buf, "comparing β-reduction strategies for {}:\n", term).unwrap();
    for order in orders {
        writeln!(buf, "{}:{}{}",
            order,
            " ".repeat(19 - format!("{}", order).len()),
            term.to_owned().beta(*order, 0, verbose)
        ).unwrap();
    }
}

impl Term {
    /// Applies `self` to another `Term` and performs substitution, consuming `self` in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::parser::*;
    ///
    /// let lhs    = parse(&"λλ42(λ13)", DeBruijn).unwrap();
    /// let rhs    = parse(&"λ51", DeBruijn).unwrap();
    /// let result = parse(&"λ3(λ61)(λ1(λ71))", DeBruijn).unwrap();
    ///
    /// assert_eq!(lhs.apply(&rhs), Ok(result));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not an `Abs`traction.
    pub fn apply(self, rhs: &Term) -> Result<Term, TermError> {
        apply(self, rhs)
    }

    /// Reduces an `App`lication by substitution and variable update.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    /// use lambda_calculus::combinators::i;
    ///
    /// assert_eq!(app(i(), Var(1)).eval(), Ok(Var(1)));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not an `App`lication or if its left hand
    /// side term is not an `Abs`traction.
    pub fn eval(self) -> Result<Term, TermError> {
        let (lhs, rhs) = self.unapp()?;

        apply(lhs, &rhs)
    }

    fn eval_with_info(&mut self, depth: u32, count: &mut usize, verbose: bool) {
        if verbose { println!("\n{}. {}", *count + 1, show_precedence_cla(self, 0, depth)) }

        let mut to_eval = mem::replace(self, Var(0)); // replace self with a dummy
        to_eval = to_eval.eval().unwrap(); // safe; only called in reduction sites
        mem::replace(self, to_eval); // move self back to its place
        *count += 1;

        if verbose {
            let indent_len = ((*count + 1) as f32).log10().trunc() as usize + 5;
            println!("=>{}{}", " ".repeat(indent_len), show_precedence_cla(self, 0, depth))
        }
    }

    fn is_reducible(&self, limit: usize, count: &usize) -> bool {
        self.lhs_ref().and_then(|t| t.unabs_ref()).is_ok() && (limit == 0 || *count < limit )
    }

    /// Performs β-reduction on a `Term` with the specified evaluation `Order`, an optional limit
    /// on number of reductions (`0` means no limit) and optional display of reduction steps; it
    /// returns the number of performed reductions.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let expression = parse(&"(λa.λb.λc.b (a b c)) (λa.λb.b)", Classic);
    /// let reduced    = parse(&"λa.λb.a b", Classic);
    ///
    /// assert!(expression.is_ok());
    /// assert!(reduced.is_ok());
    ///
    /// let mut expression = expression.unwrap();
    /// expression.beta(NOR, 0, false);
    ///
    /// assert_eq!(expression, reduced.unwrap());
    /// ```
    pub fn beta(&mut self, order: Order, limit: usize, verbose: bool) -> usize {
        if verbose {
            println!("β-reducing {} [{} order{}]:",
                self,
                order,
                if limit != 0 {
                    format!(", limit of {} reduction{}", limit, if limit == 1 { "" } else { "s" })
                } else {
                    "".into()
                }
            );
        };

        let mut count = 0;

        match order {
            CBN => self.beta_cbn(0, limit, &mut count, verbose),
            NOR => self.beta_nor(0, limit, &mut count, verbose),
            CBV => self.beta_cbv(0, limit, &mut count, verbose),
            APP => self.beta_app(0, limit, &mut count, verbose),
            HSP => self.beta_hsp(0, limit, &mut count, verbose),
            HNO => self.beta_hno(0, limit, &mut count, verbose),
            HAP => self.beta_hap(0, limit, &mut count, verbose)
        }

        if verbose {
            println!("\nresult after {} reduction{}: {}\n",
                count,
                if count == 1 { "" } else { "s" }, self
            );
        };

        count
    }

    fn beta_cbn(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        if let App(_, _) = *self {
            self.lhs_mut().unwrap().beta_cbn(depth, limit, count, verbose);

            if self.is_reducible(limit, count) {
                self.eval_with_info(depth, count, verbose);
                self.beta_cbn(depth, limit, count, verbose);
            }
        }
    }

    fn beta_nor(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_nor(depth + 1, limit, count, verbose),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_cbn(depth, limit, count, verbose);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count, verbose);
                    self.beta_nor(depth, limit, count, verbose);
                } else {
                    self.lhs_mut().unwrap().beta_nor(depth, limit, count, verbose);
                    self.rhs_mut().unwrap().beta_nor(depth, limit, count, verbose);
                }
            },
            _ => ()
        }
    }

    fn beta_cbv(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        if let App(_, _) = *self {
            self.lhs_mut().unwrap().beta_cbv(depth, limit, count, verbose);
            self.rhs_mut().unwrap().beta_cbv(depth, limit, count, verbose);

            if self.is_reducible(limit, count) {
                self.eval_with_info(depth, count, verbose);
                self.beta_cbv(depth, limit, count, verbose);
            }
        }
    }

    fn beta_app(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_app(depth + 1, limit, count, verbose),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_app(depth, limit, count, verbose);
                self.rhs_mut().unwrap().beta_app(depth, limit, count, verbose);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count, verbose);
                    self.beta_app(depth, limit, count, verbose);
                }
            },
            _ => ()
        }
    }

    fn beta_hap(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_hap(depth + 1, limit, count, verbose),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_cbv(depth, limit, count, verbose);
                self.rhs_mut().unwrap().beta_hap(depth, limit, count, verbose);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count, verbose);
                    self.beta_hap(depth, limit, count, verbose);
                } else {
                    self.lhs_mut().unwrap().beta_hap(depth, limit, count, verbose);
                }
            },
            _ => ()
        }
    }

    fn beta_hsp(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_hsp(depth + 1, limit, count, verbose),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_hsp(depth, limit, count, verbose);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count, verbose);
                    self.beta_hsp(depth, limit, count, verbose)
                }
            },
            _ => ()
        }
    }

    fn beta_hno(&mut self, depth: u32, limit: usize, count: &mut usize, verbose: bool) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_hno(depth + 1, limit, count, verbose),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_hsp(depth, limit, count, verbose);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count, verbose);
                    self.beta_hno(depth, limit, count, verbose)
                } else {
                    self.lhs_mut().unwrap().beta_hno(depth, limit, count, verbose);
                    self.rhs_mut().unwrap().beta_hno(depth, limit, count, verbose);
                }
            },
            _ => ()
        }
    }
}

impl fmt::Display for Order {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match *self {
            NOR => "normal",
            CBN => "call-by-name",
            HSP => "head spine",
            HNO => "hybrid normal",
            APP => "applicative",
            CBV => "call-by-value",
            HAP => "hybrid applicative"
        })
    }
}
