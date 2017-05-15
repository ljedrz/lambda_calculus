//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

use term::*;
use term::Term::*;
use self::Order::*;
use std::fmt;

/// Set to `true` to see all the steps of β-reductions. The default is `false`.
pub const SHOW_REDUCTIONS: bool = false;

/// The [evaluation order](http://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf) of
/// β-reductions. The default is `Normal`.
///
/// They don't always yield the same result:
///
/// - The `Normal`, `HybridNormal`, `Applicative` and `HybridApplicative` orders reduce expressions
/// to their normal forms
/// - The `Applicative` order will fail to fully reduce expressions containing functions
/// without a normal form, e.g. the `Y` combinator (they will expand forever)
/// - The `CallByName` order reduces to weak head normal form
/// - The `CallByValue` order reduces to weak normal form
/// - The `HeadSpine` order reduces to head normal form
#[derive(Debug, PartialEq)]
pub enum Order {
    /// leftmost outermost
    Normal,
    /// leftmost outermost, but not inside abstractions
    CallByName,
    /// leftmost outermost, but abstractions reduced only in head position
    HeadSpine,
    /// a hybrid between `HeadSpine` and `Normal`
    HybridNormal,
    /// leftmost innermost
    Applicative,
    /// leftmost innermost, but not inside abstractions
    CallByValue,
    /// a hybrid between `CallByValue` and `Applicative`
    HybridApplicative
}

/// Applies two `Term`s with substitution and variable update, consuming the first one in the
/// process. It produces an `Error` if the first `Term` is not an `Abs`traction.
///
/// # Example
/// ```
/// use lambda_calculus::reduction::apply;
/// use lambda_calculus::parser::parse;
///
/// let lhs    = parse(&"λλ42(λ13)").unwrap();
/// let rhs    = parse(&"λ51").unwrap();
/// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
///
/// assert_eq!(apply(lhs, &rhs), Ok(result));
/// ```
pub fn apply(mut lhs: Term, rhs: &Term) -> Result<Term, Error> {
    _apply(&mut lhs, rhs, 0);

    lhs.unabs()
}

fn _apply(lhs: &mut Term, rhs: &Term, depth: usize) {
    match *lhs {
        Var(i) => if i == depth {
            *lhs = rhs.clone(); // substitute a top-level variable from lhs with rhs
            update_free_variables(lhs, depth - 1, 0); // update indices of free variables from rhs
        } else if i > depth {
            *lhs = Var(i - 1) // decrement a free variable's index
        },
        Abs(_) => {
            _apply(lhs.unabs_ref_mut().unwrap(), rhs, depth + 1)
        },
        App(_, _) => {
            _apply(lhs.lhs_ref_mut().unwrap(), rhs, depth);
            _apply(lhs.rhs_ref_mut().unwrap(), rhs, depth)
        }
    }
}

fn update_free_variables(term: &mut Term, added_depth: usize, own_depth: usize) {
    match *term {
        Var(i) => if i > own_depth {
            *term = Var(i + added_depth)
        },
        Abs(_) => {
            update_free_variables(term.unabs_ref_mut().unwrap(), added_depth, own_depth + 1)
        },
        App(_, _) => {
            update_free_variables(term.lhs_ref_mut().unwrap(), added_depth, own_depth);
            update_free_variables(term.rhs_ref_mut().unwrap(), added_depth, own_depth)
        }
    }
}

/// Performs β-reduction on a `Term` with the specified evaluation `Order` and an optional limit on
/// number of reductions (`0` means no limit).
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::pred;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::Normal;
///
/// let pred_one = pred().app(1.into());
///
/// assert_eq!(beta(pred_one, &Normal, 0), 0.into());
/// ```
pub fn beta(mut term: Term, order: &Order, limit: usize) -> Term {
    term.beta(order, limit);
    term
}

/// Prints the number of reductions required for `term` to reach the final form with all the
/// available reduction strategies, optionally excluding the ones from the given list. Such
/// exclusions might be necessary, especially if the expression contains the fixed-point combinator.
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::factorial;
/// use lambda_calculus::reduction::benchmark;
/// use lambda_calculus::reduction::Order::*;
///
/// benchmark(&factorial().app(3.into()), &[CallByName, CallByValue, HeadSpine]);
///
/// // stdout:
///
/// // normal:             46
/// // applicative:        39
/// // hybrid normal:      46
/// // hybrid applicative: 39
/// ```
pub fn benchmark(term: &Term, exclude: &[Order]) {
    let mut count = 0;
    if !exclude.contains(&CallByName) {
        term.clone().beta_cbn(0, 0, &mut count);
        println!("{}:       {}", CallByName, count);
        count = 0;
    }
    if !exclude.contains(&Normal) {
        term.clone().beta_nor(0, 0, &mut count);
        println!("{}:             {}", Normal, count);
        count = 0;
    }
    if !exclude.contains(&CallByValue) {
        term.clone().beta_cbv(0, 0, &mut count);
        println!("{}:      {}", CallByValue, count);
        count = 0;
    }
    if !exclude.contains(&Applicative) {
        term.clone().beta_app(0, 0, &mut count);
        println!("{}:        {}", Applicative, count);
        count = 0;
    }
    if !exclude.contains(&HeadSpine) {
        term.clone().beta_hs(0, 0, &mut count);
        println!("{}:         {}", HeadSpine, count);
        count = 0;
    }
    if !exclude.contains(&HybridNormal) {
        term.clone().beta_hnor(0, 0, &mut count);
        println!("{}:      {}", HybridNormal, count);
        count = 0;
    }
    if !exclude.contains(&HybridApplicative) {
        term.clone().beta_happ(0, 0, &mut count);
        println!("{}: {}", HybridApplicative, count);
    }
}

impl Term {
    /// Applies `self` to another `Term` and performs substitution, consuming `self` in the process.
    /// It produces an `Error` if `self` is not an `Abs`traction.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::parser::parse;
    ///
    /// let lhs    = parse(&"λλ42(λ13)").unwrap();
    /// let rhs    = parse(&"λ51").unwrap();
    /// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
    ///
    /// assert_eq!(lhs.apply(&rhs), Ok(result));
    /// ```
    pub fn apply(self, rhs: &Term) -> Result<Term, Error> {
        apply(self, rhs)
    }

    /// Reduces an `App`lication by substitution and variable update. It produces an `Error` if
    /// `self` is not an `App`lication.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::{app, abs};
    /// use lambda_calculus::term::Term::Var;
    /// use lambda_calculus::arithmetic::zero;
    /// use lambda_calculus::combinators::i;
    ///
    /// assert_eq!(app(i(), zero()).eval(), Ok(zero()));
    /// ```
    pub fn eval(self) -> Result<Term, Error> {
        let (lhs, rhs) = try!(self.unapp());

        apply(lhs, &rhs)
    }

    fn eval_with_info(&mut self, depth: u32, count: &usize) {
        if SHOW_REDUCTIONS {
            print!("\n{}. {}\n=>", count + 1, show_precedence(self, 0, depth));
            let mut indent_len = ((*count + 1) as f32).log10().trunc() as usize + 3;
            if DISPLAY_CLASSIC { indent_len += 3 }
            for _ in 0..indent_len { print!(" ") };
        };
        let copy = self.clone();
        *self = copy.eval().unwrap();
        if SHOW_REDUCTIONS { println!("{}", show_precedence(self, 0, depth)) };
    }

    fn is_reducible(&self, limit: usize, count: &usize) -> bool {
        self.lhs_ref().unwrap().unabs_ref().is_ok() &&
        (limit == 0 || *count < limit )
    }

    /// Performs β-reduction on a `Term` with the specified evaluation `Order` and an optional
    /// limit on number of reductions (`0` means no limit).
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::pred;
    /// use lambda_calculus::reduction::Order::Normal;
    ///
    /// let mut pred_one = pred().app(1.into());
    /// pred_one.beta(&Normal, 0);
    ///
    /// assert_eq!(pred_one, 0.into());
    /// ```
    pub fn beta(&mut self, order: &Order, limit: usize) {
        if SHOW_REDUCTIONS {
            println!("reducing {} [{} order{}]:", self, order,
                if limit != 0 {
                    format!(", limit of {} reduction{}", limit,
                        if limit == 1 { "" } else { "s" }
                    )
                } else {
                    "".into()
                }
            );
        };

        let mut count = 0;

        match *order {
            CallByName        => self.beta_cbn(0, limit, &mut count),
            Normal            => self.beta_nor(0, limit, &mut count),
            CallByValue       => self.beta_cbv(0, limit, &mut count),
            Applicative       => self.beta_app(0, limit, &mut count),
            HeadSpine         => self.beta_hs(0, limit, &mut count),
            HybridNormal      => self.beta_hnor(0, limit, &mut count),
            HybridApplicative => self.beta_happ(0, limit, &mut count)
        }
        if SHOW_REDUCTIONS {
            println!("\nresult after {} reduction{}: {}\n", count,
                if limit == 1 { "" } else { "s" }, self);
        };
    }

    fn beta_cbn(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_cbn(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_cbn(depth, limit, count);
                }
            },
            _ => ()
        }
    }

    fn beta_nor(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_nor(depth + 1, limit, count),
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_cbn(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_nor(depth, limit, count);
                } else {
                    self.lhs_ref_mut().unwrap().beta_nor(depth, limit, count);
                    self.rhs_ref_mut().unwrap().beta_nor(depth, limit, count);
                }
            }
        }
    }

    fn beta_cbv(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_cbv(depth, limit, count);
                self.rhs_ref_mut().unwrap().beta_cbv(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_cbv(depth, limit, count);
                }
            },
            _ => ()
        }
    }

    fn beta_app(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_app(depth + 1, limit, count),
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_app(depth, limit, count);
                self.rhs_ref_mut().unwrap().beta_app(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_app(depth, limit, count);
                }
            }
        }
    }

    fn beta_happ(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_happ(depth + 1, limit, count),
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_cbv(depth, limit, count);
                self.rhs_ref_mut().unwrap().beta_happ(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_happ(depth, limit, count);
                } else {
                    self.lhs_ref_mut().unwrap().beta_happ(depth, limit, count);
                }
            }
        }
    }

    fn beta_hs(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_hs(depth + 1, limit, count),
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_cbn(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_hs(depth, limit, count)
                }
            }
        }
    }

    fn beta_hnor(&mut self, depth: u32, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_hnor(depth + 1, limit, count),
            App(_, _) => {
                self.lhs_ref_mut().unwrap().beta_hs(depth, limit, count);

                if self.is_reducible(limit, count) {
                    self.eval_with_info(depth, count);
                    *count += 1;
                    self.beta_hnor(depth, limit, count)
                } else {
                    self.lhs_ref_mut().unwrap().beta_hnor(depth, limit, count);
                    self.rhs_ref_mut().unwrap().beta_hnor(depth, limit, count);
                }
            }
        }
    }
}

impl fmt::Display for Order {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match *self {
            Normal => "normal",
            CallByName => "call-by-name",
            HeadSpine => "head spine",
            HybridNormal => "hybrid normal",
            Applicative => "applicative",
            CallByValue => "call-by-value",
            HybridApplicative => "hybrid applicative"
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use parser::parse;
    use combinators::{i, omm};

    #[test]
    fn normal_order() {
        let reduces_instantly = parse(&"(λλ1)((λλλ((32)1))(λλ2))").unwrap();
        assert_eq!(beta(reduces_instantly.clone(), &Normal, 0),
                   beta(reduces_instantly,         &Normal, 1)
        );

        let should_reduce = parse(&"(λ2)((λ111)(λ111))").unwrap();
        assert_eq!(beta(should_reduce, &Normal, 0), Var(1));

        let does_reduce = app(abs(Var(2)), omm());
        assert_eq!(beta(does_reduce, &Normal, 0), Var(1));
    }

    #[test]
    fn call_by_name_order() {
        let mut expr = app(abs(app(i(), Var(1))), app(i(), i()));
        expr.beta(&CallByName, 1);
        assert_eq!(expr, app(i(), app(i(), i())));
        expr.beta(&CallByName, 1);
        assert_eq!(expr, app(i(), i()));
        expr.beta(&CallByName, 1);
        assert_eq!(expr, i());
    }

    #[test]
    fn applicative_order() {
        let expr = parse(&"λ1(((λλλ1)1)((λλ21)1))").unwrap();
        assert_eq!(&format!("{}", beta(expr, &Applicative, 1)), "λ1((λλ1)((λλ21)1))");

        let expands = parse(&"(λ2)((λ111)(λ111))").unwrap();
        assert_eq!(&format!("{}", beta(expands, &Applicative, 1)), "(λ2)((λ111)(λ111)(λ111))");

        let mut wont_reduce = app(abs(Var(2)), omm());
        wont_reduce.beta(&Applicative, 3);
        assert_eq!(wont_reduce, app(abs(Var(2)), omm()));
    }

    #[test]
    fn call_by_value_order() {
        let mut expr = app(abs(app(i(), Var(1))), app(i(), i()));
        expr.beta(&CallByValue, 1);
        assert_eq!(expr, app(abs(app(i(), Var(1))), i()));
        expr.beta(&CallByValue, 1);
        assert_eq!(expr, app(i(), i()));
        expr.beta(&CallByValue, 1);
        assert_eq!(expr, i());
    }
}
