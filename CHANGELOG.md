Version 2.0.0
=============

Thanks
-------
@billpmurphy for the idea to make `reduction::beta` IO-free, splitting conversions (and
thus allowing all encodings to be compiled together), adding `term::is_supercombinator`,
`option::{map, unwrap_or, and_then}`, `church::{to_scott, to_parigot, to_stumpfu}`, `combinators::T`
and `scott::{is_zero, to_church}`, improving conversions into terms and adding
`impl<T> IntoChurch for Option<T> where T: IntoChurch`

Breaking changes
-------
- restructure and rename modules
- rework compilation features
- remove `impl Term` from Church data types
- remove `reduction::compare`
- remove `Term::{app, apply}`
- rename `term::Error` to `term::TermError`
- rename `TermError` variant names
- rename combinators
- rename `*::numerals::plus` to `add`
- rename `*::numerals::mult` to `mul`
- rename `church::numerals::{lshift, rshift}` to `{shl, shr}`
- rename `Term::beta` to `Term::reduce`
- rename `church::lists::null` to `is_nil`
- rename `parser::Error` to `ParseError`
- rename `combinators::T` to `R`
- simplify `term::Error`
- unify test and bench names
- make `reduction::beta` IO-free
- make `ParseError::InvalidCharacter` 0-indexed
- split `Into<Term>` conversion into `IntoChurch`, `IntoScott` and `IntoParigot`

Changes
-------
- fix the empty case in `list::take_while`
- refactor benchmarks using macros
- refactor integration tests using macros
- improve documentation
- implement conversions to pair, list and option for all numeral types
- add Stump-Fu numeral encoding
- add Church-, Scott- and Parigot-encoded list
- add `option::{map, unwrap_or, and_then}`
- add `term::is_supercombinator`
- add `stumpfu::{zero, is_zero, one, succ, pred, add}`
- add an `encoding` feature and make it default
- add `parigot::{is_zero, one, mult, sub}`
- add `impl<T> IntoChurch for Option<T> where T: IntoChurch`
- add macros for automated creation of conversion traits and implementations
- add `scott::{is_zero, one, add, mul, pow}`
- add `church::{to_scott, to_parigot, to_stumpfu}`
- add `scott::to_church`
- add `combinators::T` (Turing combinator)
- add `lists::{church, scott, parigot}::{nil, is_nil, cons, head, tail}`

Version 1.4.0
=============

Thanks
-------
@billpmurphy for creating `church::option`, adding `option::{none, some, is_none, is_some,
map_or}`, adding `church::lists::{init, zip, zip_with, take, take_while}` and simplifying
`church::lists::last`

Changes
-------

- add Scott encoding as a compilation feature
- add a Scott numerals module
- add `scott::{zero, succ, pred}`
- add Parigot encoding as a compilation feature
- add a Parigot numerals module
- add `parigot::{zero, succ, pred, plus}`
- add a Church option module
- add `church::option::{is_none, is_some, map_or}`
- add `church::pairs::swap`
- add `church::lists::{init, zip, zip_with, take_while}`
- simplify `church::lists::last`
- more fine-grained parser benchmarks
- add Church list benchmarks

Version 1.3.0
=============

Thanks
-------
@billpmurphy for adding `church::lists::last`

Changes
-------

- add `church::lists::last`
- change all instances of `try!()` to `?`
- replace 2 `clone()`s with `replace()`s (**big** performance wins)
- simplify doctest imports in booleans.rs
- simplify and improve doctests in combinators.rs, lists.rs, pairs.rs and numerals.rs
- reorganize unit tests in lists.rs
- remove lots of doctest boilerplate
- some code readability improvements
- more benchmarks

Version 1.2.0
=============

Thanks
-------
@billpmurphy for adding `church::numerals::{min, max, lshift, rshift, is_even, is_odd}` and
`church::pairs::uncurry`

Changes
-------

- add `church::numerals::{min, max, lshift, rshift, is_even, is_odd}` for Church numerals
- add `church::pairs::uncurry`
- add `abs!()` macro for multiple abstraction and use it internally
- simplify many `church::numerals` functions using `church::numerals::{one, pred}`
- move integration tests to a [tests](https://github.com/ljedrz/lambda_calculus/tree/master/tests) folder

Version 1.1.1
=============

Changes
-------

- remove one unnecessary mutability
- add maintenance badges

Version 1.1.0
=============

Changes
-------

- core tests no longer use Church-encoded data
- adhere to [C-REEXPORT](https://github.com/brson/rust-api-guidelines#c-reexport)
- improved parser performance
- improved readability of `reduction::compare`
- added benchmarks
- fixed two doc links
- minor code improvements

Version 1.0.0
=============

First stable release.
