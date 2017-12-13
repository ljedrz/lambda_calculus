Version 2.0.0
=============

Thanks
-------
@billpmurphy for the idea to make `reduction::{beta, compare}` IO-free

Breaking changes
-------

- adjust compilation features
- remove `impl Term` from Church data types
- simplify and rename `term::Error` to `term::TermError`
- shorten `TermError` variant names
- rename `church` modules
- rename combinators
- unify test and bench names
- make `reduction::compare` and `reduction::beta` IO-free
- add `reduction::beta-verbose`

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
- add `zero()`, `succ()` and `pred()` for Scott numerals
- add Parigot encoding as a compilation feature
- add a Parigot numerals module
- add `zero()`, `succ()`, `pred()` and `plus()` for Parigot numerals
- add a Church option module
- add `is_none()`, `is_some()` and `map_or()` for Church option
- add `swap()` for Church pairs
- add `init()` for Church lists
- add `zip()` and `zip_with()`, `take()` and `take_while()` for Church lists
- simplify `last()`
- more fine-grained parser benchmarks
- add Church list benchmarks

Version 1.3.0
=============

Thanks
-------
@billpmurphy for adding `church::lists::last()`

Changes
-------

- add `last()` for Church lists
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

- add `min()` and `max()` for Church numerals
- add `lshift()` and `rshift()` for Church numerals
- add `uncurry()` for Church pairs
- add `is_even()` and `is_odd()` for Church numerals
- add `abs!()` macro for multiple abstraction and use it internally
- simplify many functions in numerals.rs with `pred()` and `one()`
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
