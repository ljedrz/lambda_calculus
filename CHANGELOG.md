Version 1.3.0
=============

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
