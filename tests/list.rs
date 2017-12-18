#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::list::*;

macro_rules! test_list {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(beta(app!($function(), $($n.into_church()),*), HAP, 0),  $result.into_church());)*
            $(assert_eq!(beta(app!($function(), $($n.into_scott()),*), HAP, 0),   $result.into_scott());)*
            $(assert_eq!(beta(app!($function(), $($n.into_parigot()),*), HAP, 0), $result.into_parigot());)*
            $(assert_eq!(beta(app!($function(), $($n.into_stumpfu()),*), HAP, 0), $result.into_stumpfu());)*
        }
    );
}

macro_rules! test_list_enc {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(beta(app!($function(Church),  $($n.into_church()),*), HAP, 0),  $result.into_church());)*
            $(assert_eq!(beta(app!($function(Scott),   $($n.into_scott()),*), HAP, 0),   $result.into_scott());)*
            $(assert_eq!(beta(app!($function(Parigot), $($n.into_parigot()),*), HAP, 0), $result.into_parigot());)*
            $(assert_eq!(beta(app!($function(StumpFu), $($n.into_stumpfu()),*), HAP, 0), $result.into_stumpfu());)*
        }
    );
}

fn empty() -> Vec<usize> { vec![] } // a workaround to pass vec![] to the testing macro

test_list!(list_head, head,
    vec![1] => 1,
    vec![1, 2] => 1,
    vec![1, 2, 3] => 1
);

test_list!(list_tail, tail,
    vec![1] => empty(),
    vec![1, 2] => vec![2],
    vec![1, 2, 3] => vec![2, 3]
);

test_list_enc!(list_length, length,
    empty() => 0,
    vec![1] => 1,
    vec![1, 2] => 2,
    vec![1, 2, 3] => 3
);

// test_list_enc!(list_index, index,

test_list!(list_reverse, reverse,
    empty() => empty(),
    vec![1] => vec![1],
    vec![1, 2] => vec![2, 1],
    vec![1, 2, 3] => vec![3, 2, 1]
);

// test_list_enc!(list_list, list,

test_list!(list_append, append,
    empty(), empty() => empty(),
    empty(), vec![1] => vec![1],
    vec![1], empty() => vec![1],
    vec![1], vec![2] => vec![1, 2],
    vec![1, 2], vec![3] => vec![1, 2, 3],
    vec![1], vec![2, 3] => vec![1, 2, 3],
    vec![1, 2], vec![3, 4] => vec![1, 2, 3, 4]
);

/* TODO: figure out passing multiple functions (inconsistent lockstep iteration) */

// test_list!(list_map, map, add,

// test_list!(list_foldl, foldl, add,

// test_list!(list_foldr, foldr, add,

// test_list!(list_filter, filter, is_zero,

test_list!(list_last, last,
    vec![1] => 1,
    vec![1, 2] => 2,
    vec![1, 2, 3] => 3
);

test_list!(list_init, init,
    vec![1] => empty(),
    vec![1, 2] => vec![1],
    vec![1, 2, 3] => vec![1, 2]
);

test_list!(list_zip, zip,
    empty(), vec![1] => empty(),
    vec![1], empty() => empty(),
    vec![1], vec![1] => vec![(1, 1)],
    vec![1, 2], vec![1] => vec![(1, 1)],
    vec![1], vec![1, 2] => vec![(1, 1)],
    vec![1, 2], vec![3, 4] => vec![(1, 3), (2, 4)]
);

//test_list!(list_zip, zip_with, add,

test_list_enc!(list_take, take,
    0, empty() => empty(),
    1, empty() => empty(),
    0, vec![1] => empty(),
    1, vec![1] => vec![1],
    2, vec![1] => vec![1],
    1, vec![1, 2] => vec![1],
    2, vec![1, 2] => vec![1, 2],
    3, vec![1, 2] => vec![1, 2]
);

//test_list!(list_take_while, take_while, is_zero,
