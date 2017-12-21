#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::list::*;
use lambda::data::numerals::{church, scott, parigot, stumpfu};

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

// hof as in higher-order function; a temporary workaround until I think of a more generic test_list
macro_rules! test_list_hof {
    ($name:ident, $hof:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(beta(app!($hof(), church::$function(),  $($n.into_church()),*),  HAP, 0), $result.into_church());)*
            $(assert_eq!(beta(app!($hof(), scott::$function(),   $($n.into_scott()),*),   HNO, 0), $result.into_scott());)*
            $(assert_eq!(beta(app!($hof(), parigot::$function(), $($n.into_parigot()),*), HAP, 0), $result.into_parigot());)*
            $(assert_eq!(beta(app!($hof(), stumpfu::$function(), $($n.into_stumpfu()),*), HAP, 0), $result.into_stumpfu());)*
        }
    );
}

// hof as in higher-order function; a temporary workaround until I think of a more generic test_list
macro_rules! test_list_hof2 {
    ($name:ident, $hof:ident, $function:ident, $a:expr, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(beta(app!($hof(), church::$function(),  $a.into_church(), $($n.into_church()),*),  HAP, 0), $result.into_church());)*
            $(assert_eq!(beta(app!($hof(), scott::$function(),   $a.into_scott(), $($n.into_scott()),*),   HNO, 0), $result.into_scott());)*
            $(assert_eq!(beta(app!($hof(), parigot::$function(), $a.into_parigot(), $($n.into_parigot()),*), HAP, 0), $result.into_parigot());)*
            $(assert_eq!(beta(app!($hof(), stumpfu::$function(), $a.into_stumpfu(), $($n.into_stumpfu()),*), HAP, 0), $result.into_stumpfu());)*
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

// test_list_enc!(list_length, length,

// test_list_enc!(list_index, index,

test_list!(list_reverse, reverse,
    empty() => empty(),
    vec![1] => vec![1],
    vec![1, 2] => vec![2, 1],
    vec![1, 2, 3] => vec![3, 2, 1]
);

// list() not finished
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

test_list_hof!(list_map, map, succ,
    empty() => empty(),
    vec![1] => vec![2],
    vec![1, 2] => vec![2, 3],
    vec![1, 2, 3] => vec![2, 3, 4]
);

test_list_hof2!(list_foldl, foldl, add, 0,
    empty() => 0,
    vec![1] => 1,
    vec![1, 2] => 3,
    vec![1, 2, 3] => 6
);

test_list_hof2!(list_foldr, foldr, add, 0,
    empty() => 0,
    vec![1] => 1,
    vec![1, 2] => 3,
    vec![1, 2, 3] => 6
);

test_list_hof!(list_filter, filter, is_zero,
    empty() => empty(),
    vec![1] => empty(),
    vec![1, 0] => vec![0],
    vec![0, 1] => vec![0],
    vec![0, 1, 0] => vec![0, 0]
);

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

test_list_hof!(list_zip_with, zip_with, add,
    empty(), vec![1] => empty(),
    vec![1], empty() => empty(),
    vec![1], vec![1] => vec![2],
    vec![1, 2], vec![1] => vec![2],
    vec![1], vec![1, 2] => vec![2],
    vec![1, 2], vec![3, 4] => vec![4, 6]
);

//test_list_enc!(list_take, take,

test_list_hof!(list_take_while, take_while, is_zero,
    empty() => empty(),
    vec![0] => vec![0],
    vec![1] => empty(),
    vec![1, 0] => empty(),
    vec![0, 1] => vec![0],
    vec![0, 0, 1] => vec![0, 0]
);
