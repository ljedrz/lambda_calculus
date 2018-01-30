#![cfg(feature = "encoding")]
#![allow(warnings)] // silence unnecessary mutability for empty church vectors

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::list::pair::*;
use lambda::data::num::church::is_zero;

macro_rules! vec_church {
    ( $( $e:expr ),* ) => {
        {
            let mut vec = Vec::new();
            $( vec.push($e.into_church()); )*
            vec
        }
    };
}

macro_rules! test_pair_list {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(
                beta(app!($function(), $($n),*), HAP, 0),
                $result
            );)*
        }
    );
}

macro_rules! test_pair_list_lists_to_num {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(
                beta(app!($function(), $($n.into_pair_list()),*), HAP, 0),
                $result.into_church()
            );)*
        }
    );
}

macro_rules! test_pair_list_all_lists {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(
                beta(app!($function(), $($n.into_pair_list()),*), HAP, 0),
                $result.into_pair_list()
            );)*
        }
    );
}

test_pair_list_lists_to_num!(pair_list_head, head,
          vec_church![1] => 1,
       vec_church![1, 2] => 1,
    vec_church![1, 2, 3] => 1
);

test_pair_list_all_lists!(pair_list_tail, tail,
          vec_church![1] =>     vec_church![],
       vec_church![1, 2] =>    vec_church![2],
    vec_church![1, 2, 3] => vec_church![2, 3]
);

test_pair_list_lists_to_num!(pair_list_length, length,
           vec_church![] => 0,
          vec_church![1] => 1,
       vec_church![1, 2] => 2,
    vec_church![1, 2, 3] => 3
);

test_pair_list!(pair_list_index, index,
    0.into_church(),       vec_church![1].into_pair_list() => 1.into_church(),
    1.into_church(),    vec_church![1, 2].into_pair_list() => 2.into_church(),
    2.into_church(), vec_church![1, 2, 3].into_pair_list() => 3.into_church()
);

test_pair_list_all_lists!(pair_list_reverse, reverse,
           vec_church![] =>        vec_church![],
          vec_church![1] =>       vec_church![1],
       vec_church![1, 2] =>    vec_church![2, 1],
    vec_church![1, 2, 3] => vec_church![3, 2, 1]
);

test_pair_list!(pair_list_list, list,
    0.into_church()                                   =>     vec_church![].into_pair_list(),
    1.into_church(), 1.into_church()                  =>    vec_church![1].into_pair_list(),
    2.into_church(), 1.into_church(), 2.into_church() => vec_church![1, 2].into_pair_list()
);

test_pair_list_all_lists!(pair_list_append, append,
        vec_church![],     vec_church![] =>           vec_church![],
        vec_church![],    vec_church![1] =>          vec_church![1],
       vec_church![1],     vec_church![] =>          vec_church![1],
       vec_church![1],    vec_church![2] =>       vec_church![1, 2],
    vec_church![1, 2],    vec_church![3] =>    vec_church![1, 2, 3],
       vec_church![1], vec_church![2, 3] =>    vec_church![1, 2, 3],
    vec_church![1, 2], vec_church![3, 4] => vec_church![1, 2, 3, 4]
);

test_pair_list!(pair_list_drop, drop,
    0.into_church(),        vec_church![].into_pair_list() =>  vec_church![].into_pair_list(),
    0.into_church(),       vec_church![1].into_pair_list() => vec_church![1].into_pair_list(),
    1.into_church(),       vec_church![1].into_pair_list() =>  vec_church![].into_pair_list(),
    1.into_church(),    vec_church![1, 2].into_pair_list() => vec_church![2].into_pair_list(),
    2.into_church(), vec_church![1, 2, 3].into_pair_list() => vec_church![3].into_pair_list()
);

test_pair_list!(pair_list_drop_while, drop_while,
    is_zero(),     vec_church![].into_pair_list() =>     vec_church![].into_pair_list(),
    is_zero(),    vec_church![1].into_pair_list() =>    vec_church![1].into_pair_list(),
    is_zero(), vec_church![0, 1].into_pair_list() =>    vec_church![1].into_pair_list(),
    is_zero(), vec_church![1, 0].into_pair_list() => vec_church![1, 0].into_pair_list()
);

test_pair_list!(pair_list_replicate, replicate,
    0.into_church(), 2.into_church() => vec_church![].into_pair_list(),
    1.into_church(), 2.into_church() => vec_church![2].into_pair_list(),
    2.into_church(), 2.into_church() => vec_church![2, 2].into_pair_list(),
    3.into_church(), 2.into_church() => vec_church![2, 2, 2].into_pair_list()
);

/*
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

test_list_hof!(list_take_while, take_while, is_zero,
    empty() => empty(),
    vec![0] => vec![0],
    vec![1] => empty(),
    vec![1, 0] => empty(),
    vec![0, 1] => vec![0],
    vec![0, 0, 1] => vec![0, 0]
);
*/
