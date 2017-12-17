#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::list::*;
//use lambda::data::numerals::church::{add, is_zero};

macro_rules! test_list {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(beta(app!($function(), $($n.into_church()),*), HAP, 0), $result.into_church());)*
            $(assert_eq!(beta(app!($function(), $($n.into_scott()),*), HAP, 0), $result.into_scott());)*
            $(assert_eq!(beta(app!($function(), $($n.into_parigot()),*), HAP, 0), $result.into_parigot());)*
            $(assert_eq!(beta(app!($function(), $($n.into_stumpfu()),*), HAP, 0), $result.into_stumpfu());)*
        }
    );
}

test_list!(list_last, last,
    // TODO: test empty list?
    vec![1] => 1,
    vec![1, 2, 3] => 3
);

test_list!(list_init, init,
    // TODO: test singleton list?
    vec![1, 2] => vec![1],
    vec![1, 2, 3] => vec![1, 2]
);

test_list!(list_zip, zip,
    // TODO: test empty list
    vec![1], vec![1] => vec![(1, 1)],
    vec![1, 2], vec![1] => vec![(1, 1)],
    vec![1], vec![1, 2] => vec![(1, 1)],
    vec![1, 2], vec![3, 4] => vec![(1, 3), (2, 4)]
);
/* TODO: figure out passing multiple functions (inconsistent lockstep iteration)
test_list!(list_zip, zip_with, add,
    // TODO: test empty list
    vec![1], vec![1] => vec![2],
    vec![1, 2], vec![1] => vec![2],
    vec![1], vec![1, 2] => vec![2],
    vec![1, 2], vec![3, 4] => vec![4, 6]
);
#[test]
fn list_take_while() {
    let l1 = || { vec![0, 0, 2, 3].into_scott() };
    let l2 = || { vec![0, 0].into_scott() };
    let l3 = || { vec![1, 4, 2, 3].into_scott() };
    let l4 = || { vec![0, 4, 0, 0].into_scott() };
    let l5 = || { vec![0].into_scott() };

    assert_eq!(beta(app!(take_while(), is_zero(), nil()), HAP, 0), nil());
    assert_eq!(beta(app!(take_while(), is_zero(), l1()), HAP, 0), l2());
    assert_eq!(beta(app!(take_while(), is_zero(), l2()), HAP, 0), l2());
    assert_eq!(beta(app!(take_while(), is_zero(), l3()), HAP, 0), nil());
    assert_eq!(beta(app!(take_while(), is_zero(), l4()), HAP, 0), l5());
}
*/
