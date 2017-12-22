#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::list::{church, scott, parigot};

macro_rules! test_list {
    ($name:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(
                assert_eq!(
                    beta(app!(church::$function(), $($n.into_church()),*), HAP, 0),
                    $result.into_church()
                );
                assert_eq!(
                    beta(app!(scott::$function(), $($n.into_scott()),*), HAP, 0),
                    $result.into_scott()
                );
                assert_eq!(
                    beta(app!(parigot::$function(), $($n.into_parigot()),*), HAP, 0),
                    $result.into_parigot()
                );
            )*
        }
    );
}

fn nil() -> Vec<Term> { vec![] } // a nil workaround for macro purposes

test_list!(list_head, head,
          vec![1] => 1,
       vec![1, 2] => 1,
    vec![1, 2, 3] => 1
);

test_list!(list_tail, tail,
             vec![1] =>         nil(),
          vec![1, 2] =>       vec![2],
       vec![1, 2, 3] =>    vec![2, 3],
    vec![1, 2, 3, 4] => vec![2, 3, 4]
);
