# weight-cache

A cache that holds a limited number of key-value pairs. When the capacity of
the cache is exceeded, the least-recently-used (where "used" means a look-up
or putting the pair into the cache) pair is automatically removed.

Contrary to the [lru-cache](https://crates.io/crates/lru-cache) crate (which
this crate is heavily inspired by!), the capacity is not the number of items
in the cache, but can be given by an arbitrary criterion by implementing
[`Weighable`] for the value type V. A straight-forward example of this would
be to use the allocated size of the object, and provide a total capacity
which must not be exceeded by the cache.

## Examples
```rust
use weight_cache::{Weighable, WeightCache};
use std::num::NonZeroUsize;

#[derive(PartialEq, Debug)]
enum Food {
    Milk { milliliters: usize },
    Cucumber { pieces: usize },
    Meat { grams: usize },
    Potato { pieces: usize },
    Crab { grams: usize },
}

impl Weighable for Food {
    fn measure(value: &Self) -> usize {
        match value {
            Food::Milk { milliliters } => milliliters * 104 / 100,
            Food::Cucumber { pieces } => pieces * 158,
            Food::Meat { grams } => *grams,
            Food::Potato { pieces } => pieces * 175,
            Food::Crab { grams } => *grams,
        }
    }
}

let mut cache = WeightCache::new(NonZeroUsize::new(500).unwrap());

// Can't put too much in!
assert!(cache.put(0, Food::Meat { grams: 600 }).is_err());
assert!(cache.is_empty());

cache.put(1, Food::Milk { milliliters: 100 }).unwrap();
assert!(!cache.is_empty());
assert_eq!(*cache.get(&1).unwrap(), Food::Milk { milliliters: 100 });

cache.put(2, Food::Crab { grams: 300 }).unwrap();
assert_eq!(*cache.get(&2).unwrap(), Food::Crab { grams: 300 });
assert_eq!(*cache.get(&1).unwrap(), Food::Milk { milliliters: 100 });

cache.put(3, Food::Potato { pieces: 2 }).unwrap();
assert_eq!(*cache.get(&3).unwrap(), Food::Potato { pieces: 2});
assert!(cache.get(&2).is_none()); // 1 has been touched last
assert_eq!(*cache.get(&1).unwrap(), Food::Milk { milliliters: 100 });
```

## Feature flags

* `metrics`: Enables metric gathering on the cache. Register a
[`prometheus::Registry`] with a call to [`WeightCache::register`]; set a
custom metric namespace with [`WeightCache::new_with_namespace`]

License: MIT OR Apache-2.0
