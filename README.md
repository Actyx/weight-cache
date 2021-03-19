# weight-cache

A cache that holds a limited number of key-value pairs. When the capacity of
the cache is exceeded, the least-recently-used (where "used" means a look-up
or putting the pair into the cache) pair is automatically removed.

Contrary to the lru-cache crate[0] (which this crate is heavily inspired
by!), the capacity is not the number of items in the cache, but can be given
by an arbitrary criterion by implementing [`Weigheable`] for the value type
V. A straight-forward example of this would be to use the allocated size of
the object, and provide a total capacity which must not be exceeded by the
cache.
[0]:https://crates.io/crates/lru-cache

## Examples
```rust
use weight_cache::{Weigheable, WeightCache};
use std::num::NonZeroUsize;

#[derive(PartialEq, Debug)]
enum Food {
    Milk { milliliters: usize },
    Cucumber { pieces: usize },
    Meat { grams: usize },
    Potato { pieces: usize },
    Crab { grams: usize },
}

impl Weigheable<Food> for Food {
    fn measure(value: &Food) -> usize {
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
assert_eq!(*cache.get_mut(&1).unwrap(), Food::Milk { milliliters: 100 });

cache.put(2, Food::Crab { grams: 300 }).unwrap();
assert_eq!(*cache.get_mut(&2).unwrap(), Food::Crab { grams: 300 });
assert_eq!(*cache.get_mut(&1).unwrap(), Food::Milk { milliliters: 100 });

cache.put(3, Food::Potato { pieces: 2 }).unwrap();
assert_eq!(*cache.get_mut(&3).unwrap(), Food::Potato { pieces: 2});
assert!(cache.get_mut(&2).is_none()); // 1 has been touched last
assert_eq!(*cache.get_mut(&1).unwrap(), Food::Milk { milliliters: 100 });
```

License: MIT OR Apache-2.0
