//! A cache that holds a limited number of key-value pairs. When the capacity of
//! the cache is exceeded, the least-recently-used (where "used" means a look-up
//! or putting the pair into the cache) pair is automatically removed.
//!
//! Contrary to the [lru-cache](https://crates.io/crates/lru-cache) crate (which
//! this crate is heavily inspired by!), the capacity is not the number of items
//! in the cache, but can be given by an arbitrary criterion by implementing
//! [`Weighable`] for the value type V. A straight-forward example of this would
//! be to use the allocated size of the object, and provide a total capacity
//! which must not be exceeded by the cache.
//!
//! # Examples
//!```
//! use weight_cache::{Weighable, WeightCache};
//! use std::num::NonZeroUsize;
//!
//! #[derive(PartialEq, Debug)]
//! enum Food {
//!     Milk { milliliters: usize },
//!     Cucumber { pieces: usize },
//!     Meat { grams: usize },
//!     Potato { pieces: usize },
//!     Crab { grams: usize },
//! }
//!
//! impl Weighable for Food {
//!     fn measure(value: &Self) -> usize {
//!         match value {
//!             Food::Milk { milliliters } => milliliters * 104 / 100,
//!             Food::Cucumber { pieces } => pieces * 158,
//!             Food::Meat { grams } => *grams,
//!             Food::Potato { pieces } => pieces * 175,
//!             Food::Crab { grams } => *grams,
//!         }
//!     }
//! }
//!
//! let mut cache = WeightCache::new(NonZeroUsize::new(500).unwrap());
//!
//! // Can't put too much in!
//! assert!(cache.put(0, Food::Meat { grams: 600 }).is_err());
//! assert!(cache.is_empty());
//!
//! cache.put(1, Food::Milk { milliliters: 100 }).unwrap();
//! assert!(!cache.is_empty());
//! assert_eq!(*cache.get(&1).unwrap(), Food::Milk { milliliters: 100 });
//!
//! cache.put(2, Food::Crab { grams: 300 }).unwrap();
//! assert_eq!(*cache.get(&2).unwrap(), Food::Crab { grams: 300 });
//! assert_eq!(*cache.get(&1).unwrap(), Food::Milk { milliliters: 100 });
//!
//! cache.put(3, Food::Potato { pieces: 2 }).unwrap();
//! assert_eq!(*cache.get(&3).unwrap(), Food::Potato { pieces: 2});
//! assert!(cache.get(&2).is_none()); // 1 has been touched last
//! assert_eq!(*cache.get(&1).unwrap(), Food::Milk { milliliters: 100 });
//!```
//!
//! # Feature flags
//!
//! * `metrics`: Enables metric gathering on the cache. Register a
//!              [`prometheus::Registry`] with a call to [`WeightCache::register`]

use hash_map::RandomState;
use linked_hash_map::LinkedHashMap;
#[cfg(feature = "metrics")]
use prometheus::{
    core::{AtomicU64, GenericCounter, GenericGauge},
    Registry,
};
use std::{
    collections::hash_map,
    fmt,
    hash::{BuildHasher, Hash},
    num::NonZeroUsize,
};

/// A trait to implemented for the value type, providing a way to
/// [`Weighable::measure`] the thing.
pub trait Weighable {
    fn measure(value: &Self) -> usize;
}

#[derive(Debug)]
/// An error indicating that the to-be-inserted value is bigger than the max size
/// of the cache.
pub struct ValueTooBigError;
impl std::error::Error for ValueTooBigError {}
impl fmt::Display for ValueTooBigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Value is bigger than the configured max size of the cache"
        )
    }
}

struct ValueWithWeight<V> {
    value: V,
    weight: usize,
}
/// A cache that holds a limited number of key-value pairs. When the capacity of
/// the cache is exceeded, the least-recently-used (where "used" means a look-up
/// or putting the pair into the cache) pairs are automatically removed until the
/// size limit is met again.
pub struct WeightCache<K, V, S = hash_map::RandomState> {
    max: usize,
    current: usize,
    inner: LinkedHashMap<K, ValueWithWeight<V>, S>,
    #[cfg(feature = "metrics")]
    metrics: Metrics,
}
impl<K, V, S> fmt::Debug for WeightCache<K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WeightCache")
            .field("max", &self.max)
            .field("current", &self.current)
            .finish()
    }
}

impl<K: Hash + Eq, V: Weighable> Default for WeightCache<K, V> {
    fn default() -> Self {
        WeightCache::<K, V, RandomState>::new(NonZeroUsize::new(usize::MAX).expect("MAX > 0"))
    }
}

#[cfg(feature = "metrics")]
struct Metrics {
    hits: GenericCounter<AtomicU64>,
    misses: GenericCounter<AtomicU64>,
    inserts: GenericCounter<AtomicU64>,
    inserts_fail: GenericCounter<AtomicU64>,
    size: GenericGauge<AtomicU64>,
}
#[cfg(feature = "metrics")]
impl Default for Metrics {
    fn default() -> Self {
        let cache_size = GenericGauge::new("cache_size", "Current size of the cache").unwrap();
        cache_size.set(0);
        Self {
            hits: GenericCounter::new("cache_hit", "Number of cache hits").unwrap(),
            misses: GenericCounter::new("cache_miss", "Number of cache misses").unwrap(),
            inserts: GenericCounter::new("cache_insert", "Number of successful cache insertions")
                .unwrap(),
            inserts_fail: GenericCounter::new(
                "cache_insert_fail",
                "Number of failed cache insertions",
            )
            .unwrap(),
            size: cache_size,
        }
    }
}

impl<K: Hash + Eq, V: Weighable> WeightCache<K, V> {
    pub fn new(capacity: NonZeroUsize) -> Self {
        Self {
            max: capacity.get(),
            current: 0,
            inner: LinkedHashMap::new(),
            #[cfg(feature = "metrics")]
            metrics: Metrics::default(),
        }
    }
}
impl<K: Hash + Eq, V: Weighable, S: BuildHasher> WeightCache<K, V, S> {
    /// Create a [`WeightCache`] with a custom hasher.
    pub fn with_hasher(capacity: NonZeroUsize, hasher: S) -> Self {
        Self {
            max: capacity.get(),
            current: 0,
            inner: LinkedHashMap::with_hasher(hasher),
            #[cfg(feature = "metrics")]
            metrics: Metrics::default(),
        }
    }
    #[cfg(feature = "metrics")]
    /// Registers metrics with a [`prometheus::Registry`]
    pub fn register(&self, registry: &Registry) -> Result<(), prometheus::Error> {
        registry.register(Box::new(self.metrics.hits.clone()))?;
        registry.register(Box::new(self.metrics.misses.clone()))?;
        registry.register(Box::new(self.metrics.inserts.clone()))?;
        registry.register(Box::new(self.metrics.inserts_fail.clone()))?;
        registry.register(Box::new(self.metrics.size.clone()))?;
        Ok(())
    }

    /// Returns a reference to the value corresponding to the given key, if it
    /// exists.
    pub fn get(&mut self, k: &K) -> Option<&V> {
        if let Some(v) = self.inner.get_refresh(k) {
            #[cfg(feature = "metrics")]
            self.metrics.hits.inc();
            Some(&v.value as &V)
        } else {
            #[cfg(feature = "metrics")]
            self.metrics.misses.inc();
            None
        }
    }

    /// Returns the number of key-value pairs in the cache.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the cache contains no key-value pairs.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Inserts a key-value pair into the cache. Returns an error if the value is
    /// bigger than the cache's configured max size.
    pub fn put(&mut self, key: K, value: V) -> Result<(), ValueTooBigError> {
        let weight = V::measure(&value);
        if weight > self.max {
            #[cfg(feature = "metrics")]
            self.metrics.inserts_fail.inc();
            Err(ValueTooBigError)
        } else {
            self.current += weight;
            // did we remove an element?
            if let Some(x) = self.inner.insert(key, ValueWithWeight { value, weight }) {
                self.current -= x.weight;
            }

            // remove elements until we're below the size boundary again
            self.shrink_to_fit();
            #[cfg(feature = "metrics")]
            self.metrics.inserts.inc();
            Ok(())
        }
    }

    fn shrink_to_fit(&mut self) {
        while self.current > self.max && !self.inner.is_empty() {
            let (_, v) = self.inner.pop_front().expect("Not empty");
            self.current -= v.weight;
        }
        #[cfg(feature = "metrics")]
        self.metrics.size.set(self.current as u64);
    }
}

impl<K: Hash + Eq + 'static, V: Weighable + 'static, S: BuildHasher> WeightCache<K, V, S> {
    /// Returns an iterator over the cache's key-value pairs in least- to
    /// most-recently-used order consuming the cache.
    pub fn consume(self) -> Box<dyn Iterator<Item = (K, V)> + 'static> {
        #[cfg(feature = "metrics")]
        self.metrics.size.set(0);
        Box::new(self.inner.into_iter().map(|(k, v)| (k, v.value)))
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use super::*;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    #[derive(Clone, Debug, PartialEq)]
    struct HeavyWeight(usize);
    impl Weighable for HeavyWeight {
        fn measure(v: &Self) -> usize {
            v.0
        }
    }
    impl Arbitrary for HeavyWeight {
        fn arbitrary(g: &mut Gen) -> Self {
            Self(usize::arbitrary(g))
        }
        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            Box::new(usize::shrink(&self.0).map(HeavyWeight))
        }
    }
    #[derive(Clone, Debug, PartialEq)]
    struct UnitWeight;
    impl Weighable for UnitWeight {
        fn measure(_: &Self) -> usize {
            1
        }
    }
    impl Arbitrary for UnitWeight {
        fn arbitrary(_: &mut Gen) -> Self {
            Self
        }
    }

    #[test]
    fn should_not_evict_under_max_size() {
        let xs: Vec<_> = (0..10000).map(HeavyWeight).collect();
        let mut cache = WeightCache::<usize, HeavyWeight>::new(usize::MAX.try_into().unwrap());
        for (k, v) in xs.iter().enumerate() {
            cache.put(k, v.clone()).expect("empty")
        }
        let cached = cache.consume().map(|x| x.1).collect::<Vec<_>>();

        assert_eq!(xs, cached);
    }

    #[cfg(feature = "metrics")]
    #[test]
    fn should_gather_metrics() {
        let mut cache = WeightCache::<usize, UnitWeight>::new(3.try_into().unwrap());
        let registry = Registry::new();
        cache.register(&registry).unwrap();
        for i in 0usize..5 {
            cache.put(i, UnitWeight).unwrap();
        }
        for i in 0usize..5 {
            cache.get(&i);
        }
        for metric in registry.gather() {
            println!("{} {:?}", metric.get_name(), metric.get_metric()[0]);
            match metric.get_name() {
                "cache_size" => {
                    assert_eq!(3, metric.get_metric()[0].get_gauge().get_value() as usize)
                }
                "cache_insert" => {
                    assert_eq!(5, metric.get_metric()[0].get_counter().get_value() as usize)
                }
                "cache_insert_fail" => {
                    assert_eq!(0, metric.get_metric()[0].get_counter().get_value() as usize)
                }
                "cache_hit" => {
                    assert_eq!(3, metric.get_metric()[0].get_counter().get_value() as usize)
                }
                "cache_miss" => {
                    assert_eq!(2, metric.get_metric()[0].get_counter().get_value() as usize)
                }
                x => panic!("unknown metrics {}", x),
            }
        }
    }

    #[quickcheck]
    fn should_reject_too_heavy_values(total_size: NonZeroUsize, input: HeavyWeight) -> bool {
        let mut cache = WeightCache::<usize, HeavyWeight>::new(total_size);
        let res = cache.put(42, input.clone());
        match res {
            Ok(_) if input.0 < total_size.get() => true,
            Err(_) if input.0 >= total_size.get() => true,
            _ => false,
        }
    }

    #[quickcheck]
    fn should_evict_once_the_size_target_is_hit(
        input: Vec<UnitWeight>,
        max_size: NonZeroUsize,
    ) -> bool {
        let mut cache_size = 0usize;
        let mut cache = WeightCache::<usize, UnitWeight>::new(max_size);
        for (k, v) in input.into_iter().enumerate() {
            let weight = UnitWeight::measure(&v);
            cache_size += weight;
            let len_before = cache.len();
            cache.put(k, v).unwrap();
            let len_after = cache.len();
            if cache_size > max_size.get() {
                assert_eq!(len_before, len_after);
                cache_size -= weight;
            } else {
                assert_eq!(len_before + 1, len_after);
            }
        }

        true
    }
}
