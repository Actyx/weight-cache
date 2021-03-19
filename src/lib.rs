//! A cache that holds a limited number of key-value pairs. When the capacity of
//! the cache is exceeded, the least-recently-used (where "used" means a look-up
//! or putting the pair into the cache) pair is automatically removed.
//!
//! Contrary to the lru-cache crate[0] (which this crate is heavily inspired
//! by!), the capacity is not the number of items in the cache, but can be given
//! by an arbitrary criterion by implementing [`Weigheable`] for the value type
//! V. A straight-forward example of this would be to use the allocated size of
//! the object, and provide a total capacity which must not be exceeded by the
//! cache.
//! [0]: https://crates.io/crates/lru-cache
//!
//! # Examples
//!```
//! use weight_cache::{Weigheable, WeightCache};
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
//! impl Weigheable<Food> for Food {
//!     fn measure(value: &Food) -> usize {
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
//! assert_eq!(*cache.get_mut(&1).unwrap(), Food::Milk { milliliters: 100 });
//!
//! cache.put(2, Food::Crab { grams: 300 }).unwrap();
//! assert_eq!(*cache.get_mut(&2).unwrap(), Food::Crab { grams: 300 });
//! assert_eq!(*cache.get_mut(&1).unwrap(), Food::Milk { milliliters: 100 });
//!
//! cache.put(3, Food::Potato { pieces: 2 }).unwrap();
//! assert_eq!(*cache.get_mut(&3).unwrap(), Food::Potato { pieces: 2});
//! assert!(cache.get_mut(&2).is_none()); // 1 has been touched last
//! assert_eq!(*cache.get_mut(&1).unwrap(), Food::Milk { milliliters: 100 });
//!```

use hash_map::RandomState;
use linked_hash_map::LinkedHashMap;
use std::{
    collections::hash_map,
    fmt,
    hash::{BuildHasher, Hash},
    num::NonZeroUsize,
};

pub trait Weigheable<V> {
    fn measure(value: &V) -> usize;
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

pub struct WeightCache<K, V, S = hash_map::RandomState> {
    max: usize,
    current: usize,
    inner: LinkedHashMap<K, V, S>,
}
impl<K, V, S> fmt::Debug for WeightCache<K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WeightCache")
            .field("max", &self.max)
            .field("current", &self.current)
            .finish()
    }
}

impl<K: Hash + Eq, V: Weigheable<V>> Default for WeightCache<K, V> {
    fn default() -> Self {
        WeightCache::<K, V, RandomState>::new(NonZeroUsize::new(usize::MAX).expect("MAX > 0"))
    }
}

impl<K: Hash + Eq, V: Weigheable<V>> WeightCache<K, V> {
    pub fn new(capacity: NonZeroUsize) -> Self {
        Self {
            max: capacity.get(),
            current: 0,
            inner: LinkedHashMap::new(),
        }
    }
}
impl<K: Hash + Eq, V: Weigheable<V>, S: BuildHasher> WeightCache<K, V, S> {
    /// Create a [`WeightCache`] with a custom hasher.
    pub fn with_hasher(capacity: NonZeroUsize, hasher: S) -> Self {
        Self {
            max: capacity.get(),
            current: 0,
            inner: LinkedHashMap::with_hasher(hasher),
        }
    }

    /// Returns a reference to the value corresponding to the given key, if it
    /// exists.
    pub fn get(&mut self, k: &K) -> Option<&V> {
        self.inner.get_refresh(k).map(|v| v as &V)
    }

    /// Returns a mutable reference to the value corresponding to the given key,
    /// if it exists.
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        self.inner.get_refresh(k)
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
    /// too bigger than the cache's configured max size.
    pub fn put(&mut self, key: K, value: V) -> Result<(), ValueTooBigError> {
        let weight = V::measure(&value);
        if weight > self.max {
            return Err(ValueTooBigError);
        } else {
            self.current += weight;
            // did we remove an element?
            if let Some(x) = self.inner.insert(key, value) {
                self.current -= V::measure(&x);
            }

            while self.current > self.max && !self.inner.is_empty() {
                if let Some((_, v)) = self.inner.pop_front() {
                    self.current -= V::measure(&v);
                }
            }

            // remove elements until we're below the size boundary again
            self.shrink_to_fit();
            Ok(())
        }
    }

    /// Returns an iterator over the cache's key-value pairs in least- to
    /// most-recently-used order.
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.inner.iter())
    }

    /// Returns a mutable iterator over the cache's key-value pairs in least- to
    /// most-recently-used order.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut(self.inner.iter_mut())
    }
    fn shrink_to_fit(&mut self) {
        while self.current > self.max && !self.inner.is_empty() {
            let (_, v) = self.inner.pop_front().expect("Not empty");
            self.current -= V::measure(&v);
        }
    }
}
impl<K: Hash + Eq, V, S: BuildHasher + Default> IntoIterator for WeightCache<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.inner.into_iter())
    }
}
/// An iterator over a cache's key-value pairs in least- to most-recently-used
/// order.
#[derive(Clone)]
pub struct IntoIter<K, V>(linked_hash_map::IntoIter<K, V>);

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<(K, V)> {
        self.0.next_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
/// An iterator over a cache's key-value pairs in least- to most-recently-used
/// order.
///
/// Accessing a cache through the iterator does _not_ affect the cache's LRU state.
pub struct Iter<'a, K: 'a, V: 'a>(linked_hash_map::Iter<'a, K, V>);

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        Iter(self.0.clone())
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        self.0.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
/// An iterator over a cache's key-value pairs in least- to most-recently-used
/// order with mutable references to the values.
///
/// Accessing a cache through the iterator does _not_ affect the cache's LRU state.
pub struct IterMut<'a, K: 'a, V: 'a>(linked_hash_map::IterMut<'a, K, V>);

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.0.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.0.len()
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
    impl Weigheable<HeavyWeight> for HeavyWeight {
        fn measure(v: &HeavyWeight) -> usize {
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
    impl Weigheable<UnitWeight> for UnitWeight {
        fn measure(_: &UnitWeight) -> usize {
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
        let cached = cache.into_iter().map(|x| x.1).collect::<Vec<_>>();

        assert_eq!(xs, cached);
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
