#![doc = include_str!("../README.md")]

use {
  ::core::{
    any::{Any, TypeId},
    hash::{BuildHasherDefault, Hasher},
  },
  ::hashbrown::HashMap,
};

/// A collection that can store one value of each distinct type
pub struct TypeMap {
  map: HashMap<TypeId, Box<dyn Any>, IdentityHasher>,
}

impl TypeMap {
  /// Create a new TypeMap collection
  #[inline]
  pub fn new() -> Self {
    TypeMap {
      map: HashMap::with_hasher(BuildHasherDefault::default()),
    }
  }

  /// Inserts a value into the collection
  ///
  /// If the collection did not have a value present of the specified type,
  /// `None` is returned.
  ///
  /// If the collection did have a value present of the specified type, then
  /// the value is updated, and the old value is returned.
  #[inline]
  pub fn insert<T: 'static>(&mut self, v: T) -> Option<T> {
    let id = TypeId::of::<T>();
    let old = self.map.insert(id, Box::new(v))?;
    let old = old.downcast::<T>().ok()?;
    Some(*old)
  }

  /// Removes the value of the specified type from the collection, returning
  /// the value if it existed
  #[inline]
  pub fn remove<T: 'static>(&mut self) -> Option<T> {
    let id = TypeId::of::<T>();
    let val = self.map.remove(&id)?;
    let val = val.downcast::<T>().ok()?;
    Some(*val)
  }

  /// Returns `true` if the collection contains a value of the specified type
  #[inline]
  pub fn exists<T: 'static>(&mut self) -> bool {
    let id = TypeId::of::<T>();
    self.map.contains_key(&id)
  }

  /// Returns a reference to the value of the specified type
  #[inline]
  pub fn get<T: 'static>(&self) -> Option<&T> {
    let id = TypeId::of::<T>();
    let val = self.map.get(&id)?;
    val.downcast_ref::<T>()
  }

  /// Returns a mutable reference to the value of the specified type
  #[inline]
  pub fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
    let id = TypeId::of::<T>();
    let val = self.map.get_mut(&id)?;
    val.downcast_mut::<T>()
  }

  /// Returns multiple references to the values of the specified types
  #[inline]
  pub fn get_many<Ts: 'static + GetMany>(
    &self,
  ) -> Option<<Ts as GetMany>::Ref<'_>> {
    <Ts as GetMany>::get_many(self)
  }

  /// Returns multiple mutable references to the values of the specified types
  #[inline]
  pub fn get_many_mut<Ts: 'static + GetMany>(
    &mut self,
  ) -> Option<<Ts as GetMany>::Mut<'_>> {
    <Ts as GetMany>::get_many_mut(self)
  }
}

use get_many::GetMany;
mod get_many {
  use super::{TypeId, TypeMap};

  pub trait GetMany {
    type Ref<'s>;
    type Mut<'s>;

    fn get_many(map: &TypeMap) -> Option<Self::Ref<'_>>;
    fn get_many_mut(map: &mut TypeMap) -> Option<Self::Mut<'_>>;
  }

  macro_rules! impl_get_many {
    ($($T:ident),*) => {
      impl<$($T: 'static),*> GetMany for ($($T,)*) {
        type Ref<'s> = ($(&'s $T),*,);
        type Mut<'s> = ($(&'s mut $T),*,);

        #[allow(non_snake_case)]
        #[inline]
        fn get_many(type_map: &TypeMap) -> Option<Self::Ref<'_>> {
          let [$($T),*] = [$(&TypeId::of::<$T>()),*];
          let [$($T),*] = [$(type_map.map.get($T)?),*,];
          Some(($($T.downcast_ref()?),*,))
        }

        #[allow(non_snake_case)]
        #[inline]
        fn get_many_mut(type_map: &mut TypeMap) -> Option<Self::Mut<'_>> {
          let ids = [$(&TypeId::of::<$T>()),*];
          let [$($T),*] = type_map.map.get_many_mut(ids)?;
          Some(($($T.downcast_mut()?),*,))
        }
      }
    };
  }

  impl_get_many!(A);
  impl_get_many!(A, B);
  impl_get_many!(A, B, C);
  impl_get_many!(A, B, C, D);
  impl_get_many!(A, B, C, D, E);
  impl_get_many!(A, B, C, D, E, F);
  impl_get_many!(A, B, C, D, E, F, G);
  impl_get_many!(A, B, C, D, E, F, G, H);
}

/// Since we are using [`TypeId`]s as keys, and since [`TypeId`] is already a
/// high quality hash, we'd like to avoid unnecessarily re-hashing it.
///
/// We define a [`Hasher`] that just copies the bytes that are written into the
/// output. Since the impl of [`Hash`] for [`TypeId`] is just
/// `(self.t as u64).hash(state)` this ought to resolve to a no-op.
///
/// An alternative approach would be to use [`::hashbrown::HashTable`]'s API,
/// however that is a lot more work.
type IdentityHasher = BuildHasherDefault<Identity>;

#[derive(Default)]
struct Identity(u64);

impl Hasher for Identity {
  #[inline]
  fn finish(&self) -> u64 {
    self.0
  }
  #[inline]
  fn write_u64(&mut self, i: u64) {
    self.0 = i;
  }
  #[inline]
  fn write(&mut self, bytes: &[u8]) {
    // write the last 8 bytes into the state, or fewer bytes if there are fewer
    let mut b = self.0.to_ne_bytes();

    let len = bytes.len();
    let span = &mut b[(8 - len).min(0)..];
    span.copy_from_slice(&bytes[(len - 8).min(0)..]);

    self.0 = u64::from_ne_bytes(b);
  }
}

#[cfg(any(test, doctest))]
pub mod tests {
  use super::*;

  #[derive(PartialEq, Eq, Debug)]
  struct Thing {
    s: String,
  }

  #[test]
  fn get_nonexistent_value() {
    let map = TypeMap::new();

    assert!(
      map.get::<Thing>().is_none(),
      "No value should exist for type"
    );
  }

  #[test]
  fn insert_and_get() {
    let mut map = TypeMap::new();

    map.insert(Thing {
      s: "hello, TypeMap!".to_owned(),
    });

    assert_eq!(
      map.get::<Thing>(),
      Some(&Thing {
        s: "hello, TypeMap!".to_owned()
      }),
      "The value for the type should match"
    );
  }

  #[test]
  fn mutate_val() {
    let mut map = TypeMap::new();

    map.insert(Thing {
      s: "hello, TypeMap!".to_owned(),
    });

    {
      let thing = map.get_mut::<Thing>().expect("value not found in map");
      thing.s = thing.s.replace("hello", "goodbye");
    }

    assert_eq!(
      map.get::<Thing>(),
      Some(&Thing {
        s: "goodbye, TypeMap!".to_owned()
      }),
      "The value for the type should match the updated value"
    );
  }

  #[test]
  fn get_many() {
    let mut map = TypeMap::new();
    {
      map.insert(1u8);
      map.insert(2u16);
      map.insert(3u32);
    }

    let (c, b, a) = map
      .get_many::<(u32, u16, u8)>()
      .expect("Failed to get_many");

    assert_eq!(
      (a, b, c),
      (&1, &2, &3),
      "The value for the type should match the updated value"
    );
  }

  #[test]
  fn get_many_mut() {
    let mut map = TypeMap::new();

    map.insert(1u8);
    map.insert(2u16);
    map.insert(3u32);

    {
      let (c, b, a) = map
        .get_many_mut::<(u32, u16, u8)>()
        .expect("Failed to get_many_mut");
      *a = (*a) * 10 + 1;
      *b = (*b) * 100 + 2;
      *c = (*c) * 1000 + 3;
    }

    let (Some(c), Some(b), Some(a)) =
      (map.get::<u32>(), map.get::<u16>(), map.get::<u8>())
    else {
      panic!("Failed to get")
    };

    assert_eq!(
      (a, b, c),
      (&11, &202, &3003),
      "The value for the type should match the updated value"
    );
  }
}
