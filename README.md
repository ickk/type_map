`type_map`
==========

A collection that can store one value of each distinct type.

```rust
# use ::type_map::TypeMap;
let mut map = TypeMap::new();
map.insert(5u8);
assert_eq!(map.get::<u8>(), Some(&5));
```

Supports usual map operations like`insert`, `remove`, `get`, `get_mut`,
`get_many`, `get_many_mut`.

```rust
# use ::type_map::TypeMap;
let mut map = TypeMap::new();
map.insert(2u16);
map.insert(3u32);
{
  let (b, c) = map.get_many_mut::<(u16, u32)>().unwrap();
  *b = (*b) * 100 + 2;
  *c = (*c) * 1000 + 3;
}
assert_eq!(map.get::<u32>(), Some(&3003));
assert_eq!(map.get::<u16>(), Some(&202));
```


License
-------

This crate is licensed under any of the
[Apache license, Version 2.0](./LICENSE-APACHE),
or the
[MIT license](./LICENSE-MIT),
or the
[Zlib license](./LICENSE-ZLIB)
at your option.

Unless explicitly stated otherwise, any contributions you intentionally submit
for inclusion in this work shall be licensed accordingly.
