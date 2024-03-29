# `car`

macro based array manipulation constant techniques

## you wanted a quick LUT in const? here you go!

```rust
// please note that this is in no way performant or a good idea.
let squares: [usize; 0xffffffff] = car::from_fn!(|i| i * 2);
```

## completely stable!

for once!