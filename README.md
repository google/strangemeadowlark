This is a parser for the Starlark language, a dialect of Python 
intended for use as a configuration language (for example, to
configure builds in bazel).

This implementation is a port of
[starlark-go](https://github.com/google/starlark-go) to Rust.

## Development

### Test with Leak Sanitizer

This library uses `bumpalo` and an AST that is using references. This has the
advantage of enabling pattern matching on ASTs. However as the [docs](https://docs.rs/bumpalo/latest/bumpalo/struct.Bump.html) bumpalo will not call `Drop` and that makes
it very easy to leak memory.

```
RUSTFLAGS="-Z sanitizer=leak -Zexport-executable-symbols" cargo test --target x86_64-unknown-linux-gnu
```

The `-Zexport-executable-symbols` is a [workaround](
https://github.com/rust-lang/rust/issues/111073#issuecomment-2104652448).

The stacktraces will not be useful, unless they are symbolized. For that, you
want `llvm-symbolizer` in your path.