This package implements parsing and name resolution for the Starlark language.
Starlark is a dialect of Python intended for use as a configuration language.
Its main use is for extending the [Bazel](https://bazel.build/) build system.

This partial implementation is a port of
[starlark-go](https://github.com/google/starlark-go) to Rust.

The main use of this package is for extracting information from BUILD files.
There is a basic interpreter, but it is more than unlikely to evolve into
a full implementation.

If you want a complete implementation, you may want to reach for
[starlark-go](https://github.com/google/starlark-go) or
try [starlark-rust](https://github.com/facebook/starlark-rust) instead.

## Development

### Testing

To run the standard test suite:

```bash
cargo test
```

#### Buildifier Parity Tests

This project includes integration tests that verify the pretty-printed output against `buildifier`, the standard formatter for Starlark. These tests ensure that `strangemeadowlark` produces output that is consistent with the canonical style.

To run these tests specifically:

```bash
cargo test --test buildifier_parity_test
```

**Note:** These tests require the `buildifier` binary to be installed and available in your system's `PATH`. If `buildifier` is not found, the tests will be skipped automatically (marked as passed with a message).

### Test with Leak Sanitizer

This library uses `bumpalo` and an AST that is using references. This has the
advantage of enabling pattern matching on ASTs. However as the [docs](https://docs.rs/bumpalo/latest/bumpalo/struct.Bump.html) say,
bumpalo will not call `Drop`, and this makes it very easy to leak memory.

When making changes, run the following to detect leaks:

```
RUSTFLAGS="-Z sanitizer=leak -Zexport-executable-symbols" cargo test --target x86_64-unknown-linux-gnu
```

The `-Zexport-executable-symbols` is a [workaround](
https://github.com/rust-lang/rust/issues/111073#issuecomment-2104652448).

The stacktraces will not be useful, unless they are symbolized. For that, you
want `llvm-symbolizer` in your path.
