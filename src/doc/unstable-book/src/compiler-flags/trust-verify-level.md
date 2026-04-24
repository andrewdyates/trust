# `trust-verify-level`

The tracking issue for this feature is internal to tRust.

------------------------

Controls the proof depth used by tRust's native MIR verification transport.

For public verifier usage, prefer `cargo trust check` and
`cargo trust check --format json`. Those commands are the supported front door;
this flag is the lower-level knob they pass through when a discoverable native
tRust compiler exposes `-Z trust-verify`.

```text
rustc -Z trust-verify -Z trust-verify-level=0 your_file.rs
```

The currently supported levels are:

- `0`: safety obligations. This is the strongest public story today.
- `1`: contract and functional obligations. Present, but still settling.
- `2`: deeper or domain-specific obligations. Experimental.

Higher-level docs often refer to these as `L0`, `L1`, and `L2`; `cargo-trust`
maps those names to `0`, `1`, and `2` for the native compiler path.

Native/stage1 availability for this path is still tracked work rather than a
universally shipped guarantee, so do not treat direct `rustc -Z ...` use as the
normal first-run workflow.

This flag only has effect when `-Z trust-verify` is also enabled.
