# AnabelianAlgorithms

Lean 4 modules for extracted anabelian-algorithm examples and the supporting Mathlib-style API used
by them.  The repository is organized as a standalone Lake package whose public module root is
`AnabelianAlgorithms`.

The project depends on the public GitHub package
[`dagurtomas/AnabelianLib`](https://github.com/dagurtomas/AnabelianLib); Mathlib and the remaining
Lean dependencies are inherited through Lake and pinned by `lake-manifest.json`.  No local sibling
checkout is required.

## Main entry points

- `AnabelianAlgorithms.Examples.NeukirchUchida.Main` — standalone profunctor-form
  Neukirch--Uchida package.
- `AnabelianAlgorithms.Examples.NeukirchUchida.LeanEvalComparison` — comparison/evaluation module
  for the Neukirch--Uchida example.
- `AnabelianAlgorithms.Examples.MochizukiThm.Main` — standalone Hom-form package for proper
  hyperbolic curves over `p`-adic local fields.

Many declarations keep their original `Anabelian` namespaces for compatibility with the source
material, while module names live under `AnabelianAlgorithms`.

## Repository layout

- `AnabelianAlgorithms/Examples/` contains the two example packages.
- `AnabelianAlgorithms/Examples/MochizukiThm/` splits the Mochizuki-style Hom-form construction into
  smaller modules for local fields, curves, augmented profinite groups, pointed étale `π₁`, and
  reconstruction data.
- `AnabelianAlgorithms/Mathlib/` contains project-local Mathlib-style support files.
- `AnabelianAlgorithms/Linter/NonstandardAxioms.lean` defines a linter that reports declarations
  depending on nonstandard axioms.

The theorem-level boundaries in the examples are isolated as axioms.  The nonstandard-axiom linter
is available to make those boundaries visible when desired.

## Building

This project uses the Lean toolchain specified in `lean-toolchain`:

```text
leanprover/lean4:v4.32.0-rc1
```

Typical setup and build commands:

```bash
lake update
lake exe cache get
lake build AnabelianAlgorithms
```

Useful narrower checks:

```bash
lake build AnabelianAlgorithms.Examples.NeukirchUchida.Main
lake build AnabelianAlgorithms.Examples.MochizukiThm.Main
```

The root build currently succeeds, but may print expected nonstandard-axiom warnings in example
boundary modules and existing `linter.style.header` diagnostics from some local Mathlib-style
support files.

## Attribution

Files copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`, retain their
original attribution headers.  This includes the finite-étale/fundamental-group support modules
under `AnabelianAlgorithms/Examples/MochizukiThm/FromPi1` and selected support files under
`AnabelianAlgorithms/Mathlib/RingTheory`.

## License

Released under the Apache 2.0 license; see `LICENSE`.
