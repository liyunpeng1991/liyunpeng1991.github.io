# Reproducible Lean proof of the all-radii theorem

The exact final declaration is [`MaximumModulus.bounded_maxPoints_at_arbitrarily_large_radii`](MaximumModulus/AllRadii.lean#L26). For every nonzero entire `f : ℂ → ℂ` which is not `c * z^m` with `c ≠ 0` and `m : ℕ`, it proves:

```lean
∃ B : ℕ, ∀ R : ℝ, 0 < R → ∃ r : ℝ, R < r ∧
  ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).Finite ∧
  ({z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}).ncard ≤ B
```

The bound is chosen before every threshold. Actual maximum-point finiteness is an explicit conclusion. `all_radii_growth_impossible` proves the negative implication, and `finite_maxPoints` proves finiteness on every positive circle.

The proof uses exact finite inverse-root families, distinct-pair counts, and continuation of the closure of the regular high-count targets through finite values, the omitted value, and infinity. It uses the compact sphere and nonconstant product coordinates to force the high-count set to be empty. A countable exceptional set and the maximum envelope then supply good radii. The optional stronger exceptional-radius and sharpness assertions are outside this delivery.

## Exact dependencies

- Lean toolchain: `leanprover/lean4:v4.35.0-rc4`.
- Lean commit: `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`.
- mathlib: `81d17696471311f5e3e2f034236df7a781449f7e`.
- Every transitive package revision is locked in `lake-manifest.json`.

## Build and check

Install the exact toolchain specified by `lean-toolchain`, and run these commands from this `lean/` directory:

```sh
python3 scripts/fetch_cache.py
lake build
lake env lean CheckAxioms.lean
```

For the complete project verification, including direct source checks, sequential project kernel replays, transitive axiom inspections, and provenance checks:

```sh
sh scripts/verify.sh
```

The unchanged earlier manuscript must be at `../maximum_modulus_points.tex`, as supplied by this directory layout. The integrity check expects its recorded SHA-256. `verify.sh` removes this project's generated `.lake/build`, rebuilds against pinned imports, and records commands and outputs in a generated `logs/` directory. Do not upgrade dependencies. The cache helper chooses imported mathlib modules and falls back to mathlib's official Azure cache; generated toolchains and build caches are not distributed here.

The original run used the exact macOS arm64 toolchain. The `lean-toolchain` pin also identifies the exact Lean version for another supported platform. The scripts automatically prefer a matching local toolchain under `.tools/` if one is present.

## Paper and evidence

- [Revised mathematical paper source](docs/continuation_expansion.tex).
- [Original problem sources](docs/sources.md), [dependency map](docs/dependency-map.md), and [final source review](docs/final-proof-review.md).
- [Public evidence guide](verification/README.md) and [complete historical verification report](verification/prize-report.md).
- [Complete final target axioms](verification/evidence/target-axioms-complete.txt): only `propext`, `Classical.choice`, and `Quot.sound`.

The project is published on [`main`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/main/proofs/maximum-modulus/lean) in `https://github.com/liyunpeng1991/liyunpeng1991.github.io`. The exact source input A is [`c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus/lean). For reproducibility, check out that full revision rather than assuming a later `main` is the same input.

[Fresh verification of publication A](verification/public-commit-report.md) **passed**: the clean project verification, all 43 source checks and 42 project-module kernel replays, all eight target checks, and the exported-proof comparator with all five bundled additional kernels plus Lean default exited 0. The 126 production axiom reports and all eight targets contain only `propext`, `Classical.choice`, and `Quot.sound`. The complete curated fresh commands/logs and post-run source/dependency/tool stability checks are attached. The [historical report](verification/prize-report.md) records successful checks of temporary snapshot `8b731b51dcb0ed3d7e8c6463b6266c35d8099c85` separately.

The 53 production source/config/script files in A remain byte-identical to the verified source. A later evidence publication B updates these READMEs and adds logs without changing that proof input. Original command paths and timestamps are retained to identify the actual execution, not rewritten as a new run. The historical root staging manifest excludes the new README/evidence updates; see the root `PUBLICATION-MANIFEST.json` for their payload hashes.
