# Project Turing - Task 6 golden answer

Lean 4 project with complete proofs of five statements about exponential sums over squares
and one cotangent sum. The required file is `TuringTask/Basic.lean`.

## Pinned environment

- Lean toolchain: `leanprover/lean4:v4.33.0-rc1` (file `lean-toolchain`)
- Mathlib: the pinned checkout at `/opt/mathlib4`, commit `9944fe2973b8dc0b86949101ed98232c07cd54a0`
  (files `lakefile.toml` and `lake-manifest.json`; the other packages are the ones locked by
  that Mathlib commit)

## Build and check (offline, no edits needed)

    lake build
    lake env lean StatementAndAxiomsCheck.lean

If the environment requires it, run `lean-offline-init` first; it only links the locally
installed Mathlib dependencies into `.lake/packages` and downloads nothing.

The second command re-states the two definitions and the five theorems of the prompt, so it
fails if any of them was changed, and it prints the axioms used by each of the five theorems.

The six source files form one import chain, so `lake build` compiles them one after the other.

## Files

- `TuringTask/Poly.lean`: Gaussian binomial coefficients and an alternating-sum identity in Z[X]
- `TuringTask/Root.lean`: the identity at a root of unity; two facts about finite sums
- `TuringTask/Sums.lean`: the sums over squares and over triangular numbers for odd n
- `TuringTask/Char.lean`: sums with the Legendre symbol; the product for two odd primes
- `TuringTask/Cot.lean`: the cotangent sum
- `TuringTask/Basic.lean`: the two definitions and the five theorems
