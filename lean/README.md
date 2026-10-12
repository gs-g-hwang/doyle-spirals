# DoyleFormal: Lean 4 proofs for the papers on Doyle spirals

This is a formal verification in Lean 4 and Mathlib of the results listed in the Data availability statements of papers A, B and C (see the top-level README). `STATEMENTS.md` maps each paper statement to the Lean file and declarations that prove it.

## Build

| Item | Version |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc4` (`lean-toolchain`) |
| Mathlib | tag `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` (`lake-manifest.json`) |

```
lake exe cache get
lake build
```
A clean build compiles 49 files and Mathlib's prebuilt cache. The sources contain no `sorry` and no `admit`:
```
grep -rnwE "sorry|admit" DoyleFormal    # prints nothing
```
Do not run `lake update`, because it would move Mathlib away from the pinned version.

## Hypotheses

Two results are not proved in Lean. They enter only as explicit hypotheses of the theorems that use them:
- **`GelfondSchneider`** (`BdsClass.lean`) is the Gelfond–Schneider theorem. It is used only for the transcendence statements `psi_phi_transcendental` and `t_rat_or_transcendental` (A, Corollaries 7.6–7.7). It is not yet in Mathlib.
- **He's estimate** s_k ≤ C/k (Z.-X. He, 1991) is a hypothesis of `doyle_opt` (C, Theorem 4.1).

## Licence

Apache License 2.0, the same licence as Lean and Mathlib. The licence text is in `LICENSE` at the top level of the repository.

## Files

All modules are listed in `DoyleFormal.lean`. Each file begins with a docstring that names the paper statements it covers.
