# Doyle spirals of the quadratic family: scripts, data and Lean proofs

This repository accompanies three papers by Hai-Yeh Hwang and Gwang-Syung George Hwang:

- **A.** *The Quadratic Family of Doyle Spirals: Similar Triangles, Mirror Symmetry and the Golden Section*
- **B.** *Resonant Doyle Spirals: First Overlap, Coxeter's Quadruple and Tilings by Similar Triangles*
- **C.** *Doyle Spirals and the Rodin–Sullivan Rigidity Constants*

It contains:
- the Python scripts that draw every figure;
- the scripts that recompute every table and every computation in the papers, including the interval-arithmetic proofs;
- the Lean 4 project that formally verifies the results listed in the Data availability statements of the papers.

## Contents

| Folder | What it contains |
|---|---|
| `paperA/figures/` | `fig01_…py` – `fig14_…py` draw Figures 1–14 of A (the PNGs are the figures as printed). `doylefig.py` holds the shared drawing style; `first_overlap*.py` are helper modules. |
| `paperA/computations/` | `golden_three_rings.py` (golden configuration: no overlap within three rings, overlap at the fourth); `residual_scan.py` (the residual plot on a 1601 × 1601 grid, Section 9). |
| `paperA/tables/` | `tables_A.py`: Tables 1 and 2 of A. |
| `paperB/figures/` | Figures 1–5 of B. |
| `paperB/computations/` | `two_shapes_verify.py` (interval-arithmetic proof in Proposition 7.1 (3)), `two_shapes.py` (the floating-point version), `bn_algebra.py` (minimal polynomials of B_n), `ties_and_delta.py` (check of the first-overlap rule on a grid). |
| `paperB/tables/` | `table_Bn_algebraic.py`: Table 1 of B. |
| `paperC/figures/` | Figure 1 of C. |
| `paperC/computations/` | `check_appendix_A1.py`: numerical check of Proposition A.4. |
| `paperC/rigidity-constants/` | Proposition 5.1 of C (s₂ > 14.8376, s₃ > 3.7317): certificates, search, and two independent verifications (mpmath intervals, Arb). See its README. |
| `paperC/tables/` | `table_sk.py`: Table 1 of C. |
| `lean/` | The Lean 4 project `DoyleFormal`. `lean/STATEMENTS.md` maps each statement in the papers to the Lean declarations that prove it. |
| `TABLES.md` | How each table is checked against the paper. |

## Python

The scripts were tested with Python 3.12 and the versions in `requirements.txt`:
```
python -m venv .venv
.venv/Scripts/activate            # Windows; on Linux/macOS: source .venv/bin/activate
pip install -r requirements.txt
```
Each script runs from its own folder and writes its output there. For example:
```
cd paperA/figures && python fig06_golden_center_grid.py
cd paperC/rigidity-constants && python verify_sk.py 2 && python verify_sk.py 3
cd paperA/tables && python tables_A.py
```
The figure scripts reproduce the PNGs in this repository byte for byte with the versions in `requirements.txt`. Most scripts take a few seconds. `bn_algebra.py` takes about 40 s and `check_appendix_A1.py` about 75 s.

## Lean 4

The pinned versions are Lean `v4.35.0-rc4` and Mathlib `v4.35.0-rc4`, set by `lean/lean-toolchain` and `lean/lake-manifest.json`. With [elan](https://github.com/leanprover/elan) installed:
```
cd lean
lake exe cache get     # downloads the compiled Mathlib
lake build
```
The project has 49 files and no `sorry`. Two results are taken as hypotheses and stated as such in the papers:
- the Gelfond–Schneider theorem, which is not in Mathlib and is used only for the transcendence statements of A, Corollaries 7.6–7.7;
- He's estimate s_k ≤ C/k, used in C, Theorem 4.1.

## Citation

Please cite the papers. To cite this repository, use the "Cite this repository" button (from `CITATION.cff`) or its Zenodo DOI.

## Licence

Copyright 2026 Hai-Yeh Hwang and Gwang-Syung George Hwang.

- **Code** (all `.py` and `.lean` files, the Lake configuration and the workflow files) is licensed under the **Apache License 2.0**; see `LICENSE`.
- **Figures and data** (the `.png` figures and the `.npy` certificates in `paperC/rigidity-constants/`) are licensed under **Creative Commons Attribution 4.0 International (CC BY 4.0)**; see `LICENSE-figures`. When you reuse a figure, credit the authors and cite the paper it appears in.
