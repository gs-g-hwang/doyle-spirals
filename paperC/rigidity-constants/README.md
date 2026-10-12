# Proposition 5.1 of paper C: computer-assisted lower bounds for s₂ and s₃

**Claim.** s₂ > 14.8376 and s₃ > 3.7317. Explicit univalent hexagonal packings of 2 and 3 generations
have a neighbor of the central circle with radius ratio

- ρ₂ ∈ [15.837684647118901, 15.837684647118902]
- ρ₃ ∈ [4.731780877904626, 4.731780877904627]

## Files

| File | Content |
|---|---|
| `sk_best_k2.npy`, `sk_best_k3.npy` | **Certificates**: double-precision log-radii of all non-central circles (central radius 1), from the SLSQP search. The boundary radii are used as exact binary rationals. |
| `sk_optimize.py` | Combinatorics of the k-ring patch (`setup`) and the search (`solve`, SciPy SLSQP). Not needed for verification except `setup`. |
| `verify_sk.py` | Verification in 60-digit interval arithmetic (mpmath `iv`): Krawczyk test for the interior radii, interval layout, disjointness of all non-adjacent pairs. |
| `verify_sk_arb.py` | Independent re-verification in Arb ball arithmetic (python-flint, 240 bits). It shares only the certificates and `setup`. |
| `sk_verify.py` | Quick high-precision check (mpmath, not intervals) of a certificate: `python sk_verify.py 2`. |
| `sk_k3c.py` | The randomized SLSQP search for k = 3 that produced `sk_best_k3.npy`. |

**Caution:** `sk_optimize.py` and `sk_k3c.py` overwrite `sk_best_k*.npy`. To redo the search without losing the certificates, run them in a copy of this folder. The verification scripts only read the certificates.

## Reproduce

```
pip install numpy scipy mpmath python-flint
python verify_sk.py 2        # and 3
python verify_sk_arb.py 2    # and 3
```

Tested 2026-10-11 with Python 3, numpy 2.1.2, scipy 1.15.1, mpmath 1.3.0, python-flint 0.9.0. Each run takes about a second.

## Expected output

| k | interior unknowns | non-adjacent pairs | min relative margin | lower bound |
|---|---|---|---|---|
| 2 | 7 | 129 | 2.0 × 10⁻⁶ | s₂ ≥ 14.83768465 |
| 3 | 19 | 576 | 2.0 × 10⁻⁶ | s₃ ≥ 3.731780878 |

Both scripts give these values.
