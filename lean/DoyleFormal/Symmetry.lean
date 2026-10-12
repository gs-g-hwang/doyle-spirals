/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Rigidity

/-!
# Mirror symmetry (paper A, Theorem 4.1) — Phase 4f

* `mirror_symmetry` (Theorem A 4.1, `⇐`): for `A = B²`, complex conjugation maps `K(p,q)` to
  `K(τ(p,q))` with the indirect lattice automorphism `τ(p,q) = (p+q, −q)`: equal radii and
  `conj z(p,q) = z(p+q, −q)`. By `prop_5_4` this holds for `D_B` itself.
* `mirror_radius` (Theorem A 4.1, `⇒`, the radius comparison): with the radius function
  `A^p B^q`, `r(τ(0,1)) = r(0,1)` forces `A = B²`. That `τ` is the only indirect lattice
  automorphism fixing `(0,0)` and `(1,0)` is `indirect_aut_unique` in `LatticeAut.lean`.
-/

namespace DoyleFormal

open Complex

lemma conj_exp_mul_I (ψ : ℝ) : (starRingEnd ℂ) (exp (ψ * I)) = (exp (ψ * I))⁻¹ := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_neg]
  ring_nf

/-- **Theorem A 4.1 (`⇐`).** The quadratic family is mirror symmetric:
`conj z(p,q) = z(p+q, −q)` and `r(p+q, −q) = r(p,q)`. -/
theorem mirror_symmetry {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    (starRingEnd ℂ) (zc B ψ p q) = zc B ψ (p + q) (-q) ∧ rad B (p + q) (-q) = rad B p q := by
  have hB0 : B ≠ 0 := by linarith
  refine ⟨?_, by unfold rad; congr 1; ring⟩
  have h1 := zc_sub_X ψ hB0 p q
  have h2 := zc_sub_X ψ hB0 (p + q) (-q)
  rw [show 2 * (p + q) + -q = 2 * p + q by ring, zpow_neg, ← inv_zpow,
    ← conj_exp_mul_I] at h2
  have hc : (starRingEnd ℂ) (zc B ψ p q - X B)
      = (B : ℂ) ^ (2 * p + q) * (starRingEnd ℂ) (exp (ψ * I)) ^ q * (-(X B : ℂ)) := by
    rw [h1, map_mul, map_mul, map_neg, map_zpow₀, map_zpow₀, Complex.conj_ofReal,
      Complex.conj_ofReal]
  rw [map_sub, Complex.conj_ofReal] at hc
  linear_combination hc - h2

/-- **Theorem A 4.1 (`⇒`), radius comparison.** For `A, B > 0`, the radii `A/B` of
`τ(0,1) = (1,−1)` and `B` of `(0,1)` agree iff `A = B²`. -/
theorem mirror_radius {A B : ℝ} (hB : 0 < B) : A / B = B ↔ A = B ^ 2 := by
  rw [div_eq_iff hB.ne']
  constructor <;> intro h <;> linear_combination h

/-- With `prop_5_4`: every configuration with radii `B^{2p+q}` normalized by `z(0,0) = 0`,
`z(1,0) = 1 + B²` is invariant under conjugation with `τ(p,q) = (p+q, −q)`. -/
theorem config_mirror {B : ℝ} (hB : 1 < B) {z : ℤ → ℤ → ℂ} (hz : IsConfig (rad B) z)
    (h0 : z 0 0 = 0) (h1 : z 1 0 = ((1 + B ^ 2 : ℝ) : ℂ)) (p q : ℤ) :
    (starRingEnd ℂ) (z p q) = z (p + q) (-q) := by
  rw [prop_5_4 hB hz h0 h1, prop_5_4 hB hz h0 h1]
  exact (mirror_symmetry (psi B) hB p q).1

end DoyleFormal
