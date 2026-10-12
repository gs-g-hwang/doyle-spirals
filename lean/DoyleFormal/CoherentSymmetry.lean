/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.SymmetryConverse

/-!
# Symmetry and shape of the resonant spirals (paper B, Theorem 7.2, converse part) — Phase 4k

* `rotation_step`: the rotation `z ↦ X + e^{2iψ}(z − X)` maps `K(p,q)` to `K(p−1, q+2)` (same
  radius). For `ψ = π/n` it has order `n`: `D_{B_n}` has `n`-fold rotational symmetry about `X`
  (`coherent_rotation`, `rotation_order`). Mirror symmetry is `mirror_symmetry`.
* `cell_sides_lt`: for `B > 1` the cell triangle (radii `1, B, B²`) has sides
  `1 + B < 1 + B² < B + B²`.
* `cell_shape_inj`: the shape of the cell triangle determines `B`.
* `resonant_nonsimilar`: distinct `n` give non-similar cell triangles, hence non-similar
  tilings.

The covering part of Theorem B 7.2 (every coherent packing with similar triangles is one of
these) is not formalized.
-/

namespace DoyleFormal

open Complex

/-- The rotation about `X` by `2ψ` maps the circle at `(p,q)` to the circle at
`(p−1, q+2)`, with the same radius. -/
theorem rotation_step {B : ℝ} (ψ : ℝ) (hB : 0 < B) (p q : ℤ) :
    zc B ψ (p - 1) (q + 2) - X B = exp (2 * ψ * I) * (zc B ψ p q - X B) ∧
      rad B (p - 1) (q + 2) = rad B p q := by
  have hB0 : B ≠ 0 := hB.ne'
  have he : exp (ψ * I) ≠ 0 := exp_ne_zero _
  refine ⟨?_, by unfold rad; congr 1; ring⟩
  have h2 : exp (2 * ψ * I) = exp (ψ * I) ^ 2 := by
    rw [sq, ← Complex.exp_add]; ring_nf
  rw [zc_sub_X ψ hB0, zc_sub_X ψ hB0, show 2 * (p - 1) + (q + 2) = 2 * p + q by ring,
    zpow_add₀ he, h2]
  simp only [zpow_ofNat]
  ring

/-- **`n`-fold rotational symmetry.** For `ψ = π/n` the rotation about `X` by `2π/n` maps
`K(p,q)` to `K(p−1, q+2)`. -/
theorem coherent_rotation {B : ℝ} (hB : 0 < B) {n : ℕ} (hψn : psi B = Real.pi / n)
    (p q : ℤ) :
    zc B (psi B) (p - 1) (q + 2) - X B =
        exp (2 * (Real.pi / n) * I) * (zc B (psi B) p q - X B) ∧
      rad B (p - 1) (q + 2) = rad B p q := by
  have h := rotation_step (psi B) hB p q
  rw [hψn] at h ⊢
  push_cast at h ⊢
  exact h

/-- The rotation by `2π/n` has order `n`. -/
theorem rotation_order {n : ℕ} (hn : 1 ≤ n) : exp (2 * (Real.pi / n) * I) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [show (n : ℂ) * (2 * (Real.pi / n) * I) = 2 * Real.pi * I by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- For `B > 1` the sides of the cell triangle with radii `1, B, B²` are ordered
`1 + B < 1 + B² < B + B²`. -/
theorem cell_sides_lt {B : ℝ} (hB : 1 < B) : 1 + B < 1 + B ^ 2 ∧ 1 + B ^ 2 < B + B ^ 2 := by
  constructor <;> nlinarith

/-- **The shape determines `B`.** If the cell triangles for `B > 0` and `B'` are similar, with
the sides matched in increasing order (as any similarity does, by `cell_sides_lt`), then
`B = B'`. -/
theorem cell_shape_inj {B B' μ : ℝ} (hB : 0 < B) (hμ : 0 < μ)
    (h1 : 1 + B' = μ * (1 + B)) (h3 : B' + B' ^ 2 = μ * (B + B ^ 2)) : B' = B := by
  have h : B' * (1 + B') = B * (1 + B') := by
    linear_combination h3 - B * h1
  have hpos : 0 < 1 + B' := by rw [h1]; positivity
  exact mul_right_cancel₀ hpos.ne' h

/-- **Distinct `n` give non-similar tilings.** If `ψ(B) = π/n` and `ψ(B') = π/m` with
`B > 1` and the cell triangles are similar, then `n = m`. -/
theorem resonant_nonsimilar {B B' μ : ℝ} (hB : 1 < B) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hψn : psi B = Real.pi / n) (hψm : psi B' = Real.pi / m)
    (hμ : 0 < μ) (h1 : 1 + B' = μ * (1 + B)) (h3 : B' + B' ^ 2 = μ * (B + B ^ 2)) :
    n = m := by
  have hBB := cell_shape_inj (by linarith) hμ h1 h3
  rw [hBB, hψn] at hψm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have : (n : ℝ) = m := by
    field_simp at hψm
    nlinarith [Real.pi_pos]
  exact_mod_cast this

end DoyleFormal
