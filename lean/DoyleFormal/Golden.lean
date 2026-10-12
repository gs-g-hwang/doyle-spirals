/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The golden member of the quadratic family (paper A, Section 6)

Only algebra about the real numbers is used.

* `golden_iff`        : for `B > 0`, `B² − 1 = B ↔ B = φ`
  (the golden case of Theorem A 6.1).
* `X_phi`             : the spiral center `X = −(B²+1)/(B²−1)` equals `−√5` at `B = φ`.
* `golden_cell_sides` : the cell triangle with radii `1, φ, φ²` has sides
  `1+φ = φ²`, `1+φ² = √5 φ`, `φ+φ² = φ³`, i.e. it is similar to `φ : √5 : φ²`
  (Proposition A 6.3).
-/

namespace DoyleFormal

open Real

lemma sqrt5_sq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma one_lt_sqrt5 : 1 < √5 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma one_lt_phi : 1 < φ := by
  unfold φ; linarith [one_lt_sqrt5]

lemma phi_pos : 0 < φ := by linarith [one_lt_phi]

lemma phi_ne_zero : φ ≠ 0 := phi_pos.ne'

/-- `φ² − 1 = φ`, the form used in Theorem A 6.1. -/
lemma phi_sq_sub_one : φ ^ 2 - 1 = φ := by linarith [phi_sq]

/-- Golden case of Theorem A 6.1: for a positive ratio `B`,
`B² − 1 = B` holds exactly when `B` is the golden ratio. -/
theorem golden_iff {B : ℝ} (hB : 0 < B) : B ^ 2 - 1 = B ↔ B = φ := by
  constructor
  · intro h
    have hfac : (B - φ) * (B - (1 - √5) / 2) = 0 := by
      unfold φ; linear_combination h - (1 / 4 : ℝ) * sqrt5_sq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith
    · nlinarith [one_lt_sqrt5]
  · rintro rfl; exact phi_sq_sub_one

/-- The center of the spiral, `X = −(B² + 1)/(B² − 1)`. -/
noncomputable def X (B : ℝ) : ℝ := -(B ^ 2 + 1) / (B ^ 2 - 1)

/-- At the golden ratio the center is `X = −√5`. -/
theorem X_phi : X φ = -√5 := by
  unfold X
  rw [phi_sq_sub_one, div_eq_iff phi_ne_zero]
  have h := phi_sq
  unfold φ at h ⊢
  linear_combination h

/-- Side lengths of the golden cell triangle (radii `1, φ, φ²`, tangent circles):
`|OP₁| = 1 + φ = φ²`, `|OP₀| = 1 + φ² = √5·φ`, `|P₀P₁| = φ + φ² = φ³`. -/
theorem golden_cell_sides :
    1 + φ = φ ^ 2 ∧ 1 + φ ^ 2 = √5 * φ ∧ φ + φ ^ 2 = φ ^ 3 := by
  have h := phi_sq
  refine ⟨by linarith, ?_, ?_⟩
  · unfold φ at h ⊢; linear_combination h - (1 / 2 : ℝ) * sqrt5_sq
  · linear_combination (-φ) * h

/-- Proposition A 6.3: dividing the sides by `φ` gives the ratio `φ : √5 : φ²`. -/
theorem golden_cell_shape :
    (1 + φ) / φ = φ ∧ (1 + φ ^ 2) / φ = √5 ∧ (φ + φ ^ 2) / φ = φ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := golden_cell_sides
  refine ⟨?_, ?_, ?_⟩ <;> rw [div_eq_iff phi_ne_zero]
  · rw [h1]; ring
  · rw [h2]
  · rw [h3]; ring

end DoyleFormal
