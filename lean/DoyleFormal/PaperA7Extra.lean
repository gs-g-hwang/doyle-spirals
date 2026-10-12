/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.BdsClass
import DoyleFormal.FlowerGeom

/-!
# Two numerical statements of paper A, Section 7

* `cos_angleAt_mid`, `coxeter_middle_angle` (**Proposition A 7.8**): the angle of the cell triangle
  at the vertex of radius `B` has `cos θ_{P₁} = (B² + 1)/(B + 1)² = 1/(1 + η)`, and for
  `B₂ = φ + √φ` it is `θ_{P₁} = arccos(1/φ)`.
* `t_phi_gt` (**Corollary A 7.6**): `t(φ) = π/ψ(φ) > 39/10`, so with `t_phi_bounds` the golden
  configuration lies in `(3.9, 4)`, just below the coherent spiral `[4,8]`. The proof bounds
  `cos(10π/39) = 2cos²(5π/39) − 1` with Mathlib's `Real.cos_bound` and `π > 3.141592`.
-/

namespace DoyleFormal

open Real

/-- `cos(2 arctan u) = (1 − u²)/(1 + u²)`. -/
lemma cos_two_arctan (u : ℝ) : cos (2 * arctan u) = (1 - u ^ 2) / (1 + u ^ 2) := by
  have h1 : 0 < 1 + u ^ 2 := by positivity
  rw [cos_two_mul, cos_arctan, div_pow, one_pow, Real.sq_sqrt h1.le]
  field_simp
  ring

/-- **Proposition A 7.8.** In the cell triangle with radii `1, B, B²`, the angle at the vertex of
radius `B` has `cos θ_{P₁} = (B² + 1)/(B + 1)² = 1/(1 + η)`. -/
theorem cos_angleAt_mid {B : ℝ} (hB : 0 < B) :
    cos (angleAt B 1 (B ^ 2)) = (B ^ 2 + 1) / (B + 1) ^ 2 ∧
      (B ^ 2 + 1) / (B + 1) ^ 2 = 1 / (1 + eta B) := by
  refine ⟨?_, ?_⟩
  · rw [cos_angleAt hB one_pos (by positivity)]
    have : B + 1 ≠ 0 := by positivity
    field_simp
    ring
  · unfold eta
    field_simp
    ring

/-- **Proposition A 7.8.** For `B₂ = φ + √φ` the middle angle of the cell triangle is
`θ_{P₁} = arccos(1/φ)`. -/
theorem coxeter_middle_angle : angleAt (φ + √φ) 1 ((φ + √φ) ^ 2) = arccos (1 / φ) := by
  have hp := phi_pos
  set B := φ + √φ with hBdef
  have hB0 : 0 < B := by positivity
  have hB1 : 1 < B := by
    have : 1 < √φ := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) one_lt_phi
    linarith
  -- `η(B₂) = 1/φ`, from `B + 1/B = 2φ`
  have hsum : B + B⁻¹ = 2 * φ := ((coxeter_tfae hB1).out 3 2).1 hBdef
  have hη : eta B = 1 / φ := by
    unfold eta
    have : B ^ 2 + 1 = 2 * φ * B := by
      field_simp at hsum; linarith
    rw [this]; field_simp
  have hcos : cos (angleAt B 1 (B ^ 2)) = 1 / φ := by
    obtain ⟨h1, h2⟩ := cos_angleAt_mid hB0
    rw [h1, h2, hη]
    have : φ ^ 2 = φ + 1 := phi_sq
    field_simp
    linarith
  -- the angle lies in `[0, π]`
  have hpos : 0 ≤ angleAt B 1 (B ^ 2) := by
    unfold angleAt
    have : 0 < 1 / (nu B 1 (B ^ 2) * B) := by
      have := nu_pos hB0 one_pos (by positivity : (0 : ℝ) < B ^ 2); positivity
    linarith [arctan_pos.2 this]
  have hlt : angleAt B 1 (B ^ 2) ≤ π := by
    unfold angleAt
    linarith [arctan_lt_pi_div_two (1 / (nu B 1 (B ^ 2) * B))]
  rw [← hcos, arccos_cos hpos hlt]

/-- `cos y ≤ 1 − y²/2 + (5/96) y⁴` for `|y| ≤ 1` (from `Real.cos_bound`). -/
lemma cos_le_quartic {y : ℝ} (hy : |y| ≤ 1) : cos y ≤ 1 - y ^ 2 / 2 + 5 / 96 * y ^ 4 := by
  have h := Real.cos_bound hy
  rw [abs_le] at h
  have : |y| ^ 4 = y ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  rw [this] at h
  linarith [h.2]

/-- **Corollary A 7.6.** `t(φ) = π/ψ(φ) > 3.9`. -/
theorem t_phi_gt : (39 / 10 : ℝ) < Real.pi / psi φ := by
  have hpi : (3141592 / 1000000 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  set y := Real.pi * (5 / 39) with hy
  set y0 : ℝ := 3141592 / 1000000 * (5 / 39) with hy0def
  have hy0 : y0 < y := by rw [hy, hy0def]; linarith
  have hy1 : y ≤ 1 := by rw [hy]; linarith
  have hy0' : 0 < y := by rw [hy]; positivity
  have hy00 : 0 ≤ y0 := by rw [hy0def]; norm_num
  have hy01 : y0 ≤ 1 := by rw [hy0def]; norm_num
  have hy0num : y0 = 3141592 / 1000000 * (5 / 39) := hy0def
  clear_value y0
  -- upper bound for `cos y`
  have hc : cos y ≤ 1 - y0 ^ 2 / 2 + 5 / 96 * y0 ^ 4 := by
    have h1 := cos_le_quartic (y := y) (by rw [abs_of_pos hy0']; exact hy1)
    have hyy : y0 ^ 2 ≤ y ^ 2 := by nlinarith
    have hs : y ^ 2 + y0 ^ 2 ≤ 2 := by nlinarith
    have key : (1 - y0 ^ 2 / 2 + 5 / 96 * y0 ^ 4) - (1 - y ^ 2 / 2 + 5 / 96 * y ^ 4) =
        (y ^ 2 - y0 ^ 2) * (1 / 2 - 5 / 96 * (y ^ 2 + y0 ^ 2)) := by ring
    have : 0 ≤ (y ^ 2 - y0 ^ 2) * (1 / 2 - 5 / 96 * (y ^ 2 + y0 ^ 2)) :=
      mul_nonneg (sub_nonneg.2 hyy) (by linarith)
    linarith
  have hcpos : 0 ≤ cos y := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith)
    (by rw [hy]; linarith [Real.pi_pos])
  -- `cos(10π/39) = 2cos²(5π/39) − 1 < (2√5 − 1)/5 = cos ψ(φ)`
  have hcos2 : cos (Real.pi / (39 / 10)) = 2 * cos y ^ 2 - 1 := by
    rw [show Real.pi / (39 / 10) = 2 * y by rw [hy]; ring, cos_two_mul]
  have h5 : (2236 / 1000 : ℝ) < √5 := by
    rw [show (2236 / 1000 : ℝ) = √((2236 / 1000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hlt : cos (Real.pi / (39 / 10)) < cosPsi φ := by
    rw [hcos2, cosPsi_phi]
    have hb : cos y ^ 2 ≤ (1 - y0 ^ 2 / 2 + 5 / 96 * y0 ^ 4) ^ 2 := pow_le_pow_left₀ hcpos hc 2
    have hnum : 2 * (1 - y0 ^ 2 / 2 + 5 / 96 * y0 ^ 4) ^ 2 - 1 < (2 * (2236 / 1000) - 1) / 5 := by
      rw [hy0num]; norm_num
    linarith
  have hψ := psi_mem_Ioo one_lt_phi
  -- monotonicity of `cos` on `[0, π]`
  have hψlt : psi φ < Real.pi / (39 / 10) := by
    by_contra hge
    push Not at hge
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hψ.2.le hge
    rw [cos_psi one_lt_phi] at this
    linarith
  rw [lt_div_iff₀ hψ.1]
  have : psi φ * (39 / 10) < Real.pi := by
    rw [lt_div_iff₀ (by norm_num)] at hψlt; linarith
  linarith

end DoyleFormal
