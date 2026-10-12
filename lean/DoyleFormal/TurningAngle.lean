/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Golden
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The turning angle ψ (paper A, Section 7.1)

Formalizes Proposition A 7.1 and Corollary A 7.2, plus the golden values
(A, eq. (7.2)) and Coxeter's ratio `B₂ = φ + √φ`.

* `cosPsi B = −(B⁴ − 2B³ − 2B² − 2B + 1)/(B² + 1)²` is the closed form of `cos ψ`, and
  `psi B = arccos (cosPsi B)` is the turning angle.
* `turning_angle` is the analytic part of the proof of Proposition A 7.1. It takes as
  hypotheses `ψ = θ_O − θ_{P₀}` and the half-angle tangents `1/ν`, `1/(νB²)` of Remark A 3.9.
  Those come from the geometry of the configuration, which is not formalized here.
* `cosPsi_eq_eta`, `one_sub_cosPsi_half`: equation (7.1) with `η = sech log B` (`eta_eq_sech`).
* `psi_strictMonoOn`, `psi_mem_Ioo`, `exists_unique_psi`: `B ↦ ψ(B)` is a strictly increasing
  bijection `(1, ∞) → (0, π)`. Surjectivity comes from the explicit inverse of Corollary A 7.2.
* `resonant`, `resonant_formula`: Corollary A 7.2.
* `cosPsi_phi`, `tanSqHalf_phi`: the golden values; `psi_coxeter`: `ψ(φ + √φ) = π/2`.
-/

namespace DoyleFormal

open Real Set

/-- `cos ψ` as a function of `B` (Proposition A 7.1). -/
noncomputable def cosPsi (B : ℝ) : ℝ :=
  -(B ^ 4 - 2 * B ^ 3 - 2 * B ^ 2 - 2 * B + 1) / (B ^ 2 + 1) ^ 2

/-- `η = sech log B = 2B/(B² + 1)`. -/
noncomputable def eta (B : ℝ) : ℝ := 2 * B / (B ^ 2 + 1)

/-- `tan²(ψ/2)` as a function of `B` (Proposition A 7.1). -/
noncomputable def tanSqHalf (B : ℝ) : ℝ := (B - 1) ^ 2 * (B ^ 2 + B + 1) / (B * (B + 1) ^ 2)

/-- The turning angle `ψ(B) ∈ [0, π]`. -/
noncomputable def psi (B : ℝ) : ℝ := arccos (cosPsi B)

/-! ### Algebraic identities -/

lemma eta_eq_sech {B : ℝ} (hB : 0 < B) : eta B = 1 / cosh (log B) := by
  rw [cosh_log hB]
  have : B ≠ 0 := hB.ne'
  unfold eta
  field_simp

/-- Equation (7.1): `cos ψ = η² + η − 1`. -/
theorem cosPsi_eq_eta (B : ℝ) : cosPsi B = eta B ^ 2 + eta B - 1 := by
  have : B ^ 2 + 1 ≠ 0 := by positivity
  unfold cosPsi eta
  field_simp
  ring

/-- Equation (7.1): `sin²(ψ/2) = (1 − cos ψ)/2 = (B − 1)²(B² + B + 1)/(B² + 1)²`. -/
theorem one_sub_cosPsi_half (B : ℝ) :
    (1 - cosPsi B) / 2 = (B - 1) ^ 2 * (B ^ 2 + B + 1) / (B ^ 2 + 1) ^ 2 := by
  have : B ^ 2 + 1 ≠ 0 := by positivity
  unfold cosPsi
  field_simp
  ring

/-- Equation (7.1) in the variable `η`: `sin²(ψ/2) = (1 − η)(2 + η)/2`. -/
theorem sin_sq_half_eta (B : ℝ) :
    (1 - eta B) * (2 + eta B) / 2 = (B - 1) ^ 2 * (B ^ 2 + B + 1) / (B ^ 2 + 1) ^ 2 := by
  have : B ^ 2 + 1 ≠ 0 := by positivity
  unfold eta
  field_simp
  ring

lemma tanSqHalf_nonneg {B : ℝ} (hB : 0 < B) : 0 ≤ tanSqHalf B := by
  unfold tanSqHalf
  have : 0 < B ^ 2 + B + 1 := by positivity
  positivity

/-- `cos ψ = (1 − tan²(ψ/2))/(1 + tan²(ψ/2))` with the two closed forms. -/
theorem cosPsi_eq_tan {B : ℝ} (hB : 0 < B) :
    cosPsi B = (1 - tanSqHalf B) / (1 + tanSqHalf B) := by
  have hT := tanSqHalf_nonneg hB
  rw [eq_div_iff (by linarith)]
  have h1 : B ≠ 0 := hB.ne'
  have h2 : B + 1 ≠ 0 := by linarith
  have h3 : B ^ 2 + 1 ≠ 0 := by positivity
  unfold cosPsi tanSqHalf
  field_simp
  ring

/-- Half-angle algebra in the proof of Proposition A 7.1: if `tan(θ_O/2) = 1/ν`,
`tan(θ_{P₀}/2) = 1/(νB²)` and `ν²B³ = 1 + B + B²` (Remark A 3.9), then the tangent of
`(θ_O − θ_{P₀})/2`, computed by the subtraction formula, squares to `tanSqHalf B`. -/
theorem tan_half_diff_sq {B ν : ℝ} (hB : 0 < B) (hν : 0 < ν)
    (hνB : ν ^ 2 * B ^ 3 = 1 + B + B ^ 2) :
    ((1 / ν - 1 / (ν * B ^ 2)) / (1 + 1 / ν * (1 / (ν * B ^ 2)))) ^ 2 = tanSqHalf B := by
  have h1 : (1 / ν - 1 / (ν * B ^ 2)) / (1 + 1 / ν * (1 / (ν * B ^ 2)))
      = ν * B * (B ^ 2 - 1) / (ν ^ 2 * B ^ 3 + B) := by
    have : ν ≠ 0 := hν.ne'
    have : B ≠ 0 := hB.ne'
    have : ν ^ 2 * B ^ 3 + B ≠ 0 := by positivity
    have : ν ^ 2 * B ^ 2 + 1 ≠ 0 := by positivity
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  rw [h1, div_pow]
  unfold tanSqHalf
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (B - 1) ^ 2 * ((B + 1) ^ 4 - (1 + B + B ^ 2) * (ν ^ 2 * B ^ 3
    + (1 + B + B ^ 2)) - 2 * B * (1 + B + B ^ 2)) * hνB

/-! ### Trigonometry -/

lemma tan_sub_of_cos_pos {a b : ℝ} (ha : 0 < cos a) (hb : 0 < cos b) :
    tan (a - b) = (tan a - tan b) / (1 + tan a * tan b) := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, sin_sub, cos_sub]
  have h1 : cos a ≠ 0 := ha.ne'
  have h2 : cos b ≠ 0 := hb.ne'
  rcases eq_or_ne (cos a * cos b + sin a * sin b) 0 with h | h
  · have h' : cos a * cos b + sin a * sin b = 0 := h
    rw [h', div_zero]
    have : 1 + sin a / cos a * (sin b / cos b) = 0 := by
      field_simp; linear_combination h'
    rw [this, div_zero]
  · field_simp

lemma cos_eq_of_tan_half {x : ℝ} (hx : cos (x / 2) ≠ 0) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  have hx2 : x = 2 * (x / 2) := by ring
  conv_lhs => rw [hx2, cos_two_mul]
  rw [tan_eq_sin_div_cos]
  have hs := sin_sq_add_cos_sq (x / 2)
  field_simp
  linear_combination 2 * cos (x / 2) ^ 2 * hs

/-- **Proposition A 7.1, analytic part.** Let `α = θ_O/2` and `β = θ_{P₀}/2`, both in
`(0, π/2)`, with `tan α = 1/ν`, `tan β = 1/(νB²)` and `ν²B³ = 1 + B + B²`. Then the turning
angle `ψ = θ_O − θ_{P₀} = 2α − 2β` satisfies `tan²(ψ/2) = tanSqHalf B` and
`cos ψ = cosPsi B`. -/
theorem turning_angle {B ν α β : ℝ} (hB : 0 < B) (hν : 0 < ν)
    (hνB : ν ^ 2 * B ^ 3 = 1 + B + B ^ 2)
    (hα : α ∈ Ioo 0 (π / 2)) (hβ : β ∈ Ioo 0 (π / 2))
    (htα : tan α = 1 / ν) (htβ : tan β = 1 / (ν * B ^ 2)) :
    tan (α - β) ^ 2 = tanSqHalf B ∧ cos (2 * α - 2 * β) = cosPsi B := by
  have hca : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith [hα.1, pi_pos], hα.2⟩
  have hcb : 0 < cos β := cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, pi_pos], hβ.2⟩
  have hcab : 0 < cos (α - β) :=
    cos_pos_of_mem_Ioo ⟨by linarith [hα.1, hβ.2], by linarith [hα.2, hβ.1]⟩
  have htan : tan (α - β) ^ 2 = tanSqHalf B := by
    rw [tan_sub_of_cos_pos hca hcb, htα, htβ]
    exact tan_half_diff_sq hB hν hνB
  refine ⟨htan, ?_⟩
  have hhalf : (2 * α - 2 * β) / 2 = α - β := by ring
  rw [cos_eq_of_tan_half (by rw [hhalf]; exact hcab.ne'), hhalf, htan, cosPsi_eq_tan hB]

/-! ### Range and monotonicity -/

lemma eta_pos {B : ℝ} (hB : 0 < B) : 0 < eta B := by unfold eta; positivity

lemma eta_lt_one {B : ℝ} (hB : 1 < B) : eta B < 1 := by
  unfold eta
  rw [div_lt_one (by positivity)]
  nlinarith [pow_pos (sub_pos.2 hB) 2]

lemma eta_strictAntiOn : StrictAntiOn eta (Ioi 1) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  unfold eta
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hxy1 : 0 < x * y - 1 := by nlinarith
  nlinarith [mul_pos (sub_pos.2 hxy) hxy1]

theorem cosPsi_strictAntiOn : StrictAntiOn cosPsi (Ioi 1) := by
  intro x hx y hy hxy
  have h := eta_strictAntiOn hx hy hxy
  have hy0 : 0 < eta y := eta_pos (by simp only [mem_Ioi] at hy; linarith)
  rw [cosPsi_eq_eta, cosPsi_eq_eta]
  nlinarith

theorem cosPsi_mem_Ioo {B : ℝ} (hB : 1 < B) : cosPsi B ∈ Ioo (-1) 1 := by
  have h0 := eta_pos (by linarith : (0 : ℝ) < B)
  have h1 := eta_lt_one hB
  rw [cosPsi_eq_eta]
  constructor <;> nlinarith

theorem cos_psi {B : ℝ} (hB : 1 < B) : cos (psi B) = cosPsi B :=
  cos_arccos (cosPsi_mem_Ioo hB).1.le (cosPsi_mem_Ioo hB).2.le

/-- `ψ(B) ∈ (0, π)` for `B > 1`; in particular `ψ ≠ π` (Corollary A 7.2, last sentence). -/
theorem psi_mem_Ioo {B : ℝ} (hB : 1 < B) : psi B ∈ Ioo 0 π :=
  ⟨arccos_pos.2 (cosPsi_mem_Ioo hB).2, arccos_lt_pi.2 (cosPsi_mem_Ioo hB).1⟩

/-- `B ↦ ψ(B)` is strictly increasing on `(1, ∞)` (Proposition A 7.1). -/
theorem psi_strictMonoOn : StrictMonoOn psi (Ioi 1) := by
  intro x hx y hy hxy
  have hx' := cosPsi_mem_Ioo hx
  have hy' := cosPsi_mem_Ioo hy
  exact strictAntiOn_arccos ⟨hy'.1.le, hy'.2.le⟩ ⟨hx'.1.le, hx'.2.le⟩
    (cosPsi_strictAntiOn hx hy hxy)

/-! ### The explicit inverse (Corollary A 7.2) -/

/-- `η` as a function of `c = cos ψ`: the positive root of `η² + η − 1 = c`. -/
noncomputable def etaOfCos (c : ℝ) : ℝ := (√(5 + 4 * c) - 1) / 2

/-- `B` as a function of `η`: the root `> 1` of `2B/(B² + 1) = η`. -/
noncomputable def BofEta (η : ℝ) : ℝ := (1 + √(1 - η ^ 2)) / η

lemma etaOfCos_spec {c : ℝ} (hc1 : -1 < c) (hc2 : c < 1) :
    0 < etaOfCos c ∧ etaOfCos c < 1 ∧ etaOfCos c ^ 2 + etaOfCos c - 1 = c := by
  have hs : √(5 + 4 * c) ^ 2 = 5 + 4 * c := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ √(5 + 4 * c) := Real.sqrt_nonneg _
  unfold etaOfCos
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · linear_combination (1 / 4 : ℝ) * hs

lemma BofEta_spec {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    eta (BofEta η) = η ∧ 1 < BofEta η := by
  have hr : √(1 - η ^ 2) ^ 2 = 1 - η ^ 2 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ √(1 - η ^ 2) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · unfold eta BofEta
    have : η ≠ 0 := h0.ne'
    have : 0 < (1 + √(1 - η ^ 2)) / η := by positivity
    rw [div_eq_iff (by positivity)]
    field_simp
    linear_combination (-1 : ℝ) * hr
  · unfold BofEta
    rw [lt_div_iff₀ h0]
    linarith

/-- **`ψ` is a bijection `(1, ∞) → (0, π)`** (Proposition A 7.1, last sentence):
every `t ∈ (0, π)` is `ψ(B)` for exactly one `B > 1`. -/
theorem exists_unique_psi {t : ℝ} (ht0 : 0 < t) (htπ : t < π) :
    ∃! B, 1 < B ∧ psi B = t := by
  have hc1 : -1 < cos t := by
    have := strictAntiOn_cos ⟨ht0.le, htπ.le⟩ ⟨pi_pos.le, le_rfl⟩ htπ
    rwa [cos_pi] at this
  have hc2 : cos t < 1 := by
    have := strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨ht0.le, htπ.le⟩ ht0
    rwa [cos_zero] at this
  obtain ⟨he0, he1, hec⟩ := etaOfCos_spec hc1 hc2
  obtain ⟨hBe, hB1⟩ := BofEta_spec he0 he1
  refine ⟨BofEta (etaOfCos (cos t)), ⟨hB1, ?_⟩, ?_⟩
  · unfold psi
    rw [cosPsi_eq_eta, hBe, hec, arccos_cos ht0.le htπ.le]
  · rintro y ⟨hy1, hyt⟩
    have hpsi : psi y = psi (BofEta (etaOfCos (cos t))) := by
      rw [hyt]; unfold psi; rw [cosPsi_eq_eta, hBe, hec, arccos_cos ht0.le htπ.le]
    exact psi_strictMonoOn.injOn (mem_Ioi.2 hy1) (mem_Ioi.2 hB1) hpsi

/-- **Corollary A 7.2.** For every integer `n ≥ 2` there is exactly one `B_n > 1`
with `ψ(B_n) = π/n`. -/
theorem resonant (n : ℕ) (hn : 2 ≤ n) : ∃! B, 1 < B ∧ psi B = π / n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  exact exists_unique_psi (by positivity) (div_lt_self pi_pos hn')

/-- **Corollary A 7.2, explicit form.**
`B_n = (1 + √(1 − η_n²))/η_n` with `η_n = (√(5 + 4 cos(π/n)) − 1)/2`. -/
theorem resonant_formula (n : ℕ) (hn : 2 ≤ n) :
    1 < BofEta (etaOfCos (cos (π / n))) ∧ psi (BofEta (etaOfCos (cos (π / n)))) = π / n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 < π / n := by positivity
  have htπ : π / n < π := div_lt_self pi_pos hn'
  have hc1 : -1 < cos (π / n) := by
    have := strictAntiOn_cos ⟨ht0.le, htπ.le⟩ ⟨pi_pos.le, le_rfl⟩ htπ
    rwa [cos_pi] at this
  have hc2 : cos (π / n) < 1 := by
    have := strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨ht0.le, htπ.le⟩ ht0
    rwa [cos_zero] at this
  obtain ⟨he0, he1, hec⟩ := etaOfCos_spec hc1 hc2
  obtain ⟨hBe, hB1⟩ := BofEta_spec he0 he1
  refine ⟨hB1, ?_⟩
  unfold psi
  rw [cosPsi_eq_eta, hBe, hec, arccos_cos ht0.le htπ.le]

/-! ### Golden values (A, eq. (7.2)) and Coxeter's ratio -/

lemma eta_phi : eta φ = 2 / √5 := by
  have h := golden_cell_sides.2.1
  have h5 : (0 : ℝ) < √5 := by linarith [one_lt_sqrt5]
  unfold eta
  rw [add_comm, h, div_eq_div_iff (mul_pos h5 phi_pos).ne' h5.ne']
  ring

/-- `cos ψ(φ) = (2√5 − 1)/5`. -/
theorem cosPsi_phi : cosPsi φ = (2 * √5 - 1) / 5 := by
  have h5 : (0 : ℝ) < √5 := by linarith [one_lt_sqrt5]
  rw [cosPsi_eq_eta, eta_phi]
  field_simp
  linear_combination (-4 - 2 * √5) * sqrt5_sq

/-- `tan²(ψ(φ)/2) = 2/φ⁵`. -/
theorem tanSqHalf_phi : tanSqHalf φ = 2 / φ ^ 5 := by
  have hp := phi_pos
  unfold tanSqHalf
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination φ * (φ ^ 6 + φ ^ 4 + 2 * φ ^ 2 + 2 * φ + 2) * phi_sq

/-- **Coxeter's ratio** (Proposition A 7.8 with Corollary A 7.2, `n = 2`):
`ψ(φ + √φ) = π/2`, so `B₂ = φ + √φ`. -/
theorem psi_coxeter : psi (φ + √φ) = π / 2 := by
  have hq : √φ ^ 2 = φ := Real.sq_sqrt phi_pos.le
  have hp := phi_pos
  have hpos : 0 < φ + √φ := by positivity
  have he : eta (φ + √φ) = 1 / φ := by
    unfold eta
    rw [div_eq_div_iff (by positivity) phi_ne_zero]
    linear_combination phi_sq - hq
  unfold psi
  rw [cosPsi_eq_eta, he]
  have : (1 / φ) ^ 2 + 1 / φ - 1 = 0 := by
    field_simp
    linear_combination (-1 : ℝ) * phi_sq
  rw [this, arccos_zero]

theorem coxeter_is_B2 : 1 < φ + √φ ∧ psi (φ + √φ) = π / 2 :=
  ⟨by linarith [one_lt_phi, Real.sqrt_nonneg φ], psi_coxeter⟩

end DoyleFormal
