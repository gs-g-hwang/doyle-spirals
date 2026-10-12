/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.TurningAngle
import Mathlib.NumberTheory.Niven

/-!
# The resonant parameters are algebraic (paper A, Corollary 7.2)

`B_n = (1 + √(1 − η_n²))/η_n` with `η_n = (√(5 + 4 cos(π/n)) − 1)/2`, and
`cos(π/n)` is algebraic (Mathlib, `Real.isAlgebraic_cos_rat_mul_pi`), so `B_n` is algebraic
over `ℤ`. The same holds for the golden ratio and Coxeter's ratio `φ + √φ`.
-/

namespace DoyleFormal

open Real

lemma isAlgebraic_sqrt {a : ℝ} (ha0 : 0 ≤ a) (ha : IsAlgebraic ℤ a) : IsAlgebraic ℤ (√a) :=
  IsAlgebraic.of_pow two_pos (by rw [Real.sq_sqrt ha0]; exact ha)

lemma isAlgebraic_nat (n : ℕ) : IsAlgebraic ℤ (n : ℝ) := isAlgebraic_natCast n

/-- **Corollary A 7.2: each `B_n` is an algebraic number.** -/
theorem resonant_isAlgebraic (n : ℕ) (hn : 2 ≤ n) :
    IsAlgebraic ℤ (BofEta (etaOfCos (cos (π / n)))) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 < π / n := by positivity
  have htπ : π / n < π := div_lt_self pi_pos hn'
  have hc1 : -1 < cos (π / n) := by
    have := strictAntiOn_cos ⟨ht0.le, htπ.le⟩ ⟨pi_pos.le, le_rfl⟩ htπ
    rwa [cos_pi] at this
  -- cos(π/n) is algebraic
  have hc : IsAlgebraic ℤ (cos (π / n)) := by
    have := Real.isAlgebraic_cos_rat_mul_pi (1 / (n : ℚ))
    rwa [show ((1 / (n : ℚ) : ℚ) : ℝ) * π = π / n by push_cast; ring] at this
  -- η_n is algebraic
  have h5 : IsAlgebraic ℤ (5 + 4 * cos (π / n)) := by
    have := (isAlgebraic_nat 5).add ((isAlgebraic_nat 4).mul hc)
    simpa using this
  have hs := isAlgebraic_sqrt (by linarith) h5
  have hη : IsAlgebraic ℤ (etaOfCos (cos (π / n))) := by
    unfold etaOfCos
    have := (hs.sub isAlgebraic_one).mul (isAlgebraic_nat 2).inv
    simpa [div_eq_mul_inv] using this
  -- B_n is algebraic
  have hc2 : cos (π / n) < 1 := by
    have := strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨ht0.le, htπ.le⟩ ht0
    rwa [cos_zero] at this
  obtain ⟨he0, he1, -⟩ := etaOfCos_spec hc1 hc2
  have hr := isAlgebraic_sqrt (by nlinarith) (isAlgebraic_one.sub (hη.pow 2))
  unfold BofEta
  have := (isAlgebraic_one.add hr).mul hη.inv
  simpa [div_eq_mul_inv] using this

/-- The golden ratio and Coxeter's ratio `B₂ = φ + √φ` are algebraic. -/
theorem phi_isAlgebraic : IsAlgebraic ℤ φ ∧ IsAlgebraic ℤ (φ + √φ) := by
  have h5 : IsAlgebraic ℤ (√5) := isAlgebraic_sqrt (by norm_num) (by simpa using isAlgebraic_nat 5)
  have hφ : IsAlgebraic ℤ φ := by
    unfold φ
    have := (isAlgebraic_one.add h5).mul (isAlgebraic_nat 2).inv
    simpa [div_eq_mul_inv] using this
  exact ⟨hφ, hφ.add (isAlgebraic_sqrt phi_pos.le hφ)⟩

end DoyleFormal
