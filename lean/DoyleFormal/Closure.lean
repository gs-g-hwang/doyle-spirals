/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Golden
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Closing up around `X` (paper A, Proposition 7.3)

The centers and radii of `D_B` are taken in the closed form of Proposition A 5.4:
`z(p,q) = X + B^{2p} β^q (0 − X)` with `β = B e^{iψ}`, and `r(p,q) = B^{2p+q}`.
Proposition A 5.4 itself (that the geometric configuration has this form) is not formalized.

* `closure_step`   : `z(p−j, q+2j) − X = e^{2ijψ}(z(p,q) − X)` and `r(p−j, q+2j) = r(p,q)`.
* `same_circle_iff`: `K(u) = K(u')` iff `u' − u = j(−1,2)` with `jψ ∈ πℤ`.
* `closes_after_one_turn` : the first return happens after exactly one turn iff `ψ = π/n`.
-/

namespace DoyleFormal

open Complex

/-- `β = B e^{iψ}`. -/
noncomputable def beta (B ψ : ℝ) : ℂ := (B : ℂ) * exp (ψ * I)

/-- Centers, in the closed form of Proposition A 5.4. -/
noncomputable def zc (B ψ : ℝ) (p q : ℤ) : ℂ :=
  (X B : ℂ) + (B : ℂ) ^ (2 * p) * beta B ψ ^ q * (0 - (X B : ℂ))

/-- Radii `r(p,q) = B^{2p+q}`. -/
noncomputable def rad (B : ℝ) (p q : ℤ) : ℝ := B ^ (2 * p + q)

lemma X_ne_zero {B : ℝ} (hB : 1 < B) : X B ≠ 0 := by
  unfold X
  have h1 : B ^ 2 + 1 ≠ 0 := by positivity
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  exact div_ne_zero (neg_ne_zero.2 h1) h2

lemma zc_sub_X {B : ℝ} (ψ : ℝ) (hB : B ≠ 0) (p q : ℤ) :
    zc B ψ p q - X B = (B : ℂ) ^ (2 * p + q) * exp (ψ * I) ^ q * (-(X B : ℂ)) := by
  have hB' : (B : ℂ) ≠ 0 := ofReal_ne_zero.2 hB
  unfold zc beta
  rw [mul_zpow, zpow_add₀ hB']
  ring

/-- **Proposition A 7.3, first part.** -/
theorem closure_step {B : ℝ} (ψ : ℝ) (hB : B ≠ 0) (j p q : ℤ) :
    zc B ψ (p - j) (q + 2 * j) - X B = exp (2 * j * ψ * I) * (zc B ψ p q - X B) ∧
      rad B (p - j) (q + 2 * j) = rad B p q := by
  have he : exp (ψ * I) ≠ 0 := exp_ne_zero _
  refine ⟨?_, ?_⟩
  · rw [zc_sub_X ψ hB, zc_sub_X ψ hB, show 2 * (p - j) + (q + 2 * j) = 2 * p + q by ring,
      zpow_add₀ he]
    have h2 : exp (2 * j * ψ * I) = exp (ψ * I) ^ (2 * j) := by
      rw [← exp_int_mul]; congr 1; push_cast; ring
    rw [h2]
    ring
  · unfold rad
    congr 1
    ring

lemma zc_sub_X_ne_zero {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) : zc B ψ p q - X B ≠ 0 := by
  have hB0 : B ≠ 0 := by linarith
  rw [zc_sub_X ψ hB0]
  have hX : (X B : ℂ) ≠ 0 := ofReal_ne_zero.2 (X_ne_zero hB)
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (ofReal_ne_zero.2 hB0))
    (zpow_ne_zero _ (exp_ne_zero _))) (neg_ne_zero.2 hX)

lemma exp_two_mul_eq_one_iff (j : ℤ) (ψ : ℝ) :
    exp (2 * j * ψ * I) = 1 ↔ ∃ k : ℤ, (j : ℝ) * ψ = k * Real.pi := by
  rw [exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : ((2 * j * ψ : ℝ) : ℂ) * I = ((2 * k * Real.pi : ℝ) : ℂ) * I := by
      push_cast; rw [hk]; ring
    have := ofReal_injective (mul_right_cancel₀ I_ne_zero hk')
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : ((2 * j * ψ : ℝ) : ℂ) = ((2 * k * Real.pi : ℝ) : ℂ) := by
      congr 1; linarith
    push_cast at hk'
    rw [hk']
    ring

/-- **Proposition A 7.3, second part.** Two lattice points carry the same circle
(same radius and same center) iff they differ by `j(−1,2)` with `jψ ∈ πℤ`. -/
theorem same_circle_iff {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q p' q' : ℤ) :
    (rad B p' q' = rad B p q ∧ zc B ψ p' q' = zc B ψ p q) ↔
      ∃ j : ℤ, p' = p - j ∧ q' = q + 2 * j ∧ ∃ k : ℤ, (j : ℝ) * ψ = k * Real.pi := by
  have hB0 : B ≠ 0 := by linarith
  constructor
  · rintro ⟨hr, hz⟩
    have hexp : 2 * p' + q' = 2 * p + q :=
      zpow_right_injective₀ (by linarith : (0 : ℝ) < B) (ne_of_gt hB) hr
    refine ⟨p - p', by ring, by omega, ?_⟩
    rw [← exp_two_mul_eq_one_iff]
    have hstep := (closure_step ψ hB0 (p - p') p q).1
    rw [show p - (p - p') = p' by ring, show q + 2 * (p - p') = q' by omega, hz] at hstep
    have hw := zc_sub_X_ne_zero ψ hB p q
    have : (exp (2 * ((p - p' : ℤ) : ℂ) * ψ * I) - 1) * (zc B ψ p q - X B) = 0 := by
      linear_combination -hstep
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hw
  · rintro ⟨j, rfl, rfl, hk⟩
    obtain ⟨hstep, hrad⟩ := closure_step ψ hB0 j p q
    refine ⟨hrad, ?_⟩
    rw [(exp_two_mul_eq_one_iff j ψ).2 hk, one_mul] at hstep
    linear_combination hstep

/-- **Proposition A 7.3, last sentence.** For `ψ ∈ (0, π)`, the circles first repeat
(`jψ ∈ πℤ` for `j = n` but for no `0 < j < n`) with `nψ = π`, i.e. after exactly one turn
around `X`, iff `ψ = π/n`. -/
theorem closes_after_one_turn {ψ : ℝ} (hψ0 : 0 < ψ) (hψπ : ψ < Real.pi) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) * ψ = Real.pi ∧ ∀ j : ℕ, 0 < j → j < n → ∀ k : ℤ, (j : ℝ) * ψ ≠ k * Real.pi) ↔
      ψ = Real.pi / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨h, -⟩
    field_simp
    linarith
  · intro h
    refine ⟨by rw [h]; field_simp, ?_⟩
    intro j hj0 hjn k hk
    have hj0' : (0 : ℝ) < j := by exact_mod_cast hj0
    have hjn' : (j : ℝ) < n := by exact_mod_cast hjn
    rw [h] at hk
    have hpos : 0 < (k : ℝ) * Real.pi := by
      rw [← hk]; positivity
    have hlt : (k : ℝ) * Real.pi < 1 * Real.pi := by
      rw [← hk, mul_div_assoc', div_lt_iff₀ hn']
      nlinarith [Real.pi_pos]
    have hk0 : (0 : ℝ) < k := by
      by_contra hc; nlinarith [not_lt.mp hc, Real.pi_pos]
    have hk1 : (k : ℝ) < 1 := lt_of_mul_lt_mul_right hlt Real.pi_pos.le
    have : (0 : ℤ) < k := by exact_mod_cast hk0
    have : k < (1 : ℤ) := by exact_mod_cast hk1
    omega

end DoyleFormal
