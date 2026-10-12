/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PaperC

/-!
# Paper C, Proposition 2.1 and Lemma 2.2: the structure of every Doyle spiral (Phase C2)

For a configuration `z` with radii `A^p B^q` (`A, B > 0`, `(A,B) ≠ (1,1)`):

* `IsConfig.shift`: a lattice translation of a configuration is a configuration.
* `step_similarity`: each lattice step is a direct similarity `w ↦ α w + β` with `‖α‖` the
  radius ratio.
* `doyle_structure` (**Proposition C 2.1**): there are `X` and multipliers `α₀, α₁`
  (`‖α₀‖ = A`, `‖α₁‖ = B`) with `z(p,q) − X = α₀^p α₁^q (z(0,0) − X)`, `z(0,0) ≠ X`, and
  `r(p,q) = κ ‖z(p,q) − X‖` with `κ = 1/‖z(0,0) − X‖`. (The additive map `ℒ` of the paper is
  `ℒ(p,q) = p log α₀ + q log α₁`.)
* `doyle_overlap_iff` (**Lemma C 2.2**): `K(u)` and `K(u+v)` overlap or coincide iff
  `‖α^v − 1‖ < κ (1 + ‖α^v‖)`, `α^v = α₀^a α₁^b`.
-/

namespace DoyleFormal

open Complex

theorem IsConfig.shift {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z) (a b : ℤ) :
    IsConfig (fun p q => r (p + a) (q + b)) (fun p q => z (p + a) (q + b)) where
  t10 p q := by
    have := hz.t10 (p + a) (q + b)
    rw [show p + 1 + a = p + a + 1 by ring]; exact this
  t01 p q := by
    have := hz.t01 (p + a) (q + b)
    rw [show q + 1 + b = q + b + 1 by ring]; exact this
  tm11 p q := by
    have := hz.tm11 (p + a) (q + b)
    simp only [show p - 1 + a = p + a - 1 by ring, show q + 1 + b = q + b + 1 by ring]
    exact this
  up p q := by
    have := hz.up (p + a) (q + b)
    simp only [show p + 1 + a = p + a + 1 by ring, show q + 1 + b = q + b + 1 by ring]
    exact this
  down p q := by
    have := hz.down (p + a) (q + b)
    simp only [show p - 1 + a = p + a - 1 by ring, show q + 1 + b = q + b + 1 by ring]
    exact this

section Structure

variable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {z : ℤ → ℤ → ℂ}
  (hz : IsConfig (fun p q => A ^ p * B ^ q) z)
include hA hB hz

/-- Each lattice step is a direct similarity. -/
theorem step_similarity (a b : ℤ) :
    ∃ α β : ℂ, ‖α‖ = A ^ a * B ^ b ∧ ∀ p q, z (p + a) (q + b) = α * z p q + β := by
  have hκ : 0 < A ^ a * B ^ b := by positivity
  have hs := hz.shift a b
  have hs' : IsConfig (fun p q => (A ^ a * B ^ b) * (A ^ p * B ^ q))
      (fun p q => z (p + a) (q + b)) := by
    have : (fun p q => (A ^ a * B ^ b) * (A ^ p * B ^ q)) =
        (fun p q : ℤ => A ^ (p + a) * B ^ (q + b)) := by
      funext p q; rw [zpow_add₀ hA.ne', zpow_add₀ hB.ne']; ring
    rw [this]; exact hs
  obtain ⟨α, β, hα, h⟩ := similar_of_rigidity hκ hs' hz (fun p q => by positivity)
  refine ⟨α, β, ?_, h⟩
  -- the norm of `α` from one edge
  have e1 := hs'.t10 0 0
  have e2 := hz.t10 0 0
  rw [h (0 + 1) 0, h 0 0, show α * z (0 + 1) 0 + β - (α * z 0 0 + β) = α * (z (0 + 1) 0 - z 0 0)
    by ring, norm_mul, e2] at e1
  have hS : 0 < A ^ ((0 : ℤ) + 1) * B ^ (0 : ℤ) + A ^ (0 : ℤ) * B ^ (0 : ℤ) := by positivity
  exact mul_right_cancel₀ hS.ne' (by rw [e1]; ring)

/-- **Proposition C 2.1.** -/
theorem doyle_structure (hAB : A ≠ 1 ∨ B ≠ 1) :
    ∃ X α₀ α₁ : ℂ, ‖α₀‖ = A ∧ ‖α₁‖ = B ∧ z 0 0 ≠ X ∧
      (∀ p q : ℤ, z p q - X = α₀ ^ p * α₁ ^ q * (z 0 0 - X)) ∧
      ∀ p q : ℤ, A ^ p * B ^ q = ‖z p q - X‖ / ‖z 0 0 - X‖ := by
  obtain ⟨α₀, β₀, hn0, h0⟩ := step_similarity hA hB hz 1 0
  obtain ⟨α₁, β₁, hn1, h1⟩ := step_similarity hA hB hz 0 1
  simp only [zpow_one, zpow_zero, mul_one, one_mul, add_zero] at hn0 hn1 h0 h1
  have hα₀ : α₀ ≠ 0 := by intro h; rw [h, norm_zero] at hn0; linarith
  have hα₁ : α₁ ≠ 0 := by intro h; rw [h, norm_zero] at hn1; linarith
  -- the two similarities commute
  have hcomm : α₀ * β₁ + β₀ = α₁ * β₀ + β₁ := by
    have e1 := h0 0 1
    have e2 := h1 1 0
    have e3 := h1 0 0
    have e4 := h0 0 0
    simp only [zero_add] at e1 e2 e3 e4
    rw [e3] at e1; rw [e4] at e2
    have := e1.symm.trans e2
    linear_combination this
  -- a common fixed point
  obtain ⟨X, hX0, hX1⟩ : ∃ X : ℂ, α₀ * X + β₀ = X ∧ α₁ * X + β₁ = X := by
    by_cases h : α₀ = 1
    · have h1' : α₁ ≠ 1 := by
        intro h'; rcases hAB with hA1 | hB1
        · apply hA1; rw [← hn0, h, norm_one]
        · apply hB1; rw [← hn1, h', norm_one]
      have hβ₀ : β₀ = 0 := by
        rw [h] at hcomm
        have : (α₁ - 1) * β₀ = 0 := by linear_combination -hcomm
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1')
      refine ⟨β₁ / (1 - α₁), by rw [h, hβ₀]; ring, ?_⟩
      field_simp [sub_ne_zero.2 (Ne.symm h1')]; ring
    · refine ⟨β₀ / (1 - α₀), by field_simp [sub_ne_zero.2 (Ne.symm h)]; ring, ?_⟩
      have hd : (1 - α₀) ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      field_simp
      linear_combination -hcomm
  -- the lattice exponential
  set w := fun p q => z p q - X with hw
  have hw0 : ∀ p q, w (p + 1) q = α₀ * w p q := fun p q => by
    simp only [hw]; rw [h0]; linear_combination hX0
  have hw1 : ∀ p q, w p (q + 1) = α₁ * w p q := fun p q => by
    simp only [hw]; rw [h1]; linear_combination hX1
  have hrow : ∀ p : ℤ, w p 0 = α₀ ^ p * w 0 0 := by
    intro p
    induction p using Int.induction_on with
    | zero => simp
    | succ n ih => rw [hw0, ih, zpow_add_one₀ hα₀]; ring
    | pred n ih =>
      have := hw0 (-(n : ℤ) - 1) 0
      rw [sub_add_cancel, ih] at this
      rw [zpow_sub_one₀ hα₀]
      field_simp
      linear_combination this.symm
  have hexp : ∀ p q : ℤ, w p q = α₀ ^ p * α₁ ^ q * w 0 0 := by
    intro p q
    induction q using Int.induction_on with
    | zero => simpa using hrow p
    | succ n ih => rw [hw1, ih, zpow_add_one₀ hα₁]; ring
    | pred n ih =>
      have := hw1 p (-(n : ℤ) - 1)
      rw [sub_add_cancel, ih] at this
      rw [zpow_sub_one₀ hα₁]
      field_simp
      linear_combination this.symm
  -- `z(0,0) ≠ X`
  have hz0 : w 0 0 ≠ 0 := by
    intro h
    have e := hz.t10 0 0
    have a := hexp 1 0
    rw [h, mul_zero] at a
    have hz00 : z 0 0 = X := sub_eq_zero.1 h
    have hz10 : z 1 0 = X := sub_eq_zero.1 a
    rw [zero_add, hz10, hz00, sub_self, norm_zero] at e
    simp only [zpow_one, zpow_zero, mul_one] at e
    linarith
  refine ⟨X, α₀, α₁, hn0, hn1, fun h => hz0 (by simp [hw, h]), fun p q => hexp p q,
    fun p q => ?_⟩
  have := hexp p q
  simp only [hw] at this hz0
  rw [this, norm_mul, norm_mul, norm_zpow, norm_zpow, hn0, hn1]
  field_simp [norm_ne_zero_iff.2 hz0]

omit hA hB hz in
/-- **Lemma C 2.2.** With the structure of `doyle_structure`, `K(u)` and `K(u+v)` overlap or
coincide iff `‖α^v − 1‖ < κ (1 + ‖α^v‖)`, where `α^v = α₀^a α₁^b` and `κ = 1/‖z(0,0) − X‖`. -/
theorem doyle_overlap_iff {X α₀ α₁ : ℂ} (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0) (hX : z 0 0 ≠ X)
    (hexp : ∀ p q : ℤ, z p q - X = α₀ ^ p * α₁ ^ q * (z 0 0 - X))
    (hrad : ∀ p q : ℤ, A ^ p * B ^ q = ‖z p q - X‖ / ‖z 0 0 - X‖) (p q a b : ℤ) :
    ‖z (p + a) (q + b) - z p q‖ < A ^ (p + a) * B ^ (q + b) + A ^ p * B ^ q ↔
      ‖α₀ ^ a * α₁ ^ b - 1‖ < (1 / ‖z 0 0 - X‖) * (1 + ‖α₀ ^ a * α₁ ^ b‖) := by
  have hd : 0 < ‖z 0 0 - X‖ := norm_pos_iff.2 (sub_ne_zero.2 hX)
  set g := α₀ ^ p * α₁ ^ q
  have hg : 0 < ‖g‖ := norm_pos_iff.2 (mul_ne_zero (zpow_ne_zero _ hα₀) (zpow_ne_zero _ hα₁))
  have hdiff : z (p + a) (q + b) - z p q = g * (α₀ ^ a * α₁ ^ b - 1) * (z 0 0 - X) := by
    have e1 := hexp (p + a) (q + b)
    have e2 := hexp p q
    rw [zpow_add₀ hα₀, zpow_add₀ hα₁] at e1
    linear_combination e1 - e2
  have hr1 : A ^ (p + a) * B ^ (q + b) = ‖g‖ * ‖α₀ ^ a * α₁ ^ b‖ := by
    rw [hrad, hexp, zpow_add₀ hα₀, zpow_add₀ hα₁, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_mul]
    field_simp
    rw [norm_mul]
  have hr0 : A ^ p * B ^ q = ‖g‖ := by
    rw [hrad, hexp, norm_mul]; simp only [g]; field_simp
  rw [hdiff, norm_mul, norm_mul, hr1, hr0]
  constructor
  · intro h
    have : ‖α₀ ^ a * α₁ ^ b - 1‖ * (‖g‖ * ‖z 0 0 - X‖) <
        (1 + ‖α₀ ^ a * α₁ ^ b‖) * ‖g‖ := by nlinarith
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hd]
    nlinarith
  · intro h
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hd] at h
    nlinarith

end Structure

end DoyleFormal
