/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Rigidity

/-!
# Consequences of the closed form — Phase 4c

By `prop_5_4` the closed form `zc B (psi B)` *is* `D_B`. Here:

* `T_map`, `S_map`, `S_comm_T` (Proposition A 5.4, the maps): `T(z) = X + B²(z − X)` and
  `S(z) = X + β(z − X)` shift the labels by `(1,0)` and `(0,1)`, commute and fix `X`.
* `row_ratios`, `golden_section_iff` (Theorem A 6.1): along a row,
  `|z(p+1,q) − z(p,q)| = (B²−1)|z(p,q) − X|` and `|z(p+1,q) − X| = B²|z(p,q) − X|`, and the
  golden-section condition holds iff `B = φ`.
* `overlap_iff`, `overlap_s0`, `overlap_s1`, `overlap_sm1` (Lemma B 5.1): the overlap criterion
  for `K(u)` and `K(u+w)`, `w = (a,b)`, `s = 2a + b`, in the cases used in paper B.
-/

namespace DoyleFormal

open Complex

/-! ### The maps `T` and `S` of Proposition A 5.4 -/

theorem T_map {B : ℝ} (ψ : ℝ) (hB : B ≠ 0) (p q : ℤ) :
    (X B : ℂ) + (B : ℂ) ^ 2 * (zc B ψ p q - X B) = zc B ψ (p + 1) q := by
  have hB' : (B : ℂ) ≠ 0 := ofReal_ne_zero.2 hB
  have h1 := zc_sub_X ψ hB p q
  have h2 := zc_sub_X ψ hB (p + 1) q
  rw [show 2 * (p + 1) + q = (2 * p + q) + 2 by ring, zpow_add₀ hB',
    show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h2
  linear_combination (B : ℂ) ^ 2 * h1 - h2

theorem S_map {B : ℝ} (ψ : ℝ) (hB : B ≠ 0) (p q : ℤ) :
    (X B : ℂ) + beta B ψ * (zc B ψ p q - X B) = zc B ψ p (q + 1) := by
  have hB' : (B : ℂ) ≠ 0 := ofReal_ne_zero.2 hB
  have he : exp (ψ * I) ≠ 0 := exp_ne_zero _
  have h1 := zc_sub_X ψ hB p q
  have h2 := zc_sub_X ψ hB p (q + 1)
  rw [show 2 * p + (q + 1) = (2 * p + q) + 1 by ring, zpow_add_one₀ hB',
    zpow_add_one₀ he] at h2
  unfold beta
  linear_combination (B : ℂ) * exp (ψ * I) * h1 - h2

/-- `T` and `S` commute and both fix `X`. -/
theorem S_comm_T (B ψ : ℝ) (z : ℂ) :
    (X B : ℂ) + beta B ψ * (((X B : ℂ) + (B : ℂ) ^ 2 * (z - X B)) - X B)
      = (X B : ℂ) + (B : ℂ) ^ 2 * (((X B : ℂ) + beta B ψ * (z - X B)) - X B) := by
  ring

/-! ### Theorem A 6.1 -/

lemma norm_zc_sub_X_pos {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    0 < ‖zc B ψ p q - X B‖ := norm_pos_iff.2 (zc_sub_X_ne_zero ψ hB p q)

/-- **Theorem A 6.1, the two ratio identities.** -/
theorem row_ratios {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    ‖zc B ψ (p + 1) q - zc B ψ p q‖ = (B ^ 2 - 1) * ‖zc B ψ p q - X B‖ ∧
      ‖zc B ψ (p + 1) q - X B‖ = B ^ 2 * ‖zc B ψ p q - X B‖ := by
  have hT := T_map ψ (by linarith : B ≠ 0) p q
  have hpos : 0 < B ^ 2 - 1 := by nlinarith
  constructor
  · rw [← hT, show (X B : ℂ) + (B : ℂ) ^ 2 * (zc B ψ p q - X B) - zc B ψ p q
        = ((B ^ 2 - 1 : ℝ) : ℂ) * (zc B ψ p q - X B) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  · rw [← hT, show (X B : ℂ) + (B : ℂ) ^ 2 * (zc B ψ p q - X B) - X B
        = ((B ^ 2 : ℝ) : ℂ) * (zc B ψ p q - X B) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Theorem A 6.1, the equivalence.** `z(p,q)` divides the segment from `z(p+1,q)` to `X`
in the golden section (the two ratios agree) iff `B = φ`. -/
theorem golden_section_iff {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    ‖zc B ψ (p + 1) q - zc B ψ p q‖ / ‖zc B ψ p q - X B‖
      = ‖zc B ψ (p + 1) q - X B‖ / ‖zc B ψ (p + 1) q - zc B ψ p q‖ ↔ B = φ := by
  obtain ⟨h1, h2⟩ := row_ratios ψ hB p q
  have hd := norm_zc_sub_X_pos ψ hB p q
  have hpos : 0 < B ^ 2 - 1 := by nlinarith
  rw [h1, h2, mul_div_assoc, div_self hd.ne', mul_one,
    mul_div_mul_right _ _ hd.ne', ← golden_iff (by linarith : (0 : ℝ) < B)]
  rw [eq_div_iff hpos.ne']
  constructor
  · intro h
    have : (B ^ 2 - 1 - B) * (B ^ 2 - 1 + B) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · have : 0 < B ^ 2 := by positivity
      linarith
  · intro h
    rw [h]; ring

/-! ### Lemma B 5.1 (overlap criterion) -/

lemma exp_zpow_eq (ψ : ℝ) (b : ℤ) : exp (ψ * I) ^ b = exp (((b * ψ : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- **Lemma B 5.1, general form.** The circles `K(p,q)` and `K(p+a,q+b)` overlap
(distance of centers less than the sum of the radii) iff
`X² (ρ² + 1 − 2ρ cos(bψ)) < (1 + ρ)²` with `ρ = B^{2a+b}`. -/
theorem overlap_iff {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ < rad B (p + a) (q + b) + rad B p q ↔
      X B ^ 2 * ((B ^ (2 * a + b)) ^ 2 + 1 - 2 * B ^ (2 * a + b) * Real.cos (b * ψ))
        < (1 + B ^ (2 * a + b)) ^ 2 := by
  have hB0 : 0 < B := by linarith
  have hX := X_neg hB
  have hr : 0 < rad B p q := by unfold rad; positivity
  have hρ : 0 < B ^ (2 * a + b) := zpow_pos hB0 _
  set ρ := B ^ (2 * a + b) with hρdef
  have hfac : (B : ℂ) ^ (2 * a + b) * exp (ψ * I) ^ b - 1
      = ((ρ : ℝ) : ℂ) * exp (((b * ψ : ℝ) : ℂ) * I) - 1 := by
    rw [exp_zpow_eq, hρdef, Complex.ofReal_zpow]
  rw [zc_sub_zc ψ hB0.ne' p q a b, norm_mul, norm_prefactor ψ hB p q, rad_add hB0 p q a b,
    hfac, ← hρdef]
  have hsq := norm_polar_sub_one_sq ρ (b * ψ)
  set N := ‖((ρ : ℝ) : ℂ) * exp (((b * ψ : ℝ) : ℂ) * I) - 1‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  rw [← hsq]
  have hXN : 0 ≤ -X B * N := mul_nonneg (by linarith) hN0
  have e1 : rad B p q * -X B * N < rad B p q * ρ + rad B p q ↔ -X B * N < 1 + ρ := by
    rw [show rad B p q * ρ + rad B p q = rad B p q * (1 + ρ) by ring, mul_assoc]
    exact ⟨fun h => lt_of_mul_lt_mul_left h hr.le, fun h => mul_lt_mul_of_pos_left h hr⟩
  have e2 : -X B * N < 1 + ρ ↔ (-X B * N) ^ 2 < (1 + ρ) ^ 2 :=
    ⟨fun h => pow_lt_pow_left₀ h hXN two_ne_zero,
      fun h => lt_of_pow_lt_pow_left₀ 2 (by linarith) h⟩
  rw [e1, e2, mul_pow, neg_sq]

/-- **Lemma B 5.1, case `s = 0`.** For `w = j(−1,2)`, the circles overlap iff
`X² sin²(jψ) < 1`, i.e. `|sin jψ| < 1/|X| = tanh log B`. -/
theorem overlap_s0 {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q j : ℤ) :
    ‖zc B ψ (p + -j) (q + 2 * j) - zc B ψ p q‖ < rad B (p + -j) (q + 2 * j) + rad B p q ↔
      X B ^ 2 * Real.sin (j * ψ) ^ 2 < 1 := by
  rw [overlap_iff ψ hB p q (-j) (2 * j), show 2 * -j + 2 * j = 0 by ring, zpow_zero]
  have hc : Real.cos (((2 * j : ℤ) : ℝ) * ψ) = 1 - 2 * Real.sin (j * ψ) ^ 2 := by
    rw [show (((2 * j : ℤ) : ℝ) * ψ) = 2 * (j * ψ) by push_cast; ring, Real.cos_two_mul,
      Real.cos_sq']
    ring
  rw [hc, show X B ^ 2 * (1 ^ 2 + 1 - 2 * 1 * (1 - 2 * Real.sin (j * ψ) ^ 2)) =
      4 * (X B ^ 2 * Real.sin (j * ψ) ^ 2) by ring]
  constructor <;> intro h <;> linarith

/-- **Lemma B 5.1, case `s = 1`.** If `2a + b = 1` and `cos ψ = cosPsi B` (e.g. `ψ = psi B`),
the circles overlap iff `cos ψ < cos(bψ)`, i.e. `sin²(bψ/2) < sin²(ψ/2)`. -/
theorem overlap_s1 {B ψ : ℝ} (hB : 1 < B) (hcos : Real.cos ψ = cosPsi B) (p q a b : ℤ)
    (hs : 2 * a + b = 1) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ < rad B (p + a) (q + b) + rad B p q ↔
      Real.cos ψ < Real.cos (b * ψ) := by
  rw [overlap_iff ψ hB p q a b, hs, zpow_one]
  have key := X_sq_mul hB
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  have hpos : 0 < X B ^ 2 * (2 * B) := mul_pos hX2 (by linarith)
  rw [hcos]
  have e : X B ^ 2 * (B ^ 2 + 1 - 2 * B * Real.cos (b * ψ)) - (1 + B) ^ 2
      = X B ^ 2 * (2 * B) * (cosPsi B - Real.cos (b * ψ)) := by linear_combination key
  constructor
  · intro h
    have := neg_of_mul_neg_right (show X B ^ 2 * (2 * B) * (cosPsi B - Real.cos (b * ψ)) < 0 by
      linarith) hpos.le
    linarith
  · intro h
    have := mul_neg_of_pos_of_neg hpos (show cosPsi B - Real.cos (b * ψ) < 0 by linarith)
    linarith

/-- Overlap is symmetric in the two circles. -/
lemma overlap_symm {B ψ : ℝ} (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ < rad B (p + a) (q + b) + rad B p q ↔
      ‖zc B ψ (p + a + -a) (q + b + -b) - zc B ψ (p + a) (q + b)‖
        < rad B (p + a + -a) (q + b + -b) + rad B (p + a) (q + b) := by
  rw [show p + a + -a = p by ring, show q + b + -b = q by ring,
    norm_sub_rev (zc B ψ p q) (zc B ψ (p + a) (q + b)),
    add_comm (rad B p q) (rad B (p + a) (q + b))]

/-- **Lemma B 5.1, case `s = −1`.** If `2a + b = −1`, the circles overlap iff
`cos ψ < cos(bψ)`. -/
theorem overlap_sm1 {B ψ : ℝ} (hB : 1 < B) (hcos : Real.cos ψ = cosPsi B) (p q a b : ℤ)
    (hs : 2 * a + b = -1) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ < rad B (p + a) (q + b) + rad B p q ↔
      Real.cos ψ < Real.cos (b * ψ) := by
  rw [overlap_symm, overlap_s1 hB hcos (p + a) (q + b) (-a) (-b) (by omega)]
  push_cast
  rw [neg_mul, Real.cos_neg]

end DoyleFormal
