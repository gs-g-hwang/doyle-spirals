/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Closure
import DoyleFormal.FlowerGeom

/-!
# The closed form is a configuration (paper A, Proposition 5.4 and Proposition 7.1) — Phase 4b

`Closure.lean` takes the centers in the closed form `z(p,q) = X + B^{2p} β^q (0 − X)`,
`β = B e^{iψ}`. Here we check, for `B > 1` and `cos ψ = cosPsi B` (e.g. `ψ = psi B`), that
these circles form a hexagonal circle configuration in the sense of Definition A 2.1:

* `zc_zero_zero`, `zc_one_zero` : the normalization `z(0,0) = 0`, `z(1,0) = 1 + B²`;
* `edge_10`, `edge_01`, `edge_m11` : circles at adjacent lattice points are externally
  tangent (`|z(u+d) − z(u)| = r(u+d) + r(u)` for `d = (1,0), (0,1), (−1,1)`; these three
  directions cover every lattice edge);
* `orient_up`, `orient_down` : both kinds of center triangles are positively oriented.

By Lemma A 2.2 (rigidity, not formalized) a configuration with these radii, tangencies and
orientations is determined by `z(0,0)` and `z(1,0)`; so the closed form *is* `D_B`.

Finally `psi_eq_angle_diff` proves `ψ(B) = θ_O − θ_{P₀}` for the cell triangle
(Proposition A 7.1), so `β = B e^{i(θ_O − θ_{P₀})}`.
-/

namespace DoyleFormal

open Complex EuclideanGeometry

/-- `‖t e^{iθ} − 1‖² = t² + 1 − 2t cos θ`. -/
lemma norm_polar_sub_one_sq (t θ : ℝ) :
    ‖(t : ℂ) * exp (θ * I) - 1‖ ^ 2 = t ^ 2 + 1 - 2 * t * Real.cos θ := by
  have h := norm_sub_polar_sq t 1 θ 0
  rw [show ((1 : ℝ) : ℂ) * exp (((0 : ℝ) : ℂ) * I) = 1 by simp, zero_sub, Real.cos_neg] at h
  rw [h]
  ring

lemma X_neg {B : ℝ} (hB : 1 < B) : X B < 0 := by
  unfold X
  apply div_neg_of_neg_of_pos
  · nlinarith
  · nlinarith

/-- Normalization of Proposition A 5.4: `z(0,0) = 0`. -/
theorem zc_zero_zero (B ψ : ℝ) : zc B ψ 0 0 = 0 := by
  unfold zc
  simp

/-- Normalization of Proposition A 5.4: `z(1,0) = 1 + B²`. -/
theorem zc_one_zero {B : ℝ} (ψ : ℝ) (hB : 1 < B) : zc B ψ 1 0 = ((1 + B ^ 2 : ℝ) : ℂ) := by
  have h : B ^ 2 - 1 ≠ 0 := by nlinarith
  have hz : ((B : ℂ)) ^ (2 * (1 : ℤ)) = ((B ^ 2 : ℝ) : ℂ) := by
    rw [show (2 * (1 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]; push_cast; rfl
  have hr : X B + B ^ 2 * (0 - X B) = 1 + B ^ 2 := by unfold X; field_simp; ring
  unfold zc
  rw [hz, zpow_zero, mul_one, ← hr]
  push_cast
  ring

/-- Difference of two centers, factored through the center `X`. -/
lemma zc_sub_zc {B : ℝ} (ψ : ℝ) (hB : B ≠ 0) (p q dp dq : ℤ) :
    zc B ψ (p + dp) (q + dq) - zc B ψ p q =
      ((B : ℂ) ^ (2 * p + q) * exp (ψ * I) ^ q * (-(X B : ℂ))) *
        ((B : ℂ) ^ (2 * dp + dq) * exp (ψ * I) ^ dq - 1) := by
  have hB' : (B : ℂ) ≠ 0 := ofReal_ne_zero.2 hB
  have he : exp (ψ * I) ≠ 0 := exp_ne_zero _
  have h1 := zc_sub_X ψ hB (p + dp) (q + dq)
  have h2 := zc_sub_X ψ hB p q
  rw [show zc B ψ (p + dp) (q + dq) - zc B ψ p q
      = (zc B ψ (p + dp) (q + dq) - X B) - (zc B ψ p q - X B) by ring, h1, h2,
    show 2 * (p + dp) + (q + dq) = (2 * p + q) + (2 * dp + dq) by ring, zpow_add₀ hB',
    zpow_add₀ he]
  ring

lemma norm_prefactor {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    ‖(B : ℂ) ^ (2 * p + q) * exp (ψ * I) ^ q * (-(X B : ℂ))‖ = rad B p q * (-(X B)) := by
  have hX := X_neg hB
  rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_exp_ofReal_mul_I, one_zpow,
    mul_one, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_neg hX]
  rfl

lemma rad_add {B : ℝ} (hB : 0 < B) (p q dp dq : ℤ) :
    rad B (p + dp) (q + dq) = rad B p q * B ^ (2 * dp + dq) := by
  unfold rad
  rw [show 2 * (p + dp) + (q + dq) = (2 * p + q) + (2 * dp + dq) by ring,
    zpow_add₀ hB.ne']

/-- Tangency along the edge from `(p,q)` in direction `(dp,dq)`, given the one-step factor. -/
lemma edge_of_factor {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q dp dq : ℤ)
    (hfac : ‖(B : ℂ) ^ (2 * dp + dq) * exp (ψ * I) ^ dq - 1‖ * (-(X B))
      = 1 + B ^ (2 * dp + dq)) :
    ‖zc B ψ (p + dp) (q + dq) - zc B ψ p q‖ = rad B (p + dp) (q + dq) + rad B p q := by
  rw [zc_sub_zc ψ (by linarith) p q dp dq, norm_mul, norm_prefactor ψ hB p q,
    rad_add (by linarith) p q dp dq]
  linear_combination rad B p q * hfac

/-- **Tangency in direction `(1,0)`** (the rows). -/
theorem edge_10 {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    ‖zc B ψ (p + 1) q - zc B ψ p q‖ = rad B (p + 1) q + rad B p q := by
  have h := edge_of_factor ψ hB p q 1 0 ?_
  · simpa using h
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have hpos : 0 < B ^ 2 - 1 := by nlinarith
  rw [show (2 * (1 : ℤ) + 0) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, zpow_natCast,
    zpow_zero, mul_one, show (B : ℂ) ^ 2 - 1 = ((B ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  unfold X
  field_simp
  ring

/-- The key identity behind the two oblique tangencies:
`X² (B² + 1 − 2B cos ψ) = (1 + B)²`. -/
lemma X_sq_mul {B : ℝ} (hB : 1 < B) :
    X B ^ 2 * (B ^ 2 + 1 - 2 * B * cosPsi B) = (1 + B) ^ 2 := by
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : B ^ 2 + 1 ≠ 0 := by positivity
  unfold X cosPsi
  field_simp
  ring

/-- **Tangency in direction `(0,1)`.** -/
theorem edge_01 {B ψ : ℝ} (hB : 1 < B) (hcos : Real.cos ψ = cosPsi B) (p q : ℤ) :
    ‖zc B ψ p (q + 1) - zc B ψ p q‖ = rad B p (q + 1) + rad B p q := by
  have h := edge_of_factor ψ hB p q 0 1 ?_
  · simpa using h
  have hX := X_neg hB
  rw [show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one, zpow_one, zpow_one]
  have hsq := norm_polar_sub_one_sq B ψ
  rw [hcos] at hsq
  have hn := norm_nonneg ((B : ℂ) * exp (ψ * I) - 1)
  refine (sq_eq_sq₀ (by nlinarith) (by linarith)).1 ?_
  rw [mul_pow, hsq, neg_sq]
  linear_combination X_sq_mul hB

/-- **Tangency in direction `(−1,1)`.** -/
theorem edge_m11 {B ψ : ℝ} (hB : 1 < B) (hcos : Real.cos ψ = cosPsi B) (p q : ℤ) :
    ‖zc B ψ (p + -1) (q + 1) - zc B ψ p q‖ = rad B (p + -1) (q + 1) + rad B p q := by
  have hB0 : B ≠ 0 := by linarith
  have hX := X_neg hB
  refine edge_of_factor ψ hB p q (-1) 1 ?_
  rw [show (2 * (-1 : ℤ) + 1) = -1 by norm_num, zpow_one, zpow_neg_one, zpow_neg_one,
    show ((B : ℂ))⁻¹ = ((B⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  have hsq := norm_polar_sub_one_sq B⁻¹ ψ
  rw [hcos] at hsq
  have hn := norm_nonneg (((B⁻¹ : ℝ) : ℂ) * exp (ψ * I) - 1)
  have hBi : 0 < B⁻¹ := inv_pos.2 (by linarith)
  refine (sq_eq_sq₀ (by nlinarith) (by linarith)).1 ?_
  rw [mul_pow, hsq, neg_sq]
  have key := X_sq_mul hB
  field_simp
  linear_combination key

/-- `Im(conj(c a) (c b)) = |c|² Im(conj(a) b)`. -/
lemma im_conj_mul_scale (c a b : ℂ) :
    ((starRingEnd ℂ) (c * a) * (c * b)).im = Complex.normSq c * ((starRingEnd ℂ) a * b).im := by
  rw [map_mul, show (starRingEnd ℂ) c * (starRingEnd ℂ) a * (c * b)
      = ((starRingEnd ℂ) c * c) * ((starRingEnd ℂ) a * b) by ring,
    ← Complex.normSq_eq_conj_mul_self, Complex.im_ofReal_mul]

lemma prefactor_ne_zero {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    (B : ℂ) ^ (2 * p + q) * exp (ψ * I) ^ q * (-(X B : ℂ)) ≠ 0 := by
  have hB0 : B ≠ 0 := by linarith
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (ofReal_ne_zero.2 hB0))
    (zpow_ne_zero _ (exp_ne_zero _))) (neg_ne_zero.2 (ofReal_ne_zero.2 (X_ne_zero hB)))

/-- **Upward center triangles `(p,q), (p+1,q), (p,q+1)` are positively oriented.** -/
theorem orient_up {B ψ : ℝ} (hB : 1 < B) (hψ : 0 < Real.sin ψ) (p q : ℤ) :
    0 < ((starRingEnd ℂ) (zc B ψ (p + 1) q - zc B ψ p q) *
      (zc B ψ p (q + 1) - zc B ψ p q)).im := by
  have hB0 : B ≠ 0 := by linarith
  have h1 := zc_sub_zc ψ hB0 p q 1 0
  have h2 := zc_sub_zc ψ hB0 p q 0 1
  simp only [add_zero] at h1 h2
  rw [h1, h2, im_conj_mul_scale]
  apply mul_pos (Complex.normSq_pos.2 (prefactor_ne_zero ψ hB p q))
  simp only [show (2 * (1 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
    show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one, zpow_zero, mul_one]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sq]
  nlinarith [mul_pos (mul_pos (by nlinarith : (0 : ℝ) < B * B - 1) (by linarith : (0 : ℝ) < B)) hψ]

/-- **Downward center triangles `(p,q), (p,q+1), (p−1,q+1)` are positively oriented.** -/
theorem orient_down {B ψ : ℝ} (hB : 1 < B) (hψ : 0 < Real.sin ψ) (p q : ℤ) :
    0 < ((starRingEnd ℂ) (zc B ψ p (q + 1) - zc B ψ p q) *
      (zc B ψ (p + -1) (q + 1) - zc B ψ p q)).im := by
  have hB0 : B ≠ 0 := by linarith
  have h1 := zc_sub_zc ψ hB0 p q 0 1
  have h2 := zc_sub_zc ψ hB0 p q (-1) 1
  simp only [add_zero] at h1
  rw [h1, h2, im_conj_mul_scale]
  apply mul_pos (Complex.normSq_pos.2 (prefactor_ne_zero ψ hB p q))
  rw [show (2 * (0 : ℤ) + 1) = 1 by norm_num, show (2 * (-1 : ℤ) + 1) = -1 by norm_num,
    zpow_one, zpow_one, zpow_neg_one, show ((B : ℂ))⁻¹ = ((B⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hBB : B * B⁻¹ = 1 := mul_inv_cancel₀ hB0
  have hlt : B⁻¹ < B := by
    rw [inv_lt_comm₀ (by linarith) (by linarith)]
    exact (inv_lt_one_of_one_lt₀ hB).trans hB
  have : (B - B⁻¹) * Real.sin ψ > 0 := mul_pos (by linarith) hψ
  nlinarith [this]

/-- **Proposition A 7.1, `ψ = θ_O − θ_{P₀}`.** For the cell triangle `O, P₁, P₀` of `D_B`
(radii `1, B, B²`), the turning angle `ψ(B) = arccos(cosPsi B)` equals the difference of the
angles at `O` and at `P₀`. -/
theorem psi_eq_angle_diff {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {B : ℝ} (hB : 1 < B) (O P₁ P₀ : P)
    (hOP₁ : dist O P₁ = 1 + B) (hP₁P₀ : dist P₁ P₀ = B + B ^ 2)
    (hP₀O : dist P₀ O = B ^ 2 + 1) :
    psi B = ∠ P₁ O P₀ - ∠ O P₀ P₁ := by
  have hB0 : 0 < B := by linarith
  have hB2 : 0 < B ^ 2 := by positivity
  set ν := nu 1 B (B ^ 2) with hν
  have hνpos : 0 < ν := nu_pos one_pos hB0 hB2
  have htO : Real.tan (∠ P₁ O P₀ / 2) = 1 / ν := by
    have := tangent_triple_tan_half one_pos hB0 hB2 O P₁ P₀ hOP₁ hP₁P₀ hP₀O
    rw [this, mul_one]
  have htP : Real.tan (∠ O P₀ P₁ / 2) = 1 / (ν * B ^ 2) := by
    have := tangent_triple_tan_half hB2 one_pos hB0 P₀ O P₁
      (by rw [hP₀O]) (by rw [hOP₁]) (by rw [hP₁P₀])
    rw [this, nu_perm]
  have hαO := mem_Ioo_of_tan_pos (α := ∠ P₁ O P₀ / 2) (by linarith [angle_nonneg P₁ O P₀])
    (by linarith [angle_le_pi P₁ O P₀]) (by rw [htO]; positivity)
  have hαP := mem_Ioo_of_tan_pos (α := ∠ O P₀ P₁ / 2) (by linarith [angle_nonneg O P₀ P₁])
    (by linarith [angle_le_pi O P₀ P₁]) (by rw [htP]; positivity)
  -- `tan` is increasing on `(−π/2, π/2)`, and `1/(νB²) < 1/ν`, so `θ_{P₀} < θ_O`.
  have hlt : ∠ O P₀ P₁ / 2 < ∠ P₁ O P₀ / 2 := by
    have htlt : Real.tan (∠ O P₀ P₁ / 2) < Real.tan (∠ P₁ O P₀ / 2) := by
      rw [htO, htP]
      apply one_div_lt_one_div_of_lt hνpos
      nlinarith [mul_pos hνpos (show (0 : ℝ) < B ^ 2 - 1 by nlinarith)]
    by_contra hc
    rw [not_lt] at hc
    have := Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [hαO.1, Real.pi_pos], hαO.2⟩ ⟨by linarith [hαP.1, Real.pi_pos], hαP.2⟩ hc
    linarith
  unfold psi
  rw [← cell_triangle_turning hB0 O P₁ P₀ hOP₁ hP₁P₀ hP₀O]
  apply Real.arccos_cos
  · linarith
  · linarith [angle_le_pi P₁ O P₀, angle_nonneg O P₀ P₁]

/-- **Phase 4b summary.** With `ψ = psi B`, the closed form of Proposition A 5.4 has the
normalization of `D_B`, tangencies along all lattice edges and positively oriented center
triangles, and `ψ` is the cell-triangle angle difference `θ_O − θ_{P₀}`. -/
theorem closed_form_is_configuration {B : ℝ} (hB : 1 < B) :
    zc B (psi B) 0 0 = 0 ∧ zc B (psi B) 1 0 = ((1 + B ^ 2 : ℝ) : ℂ) ∧
    (∀ p q : ℤ, ‖zc B (psi B) (p + 1) q - zc B (psi B) p q‖ = rad B (p + 1) q + rad B p q) ∧
    (∀ p q : ℤ, ‖zc B (psi B) p (q + 1) - zc B (psi B) p q‖ = rad B p (q + 1) + rad B p q) ∧
    (∀ p q : ℤ, ‖zc B (psi B) (p + -1) (q + 1) - zc B (psi B) p q‖
      = rad B (p + -1) (q + 1) + rad B p q) ∧
    (∀ p q : ℤ, 0 < ((starRingEnd ℂ) (zc B (psi B) (p + 1) q - zc B (psi B) p q) *
      (zc B (psi B) p (q + 1) - zc B (psi B) p q)).im) ∧
    (∀ p q : ℤ, 0 < ((starRingEnd ℂ) (zc B (psi B) p (q + 1) - zc B (psi B) p q) *
      (zc B (psi B) (p + -1) (q + 1) - zc B (psi B) p q)).im) := by
  have hcos := cos_psi hB
  have hsin : 0 < Real.sin (psi B) :=
    Real.sin_pos_of_pos_of_lt_pi (psi_mem_Ioo hB).1 (psi_mem_Ioo hB).2
  exact ⟨zc_zero_zero _ _, zc_one_zero _ hB, edge_10 _ hB, edge_01 hB hcos,
    edge_m11 hB hcos, orient_up hB hsin, orient_down hB hsin⟩

end DoyleFormal
