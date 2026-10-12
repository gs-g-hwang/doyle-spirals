/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Consequences

/-!
# Transport, the Ω form of the overlap test, and the first overlap — Phase 4d

* `transport` (Lemma A 2.2, second part, for lattice translations): a direct similarity
  `w ↦ c w + d` that maps `K(0,0), K(1,0)` to `K(p₀,q₀), K(p₀+1,q₀)` and scales the radius
  function correctly maps every `K(p,q)` to `K(p+p₀,q+q₀)`.
* `inversive_eq`, `overlap_iff_Omega`, `tangent_iff_Omega` (Lemma B 5.1, eqs. (6)–(7)): with
  `Ω(w) = sinh²(sλ/2)/sinh²λ + coth²λ sin²(bψ/2)`, the inversive distance of `K(u)` and
  `K(u+w)` is `2Ω − 1`; overlap iff `Ω < 1`, tangency iff `Ω = 1`.
* `overlap_s0_tanh` (Lemma B 5.1, case `s = 0`): overlap iff `|sin jψ| < tanh log B`.
* `no_overlap_far` (Lemma B 5.1, "in particular"): overlapping circles have `|s| ≤ 1`.
* The analytic core of Theorem B 5.2 (first overlap), for `ψ = psi B`, `t = π/ψ`:
  `E_no_overlap_before`, `O_no_overlap_before`, `sin_floor_mul`, `O_no_overlap_floor`,
  `O_overlap_ceil`. The translation into rings (`u, u+w` lie in the `m`-ring ball iff
  `‖w‖ ≤ 2m`) is elementary lattice combinatorics and is not formalized.
-/

namespace DoyleFormal

open Complex

/-! ### Lemma A 2.2, transport along lattice translations -/

lemma orient_affine (c d a b e : ℂ) :
    orient (c * a + d) (c * b + d) (c * e + d) = Complex.normSq c * orient a b e := by
  unfold orient
  rw [show c * b + d - (c * a + d) = c * (b - a) by ring,
    show c * e + d - (c * a + d) = c * (e - a) by ring, im_conj_mul_scale]

/-- **Lemma A 2.2, transport part, for translations of the lattice.** -/
theorem transport {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z) (c d : ℂ) (hc : c ≠ 0)
    (p₀ q₀ : ℤ) (hr : ∀ p q, r (p + p₀) (q + q₀) = ‖c‖ * r p q)
    (h0 : c * z 0 0 + d = z p₀ q₀) (h1 : c * z 1 0 + d = z (1 + p₀) q₀) :
    ∀ p q, c * z p q + d = z (p + p₀) (q + q₀) := by
  -- both sides are configurations with radii `r (p + p₀) (q + q₀)`
  have hw : IsConfig (fun p q => r (p + p₀) (q + q₀)) (fun p q => c * z p q + d) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p q
      rw [show c * z (p + 1) q + d - (c * z p q + d) = c * (z (p + 1) q - z p q) by ring,
        norm_mul, hz.t10, hr, hr]; ring
    · intro p q
      rw [show c * z p (q + 1) + d - (c * z p q + d) = c * (z p (q + 1) - z p q) by ring,
        norm_mul, hz.t01, hr, hr]; ring
    · intro p q
      rw [show c * z (p - 1) (q + 1) + d - (c * z p q + d) = c * (z (p - 1) (q + 1) - z p q)
        by ring, norm_mul, hz.tm11, hr, hr]; ring
    · intro p q
      rw [orient_affine]; exact mul_pos (Complex.normSq_pos.2 hc) (hz.up p q)
    · intro p q
      rw [orient_affine]; exact mul_pos (Complex.normSq_pos.2 hc) (hz.down p q)
  have hs : IsConfig (fun p q => r (p + p₀) (q + q₀)) (fun p q => z (p + p₀) (q + q₀)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p q
      have := hz.t10 (p + p₀) (q + q₀)
      rw [show p + 1 + p₀ = p + p₀ + 1 by ring]; exact this
    · intro p q
      have := hz.t01 (p + p₀) (q + q₀)
      rw [show q + 1 + q₀ = q + q₀ + 1 by ring]; exact this
    · intro p q
      have := hz.tm11 (p + p₀) (q + q₀)
      simp only [show p - 1 + p₀ = p + p₀ - 1 by ring, show q + 1 + q₀ = q + q₀ + 1 by ring]
      exact this
    · intro p q
      have := hz.up (p + p₀) (q + q₀)
      simp only [show p + 1 + p₀ = p + p₀ + 1 by ring, show q + 1 + q₀ = q + q₀ + 1 by ring]
      exact this
    · intro p q
      have := hz.down (p + p₀) (q + q₀)
      simp only [show p - 1 + p₀ = p + p₀ - 1 by ring, show q + 1 + q₀ = q + q₀ + 1 by ring]
      exact this
  exact rigidity hw hs (by simpa using h0) (by simpa using h1)

/-! ### The Ω form of Lemma B 5.1 -/

/-- `Ω(w) = sinh²(sλ/2)/sinh²λ + coth²λ · sin²(bψ/2)` with `λ = log B`, `s = 2a + b`. -/
noncomputable def Omega (B ψ : ℝ) (a b : ℤ) : ℝ :=
  Real.sinh (((2 * a + b : ℤ) : ℝ) * Real.log B / 2) ^ 2 / Real.sinh (Real.log B) ^ 2
    + (Real.cosh (Real.log B) / Real.sinh (Real.log B)) ^ 2 * Real.sin (b * ψ / 2) ^ 2

lemma sinh_sq_half (x : ℝ) : Real.sinh (x / 2) ^ 2 = (Real.cosh x - 1) / 2 := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have h2 := Real.cosh_sq (x / 2)
  linarith

lemma cos_eq_one_sub_two_sin_sq (y : ℝ) : Real.cos y = 1 - 2 * Real.sin (y / 2) ^ 2 := by
  have h := Real.cos_two_mul (y / 2)
  rw [show 2 * (y / 2) = y by ring] at h
  have h2 := Real.sin_sq_add_cos_sq (y / 2)
  linarith

/-- The squared distance of two centers. -/
lemma dist_sq {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ ^ 2
      = rad B p q ^ 2 * X B ^ 2 *
        ((B ^ (2 * a + b)) ^ 2 + 1 - 2 * B ^ (2 * a + b) * Real.cos (b * ψ)) := by
  have hB0 : 0 < B := by linarith
  have hfac : (B : ℂ) ^ (2 * a + b) * exp (ψ * I) ^ b - 1
      = ((B ^ (2 * a + b) : ℝ) : ℂ) * exp (((b * ψ : ℝ) : ℂ) * I) - 1 := by
    rw [exp_zpow_eq, Complex.ofReal_zpow]
  rw [zc_sub_zc ψ hB0.ne' p q a b, norm_mul, norm_prefactor ψ hB p q, hfac, mul_pow,
    norm_polar_sub_one_sq, mul_pow, neg_sq]

/-- **Lemma B 5.1, eq. (7).** The inversive distance of `K(p,q)` and `K(p+a,q+b)` is `2Ω − 1`. -/
theorem inversive_eq {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) :
    (‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ ^ 2 - rad B p q ^ 2 - rad B (p + a) (q + b) ^ 2)
      / (2 * rad B p q * rad B (p + a) (q + b)) = 2 * Omega B ψ a b - 1 := by
  have hB0 : 0 < B := by linarith
  have hr : 0 < rad B p q := by unfold rad; exact zpow_pos hB0 _
  set ρ := B ^ (2 * a + b) with hρ
  have hρ0 : 0 < ρ := zpow_pos hB0 _
  have hσ := cos_eq_one_sub_two_sin_sq (b * ψ)
  rw [dist_sq ψ hB, rad_add hB0, ← hρ, hσ]
  -- hyperbolic functions of `λ = log B` and of `sλ`
  have hsh : Real.sinh (Real.log B) = (B - B⁻¹) / 2 := Real.sinh_log hB0
  have hch : Real.cosh (Real.log B) = (B + B⁻¹) / 2 := Real.cosh_log hB0
  have hsl : ((2 * a + b : ℤ) : ℝ) * Real.log B = Real.log ρ := by rw [hρ, Real.log_zpow]
  have hhalf : Real.sinh (((2 * a + b : ℤ) : ℝ) * Real.log B / 2) ^ 2 = (ρ + ρ⁻¹ - 2) / 4 := by
    rw [sinh_sq_half, hsl, Real.cosh_log hρ0]; ring
  unfold Omega
  rw [hhalf, hsh, hch]
  have hBi : B - B⁻¹ ≠ 0 := by
    have : B⁻¹ < B := by
      rw [inv_lt_comm₀ hB0 hB0]; exact (inv_lt_one_of_one_lt₀ hB).trans hB
    linarith
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  unfold X
  field_simp
  ring

lemma inversive_lt_one_iff {d r₁ r₂ : ℝ} (hd : 0 ≤ d) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    d < r₁ + r₂ ↔ (d ^ 2 - r₁ ^ 2 - r₂ ^ 2) / (2 * r₁ * r₂) < 1 := by
  rw [div_lt_one (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_self_le_mul_self (by positivity) hc]

/-- **Lemma B 5.1, eq. (6).** Overlap iff `Ω(w) < 1`. -/
theorem overlap_iff_Omega {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ < rad B (p + a) (q + b) + rad B p q ↔
      Omega B ψ a b < 1 := by
  have hB0 : 0 < B := by linarith
  have h1 : 0 < rad B p q := by unfold rad; exact zpow_pos hB0 _
  have h2 : 0 < rad B (p + a) (q + b) := by unfold rad; exact zpow_pos hB0 _
  rw [add_comm (rad B (p + a) (q + b)), inversive_lt_one_iff (norm_nonneg _) h1 h2,
    inversive_eq ψ hB]
  constructor <;> intro h <;> linarith

/-- **Lemma B 5.1.** Tangency iff `Ω(w) = 1`. -/
theorem tangent_iff_Omega {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ = rad B (p + a) (q + b) + rad B p q ↔
      Omega B ψ a b = 1 := by
  have hB0 : 0 < B := by linarith
  have h1 : 0 < rad B p q := by unfold rad; exact zpow_pos hB0 _
  have h2 : 0 < rad B (p + a) (q + b) := by unfold rad; exact zpow_pos hB0 _
  have hI := inversive_eq ψ hB p q a b
  have hD : 0 < 2 * rad B p q * rad B (p + a) (q + b) := by positivity
  rw [div_eq_iff hD.ne'] at hI
  have hd := norm_nonneg (zc B ψ (p + a) (q + b) - zc B ψ p q)
  constructor
  · intro h
    rw [h] at hI
    have : (2 * Omega B ψ a b - 1 - 1) * (2 * rad B p q * rad B (p + a) (q + b)) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · intro h
    rw [h] at hI
    have hsq : ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ ^ 2
        = (rad B (p + a) (q + b) + rad B p q) ^ 2 := by linarith
    exact (sq_eq_sq₀ hd (by positivity)).1 hsq

/-! ### `tanh` form of the case `s = 0`, and `|s| ≤ 1` -/

lemma tanh_log_eq {B : ℝ} (hB : 1 < B) : Real.tanh (Real.log B) = (B ^ 2 - 1) / (B ^ 2 + 1) := by
  have hB0 : 0 < B := by linarith
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_log hB0, Real.cosh_log hB0]
  field_simp

lemma X_sq_mul_tanh_sq {B : ℝ} (hB : 1 < B) : X B ^ 2 * Real.tanh (Real.log B) ^ 2 = 1 := by
  rw [tanh_log_eq hB]
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  unfold X
  field_simp

/-- **Lemma B 5.1, case `s = 0`:** overlap iff `|sin jψ| < tanh log B`. -/
theorem overlap_s0_tanh {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q j : ℤ) :
    ‖zc B ψ (p + -j) (q + 2 * j) - zc B ψ p q‖ < rad B (p + -j) (q + 2 * j) + rad B p q ↔
      |Real.sin (j * ψ)| < Real.tanh (Real.log B) := by
  rw [overlap_s0 ψ hB]
  have ht : 0 < Real.tanh (Real.log B) := by
    rw [tanh_log_eq hB]; apply div_pos <;> nlinarith
  have key := X_sq_mul_tanh_sq hB
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  rw [← abs_of_pos ht, ← sq_lt_sq]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Lemma B 5.1, "in particular":** circles whose labels differ by `w` with `|2a+b| ≥ 2`
do not overlap. -/
theorem no_overlap_far {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) (hs : 2 ≤ |2 * a + b|) :
    ¬ ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ < rad B (p + a) (q + b) + rad B p q := by
  rw [overlap_iff ψ hB p q a b, not_lt]
  have hB0 : 0 < B := by linarith
  set ρ := B ^ (2 * a + b) with hρ
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have hfac : X B ^ 2 * (ρ - 1) ^ 2 - (1 + ρ) ^ 2
      = 4 * (ρ - B ^ 2) * (B ^ 2 * ρ - 1) / (B ^ 2 - 1) ^ 2 := by
    unfold X; field_simp; ring
  have hprod : 0 ≤ (ρ - B ^ 2) * (B ^ 2 * ρ - 1) := by
    rcases le_abs'.1 hs with h | h
    · -- `2a + b ≤ −2`, so `ρ ≤ B⁻²`
      have hle : ρ ≤ B ^ (-2 : ℤ) := zpow_le_zpow_right₀ hB.le h
      have : B ^ 2 * ρ ≤ 1 := by
        calc B ^ 2 * ρ ≤ B ^ 2 * B ^ (-2 : ℤ) := by gcongr
          _ = 1 := by rw [zpow_neg, zpow_ofNat]; field_simp
      have : ρ < B ^ 2 := by nlinarith
      nlinarith
    · have hle : B ^ (2 : ℤ) ≤ ρ := zpow_le_zpow_right₀ hB.le h
      rw [zpow_ofNat] at hle
      have : 1 ≤ B ^ 2 * ρ := by nlinarith
      nlinarith
  have hc := Real.cos_le_one (b * ψ)
  have hX2 : 0 ≤ X B ^ 2 := sq_nonneg _
  have hρ0 : 0 < ρ := zpow_pos hB0 _
  have : 0 ≤ 4 * (ρ - B ^ 2) * (B ^ 2 * ρ - 1) / (B ^ 2 - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _); nlinarith
  nlinarith [mul_le_mul_of_nonneg_left (show 2 * ρ * Real.cos (b * ψ) ≤ 2 * ρ by nlinarith) hX2]

/-- `cos ψ < cos(bψ)` iff `|sin(bψ/2)| < sin(ψ/2)`, for `0 < ψ < π`. -/
lemma cos_lt_cos_iff_abs_sin {ψ y : ℝ} (h0 : 0 < ψ) (h1 : ψ < Real.pi) :
    Real.cos ψ < Real.cos y ↔ |Real.sin (y / 2)| < Real.sin (ψ / 2) := by
  have hpos : 0 < Real.sin (ψ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have key : |Real.sin (y / 2)| < Real.sin (ψ / 2) ↔
      Real.sin (y / 2) ^ 2 < Real.sin (ψ / 2) ^ 2 := by
    constructor
    · intro h
      have := pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero
      rwa [sq_abs] at this
    · intro h
      exact lt_of_pow_lt_pow_left₀ 2 hpos.le (by rwa [sq_abs])
  rw [key, cos_eq_one_sub_two_sin_sq ψ, cos_eq_one_sub_two_sin_sq y]
  constructor <;> intro h <;> linarith

/-- **Lemma B 5.1, case `s = 1`, in the paper's form:** overlap iff `|sin(bψ/2)| < sin(ψ/2)`. -/
theorem overlap_s1_sin {B : ℝ} (hB : 1 < B) (p q a b : ℤ) (hs : 2 * a + b = 1) :
    ‖zc B (psi B) (p + a) (q + b) - zc B (psi B) p q‖
        < rad B (p + a) (q + b) + rad B p q ↔
      |Real.sin (b * psi B / 2)| < Real.sin (psi B / 2) := by
  rw [overlap_s1 hB (cos_psi hB) p q a b hs,
    cos_lt_cos_iff_abs_sin (psi_mem_Ioo hB).1 (psi_mem_Ioo hB).2]

/-- **Lemma B 5.1, case `s = −1`, in the paper's form.** -/
theorem overlap_sm1_sin {B : ℝ} (hB : 1 < B) (p q a b : ℤ) (hs : 2 * a + b = -1) :
    ‖zc B (psi B) (p + a) (q + b) - zc B (psi B) p q‖
        < rad B (p + a) (q + b) + rad B p q ↔
      |Real.sin (b * psi B / 2)| < Real.sin (psi B / 2) := by
  rw [overlap_sm1 hB (cos_psi hB) p q a b hs,
    cos_lt_cos_iff_abs_sin (psi_mem_Ioo hB).1 (psi_mem_Ioo hB).2]

/-! ### The analytic core of Theorem B 5.2 (first overlap) -/

lemma sin_le_sin_of_mem {ψ x : ℝ} (h0 : 0 ≤ ψ) (hψ : ψ ≤ Real.pi / 2) (h1 : ψ ≤ x)
    (h2 : x ≤ Real.pi - ψ) : Real.sin ψ ≤ Real.sin x := by
  rcases le_total x (Real.pi / 2) with hx | hx
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx h1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

lemma sin_lt_sin_of_mem {ψ x : ℝ} (h0 : 0 ≤ ψ) (_hψ : ψ ≤ Real.pi / 2) (h1 : ψ < x)
    (h2 : x < Real.pi - ψ) : Real.sin ψ < Real.sin x := by
  rcases le_total x (Real.pi / 2) with hx | hx
  · exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hx h1
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

lemma X_sq_one_sub_eta_sq {B : ℝ} (hB : 1 < B) : X B ^ 2 * (1 - eta B ^ 2) = 1 := by
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : B ^ 2 + 1 ≠ 0 := by positivity
  unfold X eta
  field_simp
  ring

/-- **Theorem B 5.2, no overlap of type (E) before ring `⌊t⌋`.** If `1 ≤ j` and
`(j+1)ψ ≤ π` (i.e. `j ≤ ⌊t⌋ − 1`), the circles `j(−1,2)` apart do not overlap. -/
theorem E_no_overlap_before {B : ℝ} (hB : 1 < B) (j : ℤ) (hj : 1 ≤ j)
    (hjt : ((j : ℝ) + 1) * psi B ≤ Real.pi) :
    ¬ X B ^ 2 * Real.sin (j * psi B) ^ 2 < 1 := by
  have hψ := psi_mem_Ioo hB
  set ψ := psi B with hψdef
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hψ2 : ψ ≤ Real.pi / 2 := by nlinarith [hψ.1]
  have hs := sin_le_sin_of_mem (x := (j : ℝ) * ψ) hψ.1.le hψ2 (by nlinarith [hψ.1])
    (by nlinarith)
  have hsψ : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hsq : Real.sin ψ ^ 2 ≤ Real.sin (j * ψ) ^ 2 := by nlinarith
  -- `sin²ψ > 1 − η² = 1/X²` because `0 ≤ cos ψ < η`
  have hc0 : 0 ≤ Real.cos ψ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hψ.1], hψ2⟩
  have hceta : Real.cos ψ < eta B := by
    have e1 := eta_lt_one hB
    have e0 := eta_pos (by linarith : (0 : ℝ) < B)
    rw [cos_psi hB, cosPsi_eq_eta]; nlinarith
  have hsin2 : Real.sin ψ ^ 2 = 1 - Real.cos ψ ^ 2 := by
    have := Real.sin_sq_add_cos_sq ψ; linarith
  have key := X_sq_one_sub_eta_sq hB
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  have : 1 - eta B ^ 2 < Real.sin ψ ^ 2 := by rw [hsin2]; nlinarith
  rw [not_lt]
  nlinarith [mul_lt_mul_of_pos_left this hX2]

/-- **Theorem B 5.2, no overlap of type (O) before ring `⌊t⌋`.** For `3 ≤ b` and
`(b+3)ψ ≤ 2π` (i.e. `b ≤ 2⌊t⌋ − 3`): `cos(bψ) < cos ψ`, so by `overlap_s1` there is no
overlap. -/
theorem O_no_overlap_before {B : ℝ} (hB : 1 < B) (b : ℤ) (hb : 3 ≤ b)
    (hbt : ((b : ℝ) + 3) * psi B ≤ 2 * Real.pi) :
    Real.cos (b * psi B) < Real.cos (psi B) := by
  have hψ := psi_mem_Ioo hB
  set ψ := psi B
  have hb' : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hψ3 : ψ ≤ Real.pi / 3 := by nlinarith [hψ.1]
  have h1 := sin_le_sin_of_mem (ψ := 3 * ψ / 2) (x := b * ψ / 2) (by linarith [hψ.1])
    (by linarith) (by nlinarith [hψ.1]) (by nlinarith)
  have h2 : Real.sin (ψ / 2) < Real.sin (3 * ψ / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hψ.1]) (by linarith) (by linarith [hψ.1])
  have hpos : 0 < Real.sin (ψ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hψ.1]) (by linarith [hψ.2, Real.pi_pos])
  rw [cos_eq_one_sub_two_sin_sq (b * ψ), cos_eq_one_sub_two_sin_sq ψ]
  nlinarith

/-- **Theorem B 5.2, ring `⌊t⌋`, type (E):** `sin(⌊t⌋ψ) = sin(rψ)` with `r = t − ⌊t⌋`, so by
`overlap_s0_tanh` the pair `⌊t⌋(−1,2)` overlaps iff `sin(rψ) < tanh log B`. -/
theorem sin_floor_mul {ψ : ℝ} (hψ : 0 < ψ) :
    Real.sin (⌊Real.pi / ψ⌋ * ψ) = Real.sin (Int.fract (Real.pi / ψ) * ψ) := by
  have h : (⌊Real.pi / ψ⌋ : ℝ) * ψ = Real.pi - Int.fract (Real.pi / ψ) * ψ := by
    rw [Int.fract, sub_mul, div_mul_cancel₀ _ hψ.ne']; ring
  rw [h, Real.sin_pi_sub]

/-- **Theorem B 5.2, ring `⌊t⌋`, type (O):** for `⌊t⌋ ≥ 2` and non-resonant `B`
(`r > 0`), `b = 2⌊t⌋ − 1` gives `cos(bψ) < cos ψ`: no overlap. -/
theorem O_no_overlap_floor {B : ℝ} (hB : 1 < B) (hn : 2 ≤ ⌊Real.pi / psi B⌋)
    (hr : 0 < Int.fract (Real.pi / psi B)) :
    Real.cos (((2 * ⌊Real.pi / psi B⌋ - 1 : ℤ) : ℝ) * psi B) < Real.cos (psi B) := by
  have hψ := psi_mem_Ioo hB
  set ψ := psi B
  set n := ⌊Real.pi / ψ⌋
  set r := Int.fract (Real.pi / ψ)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (n : ℝ) * ψ = Real.pi - r * ψ := by
    have : (n : ℝ) = Real.pi / ψ - r := by
      have := Int.floor_add_fract (Real.pi / ψ); linarith
    rw [this, sub_mul, div_mul_cancel₀ _ hψ.1.ne']
  have hr1 : r < 1 := Int.fract_lt_one _
  have hψ2 : ψ ≤ Real.pi / 2 := by nlinarith [hψ.1]
  push_cast
  have hx : (2 * (n : ℝ) - 1) * ψ / 2 = Real.pi - r * ψ - ψ / 2 := by linarith
  have h1 := sin_lt_sin_of_mem (ψ := ψ / 2) (x := (2 * (n : ℝ) - 1) * ψ / 2)
    (by linarith [hψ.1]) (by linarith [Real.pi_pos]) (by rw [hx]; nlinarith [hψ.1])
    (by rw [hx]; nlinarith [hψ.1])
  have hpos : 0 < Real.sin (ψ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hψ.1]) (by linarith [hψ.2, Real.pi_pos])
  rw [cos_eq_one_sub_two_sin_sq ((2 * (n : ℝ) - 1) * ψ), cos_eq_one_sub_two_sin_sq ψ]
  nlinarith

/-- **Theorem B 5.2, ring `⌈t⌉ = ⌊t⌋ + 1`, type (O):** for non-resonant `B`, `b = 2⌊t⌋ + 1`
gives `cos ψ < cos(bψ)`, so by `overlap_s1`/`overlap_sm1` the differences
`(−⌊t⌋, 2⌊t⌋+1)` and `(−⌊t⌋−1, 2⌊t⌋+1)` overlap. -/
theorem O_overlap_ceil {B : ℝ} (hB : 1 < B) (hr : 0 < Int.fract (Real.pi / psi B)) :
    Real.cos (psi B) < Real.cos (((2 * ⌊Real.pi / psi B⌋ + 1 : ℤ) : ℝ) * psi B) := by
  have hψ := psi_mem_Ioo hB
  set ψ := psi B
  set n := ⌊Real.pi / ψ⌋
  set r := Int.fract (Real.pi / ψ)
  have ht : (n : ℝ) * ψ = Real.pi - r * ψ := by
    have : (n : ℝ) = Real.pi / ψ - r := by
      have := Int.floor_add_fract (Real.pi / ψ); linarith
    rw [this, sub_mul, div_mul_cancel₀ _ hψ.1.ne']
  have hr1 : r < 1 := Int.fract_lt_one _
  push_cast
  -- `(2n+1)ψ/2 = π + y` with `y = (1/2 − r)ψ`, `|y| < ψ/2`
  set y := (1 / 2 - r) * ψ with hy
  have hx : (2 * (n : ℝ) + 1) * ψ / 2 = y + Real.pi := by rw [hy]; linarith
  have hsx : Real.sin ((2 * (n : ℝ) + 1) * ψ / 2) ^ 2 = Real.sin |y| ^ 2 := by
    rw [hx, Real.sin_add_pi]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_nonpos h, Real.sin_neg]
  have hyabs : |y| < ψ / 2 := by
    rw [hy, abs_mul, abs_of_pos hψ.1]
    have : |1 / 2 - r| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    nlinarith [hψ.1]
  have h1 : Real.sin |y| < Real.sin (ψ / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [abs_nonneg y, Real.pi_pos])
      (by linarith [hψ.2]) hyabs
  have h0 : 0 ≤ Real.sin |y| :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg y) (by linarith [hψ.2, hψ.1])
  rw [cos_eq_one_sub_two_sin_sq ((2 * (n : ℝ) + 1) * ψ), cos_eq_one_sub_two_sin_sq ψ, hsx]
  nlinarith

end DoyleFormal
