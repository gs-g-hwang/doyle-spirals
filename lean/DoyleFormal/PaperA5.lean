/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.DoyleOpt
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Paper A, Theorem 5.1, Corollaries 5.2–5.3, Proposition 5.7 and Proposition 7.8

For `D_B` (`B > 1`), with centers `zc B (psi B)` (equal to every normalized configuration with
radii `B^{2p+q}` by `prop_5_4`):

* `homothety` (**Theorem A 5.1**): `T(z) = B² z + (1 + B²)` fixes `X` and maps `K(p,q)` to
  `K(p+1,q)`; `homothety_config` for any normalized configuration.
* `axis_limit`, `axis_dist` (**Corollary A 5.2**): `z(−k,0) → X`, and
  `|z(−k,0)| = Σ_{j=1}^{k} (B^{−2(j−1)} + B^{−2j}) → (B²+1)/(B²−1)`.
* `rays`, `ring_rays` (**Corollary A 5.3**).
* `Lq`, `exp_Lq`, `tau_eq`, `two_pi_I_mem_iff`, `multiplier_discrete_iff`, `tau_tendsto`
  (**Proposition A 5.7**): `ℒ(p,q) = 2pλ + q(λ + iψ)`, the modulus `τ = 1/2 + iψ/(2λ)`, the
  multiplier group is discrete iff `t = π/ψ` is rational, `2πi ∈ Λ_B` iff `t ∈ ℤ`, and
  `τ → e^{iπ/3}` as `B → 1`.
* `descartes_identity`, `coxeter_tfae`, `X_coxeter` (**Proposition A 7.8**): `B⁶ ℰ(B) =
  (B²+1)³ cos ψ(B)`; `ψ = π/2 ⇔ B + B⁻¹ = 2φ ⇔ B = φ + √φ ⇔ ℰ(B) = 0`, and `X = −√φ` there.
  Item (4) of the paper (four mutually tangent circles with radii `1, B, B², B³`) is stated
  through the Descartes defect `ℰ(B) = 0`; Descartes' circle theorem itself is not formalized.
-/

namespace DoyleFormal

open Real Filter Topology

lemma X_mul {B : ℝ} (hB : 1 < B) : X B * (1 - B ^ 2) = 1 + B ^ 2 := by
  unfold X
  have : B ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp; ring

/-! ### Theorem A 5.1 -/

/-- **Theorem A 5.1.** `T(z) = B² z + (1 + B²)` fixes `X` and maps `K(p,q)` to `K(p+1,q)`. -/
theorem homothety {B : ℝ} (hB : 1 < B) (ψ : ℝ) (p q : ℤ) :
    B ^ 2 * X B + (1 + B ^ 2) = X B ∧
      (B : ℂ) ^ 2 * zc B ψ p q + ((1 + B ^ 2 : ℝ) : ℂ) = zc B ψ (p + 1) q ∧
      rad B (p + 1) q = B ^ 2 * rad B p q := by
  have hX := X_mul hB
  have hB0 : B ≠ 0 := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [← T_map ψ hB0 p q]
    have hX' : ((X B : ℝ) : ℂ) * (1 - (B : ℂ) ^ 2) = ((1 + B ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast hX
    linear_combination -hX'
  · unfold rad
    rw [show 2 * (p + 1) + q = 2 + (2 * p + q) by ring, zpow_add₀ hB0]
    norm_num

/-- Theorem A 5.1 for every configuration with radii `B^{2p+q}` and the normalization of `D_B`. -/
theorem homothety_config {B : ℝ} (hB : 1 < B) {z : ℤ → ℤ → ℂ} (hz : IsConfig (rad B) z)
    (h0 : z 0 0 = 0) (h1 : z 1 0 = ((1 + B ^ 2 : ℝ) : ℂ)) (p q : ℤ) :
    (B : ℂ) ^ 2 * z p q + ((1 + B ^ 2 : ℝ) : ℂ) = z (p + 1) q := by
  rw [prop_5_4 hB hz h0 h1, prop_5_4 hB hz h0 h1]
  exact (homothety hB _ p q).2.1

/-! ### Corollary A 5.2 -/

lemma zc_axis {B : ℝ} (hB : 1 < B) (ψ : ℝ) (k : ℕ) :
    zc B ψ (-k) 0 = ((X B * (1 - ((B ^ 2)⁻¹) ^ k) : ℝ) : ℂ) := by
  have hB0 : B ≠ 0 := by linarith
  have h := zc_sub_X ψ hB0 (-k) 0
  have e : (B : ℂ) ^ (2 * (-(k : ℤ)) + 0) = ((((B ^ 2)⁻¹) ^ k : ℝ) : ℂ) := by
    rw [add_zero, show 2 * (-(k : ℤ)) = -((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
    push_cast; rw [inv_pow, pow_mul]
  rw [e, zpow_zero, mul_one] at h
  have h2 : zc B ψ (-k) 0 = (X B : ℂ) + ((((B ^ 2)⁻¹) ^ k : ℝ) : ℂ) * (-(X B : ℂ)) := by
    linear_combination h
  rw [h2]; push_cast; ring

/-- **Corollary A 5.2.** The axis centers converge to `X`. -/
theorem axis_limit {B : ℝ} (hB : 1 < B) (ψ : ℝ) :
    Tendsto (fun k : ℕ => zc B ψ (-k) 0) atTop (𝓝 (X B : ℂ)) := by
  have hr : (B ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hr0 : 0 ≤ (B ^ 2)⁻¹ := by positivity
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr
  have h2 : Tendsto (fun k : ℕ => X B * (1 - ((B ^ 2)⁻¹) ^ k)) atTop (𝓝 (X B * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub h)
  rw [sub_zero, mul_one] at h2
  have h3 := (Complex.continuous_ofReal.tendsto _).comp h2
  exact h3.congr (fun k => (zc_axis hB ψ k).symm)

/-- **Corollary A 5.2**, distances: `S_k = |z(−k,0)| = Σ_{j=1}^{k} (B^{−2(j−1)} + B^{−2j})`,
and `S_k → (B²+1)/(B²−1)`. -/
theorem axis_dist {B : ℝ} (hB : 1 < B) (ψ : ℝ) (k : ℕ) :
    ‖zc B ψ (-k) 0‖ = ∑ j ∈ Finset.range k, (((B ^ 2)⁻¹) ^ j + ((B ^ 2)⁻¹) ^ (j + 1)) ∧
      Tendsto (fun k : ℕ => ‖zc B ψ (-k) 0‖) atTop (𝓝 ((B ^ 2 + 1) / (B ^ 2 - 1))) := by
  have hX := X_neg hB
  have hr : (B ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hr0 : 0 ≤ (B ^ 2)⁻¹ := by positivity
  have hB2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have hn : ∀ k : ℕ, ‖zc B ψ (-k) 0‖ = -X B * (1 - ((B ^ 2)⁻¹) ^ k) := by
    intro k
    rw [zc_axis hB ψ k, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
    · ring
    · have : ((B ^ 2)⁻¹) ^ k ≤ 1 := pow_le_one₀ hr0 hr.le
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [hn]
    have hg := geom_sum_eq (show (B ^ 2)⁻¹ ≠ 1 from hr.ne) k
    rw [show ∑ j ∈ Finset.range k, (((B ^ 2)⁻¹) ^ j + ((B ^ 2)⁻¹) ^ (j + 1)) =
      (1 + (B ^ 2)⁻¹) * ∑ j ∈ Finset.range k, ((B ^ 2)⁻¹) ^ j by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring, hg]
    have hB0 : B ≠ 0 := by linarith
    have h1 : (B ^ 2)⁻¹ - 1 ≠ 0 := by linarith
    have h1' : 1 - (B ^ 2)⁻¹ ≠ 0 := by linarith
    have hXr : -X B = (1 + (B ^ 2)⁻¹) / (1 - (B ^ 2)⁻¹) := by
      unfold X; field_simp
    rw [hXr]
    generalize (B ^ 2)⁻¹ = r at h1 h1' ⊢
    field_simp
    ring
  · have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr
    have h2 : Tendsto (fun k : ℕ => -X B * (1 - ((B ^ 2)⁻¹) ^ k)) atTop
        (𝓝 (-X B * (1 - 0))) := tendsto_const_nhds.mul (tendsto_const_nhds.sub h)
    rw [sub_zero, mul_one] at h2
    have h3 := h2.congr (fun k => (hn k).symm)
    rwa [show -X B = (B ^ 2 + 1) / (B ^ 2 - 1) by unfold X; ring] at h3

/-! ### Corollary A 5.3 -/

/-- **Corollary A 5.3.** For fixed `q` the centers `z(p,q)` lie on one ray from `X`, with
`|z(p+1,q) − X| = B² |z(p,q) − X|`. -/
theorem rays {B : ℝ} (hB : 1 < B) (ψ : ℝ) (p q : ℤ) :
    zc B ψ p q - X B = ((B ^ (2 * p) : ℝ) : ℂ) * (zc B ψ 0 q - X B) ∧ 0 < B ^ (2 * p) ∧
      ‖zc B ψ (p + 1) q - X B‖ = B ^ 2 * ‖zc B ψ p q - X B‖ := by
  have hB0 : B ≠ 0 := by linarith
  have hB' : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hB0
  refine ⟨?_, zpow_pos (by linarith) _, ?_⟩
  · rw [zc_sub_X ψ hB0, zc_sub_X ψ hB0, zpow_add₀ hB', mul_zero, zero_add]
    push_cast; ring
  · have h := (homothety hB ψ p q).2.1
    rw [← h]
    have hX := X_mul hB
    have hX' : ((X B : ℝ) : ℂ) * (1 - (B : ℂ) ^ 2) = ((1 + B ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast hX
    rw [show (B : ℂ) ^ 2 * zc B ψ p q + ((1 + B ^ 2 : ℝ) : ℂ) - X B =
      (B : ℂ) ^ 2 * (zc B ψ p q - X B) by linear_combination -hX', norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The centers of the `m`-ring configuration lie on the `2m+1` rays `q = −m, …, m`. -/
theorem ring_rays {m p q : ℤ} (h : hnorm p q ≤ m) : -m ≤ q ∧ q ≤ m := by
  rw [hnorm_le_iff] at h; omega

/-! ### Proposition A 5.7 -/

/-- `ℒ(p,q) = 2pλ + q(λ + iψ)`, `λ = log B`. -/
noncomputable def Lq (B : ℝ) (p q : ℤ) : ℂ :=
  2 * p * (Real.log B : ℂ) + q * ((Real.log B : ℂ) + psi B * Complex.I)

lemma exp_Lq {B : ℝ} (hB : 1 < B) (p q : ℤ) :
    Complex.exp (Lq B p q) = (B : ℂ) ^ (2 * p) * beta B (psi B) ^ q := by
  have hB0 : 0 < B := by linarith
  have hB' : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hB0.ne'
  have el : Complex.exp (Real.log B : ℂ) = B := by
    rw [← Complex.ofReal_exp, Real.exp_log hB0]
  unfold Lq beta
  rw [show 2 * (p : ℂ) * (Real.log B : ℂ) + q * ((Real.log B : ℂ) + psi B * Complex.I) =
    ((2 * p : ℤ) : ℂ) * (Real.log B : ℂ) + (q : ℂ) * (Real.log B : ℂ) +
      (q : ℂ) * (psi B * Complex.I) by push_cast; ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul, Complex.exp_int_mul, Complex.exp_int_mul, el, mul_zpow]
  ring

/-- **Proposition A 5.7.** `z(p,q) − X = e^{ℒ(p,q)} (z(0,0) − X)` for `D_B`. -/
theorem zc_Lq {B : ℝ} (hB : 1 < B) (p q : ℤ) :
    zc B (psi B) p q - X B = Complex.exp (Lq B p q) * (0 - X B) := by
  rw [exp_Lq hB]; unfold zc; ring

/-- **Proposition A 5.7 (1).** `τ = ℒ(0,1)/ℒ(1,0) = 1/2 + iψ/(2λ)`. -/
theorem tau_eq {B : ℝ} (hB : 1 < B) :
    Lq B 0 1 / Lq B 1 0 = 1 / 2 + (psi B / (2 * Real.log B) : ℝ) * Complex.I := by
  have hl : Real.log B ≠ 0 := (Real.log_pos hB).ne'
  have hl' : (Real.log B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl
  unfold Lq
  push_cast
  field_simp
  ring

/-- **Proposition A 5.7 (2), second part.** `2πi ∈ Λ_B` iff `t = π/ψ` is an integer. -/
theorem two_pi_I_mem_iff {B : ℝ} (hB : 1 < B) :
    (∃ p q : ℤ, Lq B p q = 2 * π * Complex.I) ↔ ∃ n : ℤ, π / psi B = n := by
  have hl : 0 < Real.log B := Real.log_pos hB
  have hψ := psi_mem_Ioo hB
  have hψ0 : psi B ≠ 0 := hψ.1.ne'
  constructor
  · rintro ⟨p, q, h⟩
    have hre : (2 * p + q : ℝ) * Real.log B = 0 := by
      have := congrArg Complex.re h; simp [Lq] at this; linarith
    have him : (q : ℝ) * psi B = 2 * π := by
      have := congrArg Complex.im h; simpa [Lq] using this
    have h2 : (2 * p + q : ℝ) = 0 := (mul_eq_zero.1 hre).resolve_right hl.ne'
    refine ⟨-p, ?_⟩
    rw [div_eq_iff hψ0]; push_cast
    have hq : (q : ℝ) = -2 * p := by linarith
    rw [hq] at him; linarith
  · rintro ⟨n, hn⟩
    rw [div_eq_iff hψ0] at hn
    refine ⟨-n, 2 * n, ?_⟩
    apply Complex.ext <;> simp [Lq]
    nlinarith

/-- **Proposition A 5.7 (2), first part.** The multiplier group `{B^{2p} β^q}` is discrete
(no element other than `1` within some `ε` of `1`) iff `t = π/ψ` is rational. -/
theorem multiplier_discrete_iff {B : ℝ} (hB : 1 < B) :
    (∃ ε > 0, ∀ p q : ℤ, Complex.exp (Lq B p q) ≠ 1 → ε ≤ ‖Complex.exp (Lq B p q) - 1‖) ↔
      ∃ r : ℚ, π / psi B = r := by
  have hB0 : 0 < B := by linarith
  have hψ := psi_mem_Ioo hB
  have hψ0 : 0 < psi B := hψ.1
  have hl : 0 < Real.log B := Real.log_pos hB
  -- `|e^{ℒ}| = B^{2p+q}` and the argument part `e^{iqψ}`
  have hnorm : ∀ p q : ℤ, ‖Complex.exp (Lq B p q)‖ = Real.exp ((2 * p + q) * Real.log B) := by
    intro p q; rw [Complex.norm_exp]; simp [Lq]; ring_nf
  constructor
  · rintro ⟨ε, hε, h⟩
    by_contra hirr
    push Not at hirr
    -- Dirichlet: `|k ψ/π − j|` small with `0 < k`
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * π / ε)
    have hn0 : 0 < n := by
      have : 0 < 2 * π / ε := by positivity
      exact_mod_cast this.trans hn
    obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le (psi B / π) hn0
    have hval : Complex.exp (Lq B (-k) (2 * k)) =
        Complex.exp (Complex.I * (2 * (k * psi B - j * π) : ℝ)) := by
      have e : Lq B (-k) (2 * k) = Complex.I * (2 * (k * psi B - j * π) : ℝ) +
          (j : ℤ) * (2 * π * Complex.I) := by
        simp only [Lq]; push_cast; ring
      rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hne : Complex.exp (Lq B (-k) (2 * k)) ≠ 1 := by
      rw [hval]; intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have him : 2 * (k * psi B - j * π) = m * (2 * π) := by
        have := congrArg Complex.im hm; simpa using this
      -- `2(kψ − jπ) = 2πm`, so `π/ψ = k/(j+m)`
      have hjm : ((j + m : ℤ) : ℝ) ≠ 0 := by
        intro h0; push_cast at h0
        have : (k : ℝ) * psi B = 0 := by nlinarith [Real.pi_pos]
        have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
        exact hψ0.ne' ((mul_eq_zero.1 this).resolve_left hk)
      apply hirr ((k : ℚ) / (j + m : ℤ))
      push_cast at hjm ⊢
      rw [div_eq_div_iff hψ0.ne' hjm]
      nlinarith [Real.pi_pos]
    have hle := h _ _ hne
    rw [hval] at hle
    have hb := norm_exp_I_mul_ofReal_sub_one_le (x := 2 * (k * psi B - j * π))
    rw [Real.norm_eq_abs] at hb
    have hd : |2 * (k * psi B - j * π)| ≤ 2 * π / (n + 1) := by
      rw [show 2 * (k * psi B - j * π) = 2 * π * (k * (psi B / π) - j) by field_simp, abs_mul,
        abs_of_pos (by positivity)]
      have := mul_le_mul_of_nonneg_left hjk (by positivity : (0 : ℝ) ≤ 2 * π)
      calc _ ≤ 2 * π * (1 / (n + 1)) := this
        _ = _ := by ring
    have hlt : 2 * π / (n + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn
      nlinarith
    linarith
  · rintro ⟨r, hr⟩
    -- `ψ = π b / a` with `a = r.num > 0`
    have hr0 : (0 : ℝ) < r := by rw [← hr]; positivity
    set a := r.num with ha
    set b := r.den with hb
    have ha0 : 0 < a := Rat.num_pos.2 (by exact_mod_cast hr0)
    have hb0 : (0 : ℝ) < b := by positivity
    have hψab : psi B * a = π * b := by
      have : (r : ℝ) = a / b := by rw [ha, hb]; exact_mod_cast (Rat.num_div_den r).symm
      rw [this, div_eq_div_iff hψ0.ne' hb0.ne'] at hr
      linarith
    -- the `2a`-th roots of unity other than `1`
    set N : ℕ := 2 * a.toNat with hN
    have hNpos : 0 < N := by omega
    set R := ((Polynomial.nthRoots N (1 : ℂ)).toFinset.filter (· ≠ 1)) with hR
    obtain ⟨ε1, hε1, hR1⟩ : ∃ ε1 > 0, ∀ z ∈ R, ε1 ≤ ‖z - 1‖ := by
      by_cases hne : R.Nonempty
      · obtain ⟨z0, hz0, hmin⟩ := R.exists_min_image (fun z => ‖z - 1‖) hne
        refine ⟨‖z0 - 1‖, ?_, hmin⟩
        have : z0 ≠ 1 := (Finset.mem_filter.1 hz0).2
        exact norm_pos_iff.2 (sub_ne_zero.2 this)
      · refine ⟨1, one_pos, fun z hz => (hne ⟨z, hz⟩).elim⟩
    refine ⟨min (1 - B⁻¹) ε1, lt_min (by have := inv_lt_one_of_one_lt₀ hB; linarith) hε1,
      fun p q hne => ?_⟩
    by_cases hpq : 2 * p + q = 0
    · -- `e^{ℒ} = e^{iqψ}` is a `2a`-th root of unity
      have hq : q = -2 * p := by omega
      have hpow : Complex.exp (Lq B p q) ^ N = 1 := by
        rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
        refine ⟨q * b, ?_⟩
        simp only [Lq, hN]; rw [hq]
        have hat : ((a.toNat : ℕ) : ℂ) = (a : ℂ) := by exact_mod_cast Int.toNat_of_nonneg ha0.le
        push_cast; rw [hat]
        have : (psi B : ℂ) * a = π * b := by exact_mod_cast hψab
        linear_combination (-2 * (p : ℂ) * 2 * Complex.I) * this
      have hmem : Complex.exp (Lq B p q) ∈ R := by
        rw [hR, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_nthRoots hNpos]
        exact ⟨hpow, hne⟩
      exact (min_le_right _ _).trans (hR1 _ hmem)
    · -- the modulus `B^{2p+q}` is far from `1`
      have hn := hnorm p q
      refine (min_le_left _ _).trans ?_
      refine le_trans ?_ (abs_norm_sub_norm_le _ _)
      rw [hn, norm_one]
      set n : ℤ := 2 * p + q
      have hcast : ((2 * p + q : ℤ) : ℝ) = (2 * p + q : ℝ) := by push_cast; ring
      rcases lt_or_gt_of_ne hpq with hlt | hgt
      · -- `n ≤ −1`
        have hle : ((2 * p + q : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show 2 * p + q ≤ -1 by omega)
        rw [hcast] at hle
        have h1 : Real.exp ((2 * p + q) * Real.log B) ≤ Real.exp (-Real.log B) :=
          Real.exp_le_exp.2 (by nlinarith)
        rw [Real.exp_neg, Real.exp_log hB0] at h1
        have : B⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have hle : (1 : ℝ) ≤ ((2 * p + q : ℤ) : ℝ) := by
          exact_mod_cast (show 1 ≤ 2 * p + q by omega)
        rw [hcast] at hle
        have h1 : Real.exp (Real.log B) ≤ Real.exp ((2 * p + q) * Real.log B) :=
          Real.exp_le_exp.2 (by nlinarith)
        rw [Real.exp_log hB0] at h1
        have : B⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB
        rw [abs_of_nonneg (by linarith)]
        have : 1 - B⁻¹ ≤ B - 1 := by
          have : B⁻¹ * B = 1 := inv_mul_cancel₀ hB0.ne'
          nlinarith
        linarith

/-- `sin(ψ/2) = (B − 1) √(B² + B + 1)/(B² + 1)`. -/
lemma sin_half_psi {B : ℝ} (hB : 1 < B) :
    Real.sin (psi B / 2) = (B - 1) * (√(B ^ 2 + B + 1) / (B ^ 2 + 1)) := by
  have hψ := psi_mem_Ioo hB
  have hs : 0 < Real.sin (psi B / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hψ.1]) (by linarith [hψ.2, Real.pi_pos])
  have hq : 0 ≤ B ^ 2 + B + 1 := by positivity
  have hrhs : 0 ≤ (B - 1) * (√(B ^ 2 + B + 1) / (B ^ 2 + 1)) := by
    have : 0 ≤ B - 1 := by linarith
    positivity
  have hsq : Real.sin (psi B / 2) ^ 2 = ((B - 1) * (√(B ^ 2 + B + 1) / (B ^ 2 + 1))) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (psi B / 2) = psi B by ring, cos_psi hB, mul_pow,
      div_pow, Real.sq_sqrt hq]
    unfold cosPsi
    field_simp
    ring
  exact (pow_left_inj₀ hs.le hrhs two_ne_zero).1 hsq

/-- `ψ(B)/log B → √3` as `B → 1⁺`. -/
theorem psi_div_log_tendsto :
    Tendsto (fun B => psi B / Real.log B) (𝓝[>] 1) (𝓝 (√3)) := by
  set g : ℝ → ℝ := fun B => √(B ^ 2 + B + 1) / (B ^ 2 + 1) with hg
  set u : ℝ → ℝ := fun B => (B - 1) * g B with hu
  have hg1 : Tendsto g (𝓝[>] 1) (𝓝 (√3 / 2)) := by
    have hc : Continuous g := by
      simp only [hg]
      exact (Real.continuous_sqrt.comp (by continuity)).div (by continuity)
        (fun x => by positivity)
    have hg1' : g 1 = √3 / 2 := by simp only [hg]; norm_num
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    rwa [hg1'] at this
  -- `arcsin u / u → 1`
  have hu0 : Tendsto u (𝓝[>] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto u (𝓝[>] 1) (𝓝 ((1 - 1) * (√3 / 2))) :=
        ((tendsto_id.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds).mul hg1
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with B hB
      simp only [Set.mem_Ioi] at hB
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
      have : 0 < g B := by simp only [hg]; positivity
      exact mul_ne_zero (by linarith) this.ne'
  have harc : Tendsto (fun x => Real.arcsin x / x) (𝓝[≠] 0) (𝓝 1) := by
    have h := (Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1))
    rw [hasDerivAt_iff_tendsto_slope] at h
    simp only [sub_zero, pow_two, mul_zero, Real.sqrt_one, div_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field]; simp [Real.arcsin_zero]
  have hlog : Tendsto (fun B => (B - 1) / Real.log B) (𝓝[>] 1) (𝓝 1) := by
    have h := Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
    rw [hasDerivAt_iff_tendsto_slope] at h
    have h' := (h.mono_left (nhdsWithin_mono _ (fun x (hx : 1 < x) => ne_of_gt hx))).inv₀
      (by norm_num)
    simp only [inv_one] at h'
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with B hB
    rw [slope_def_field, Real.log_one, sub_zero, inv_div]
  have hmain : Tendsto (fun B => 2 * (Real.arcsin (u B) / u B) * g B * ((B - 1) / Real.log B))
      (𝓝[>] 1) (𝓝 (2 * 1 * (√3 / 2) * 1)) :=
    ((tendsto_const_nhds.mul (harc.comp hu0)).mul hg1).mul hlog
  rw [show 2 * 1 * (√3 / 2) * 1 = √3 by ring] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with B hB
  simp only [Set.mem_Ioi] at hB
  have hψ := psi_mem_Ioo hB
  have hgp : 0 < g B := by simp only [hg]; positivity
  have hl : Real.log B ≠ 0 := (Real.log_pos hB).ne'
  have hB1 : B - 1 ≠ 0 := by linarith
  have harcsin : Real.arcsin (u B) = psi B / 2 := by
    simp only [hu, hg]; rw [← sin_half_psi hB]
    exact Real.arcsin_sin (by linarith [hψ.1, Real.pi_pos]) (by linarith [hψ.2])
  have hu' : u B = (B - 1) * g B := rfl
  have hun : u B ≠ 0 := by rw [hu']; exact mul_ne_zero hB1 hgp.ne'
  change 2 * (Real.arcsin (u B) / u B) * g B * ((B - 1) / Real.log B) = psi B / Real.log B
  rw [harcsin, hu']
  field_simp

/-- **Proposition A 5.7 (3).** `τ(B) → e^{iπ/3}` as `B → 1⁺`. -/
theorem tau_tendsto :
    Tendsto (fun B => Lq B 0 1 / Lq B 1 0) (𝓝[>] 1) (𝓝 omg) := by
  have h := psi_div_log_tendsto
  have h2 : Tendsto (fun B => (1 / 2 : ℂ) + ((psi B / (2 * Real.log B) : ℝ) : ℂ) * Complex.I)
      (𝓝[>] 1) (𝓝 ((1 / 2 : ℂ) + ((√3 / 2 : ℝ) : ℂ) * Complex.I)) := by
    have h3 : Tendsto (fun B => psi B / (2 * Real.log B)) (𝓝[>] 1) (𝓝 (√3 / 2)) := by
      have := h.div_const 2
      refine this.congr (fun B => by ring)
    exact tendsto_const_nhds.add
      (((Complex.continuous_ofReal.tendsto _).comp h3).mul tendsto_const_nhds)
  have he : (1 / 2 : ℂ) + ((√3 / 2 : ℝ) : ℂ) * Complex.I = omg := by
    apply Complex.ext <;> simp [omg]
  rw [he] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with B hB
  exact (tau_eq hB).symm

/-! ### Proposition A 7.8: Coxeter's ratio -/

/-- The Descartes defect `ℰ(B) = (Σ κⱼ)² − 2 Σ κⱼ²` of the curvatures `κⱼ = B^{−j}`,
`j = 0, …, 3`. -/
noncomputable def descartes (B : ℝ) : ℝ :=
  (1 + B⁻¹ + (B ^ 2)⁻¹ + (B ^ 3)⁻¹) ^ 2 - 2 * (1 + (B⁻¹) ^ 2 + ((B ^ 2)⁻¹) ^ 2 + ((B ^ 3)⁻¹) ^ 2)

/-- **Proposition A 7.8, eq. (7.4).** `B⁶ ℰ(B) = (B² + 1)³ cos ψ(B)`. -/
theorem descartes_identity {B : ℝ} (hB : 0 < B) :
    B ^ 6 * descartes B = (B ^ 2 + 1) ^ 3 * cosPsi B := by
  unfold descartes cosPsi
  have : B ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Proposition A 7.8.** For `B > 1` the following are equivalent: `ψ(B) = π/2`;
`B + B⁻¹ = 2φ`; `B = φ + √φ`; the Descartes defect `ℰ(B)` vanishes. -/
theorem coxeter_tfae {B : ℝ} (hB : 1 < B) :
    List.TFAE [psi B = π / 2, B + B⁻¹ = 2 * φ, B = φ + √φ, descartes B = 0] := by
  have hB0 : 0 < B := by linarith
  have hp := phi_pos
  have hq : √φ ^ 2 = φ := Real.sq_sqrt hp.le
  have h12 : psi B = π / 2 ↔ cosPsi B = 0 := by unfold psi; exact Real.arccos_eq_pi_div_two
  have h14 : cosPsi B = 0 ↔ descartes B = 0 := by
    have := descartes_identity hB0
    constructor
    · intro h; rw [h, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left (by positivity)
    · intro h; rw [h, mul_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
  have hcos : cosPsi B = 0 ↔ B + B⁻¹ = 2 * φ := by
    rw [cosPsi_eq_eta]
    have he := eta_pos hB0
    have hfac : eta B ^ 2 + eta B - 1 = (eta B - (φ - 1)) * (eta B + φ) := by
      linear_combination phi_sq
    rw [hfac, mul_eq_zero, or_iff_left (by linarith), sub_eq_zero]
    unfold eta
    have h1 : B ^ 2 + 1 ≠ 0 := by positivity
    rw [div_eq_iff h1]
    constructor
    · intro h; field_simp; nlinarith [phi_sq]
    · intro h; field_simp at h; nlinarith [phi_sq]
  have h23 : B + B⁻¹ = 2 * φ ↔ B = φ + √φ := by
    have hsq : 0 ≤ √φ := Real.sqrt_nonneg φ
    constructor
    · intro h
      have h' : (B - (φ + √φ)) * (B - (φ - √φ)) = 0 := by
        field_simp at h; linear_combination h - hq + phi_sq
      rcases mul_eq_zero.1 h' with h1 | h1
      · linarith
      · -- `φ − √φ < 1`
        exfalso
        have : φ - √φ < 1 := by
          have h1' : 1 < √φ := by
            rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) one_lt_phi
          nlinarith [phi_sq]
        linarith
    · intro h; rw [h]
      have : φ + √φ ≠ 0 := by positivity
      field_simp
      linear_combination hq - phi_sq
  tfae_have 1 ↔ 2 := h12.trans hcos
  tfae_have 2 ↔ 3 := h23
  tfae_have 1 ↔ 4 := h12.trans h14
  tfae_finish

/-- **Proposition A 7.8.** At `B₂ = φ + √φ`, `X = −√φ`. -/
theorem X_coxeter : X (φ + √φ) = -√φ := by
  have hp := phi_pos
  have hq : √φ ^ 2 = φ := Real.sq_sqrt hp.le
  have h1 : 1 < √φ := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) one_lt_phi
  unfold X
  have : (φ + √φ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [div_eq_iff this]
  linear_combination (√φ + 2 * φ - 1) * hq + (1 + √φ) * phi_sq

end DoyleFormal
