/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.SkBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Theorem C 4.1: Doyle spirals and the rigidity constants

A Doyle spiral with radii `A^p B^q` and a univalent `k`-ring patch has largest neighbor ratio
`ϱ_k` with `limsup k (ϱ_k − 1) ≤ 2π/√3`, given He's estimate `s_k = O(1/k)` as a hypothesis.

* Step 2 (`rhombus_bound`): the two center triangles of the rhombus at `(0,0)` are nearly
  equilateral, so the multipliers satisfy `|α − 1| ≤ 40 (ϱ − 1)`. This replaces the
  angle estimates of the paper.
* Step 3 (`core_limit`): along a subsequence `k log α₀ → ℓ₁`, `k log α₁ → ℓ₂`, and
  tangency and orientation give `ℓ₂ = ω ℓ₁`, `ω = e^{iπ/3}`: the limit is conformal.
* Step 4: if `|ℓ₁| > 2π/√3`, the solution `w` of `ℒ_k(w) = 2πi` lies inside the hexagon `2P`;
  rounding `k w` (error `≤ √3/2 < 1`) gives a near-period inside the `2k`-ball, and
  `near_period` gives two overlapping circles of the `k`-ring patch.
* `doyle_opt` (**Theorem C 4.1**) and `doyle_opt_sharp` (equality for `D_{B_{k+1}}`).
-/

namespace DoyleFormal

open Real Filter Topology

/-! ### Algebra: near-equilateral triangles -/

/-- `ω = e^{iπ/3}`. -/
noncomputable def omg : ℂ := ⟨1 / 2, √3 / 2⟩

lemma sqrt3_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma omg_sq : omg ^ 2 = omg - 1 := by
  have h := sqrt3_mul_self
  apply Complex.ext <;> simp [omg, pow_two] <;> nlinarith

lemma norm_omg : ‖omg‖ = 1 := by
  have h := sqrt3_mul_self
  have : ‖omg‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [omg]; nlinarith
  nlinarith [norm_nonneg omg]

lemma norm_one_sub_omg : ‖1 - omg‖ = 1 := by
  have h := sqrt3_mul_self
  have : ‖1 - omg‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [omg, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]; nlinarith
  nlinarith [norm_nonneg (1 - omg)]

/-- A positively oriented triangle with side ratios within `1 ± η` has apex ratio near `ω`. -/
lemma near_omega {t : ℂ} {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 40) (h1 : |‖t‖ - 1| ≤ η)
    (h2 : |‖t - 1‖ - 1| ≤ η) (him : 0 < t.im) : ‖t - omg‖ ≤ 10 * η := by
  have h3 := sqrt3_mul_self
  have hs3 : 1.7 < √3 := by nlinarith [Real.sqrt_nonneg 3]
  set x := t.re; set y := t.im
  set N1 := ‖t‖; set N2 := ‖t - 1‖
  have n1 : N1 ^ 2 = x ^ 2 + y ^ 2 := by
    simp only [N1]; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have n2 : N2 ^ 2 = (x - 1) ^ 2 + y ^ 2 := by
    simp only [N2]; rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, x, y]
    ring
  rw [abs_le] at h1 h2
  have hx : |x - 1 / 2| ≤ 3 * η := by
    have e : x - 1 / 2 = (N1 - N2) * (N1 + N2) / 2 := by nlinarith
    rw [e, abs_le]; constructor <;> nlinarith
  have hy2 : |y ^ 2 - 3 / 4| ≤ 6 * η := by
    have e : y ^ 2 - 3 / 4 = (N1 - 1) * (N1 + 1) - (x - 1 / 2) * (x + 1 / 2) := by nlinarith
    rw [abs_le] at hx ⊢
    rw [e]; constructor <;> nlinarith
  have hy : |y - √3 / 2| ≤ 7 * η := by
    have e : (y - √3 / 2) * (y + √3 / 2) = y ^ 2 - 3 / 4 := by nlinarith
    have hp : 0.85 < y + √3 / 2 := by linarith
    rw [abs_le] at hy2 ⊢
    constructor <;> nlinarith
  calc ‖t - omg‖ ≤ |(t - omg).re| + |(t - omg).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |x - 1 / 2| + |y - √3 / 2| := by simp [omg, x, y]
    _ ≤ 10 * η := by linarith

/-- Side ratios: `‖u/v‖` is within `ϱ − 1` of `1` when `‖u‖ = κX`, `‖v‖ = κY`, `X/Y ∈ [1/ϱ, ϱ]`. -/
lemma ratio_near {u v : ℂ} {κ X Y ϱ : ℝ} (hκ : 0 < κ) (hX : 0 < X) (hY : 0 < Y)
    (hu : ‖u‖ = κ * X) (hv : ‖v‖ = κ * Y) (h1 : X ≤ ϱ * Y) (h2 : Y ≤ ϱ * X) :
    |‖u / v‖ - 1| ≤ ϱ - 1 := by
  have hϱ : 0 < ϱ := by
    by_contra h; push Not at h; nlinarith
  rw [norm_div, hu, hv, mul_div_mul_left _ _ hκ.ne', abs_le]
  have hr1 : X / Y ≤ ϱ := by rw [div_le_iff₀ hY]; linarith
  have hr2 : 1 ≤ ϱ * (X / Y) := by rw [mul_div_assoc', le_div_iff₀ hY]; linarith
  constructor <;> nlinarith

lemma norm_sub3 {x y w : ℂ} : ‖x - y - w‖ ≤ ‖x‖ + ‖y‖ + ‖w‖ :=
  (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)

/-- `Im(u/v) > 0` from `Im(v̄ u) > 0`. -/
lemma im_div_pos {u v : ℂ} (h : 0 < ((starRingEnd ℂ) v * u).im) : 0 < (u / v).im := by
  have hv : v ≠ 0 := by rintro rfl; simp at h
  have hn : 0 < Complex.normSq v := Complex.normSq_pos.2 hv
  have e : (u / v).im = ((starRingEnd ℂ) v * u).im / Complex.normSq v := by
    rw [Complex.div_im]; simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [e]; exact div_pos h hn

/-- **Step 2 of Theorem C 4.1.** Tangency of the three sides and positive orientation of the two
center triangles of the rhombus `(0,0),(1,0),(1,1),(0,1)` force the multipliers close to `1`. -/
theorem rhombus_bound {a b : ℂ} {κ ϱ : ℝ} (hκ : 0 < κ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (tan1 : ‖a - 1‖ = κ * (1 + ‖a‖)) (tan2 : ‖b - 1‖ = κ * (1 + ‖b‖))
    (tan3 : ‖b - a‖ = κ * (‖a‖ + ‖b‖))
    (or1 : 0 < ((starRingEnd ℂ) (a - 1) * (b - 1)).im)
    (or2 : 0 < ((starRingEnd ℂ) (a * (b - 1)) * (b - a)).im)
    (r1 : ‖a‖ ≤ ϱ) (r2 : 1 ≤ ϱ * ‖a‖) (r3 : ‖b‖ ≤ ϱ) (r4 : 1 ≤ ϱ * ‖b‖)
    (r5 : ‖b‖ ≤ ϱ * ‖a‖) (r6 : ‖a‖ ≤ ϱ * ‖b‖) (hϱ : ϱ ≤ 1 + 1 / 40) :
    ‖a - 1‖ ≤ 40 * (ϱ - 1) ∧ ‖b - 1‖ ≤ 40 * (ϱ - 1) := by
  set A := ‖a‖; set B := ‖b‖
  have hA : 0 < A := norm_pos_iff.2 ha0
  have hB : 0 < B := norm_pos_iff.2 hb0
  have hϱ1 : 1 ≤ ϱ := by nlinarith
  set η := ϱ - 1
  have hη0 : 0 ≤ η := by simp only [η]; linarith
  have hη : η ≤ 1 / 40 := by simp only [η]; linarith
  have ha1 : a - 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at tan1; nlinarith
  have hb1 : b - 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at tan2; nlinarith
  have hba : b - a ≠ 0 := by
    intro h; rw [h, norm_zero] at tan3; nlinarith
  have hab : a - b ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hba
  -- the products used for the side ratios
  have p1 : A ≤ ϱ * A := by nlinarith only [hϱ1, hA]
  have p2 : B ≤ ϱ * B := by nlinarith only [hϱ1, hB]
  have p3 : B ≤ ϱ * (A * B) := by nlinarith only [r2, hB]
  have p4 : A * B ≤ ϱ * B := by nlinarith only [r1, hB]
  have p5 : A * B ≤ ϱ * (A * B) := by
    nlinarith only [mul_nonneg (sub_nonneg.2 hϱ1) (mul_pos hA hB).le]
  have p6 : A * B ≤ ϱ * A := by nlinarith only [r3, hA]
  have p7 : A ≤ ϱ * (A * B) := by nlinarith only [r4, hA]
  have tan3' : ‖a - b‖ = κ * (A + B) := by rw [norm_sub_rev]; exact tan3
  -- the three ratios
  set t1 := (b - 1) / (a - 1)
  set t2 := (b - a) / (a * (b - 1))
  set s := b * (a - 1) / (a - b)
  have nab1 : ‖a * (b - 1)‖ = κ * (A + A * B) := by rw [norm_mul, tan2]; ring
  have nba1 : ‖b * (1 - a)‖ = κ * (B + A * B) := by
    rw [norm_mul, norm_sub_rev, tan1]; ring
  have nba1' : ‖b * (a - 1)‖ = κ * (B + A * B) := by rw [norm_mul, tan1]; ring
  have t1a : |‖t1‖ - 1| ≤ η := ratio_near hκ (by positivity) (by positivity) tan2 tan1
    (by linarith) (by linarith)
  have t1b : |‖t1 - 1‖ - 1| ≤ η := by
    have e : t1 - 1 = (b - a) / (a - 1) := by simp only [t1]; field_simp; ring
    rw [e]; exact ratio_near hκ (by positivity) (by positivity) tan3 tan1
      (by linarith) (by linarith)
  have t2a : |‖t2‖ - 1| ≤ η := ratio_near hκ (by positivity) (by positivity) tan3 nab1
    (by linarith) (by linarith)
  have t2b : |‖t2 - 1‖ - 1| ≤ η := by
    have e : t2 - 1 = b * (1 - a) / (a * (b - 1)) := by simp only [t2]; field_simp; ring
    rw [e]; exact ratio_near hκ (by positivity) (by positivity) nba1 nab1
      (by linarith) (by linarith)
  have sa : |‖s‖ - 1| ≤ η := ratio_near hκ (by positivity) (by positivity) nba1' tan3'
    (by linarith) (by linarith)
  have sb : |‖s - 1‖ - 1| ≤ η := by
    have e : s - 1 = a * (b - 1) / (a - b) := by simp only [s]; field_simp; ring
    rw [e]; exact ratio_near hκ (by positivity) (by positivity) nab1 tan3'
      (by linarith) (by linarith)
  have it1 : 0 < t1.im := im_div_pos or1
  have it2 : 0 < t2.im := im_div_pos or2
  have is : 0 < s.im := by
    apply im_div_pos
    have e : ((starRingEnd ℂ) (a - b) * (b * (a - 1))).im =
        ((starRingEnd ℂ) (a * (b - 1)) * (b - a)).im := by
      simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
    rw [e]; exact or2
  have e1 := near_omega hη0 hη t1a t1b it1
  have e2 := near_omega hη0 hη t2a t2b it2
  have e3 := near_omega hη0 hη sa sb is
  have hω := omg_sq
  have nω := norm_omg
  have n1ω := norm_one_sub_omg
  set d1 := t1 - omg; set d2 := t2 - omg; set d3 := s - omg
  have hd1 : t1 = omg + d1 := by simp [d1]
  have hd2 : t2 = omg + d2 := by simp [d2]
  have hd3 : s = omg + d3 := by simp [d3]
  constructor
  · -- `(a − 1) t₁ t₂ = d₁(1 − ω) − ω d₂ − d₁ d₂`
    have key : (a - 1) * (t1 * t2) = d1 * (1 - omg) - omg * d2 - d1 * d2 := by
      have e0 : a * (t1 * t2) = t1 - 1 := by simp only [t1, t2]; field_simp; ring
      have : (a - 1) * (t1 * t2) = t1 - 1 - t1 * t2 := by linear_combination e0
      rw [this, hd1, hd2]; linear_combination -hω
    have hn : ‖a - 1‖ * (‖t1‖ * ‖t2‖) ≤ 10 * η + 10 * η + 10 * η * (10 * η) := by
      rw [← norm_mul, ← norm_mul, key]
      calc ‖d1 * (1 - omg) - omg * d2 - d1 * d2‖
          ≤ ‖d1 * (1 - omg)‖ + ‖omg * d2‖ + ‖d1 * d2‖ := norm_sub3
        _ = ‖d1‖ + ‖d2‖ + ‖d1‖ * ‖d2‖ := by rw [norm_mul, norm_mul, norm_mul, n1ω, nω]; ring
        _ ≤ _ := by gcongr
    rw [abs_le] at t1a t2a
    have hp : 0.95 ≤ ‖t1‖ * ‖t2‖ := by
      nlinarith only [t1a.1, t2a.1, hη, hη0, norm_nonneg t1, norm_nonneg t2]
    have hm : ‖a - 1‖ * 0.95 ≤ ‖a - 1‖ * (‖t1‖ * ‖t2‖) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    have hq : 10 * η * (10 * η) ≤ 2.5 * η := by nlinarith only [hη, hη0]
    linarith
  · -- `b − 1 = (1 − ω) d₃ − ω d₁ − d₁ d₃`
    have key : b - 1 = (1 - omg) * d3 - omg * d1 - d1 * d3 := by
      have e0 : (1 - t1) * s = b := by simp only [t1, s]; field_simp; ring
      rw [← e0, hd1, hd3]; linear_combination -hω
    rw [key]
    calc ‖(1 - omg) * d3 - omg * d1 - d1 * d3‖
        ≤ ‖(1 - omg) * d3‖ + ‖omg * d1‖ + ‖d1 * d3‖ := norm_sub3
      _ = ‖d3‖ + ‖d1‖ + ‖d1‖ * ‖d3‖ := by rw [norm_mul, norm_mul, norm_mul, n1ω, nω]; ring
      _ ≤ 10 * η + 10 * η + 10 * η * (10 * η) := by gcongr
      _ ≤ 40 * η := by nlinarith only [hη, hη0]

/-! ### Neighbor ratios -/

/-- The largest ratio of the radii of two neighboring circles, for radii `A^p B^q`. -/
noncomputable def nbrRatio (A B : ℝ) : ℝ :=
  max (max A A⁻¹) (max (max B B⁻¹) (max (B / A) (A / B)))

lemma nbrRatio_props {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A ≤ nbrRatio A B ∧ 1 ≤ nbrRatio A B * A ∧ B ≤ nbrRatio A B ∧ 1 ≤ nbrRatio A B * B ∧
      B ≤ nbrRatio A B * A ∧ A ≤ nbrRatio A B * B ∧ 1 ≤ nbrRatio A B := by
  set ϱ := nbrRatio A B
  have h1 : A ≤ ϱ := le_max_of_le_left (le_max_left _ _)
  have h2 : A⁻¹ ≤ ϱ := le_max_of_le_left (le_max_right _ _)
  have h3 : B ≤ ϱ := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have h4 : B⁻¹ ≤ ϱ := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have h5 : B / A ≤ ϱ := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have h6 : A / B ≤ ϱ := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have g2 : 1 ≤ ϱ * A := by
    have := mul_le_mul_of_nonneg_right h2 hA.le; rwa [inv_mul_cancel₀ hA.ne'] at this
  have g4 : 1 ≤ ϱ * B := by
    have := mul_le_mul_of_nonneg_right h4 hB.le; rwa [inv_mul_cancel₀ hB.ne'] at this
  refine ⟨h1, g2, h3, g4, (div_le_iff₀ hA).1 h5, (div_le_iff₀ hB).1 h6, ?_⟩
  by_contra h; push Not at h; nlinarith

lemma nbr_le_exp {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    nbrRatio ‖a‖ ‖b‖ ≤ Real.exp (max ‖Complex.log a‖
      (max ‖Complex.log b‖ ‖Complex.log b - Complex.log a‖)) := by
  set La := Complex.log a; set Lb := Complex.log b
  set m := max ‖La‖ (max ‖Lb‖ ‖Lb - La‖)
  have na : ‖a‖ = Real.exp La.re := by rw [← Complex.norm_exp, Complex.exp_log ha]
  have nb : ‖b‖ = Real.exp Lb.re := by rw [← Complex.norm_exp, Complex.exp_log hb]
  have h1 : |La.re| ≤ m := (Complex.abs_re_le_norm La).trans (le_max_left _ _)
  have h2 : |Lb.re| ≤ m :=
    (Complex.abs_re_le_norm Lb).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h3 : |Lb.re - La.re| ≤ m := by
    have := Complex.abs_re_le_norm (Lb - La); rw [Complex.sub_re] at this
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
  rw [abs_le] at h1 h2 h3
  unfold nbrRatio
  rw [na, nb, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_sub, ← Real.exp_sub]
  simp only [max_le_iff, Real.exp_le_exp]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-! ### Limits -/

lemma exp_sub_one_le_mul_exp (m : ℝ) : Real.exp m - 1 ≤ m * Real.exp m := by
  have h := Real.add_one_le_exp (-m)
  rw [Real.exp_neg] at h
  have hp := Real.exp_pos m
  have := mul_le_mul_of_nonneg_right h hp.le
  rw [inv_mul_cancel₀ hp.ne'] at this
  nlinarith

lemma tendsto_zero_of_mul {K : ℕ → ℝ} {x : ℕ → ℂ} {ℓ : ℂ} (hK : Tendsto K atTop atTop)
    (hx : Tendsto (fun n => (K n : ℂ) * x n) atTop (𝓝 ℓ)) : Tendsto x atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => ((K n : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp hK)
    simpa [Function.comp_def] using this
  have := hinv.mul hx
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [hK.eventually_gt_atTop 0] with n hn
  have : (K n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma tendsto_mul_exp_sub_one {K : ℕ → ℝ} {x : ℕ → ℂ} {ℓ : ℂ} (hK : Tendsto K atTop atTop)
    (hx : Tendsto (fun n => (K n : ℂ) * x n) atTop (𝓝 ℓ)) :
    Tendsto (fun n => (K n : ℂ) * (Complex.exp (x n) - 1)) atTop (𝓝 ℓ) := by
  have hx0 := tendsto_zero_of_mul hK hx
  have hd : Tendsto (fun n => (K n : ℂ) * (Complex.exp (x n) - 1) - (K n : ℂ) * x n) atTop
      (𝓝 0) := by
    have hb : Tendsto (fun n => ‖(K n : ℂ) * x n‖ * ‖x n‖) atTop (𝓝 0) := by
      have := hx.norm.mul hx0.norm; simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hK.eventually_ge_atTop 0,
      hx0.eventually (Metric.closedBall_mem_nhds 0 one_pos)] with n hn hxn
    rw [dist_zero_right] at hxn
    rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
    have := Complex.norm_exp_sub_one_sub_id_le hxn
    calc K n * ‖Complex.exp (x n) - 1 - x n‖ ≤ K n * ‖x n‖ ^ 2 := by gcongr
      _ = K n * ‖x n‖ * ‖x n‖ := by ring
  have := hx.add hd
  rw [add_zero] at this
  exact this.congr (fun n => by ring)

lemma im_div_eq (u v : ℂ) : (u / v).im = ((starRingEnd ℂ) v * u).im / Complex.normSq v := by
  rw [Complex.div_im]; simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

lemma eq_omg {t : ℂ} (h1 : ‖t‖ = 1) (h2 : ‖t - 1‖ = 1) (h3 : 0 ≤ t.im) : t = omg := by
  have n1 : t.re ^ 2 + t.im ^ 2 = 1 := by
    have := congrArg (· ^ 2) h1; simp only [Complex.sq_norm, Complex.normSq_apply] at this
    nlinarith
  have n2 : (t.re - 1) ^ 2 + t.im ^ 2 = 1 := by
    have := congrArg (· ^ 2) h2; simp only [Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at this
    nlinarith
  have hre : t.re = 1 / 2 := by nlinarith
  have hs := sqrt3_mul_self
  have hs0 := Real.sqrt_nonneg 3
  have him : t.im = √3 / 2 := by
    have e : (t.im - √3 / 2) * (t.im + √3 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 e with h | h
    · linarith
    · nlinarith
  apply Complex.ext <;> simp [omg, hre, him]

lemma omg_norm_sq (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * omg‖ ^ 2 = x ^ 2 + x * y + y ^ 2 := by
  have hs := sqrt3_mul_self
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [omg, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im]
  nlinarith

/-- Cramer's rule for `x u + y v = 2πi` with real `x, y`. -/
lemma cramer2pi {u v : ℂ} (hD : ((starRingEnd ℂ) u * v).im ≠ 0) :
    ((-(2 * π) * v.re / ((starRingEnd ℂ) u * v).im : ℝ) : ℂ) * u +
      ((2 * π * u.re / ((starRingEnd ℂ) u * v).im : ℝ) : ℂ) * v = 2 * π * Complex.I := by
  set D := ((starRingEnd ℂ) u * v).im with hDd
  have e : D = u.re * v.im - u.im * v.re := by
    simp only [hDd, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  have hI : (2 * π * Complex.I : ℂ) = ((0 : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  apply Complex.ext
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hI]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
    field_simp; ring
  · rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hI]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add]
    field_simp; rw [e]; ring

lemma conj_scale_im (u v w : ℂ) :
    ((starRingEnd ℂ) (u * w) * (v * w)).im = Complex.normSq w * ((starRingEnd ℂ) u * v).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]; ring

set_option maxHeartbeats 1000000 in
-- the proof is one long chain of limits and estimates in a large local context
/-- **Steps 3–5 of Theorem C 4.1**, along a sequence on which `K log α₀ → ℓ₁` and
`K log α₁ → ℓ₂`: a neighbor ratio with `K (ϱ − 1) ≥ c₀ > 2π/√3` contradicts univalence. -/
theorem core_limit (a b : ℕ → ℂ) (κ K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (ha0 : ∀ n, a n ≠ 0) (hb0 : ∀ n, b n ≠ 0)
    (tan1 : ∀ n, ‖a n - 1‖ = κ n * (1 + ‖a n‖)) (tan2 : ∀ n, ‖b n - 1‖ = κ n * (1 + ‖b n‖))
    (tan3 : ∀ n, ‖b n - a n‖ = κ n * (‖a n‖ + ‖b n‖))
    (or1 : ∀ n, 0 < ((starRingEnd ℂ) (a n - 1) * (b n - 1)).im)
    (univ : ∀ n, ∀ p q : ℤ, (hnorm p q : ℝ) ≤ 2 * K n → (p, q) ≠ (0, 0) →
      κ n * (1 + ‖a n ^ p * b n ^ q‖) ≤ ‖a n ^ p * b n ^ q - 1‖)
    {ℓ1 ℓ2 : ℂ} (h1 : Tendsto (fun n => (K n : ℂ) * Complex.log (a n)) atTop (𝓝 ℓ1))
    (h2 : Tendsto (fun n => (K n : ℂ) * Complex.log (b n)) atTop (𝓝 ℓ2))
    {c0 : ℝ} (hc0 : 2 * π / √3 < c0)
    (hbad : ∀ n, c0 ≤ K n * (nbrRatio ‖a n‖ ‖b n‖ - 1)) : False := by
  have hK0 : ∀ᶠ n in atTop, 0 ≤ K n := hK.eventually_ge_atTop 0
  have ea : ∀ n, Complex.exp (Complex.log (a n)) = a n := fun n => Complex.exp_log (ha0 n)
  have eb : ∀ n, Complex.exp (Complex.log (b n)) = b n := fun n => Complex.exp_log (hb0 n)
  -- `K(α − 1) → ℓ`
  have ga : Tendsto (fun n => (K n : ℂ) * (a n - 1)) atTop (𝓝 ℓ1) :=
    (tendsto_mul_exp_sub_one hK h1).congr (fun n => by rw [ea])
  have gb : Tendsto (fun n => (K n : ℂ) * (b n - 1)) atTop (𝓝 ℓ2) :=
    (tendsto_mul_exp_sub_one hK h2).congr (fun n => by rw [eb])
  have La0 := tendsto_zero_of_mul hK h1
  have Lb0 := tendsto_zero_of_mul hK h2
  have na : Tendsto (fun n => ‖a n‖) atTop (𝓝 1) := by
    have := ((Complex.continuous_exp.tendsto 0).comp La0).norm
    rw [Complex.exp_zero, norm_one] at this
    exact this.congr (fun n => by simp [ea])
  have nb : Tendsto (fun n => ‖b n‖) atTop (𝓝 1) := by
    have := ((Complex.continuous_exp.tendsto 0).comp Lb0).norm
    rw [Complex.exp_zero, norm_one] at this
    exact this.congr (fun n => by simp [eb])
  -- `Kκ → |ℓ|/2`
  have kk : ∀ {c : ℕ → ℂ} {ℓ : ℂ}, Tendsto (fun n => (K n : ℂ) * (c n - 1)) atTop (𝓝 ℓ) →
      Tendsto (fun n => ‖c n‖) atTop (𝓝 1) → (∀ n, ‖c n - 1‖ = κ n * (1 + ‖c n‖)) →
      Tendsto (fun n => K n * κ n) atTop (𝓝 (‖ℓ‖ / 2)) := by
    intro c ℓ hc hn ht
    have := hc.norm.div (tendsto_const_nhds.add hn) (by norm_num : (1 : ℝ) + 1 ≠ 0)
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [hK0] with n hn0
    change ‖(K n : ℂ) * (c n - 1)‖ / (1 + ‖c n‖) = K n * κ n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn0, ht]
    have : 0 < 1 + ‖c n‖ := by positivity
    field_simp
  have kk1 := kk ga na tan1
  have kk2 := kk gb nb tan2
  have hn12 : ‖ℓ1‖ = ‖ℓ2‖ := by have := tendsto_nhds_unique kk1 kk2; linarith
  have hn3 : ‖ℓ2 - ℓ1‖ = ‖ℓ1‖ := by
    have e1 : Tendsto (fun n => ‖(K n : ℂ) * (b n - a n)‖) atTop (𝓝 ‖ℓ2 - ℓ1‖) :=
      (gb.sub ga).norm.congr (fun n => by congr 1; ring)
    have e2 : Tendsto (fun n => ‖(K n : ℂ) * (b n - a n)‖) atTop
        (𝓝 (‖ℓ1‖ / 2 * (1 + 1))) := by
      refine (kk1.mul (na.add nb)).congr' ?_
      filter_upwards [hK0] with n hn0
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn0, tan3]; ring
    have := tendsto_nhds_unique e1 e2; linarith
  -- orientation in the limit
  have hor : 0 ≤ ((starRingEnd ℂ) ℓ1 * ℓ2).im := by
    have hc : Tendsto (fun n => ((starRingEnd ℂ) ((K n : ℂ) * (a n - 1)) *
        ((K n : ℂ) * (b n - 1))).im) atTop (𝓝 ((starRingEnd ℂ) ℓ1 * ℓ2).im) :=
      (Complex.continuous_im.tendsto _).comp
        (((Complex.continuous_conj.tendsto _).comp ga).mul gb)
    refine ge_of_tendsto' hc (fun n => ?_)
    have e : ((starRingEnd ℂ) ((K n : ℂ) * (a n - 1)) * ((K n : ℂ) * (b n - 1))).im =
        K n * K n * ((starRingEnd ℂ) (a n - 1) * (b n - 1)).im := by
      rw [map_mul, Complex.conj_ofReal, show (K n : ℂ) * (starRingEnd ℂ) (a n - 1) *
        ((K n : ℂ) * (b n - 1)) = ((K n * K n : ℝ) : ℂ) * ((starRingEnd ℂ) (a n - 1) *
        (b n - 1)) by push_cast; ring, Complex.im_ofReal_mul]
    rw [e]; exact mul_nonneg (mul_self_nonneg _) (or1 n).le
  -- Step 5: `|ℓ₁| ≥ c₀`
  set m := fun n => max ‖Complex.log (a n)‖
    (max ‖Complex.log (b n)‖ ‖Complex.log (b n) - Complex.log (a n)‖) with hm
  have hm0 : Tendsto m atTop (𝓝 0) := by
    have := La0.norm.max (Lb0.norm.max (Lb0.sub La0).norm)
    simpa using this
  have hKm : Tendsto (fun n => K n * m n) atTop (𝓝 ‖ℓ1‖) := by
    have := h1.norm.max (h2.norm.max (h2.sub h1).norm)
    rw [← hn12, hn3, max_self, max_self] at this
    refine this.congr' ?_
    filter_upwards [hK0] with n hn0
    simp only [hm]
    rw [mul_max_of_nonneg _ _ hn0, mul_max_of_nonneg _ _ hn0, ← mul_sub, norm_mul, norm_mul,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hn0]
  have hc : c0 ≤ ‖ℓ1‖ := by
    have hlim : Tendsto (fun n => K n * m n * Real.exp (m n)) atTop (𝓝 ‖ℓ1‖) := by
      have := hKm.mul ((Real.continuous_exp.tendsto 0).comp hm0)
      rw [Real.exp_zero, mul_one] at this; exact this
    refine ge_of_tendsto hlim ?_
    filter_upwards [hK0] with n hn0
    have e1 := nbr_le_exp (ha0 n) (hb0 n)
    have e2 := exp_sub_one_le_mul_exp (m n)
    calc c0 ≤ K n * (nbrRatio ‖a n‖ ‖b n‖ - 1) := hbad n
      _ ≤ K n * (Real.exp (m n) - 1) := by gcongr
      _ ≤ K n * (m n * Real.exp (m n)) := by gcongr
      _ = K n * m n * Real.exp (m n) := by ring
  have hpi : 0 < 2 * π / √3 := by positivity
  have hl1 : ℓ1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith
  have hl1n : 0 < ‖ℓ1‖ := norm_pos_iff.2 hl1
  -- Step 3: the limit is conformal, `ℓ₂ = ω ℓ₁`
  have hl2 : ℓ2 = omg * ℓ1 := by
    have ht : ℓ2 / ℓ1 = omg := by
      apply eq_omg
      · rw [norm_div, ← hn12, div_self hl1n.ne']
      · rw [show ℓ2 / ℓ1 - 1 = (ℓ2 - ℓ1) / ℓ1 by field_simp, norm_div, hn3,
          div_self hl1n.ne']
      · rw [im_div_eq]; exact div_nonneg hor (Complex.normSq_nonneg _)
    rw [← ht, div_mul_cancel₀ ℓ2 hl1]
  rw [hl2] at h2
  -- Step 4: the period `2πi` in lattice coordinates
  set ℓa := fun n => (K n : ℂ) * Complex.log (a n) with hℓa
  set ℓb := fun n => (K n : ℂ) * Complex.log (b n) with hℓb
  set D := fun n => ((starRingEnd ℂ) (ℓa n) * ℓb n).im with hDdef
  set Di := ((starRingEnd ℂ) ℓ1 * (omg * ℓ1)).im with hDi
  have hs3 := sqrt3_mul_self
  have hDi' : Di = ‖ℓ1‖ ^ 2 * (√3 / 2) := by
    simp only [hDi]
    rw [show (starRingEnd ℂ) ℓ1 * (omg * ℓ1) = omg * (ℓ1 * (starRingEnd ℂ) ℓ1) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [omg]; ring
  have hDpos : 0 < Di := by rw [hDi']; positivity
  have hD : Tendsto D atTop (𝓝 Di) :=
    (Complex.continuous_im.tendsto _).comp (((Complex.continuous_conj.tendsto _).comp h1).mul h2)
  set xs := fun n => -(2 * π) * (ℓb n).re / D n with hxs_def
  set ys := fun n => 2 * π * (ℓa n).re / D n with hys_def
  set x0 := -(2 * π) * (omg * ℓ1).re / Di with hx0_def
  set y0 := 2 * π * ℓ1.re / Di with hy0_def
  have hxs : Tendsto xs atTop (𝓝 x0) :=
    (tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp h2)).div hD hDpos.ne'
  have hys : Tendsto ys atTop (𝓝 y0) :=
    (tendsto_const_nhds.mul ((Complex.continuous_re.tendsto _).comp h1)).div hD hDpos.ne'
  have hid0 : (x0 : ℂ) * ℓ1 + (y0 : ℂ) * (omg * ℓ1) = 2 * π * Complex.I :=
    cramer2pi (u := ℓ1) (v := omg * ℓ1) hDpos.ne'
  set Q := x0 ^ 2 + x0 * y0 + y0 ^ 2 with hQ
  have hQ' : ‖ℓ1‖ ^ 2 * Q = 4 * π ^ 2 := by
    have e : ℓ1 * ((x0 : ℂ) + (y0 : ℂ) * omg) = 2 * π * Complex.I := by
      rw [← hid0]; ring
    have := congrArg (fun w => ‖w‖ ^ 2) e
    rw [norm_mul, mul_pow, omg_norm_sq] at this
    rw [this]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]; ring
  have hlt : 2 * π < ‖ℓ1‖ * √3 := by
    have := hc0.trans_le hc; rwa [div_lt_iff₀ (by positivity)] at this
  have hQ3 : Q < 3 := by
    by_contra h; push Not at h
    have : 4 * π ^ 2 < 3 * ‖ℓ1‖ ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith
  have hQ0 : 0 < Q := by
    by_contra h; push Not at h
    have : ‖ℓ1‖ ^ 2 * Q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    nlinarith [Real.pi_pos]
  have q1 : 3 * x0 ^ 2 ≤ 4 * Q := by nlinarith only [hQ, sq_nonneg (x0 + 2 * y0)]
  have q2 : 3 * y0 ^ 2 ≤ 4 * Q := by nlinarith only [hQ, sq_nonneg (2 * x0 + y0)]
  have q3 : 3 * (x0 + y0) ^ 2 ≤ 4 * Q := by nlinarith only [hQ, sq_nonneg (x0 - y0)]
  have bx : |x0| < 2 := abs_lt.2 ⟨by nlinarith only [q1, hQ3], by nlinarith only [q1, hQ3]⟩
  have byy : |y0| < 2 := abs_lt.2 ⟨by nlinarith only [q2, hQ3], by nlinarith only [q2, hQ3]⟩
  have bxy : |x0 + y0| < 2 :=
    abs_lt.2 ⟨by nlinarith only [q3, hQ3], by nlinarith only [q3, hQ3]⟩
  set μ := max |x0| |y0| with hμ
  have hμ0 : 0 < μ := by
    by_contra h; push Not at h
    have h1' : |x0| ≤ 0 := (le_max_left _ _).trans h
    have h2' : |y0| ≤ 0 := (le_max_right _ _).trans h
    have ex : x0 = 0 := abs_nonpos_iff.1 h1'
    have ey : y0 = 0 := abs_nonpos_iff.1 h2'
    rw [hQ, ex, ey] at hQ0; norm_num at hQ0
  set M := max |x0| (max |y0| |x0 + y0|) with hM
  have hM2 : M < 2 := max_lt bx (max_lt byy bxy)
  set δ := (2 - M) / 2 with hδ
  have hδ0 : 0 < δ := by simp only [hδ]; linarith
  have hMδ : M < 2 - δ := by simp only [hδ]; linarith
  have ev1 : ∀ᶠ n in atTop, |xs n| < 2 - δ :=
    hxs.abs.eventually (gt_mem_nhds ((le_max_left _ _).trans_lt hMδ))
  have ev2 : ∀ᶠ n in atTop, |ys n| < 2 - δ :=
    hys.abs.eventually (gt_mem_nhds (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hMδ))
  have ev3 : ∀ᶠ n in atTop, |xs n + ys n| < 2 - δ :=
    (hxs.add hys).abs.eventually
      (gt_mem_nhds (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hMδ))
  have ev4 : ∀ᶠ n in atTop, μ / 2 < max |xs n| |ys n| :=
    (hxs.abs.max hys.abs).eventually (lt_mem_nhds (half_lt_self hμ0))
  have ev5 : ∀ᶠ n in atTop, 0 < D n := hD.eventually (lt_mem_nhds hDpos)
  -- the near-period inequality
  set e := fun n => (‖ℓa n - ℓ1‖ + ‖ℓb n - omg * ℓ1‖) / 2 with he
  set E := fun n => ‖ℓ1‖ * (√3 / 2) + e n with hE
  set εn := fun n => E n / K n with hεn
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := ((h1.sub_const ℓ1).norm.add (h2.sub_const (omg * ℓ1)).norm).div_const 2
    simpa using this
  have hE0 : Tendsto E atTop (𝓝 (‖ℓ1‖ * (√3 / 2))) := by
    have := (tendsto_const_nhds (x := ‖ℓ1‖ * (√3 / 2))).add he0
    simpa using this
  have hε0 : Tendsto εn atTop (𝓝 0) := hE0.div_atTop hK
  have hF : Tendsto (fun n => 2 * (K n * κ n) * Real.exp (-εn n) - E n * Real.exp (εn n))
      atTop (𝓝 (2 * (‖ℓ1‖ / 2) * Real.exp (-0) - ‖ℓ1‖ * (√3 / 2) * Real.exp 0)) :=
    ((tendsto_const_nhds.mul kk1).mul ((Real.continuous_exp.tendsto _).comp hε0.neg)).sub
      (hE0.mul ((Real.continuous_exp.tendsto _).comp hε0))
  have hFpos : 0 < 2 * (‖ℓ1‖ / 2) * Real.exp (-0) - ‖ℓ1‖ * (√3 / 2) * Real.exp 0 := by
    rw [neg_zero, Real.exp_zero]
    have : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
    nlinarith only [mul_lt_mul_of_pos_left this hl1n]
  have ev6 : ∀ᶠ n in atTop, 0 < 2 * (K n * κ n) * Real.exp (-εn n) - E n * Real.exp (εn n) :=
    hF.eventually (lt_mem_nhds hFpos)
  obtain ⟨n, h1n, h2n, h3n, h4n, h5n, h6n, hKδ, hKμ⟩ :=
    (ev1.and <| ev2.and <| ev3.and <| ev4.and <| ev5.and <| ev6.and <|
      (hK.eventually_ge_atTop (1 / δ)).and (hK.eventually_ge_atTop (1 / μ))).exists
  -- rounding
  set k := K n with hk
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity) hKδ
  have hkδ : 1 ≤ k * δ := by rwa [div_le_iff₀ hδ0] at hKδ
  have hkμ : 1 ≤ k * μ := by rwa [div_le_iff₀ hμ0] at hKμ
  set p := round (k * xs n) with hp
  set q := round (k * ys n) with hq
  set dp : ℝ := (p : ℝ) - k * xs n with hdp
  set dq : ℝ := (q : ℝ) - k * ys n with hdq
  have hdp1 : |dp| ≤ 1 / 2 := by rw [hdp, abs_sub_comm]; exact abs_sub_round _
  have hdq1 : |dq| ≤ 1 / 2 := by rw [hdq, abs_sub_comm]; exact abs_sub_round _
  rw [abs_le] at hdp1 hdq1
  have hxk : |k * xs n| ≤ k * (2 - δ) := by
    rw [abs_mul, abs_of_pos hkpos]; exact mul_le_mul_of_nonneg_left h1n.le hkpos.le
  have hyk : |k * ys n| ≤ k * (2 - δ) := by
    rw [abs_mul, abs_of_pos hkpos]; exact mul_le_mul_of_nonneg_left h2n.le hkpos.le
  have hxyk : |k * xs n + k * ys n| ≤ k * (2 - δ) := by
    rw [← mul_add, abs_mul, abs_of_pos hkpos]; exact mul_le_mul_of_nonneg_left h3n.le hkpos.le
  rw [abs_le] at hxk hyk hxyk
  have ep : (p : ℝ) = k * xs n + dp := by simp only [hdp]; ring
  have eq' : (q : ℝ) = k * ys n + dq := by simp only [hdq]; ring
  have hpq : (hnorm p q : ℝ) ≤ 2 * k := by
    unfold hnorm; push_cast
    refine max_le (abs_le.2 ⟨by linarith, by linarith⟩)
      (max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩))
  have hne : (p, q) ≠ (0, 0) := by
    intro h
    simp only [Prod.mk.injEq] at h
    have ep0 : (p : ℝ) = 0 := by exact_mod_cast h.1
    have eq0 : (q : ℝ) = 0 := by exact_mod_cast h.2
    have a1 : |k * xs n| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have a2 : |k * ys n| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos hkpos] at a1 a2
    have h7 : k * (μ / 2) < k * max |xs n| |ys n| := mul_lt_mul_of_pos_left h4n hkpos
    rw [mul_max_of_nonneg _ _ hkpos.le] at h7
    have := max_le a1 a2
    linarith
  -- the near-period
  set L := (p : ℂ) * Complex.log (a n) + (q : ℂ) * Complex.log (b n) with hL
  have hexpL : Complex.exp L = a n ^ p * b n ^ q := lattice_log (ha0 n) (hb0 n) p q
  have hcr : (xs n : ℂ) * ℓa n + (ys n : ℂ) * ℓb n = 2 * π * Complex.I :=
    cramer2pi (u := ℓa n) (v := ℓb n) h5n.ne'
  have hid : (k : ℂ) * (L - 2 * π * Complex.I) = (dp : ℂ) * ℓa n + (dq : ℂ) * ℓb n := by
    have ep' : (p : ℂ) = (k : ℂ) * (xs n : ℂ) + (dp : ℂ) := by exact_mod_cast ep
    have eq'' : (q : ℂ) = (k : ℂ) * (ys n : ℂ) + (dq : ℂ) := by exact_mod_cast eq'
    rw [hL, ep', eq'']
    simp only [hℓa, hℓb, hk] at hcr ⊢
    linear_combination (K n : ℂ) * hcr
  have hbound : ‖(dp : ℂ) * ℓa n + (dq : ℂ) * ℓb n‖ ≤ E n := by
    have e0 : (dp : ℂ) * ℓa n + (dq : ℂ) * ℓb n = ℓ1 * ((dp : ℂ) + (dq : ℂ) * omg) +
        (dp : ℂ) * (ℓa n - ℓ1) + (dq : ℂ) * (ℓb n - omg * ℓ1) := by ring
    have hr : ‖(dp : ℂ) + (dq : ℂ) * omg‖ ≤ √3 / 2 := by
      have h := omg_norm_sq dp dq
      have : ‖(dp : ℂ) + (dq : ℂ) * omg‖ ^ 2 ≤ (√3 / 2) ^ 2 := by
        rw [h]
        nlinarith only [hs3, mul_nonneg (sub_nonneg.2 hdp1.2) (neg_le_iff_add_nonneg.1 hdp1.1),
          mul_nonneg (sub_nonneg.2 hdq1.2) (neg_le_iff_add_nonneg.1 hdq1.1),
          mul_nonneg (sub_nonneg.2 hdp1.2) (neg_le_iff_add_nonneg.1 hdq1.1),
          mul_nonneg (sub_nonneg.2 hdq1.2) (neg_le_iff_add_nonneg.1 hdp1.1)]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
    rw [e0]
    calc _ ≤ ‖ℓ1 * ((dp : ℂ) + (dq : ℂ) * omg)‖ + ‖(dp : ℂ) * (ℓa n - ℓ1)‖ +
          ‖(dq : ℂ) * (ℓb n - omg * ℓ1)‖ := norm_add₃_le
      _ = ‖ℓ1‖ * ‖(dp : ℂ) + (dq : ℂ) * omg‖ + |dp| * ‖ℓa n - ℓ1‖ +
          |dq| * ‖ℓb n - omg * ℓ1‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ℓ1‖ * (√3 / 2) + 1 / 2 * ‖ℓa n - ℓ1‖ + 1 / 2 * ‖ℓb n - omg * ℓ1‖ := by
        gcongr
        · exact abs_le.2 ⟨by linarith, by linarith⟩
        · exact abs_le.2 ⟨by linarith, by linarith⟩
      _ = E n := by simp only [hE, he]; ring
  have hLb : ‖L - 2 * π * Complex.I * ((1 : ℤ) : ℂ)‖ ≤ εn n := by
    rw [Int.cast_one, mul_one]
    have : k * ‖L - 2 * π * Complex.I‖ ≤ E n := by
      rw [← hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hkpos.le] at hbound
      exact hbound
    simp only [hεn]
    rw [le_div_iff₀ hkpos]; linarith
  have hεκ : εn n * Real.exp (εn n) < 2 * κ n * Real.exp (-εn n) := by
    have e1 : E n = k * εn n := by simp only [hεn]; rw [← hk]; field_simp
    rw [e1] at h6n
    have : k * (εn n * Real.exp (εn n)) < k * (2 * κ n * Real.exp (-εn n)) := by
      simp only [hk] at h6n ⊢; linarith
    exact lt_of_mul_lt_mul_left this hkpos.le
  have hov := near_period hLb hεκ
  rw [hexpL] at hov
  have := univ n p q hpq hne
  linarith

/-- **Steps 1–2 and the compactness argument.** If `K (ϱ − 1)` is bounded, no sequence of
spirals with univalent `K`-ring data can have `K (ϱ − 1) ≥ c₀ > 2π/√3`. -/
theorem core (a b : ℕ → ℂ) (κ K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hκ : ∀ n, 0 < κ n) (ha0 : ∀ n, a n ≠ 0) (hb0 : ∀ n, b n ≠ 0)
    (tan1 : ∀ n, ‖a n - 1‖ = κ n * (1 + ‖a n‖)) (tan2 : ∀ n, ‖b n - 1‖ = κ n * (1 + ‖b n‖))
    (tan3 : ∀ n, ‖b n - a n‖ = κ n * (‖a n‖ + ‖b n‖))
    (or1 : ∀ n, 0 < ((starRingEnd ℂ) (a n - 1) * (b n - 1)).im)
    (or2 : ∀ n, 0 < ((starRingEnd ℂ) (a n * (b n - 1)) * (b n - a n)).im)
    (univ : ∀ n, ∀ p q : ℤ, (hnorm p q : ℝ) ≤ 2 * K n → (p, q) ≠ (0, 0) →
      κ n * (1 + ‖a n ^ p * b n ^ q‖) ≤ ‖a n ^ p * b n ^ q - 1‖)
    {C : ℝ} (hC : ∀ n, K n * (nbrRatio ‖a n‖ ‖b n‖ - 1) ≤ C)
    {c0 : ℝ} (hc0 : 2 * π / √3 < c0)
    (hbad : ∀ n, c0 ≤ K n * (nbrRatio ‖a n‖ ‖b n‖ - 1)) : False := by
  set η := fun n => nbrRatio ‖a n‖ ‖b n‖ - 1 with hη
  have hη0 : ∀ n, 0 ≤ η n := fun n => by
    have := (nbrRatio_props (norm_pos_iff.2 (ha0 n)) (norm_pos_iff.2 (hb0 n))).2.2.2.2.2.2
    simp only [hη]; linarith
  have hηlim : Tendsto η atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := C)).div_atTop hK) (Eventually.of_forall hη0) ?_
    filter_upwards [hK.eventually_gt_atTop 0] with n hn
    rw [le_div_iff₀ hn, mul_comm]; exact hC n
  have hC0 : 0 ≤ C := by
    have := hC 0
    by_contra h; push Not at h
    have hpi : 0 < 2 * π / √3 := by positivity
    linarith [hbad 0]
  -- Step 2: `K |log α| ≤ 60 C`
  have hbd : ∀ᶠ n in atTop, ((K n : ℂ) * Complex.log (a n), (K n : ℂ) * Complex.log (b n)) ∈
      Metric.closedBall (0 : ℂ × ℂ) (60 * C) := by
    filter_upwards [hηlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 80)),
      hK.eventually_gt_atTop 0] with n hn hKn
    obtain ⟨r1, r2, r3, r4, r5, r6, -⟩ :=
      nbrRatio_props (norm_pos_iff.2 (ha0 n)) (norm_pos_iff.2 (hb0 n))
    have hηn : nbrRatio ‖a n‖ ‖b n‖ - 1 < 1 / 80 := hn
    obtain ⟨ba, bb⟩ := rhombus_bound (hκ n) (ha0 n) (hb0 n) (tan1 n) (tan2 n) (tan3 n) (or1 n)
      (or2 n) r1 r2 r3 r4 r5 r6 (by linarith)
    have hlog : ∀ c : ℂ, ‖c - 1‖ ≤ 40 * (nbrRatio ‖a n‖ ‖b n‖ - 1) →
        ‖(K n : ℂ) * Complex.log c‖ ≤ 60 * C := by
      intro c hc
      have h12 : ‖c - 1‖ ≤ 1 / 2 := by linarith
      have := Complex.norm_log_one_add_half_le_self h12
      rw [show (1 : ℂ) + (c - 1) = c by ring] at this
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hKn.le]
      calc K n * ‖Complex.log c‖ ≤ K n * (3 / 2 * (40 * (nbrRatio ‖a n‖ ‖b n‖ - 1))) := by
            gcongr; linarith
        _ = 60 * (K n * (nbrRatio ‖a n‖ ‖b n‖ - 1)) := by ring
        _ ≤ 60 * C := by linarith [hC n]
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (hlog _ ba) (hlog _ bb)
  -- compactness
  obtain ⟨⟨ℓ1, ℓ2⟩, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hbd.frequently
  have hφK : Tendsto (K ∘ φ) atTop atTop := hK.comp hφ.tendsto_atTop
  exact core_limit (a ∘ φ) (b ∘ φ) (κ ∘ φ) (K ∘ φ) hφK (fun n => ha0 _)
    (fun n => hb0 _) (fun n => tan1 _) (fun n => tan2 _) (fun n => tan3 _) (fun n => or1 _)
    (fun n => univ _) ((continuous_fst.tendsto _).comp hlim)
    ((continuous_snd.tendsto _).comp hlim) hc0 (fun n => hbad _)

/-! ### Theorem C 4.1 -/

/-- The largest neighbor ratio of a spiral is a neighbor ratio of its central flower. -/
lemma nbrRatio_mem {A B : ℝ} :
    ∃ i : Fin 6, Rr (fun p q => A ^ p * B ^ q) ((0 : ℤ × ℤ) + ldir i) = nbrRatio A B := by
  unfold nbrRatio
  rcases max_choice (max A A⁻¹) (max (max B B⁻¹) (max (B / A) (A / B))) with h | h <;> rw [h]
  · rcases max_choice A A⁻¹ with h1 | h1 <;> rw [h1]
    · exact ⟨0, by simp [Rr, ldir]⟩
    · exact ⟨3, by simp [Rr, ldir]⟩
  · rcases max_choice (max B B⁻¹) (max (B / A) (A / B)) with h2 | h2 <;> rw [h2]
    · rcases max_choice B B⁻¹ with h3 | h3 <;> rw [h3]
      · exact ⟨1, by simp [Rr, ldir]⟩
      · exact ⟨4, by simp [Rr, ldir]⟩
    · rcases max_choice (B / A) (A / B) with h3 | h3 <;> rw [h3]
      · exact ⟨2, by simp [Rr, ldir, div_eq_inv_mul]⟩
      · exact ⟨5, by simp [Rr, ldir, div_eq_mul_inv]⟩

/-- **Theorem C 4.1.** Let `P_k` be Doyle spirals with radii `A_k^p B_k^q` whose `k`-ring
patches (centered at `(0,0)`) are univalent, and `ϱ_k` their largest neighbor ratio. Assuming
He's a priori estimate `s_k ≤ C/k`, `limsup k (ϱ_k − 1) ≤ 2π/√3`: for every `ε > 0`, eventually
`k (ϱ_k − 1) ≤ 2π/√3 + ε`. -/
theorem doyle_opt (hHe : ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → sk k ≤ ((C / k : ℝ) : EReal))
    (A B : ℕ → ℝ) (z : ℕ → ℤ → ℤ → ℂ) (hA : ∀ k, 0 < A k) (hB : ∀ k, 0 < B k)
    (hz : ∀ k, IsConfig (fun p q => A k ^ p * B k ^ q) (z k))
    (huniv : ∀ k : ℕ, ∀ u v, InBall k u → InBall k v → u ≠ v →
      Rr (fun p q => A k ^ p * B k ^ q) u + Rr (fun p q => A k ^ p * B k ^ q) v ≤
        ‖Zz (z k) u - Zz (z k) v‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, k * (nbrRatio (A k) (B k) - 1) ≤ 2 * π / √3 + ε := by
  obtain ⟨C, hC⟩ := hHe
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfr : ∃ᶠ k in atTop, 1 ≤ k ∧ 2 * π / √3 + ε < k * (nbrRatio (A k) (B k) - 1) :=
    (hcon.and_eventually (eventually_ge_atTop 1)).mono (fun k h => ⟨h.2, not_le.1 h.1⟩)
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfr
  have hpi : 0 < 2 * π / √3 := by positivity
  -- each bad spiral is not regular
  have hAB : ∀ n, A (φ n) ≠ 1 ∨ B (φ n) ≠ 1 := by
    intro n; by_contra h; push Not at h
    have := (hP n).2
    rw [h.1, h.2] at this
    simp [nbrRatio] at this; linarith
  have hst := fun n => doyle_structure (hA (φ n)) (hB (φ n)) (hz (φ n)) (hAB n)
  choose X a b hna hnb hX hexp hrad using hst
  set w := fun n => z (φ n) 0 0 - X n with hw
  have hw0 : ∀ n, w n ≠ 0 := fun n => sub_ne_zero.2 (hX n)
  have hwn : ∀ n, 0 < ‖w n‖ := fun n => norm_pos_iff.2 (hw0 n)
  have ha0 : ∀ n, a n ≠ 0 := fun n h => by
    have := hA (φ n); rw [← hna n, h, norm_zero] at this; linarith
  have hb0 : ∀ n, b n ≠ 0 := fun n h => by
    have := hB (φ n); rw [← hnb n, h, norm_zero] at this; linarith
  -- centers of the rhombus
  have zz : ∀ n (p q : ℤ), z (φ n) p q = X n + a n ^ p * b n ^ q * w n := fun n p q => by
    have := hexp n p q; simp only [hw]; linear_combination this
  have z00 : ∀ n, z (φ n) 0 0 = X n + w n := fun n => by simpa using zz n 0 0
  have z10 : ∀ n, z (φ n) 1 0 = X n + a n * w n := fun n => by simpa using zz n 1 0
  have z01 : ∀ n, z (φ n) 0 1 = X n + b n * w n := fun n => by simpa using zz n 0 1
  have z11 : ∀ n, z (φ n) 1 1 = X n + a n * b n * w n := fun n => by simpa using zz n 1 1
  set κ := fun n => 1 / ‖w n‖ with hκdef
  have hκ : ∀ n, 0 < κ n := fun n => by simp only [hκdef]; exact one_div_pos.2 (hwn n)
  have tang : ∀ n (u : ℂ) (R : ℝ), ‖u * w n‖ = R → ‖u‖ = κ n * R := fun n u R h => by
    rw [norm_mul] at h; simp only [hκdef]; field_simp [(hwn n).ne']; linarith
  have nsq : ∀ n, 0 < Complex.normSq (w n) := fun n => Complex.normSq_pos.2 (hw0 n)
  have tan1 : ∀ n, ‖a n - 1‖ = κ n * (1 + ‖a n‖) := fun n => by
    have e := (hz (φ n)).t10 0 0
    simp only [zz n, zero_add, zpow_one, zpow_zero, mul_one, one_mul] at e
    refine tang n _ _ ?_
    rw [show (a n - 1) * w n = X n + a n * w n - (X n + w n) by ring, e, hna]; ring
  have tan2 : ∀ n, ‖b n - 1‖ = κ n * (1 + ‖b n‖) := fun n => by
    have e := (hz (φ n)).t01 0 0
    simp only [zz n, zero_add, zpow_one, zpow_zero, mul_one, one_mul] at e
    refine tang n _ _ ?_
    rw [show (b n - 1) * w n = X n + b n * w n - (X n + w n) by ring, e, hnb]; ring
  have tan3 : ∀ n, ‖b n - a n‖ = κ n * (‖a n‖ + ‖b n‖) := fun n => by
    have e := (hz (φ n)).tm11 1 0
    simp only [zz n, zero_add, sub_self, zpow_one, zpow_zero, mul_one, one_mul] at e
    refine tang n _ _ ?_
    rw [show (b n - a n) * w n = X n + b n * w n - (X n + a n * w n) by ring, e, hna, hnb]
    ring
  have or1 : ∀ n, 0 < ((starRingEnd ℂ) (a n - 1) * (b n - 1)).im := fun n => by
    have e := (hz (φ n)).up 0 0
    unfold orient at e
    simp only [zz n, zero_add, zpow_one, zpow_zero, mul_one, one_mul] at e
    rw [show X n + a n * w n - (X n + w n) = (a n - 1) * w n by ring,
      show X n + b n * w n - (X n + w n) = (b n - 1) * w n by ring, conj_scale_im] at e
    exact pos_of_mul_pos_right e (nsq n).le
  have or2 : ∀ n, 0 < ((starRingEnd ℂ) (a n * (b n - 1)) * (b n - a n)).im := fun n => by
    have e := (hz (φ n)).down 1 0
    unfold orient at e
    simp only [zz n, zero_add, sub_self, zpow_one, zpow_zero, mul_one, one_mul] at e
    rw [show X n + a n * b n * w n - (X n + a n * w n) = (a n * (b n - 1)) * w n by ring,
      show X n + b n * w n - (X n + a n * w n) = (b n - a n) * w n by ring, conj_scale_im] at e
    exact pos_of_mul_pos_right e (nsq n).le
  set K := fun n => (φ n : ℝ) with hKdef
  have hK : Tendsto K atTop atTop := tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have univ : ∀ n, ∀ p q : ℤ, (hnorm p q : ℝ) ≤ 2 * K n → (p, q) ≠ (0, 0) →
      κ n * (1 + ‖a n ^ p * b n ^ q‖) ≤ ‖a n ^ p * b n ^ q - 1‖ := by
    intro n p q hpq hne
    have hpq' : hnorm p q ≤ 2 * ((φ n : ℕ) : ℤ) := by
      have : ((hnorm p q : ℤ) : ℝ) ≤ ((2 * ((φ n : ℕ) : ℤ) : ℤ) : ℝ) := by
        push_cast; exact hpq
      exact_mod_cast this
    obtain ⟨u1, u2, hu1, hu2⟩ := (ball_pair _ p q).2 hpq'
    have hu := huniv (φ n) (u1, u2) (u1 + p, u2 + q) ((inBall_iff_hnorm _ _).2 hu1)
      ((inBall_iff_hnorm _ _).2 hu2) (by
        intro h; apply hne; simp only [Prod.mk.injEq] at h ⊢; omega)
    simp only [Rr, Zz] at hu
    by_contra hcon; push Not at hcon
    have hov := (doyle_overlap_iff (ha0 n) (hb0 n) (hX n) (hexp n) (hrad n) u1 u2 p q).2 hcon
    rw [norm_sub_rev] at hov
    linarith
  have hnr : ∀ n, nbrRatio ‖a n‖ ‖b n‖ = nbrRatio (A (φ n)) (B (φ n)) := fun n => by
    rw [hna, hnb]
  have hC' : ∀ n, K n * (nbrRatio ‖a n‖ ‖b n‖ - 1) ≤ C := by
    intro n
    rw [hnr]
    have hk1 := (hP n).1
    have hkpos : (0 : ℝ) < φ n := by exact_mod_cast hk1
    obtain ⟨i, hi⟩ := nbrRatio_mem (A := A (φ n)) (B := B (φ n))
    have hϱ1 := (nbrRatio_props (hA (φ n)) (hB (φ n))).2.2.2.2.2.2
    have hmem : nbrRatio (A (φ n)) (B (φ n)) - 1 ∈ skSet (φ n) := by
      refine ⟨fun p q => A (φ n) ^ p * B (φ n) ^ q, z (φ n), i,
        ⟨(hz (φ n)).isConfigOn _, fun u _ => ?_, huniv (φ n)⟩, ?_⟩
      · simp only [Rr]; exact mul_pos (zpow_pos (hA _) _) (zpow_pos (hB _) _)
      · rw [hi]; simp only [Rr]
        rw [show ((0 : ℤ × ℤ)).1 = 0 from rfl, show ((0 : ℤ × ℤ)).2 = 0 from rfl, zpow_zero,
          zpow_zero, mul_one, div_one, abs_sub_comm, abs_of_nonneg (by linarith)]
    have h1 := (le_sk hmem).trans (hC (φ n) hk1)
    rw [EReal.coe_le_coe_iff, le_div_iff₀ hkpos] at h1
    simp only [hKdef]; linarith
  exact core a b κ K hK hκ ha0 hb0 tan1 tan2 tan3 or1 or2 univ hC'
    (c0 := 2 * π / √3 + ε) (by linarith) (fun n => by rw [hnr]; exact (hP n).2.le)

/-- `D_B` with `B ∈ [B_{k+1}, B*_k)` has a univalent `k`-ring patch. -/
lemma DB_adm {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB1 : Bres (k + 1) ≤ B) (hB2 : B < BstarAll k) :
    AdmPatch k (rad B) (zc B (psi B)) := by
  have hB : 1 < B := lt_of_lt_of_le (Bres_spec (show 2 ≤ k + 1 by omega)).1 hB1
  refine (DB_admissible hB ?_).1
  intro p q p' q' hu hu' hne
  unfold BstarAll at hB2
  by_cases h1 : k = 1
  · subst h1
    have hB2' : B < Bstar1 := by simpa using hB2
    exact patch_univalent_lower1 hB1 hB2' p q p' q' (by exact_mod_cast hu)
      (by exact_mod_cast hu') hne
  · have hB2' : B < Bstar k := by simpa [h1] using hB2
    exact patch_univalent_lower (by omega) hB1 hB2' p q p' q' hu hu' hne

lemma nbrRatio_sq {B : ℝ} (hB : 1 < B) : nbrRatio (B ^ 2) B = B ^ 2 := by
  have hB0 : 0 < B := by linarith
  have h1 : B ≤ B ^ 2 := by nlinarith
  have h2 : B⁻¹ ≤ B ^ 2 := by
    have : B⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB
    nlinarith
  have h3 : (B ^ 2)⁻¹ ≤ B ^ 2 := by
    have : (B ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    nlinarith
  have h4 : B / B ^ 2 ≤ B ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h5 : B ^ 2 / B ≤ B ^ 2 := by
    rw [div_le_iff₀ hB0]; nlinarith
  unfold nbrRatio
  exact le_antisymm (max_le (max_le le_rfl h3) (max_le (max_le h1 h2) (max_le h4 h5)))
    (le_max_of_le_left (le_max_left _ _))

/-- **Theorem C 4.1, sharpness.** The resonant spirals `P_k = D_{B_{k+1}}` (radii
`(B²)^p B^q`) have univalent `k`-ring patches and `k (ϱ_k − 1) → 2π/√3`. -/
theorem doyle_opt_sharp :
    (∀ k : ℕ, 1 ≤ k →
      AdmPatch k (rad (Bres (k + 1))) (zc (Bres (k + 1)) (psi (Bres (k + 1))))) ∧
      Tendsto (fun k : ℕ => (k : ℝ) * (nbrRatio (Bres (k + 1) ^ 2) (Bres (k + 1)) - 1)) atTop
        (𝓝 (2 * π / √3)) := by
  refine ⟨fun k hk => DB_adm hk le_rfl (Bres_lt_BstarAll hk), ?_⟩
  refine Bres_asymp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [nbrRatio_sq (Bres_spec (show 2 ≤ k + 1 by omega)).1]

end DoyleFormal
