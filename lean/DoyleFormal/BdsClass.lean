/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PaperA5
import DoyleFormal.Algebraic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The quadratic family in the classification of Beardon–Dubejko–Stephenson
# (paper A, Theorem 7.5 and Corollaries 7.6–7.7)

Let `t = π/ψ(B)`.

* **Normalization** (proof of Theorem 7.5): the embedding `ι(p,q) = 2p + q w₃` maps `ℤ²`
  bijectively onto the lattice `H = ℤw₁ + ℤw₃`, `w₁ = 1 − √3 i`, `w₃ = 1 + √3 i`; it sends the
  second-neighbor vector `(−1,2)` to `2√3 i`, and `e^{−iπ/3} · 2√3 i = 3 + √3 i = w₁ + 2w₃`.
  The real part of `ℒ(x,y) = 2xλ + y(λ + iψ)` vanishes iff `y = −2x`, and `ℒ(−t, 2t) = 2πi`.
* **Theorem 7.5 (1)–(2)** (`same_circle_rational`): if `ψ = πk/m` with `gcd(k,m) = 1`, then
  `K(u) = K(u′)` iff `u′ − u ∈ ℤ m(−1,2)`.
* **Theorem 7.5 (3)** (`same_circle_irrational`, `center_norm`, `centers_dense`,
  `irrational_overlap`): if `ψ/π` is irrational, the circles are pairwise distinct, the
  centers lie on the circles `|z − X| = |X| B^s` and are dense on each of them, and two
  distinct circles overlap.
* **Corollary 7.6**: `ψ(φ)/π` is irrational (`2cos ψ(φ)` is not an algebraic integer, while
  `2cos(rπ)` is for rational `r`), and `3 < t(φ) < 4`.
* **Transcendence** (Corollary 7.6, second part, and Corollary 7.7) is proved from the
  Gelfond–Schneider theorem, which is not in Mathlib and is stated here as the hypothesis
  `GelfondSchneider`.

Not formalized: the identification `D_B = P_𝔄` itself, which rests on the uniqueness in
Theorem 4 of Beardon–Dubejko–Stephenson (1994), and the numerical value `t(φ) = 3.9114…`.
-/

namespace DoyleFormal

open Complex

/-! ### Normalization -/

/-- The generators `w₁ = 1 − √3 i` and `w₃ = 1 + √3 i` of the lattice `H` of BDS. -/
noncomputable def w1 : ℂ := 1 - (√3 : ℝ) * I
noncomputable def w3 : ℂ := 1 + (√3 : ℝ) * I

/-- The embedding `ι(p,q) = 2p + q w₃` of our lattice. -/
noncomputable def iota (p q : ℤ) : ℂ := 2 * p + q * w3

lemma iota_eq (p q : ℤ) : iota p q = p * w1 + (p + q) * w3 := by
  unfold iota w1 w3; ring

/-- `ι` sends the nearest-neighbor directions to `w₁ + w₃ = 2` and `w₃`. -/
theorem iota_neighbors : iota 1 0 = w1 + w3 ∧ iota 0 1 = w3 := by
  unfold iota w1 w3; constructor <;> push_cast <;> ring

/-- `w₁` and `w₃` are independent over `ℝ`. -/
lemma w_indep {a b : ℝ} (h : (a : ℂ) * w1 + (b : ℂ) * w3 = 0) : a = 0 ∧ b = 0 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [w1, w3] at hre him
  constructor <;> nlinarith

/-- **`ι` maps `ℤ²` bijectively onto `H = ℤw₁ + ℤw₃`.** -/
theorem iota_bij (a b : ℤ) : ∃! u : ℤ × ℤ, iota u.1 u.2 = a * w1 + b * w3 := by
  refine ⟨(a, b - a), ?_, ?_⟩
  · simp only [iota_eq]; push_cast; ring
  · rintro ⟨p, q⟩ h
    simp only [iota_eq] at h
    have h' : (((p - a : ℤ) : ℝ) : ℂ) * w1 + (((p + q - b : ℤ) : ℝ) : ℂ) * w3 = 0 := by
      push_cast; linear_combination h
    obtain ⟨h1, h2⟩ := w_indep h'
    have e1 : p - a = 0 := by exact_mod_cast h1
    have e2 : p + q - b = 0 := by exact_mod_cast h2
    ext <;> simp <;> omega

/-- The second-neighbor vector `(−1,2)` goes to `2√3 i`, and the rotation by `−π/3` (a symmetry
of `H`) takes it to `3 + √3 i = w₁ + 2w₃`, of argument `π/6`. -/
theorem iota_second_neighbor :
    iota (-1) 2 = 2 * (√3 : ℝ) * I ∧
      ((1 / 2 : ℂ) - ((√3 / 2 : ℝ) : ℂ) * I) * (2 * (√3 : ℝ) * I) = 3 + (√3 : ℝ) * I ∧
      (3 : ℂ) + (√3 : ℝ) * I = w1 + 2 * w3 := by
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold iota w3; push_cast; ring
  · push_cast; linear_combination (-(I ^ 2)) * h3 + (-3) * I_sq
  · unfold w1 w3; ring

/-- `e^{−iπ/3} = 1/2 − (√3/2) i`. -/
lemma exp_neg_pi_div_three :
    exp (-(Real.pi / 3 : ℝ) * I) = (1 / 2 : ℂ) - ((√3 / 2 : ℝ) : ℂ) * I := by
  rw [show (-(Real.pi / 3 : ℝ) : ℂ) * I = ((-(Real.pi / 3) : ℝ) : ℂ) * I by push_cast; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast; ring

/-- `ℒ` on real arguments: `ℒ(x,y) = 2xλ + y(λ + iψ)`. -/
noncomputable def Lr (B x y : ℝ) : ℂ :=
  2 * x * (Real.log B : ℂ) + y * ((Real.log B : ℂ) + psi B * I)

/-- `ℒ(v)` is purely imaginary iff `v ∈ ℝ(−1,2)`. -/
theorem Lr_re_eq_zero_iff {B : ℝ} (hB : 1 < B) (x y : ℝ) : (Lr B x y).re = 0 ↔ y = -2 * x := by
  have hl : 0 < Real.log B := Real.log_pos hB
  simp only [Lr, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat, add_im,
    mul_im]
  constructor
  · intro h
    have : (2 * x + y) * Real.log B = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hl.ne'
    linarith
  · intro h; rw [h]; ring

/-- `ℒ(t(−1,2)) = 2πi` for `t = π/ψ`: the period of `D_B` is `t(−1,2)`. -/
theorem Lr_period {B : ℝ} (hB : 1 < B) :
    Lr B (-(Real.pi / psi B)) (2 * (Real.pi / psi B)) = 2 * Real.pi * I := by
  have hψ : psi B ≠ 0 := (psi_mem_Ioo hB).1.ne'
  unfold Lr
  apply Complex.ext <;> simp; field_simp

/-! ### Theorem 7.5 (1) and (2): rational `t` -/

/-- **Theorem A 7.5 (1)–(2).** If `ψ = πk/m` with `gcd(k,m) = 1`, `m ≥ 1`, then two lattice points
carry the same circle iff they differ by a multiple of `m(−1,2)`. For `k = 1`, `m = n` this is
the coherent case `B = B_n`; for `k ≥ 2` it is the `k`-sheeted case `t = m/k`. -/
theorem same_circle_rational {B : ℝ} (hB : 1 < B) {k m : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime k m) (hψ : psi B = Real.pi * k / m) (p q p' q' : ℤ) :
    (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ↔
      ∃ i : ℤ, p' = p - i * m ∧ q' = q + 2 * (i * m) := by
  rw [same_circle_iff _ hB]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have key : ∀ j : ℤ, (∃ K : ℤ, (j : ℝ) * psi B = K * Real.pi) ↔ (m : ℤ) ∣ j := by
    intro j
    constructor
    · rintro ⟨K, hK⟩
      rw [hψ] at hK
      have h1 : ((j * k : ℤ) : ℝ) = ((K * m : ℤ) : ℝ) := by
        push_cast
        field_simp at hK
        nlinarith [Real.pi_pos]
      have h2 : j * k = K * m := by exact_mod_cast h1
      have h3 : (m : ℤ) ∣ j * k := ⟨K, by rw [h2]; ring⟩
      exact Int.dvd_of_dvd_mul_left_of_gcd_one h3 (by
        rw [Int.gcd_natCast_natCast]; exact Nat.Coprime.symm hcop)
    · rintro ⟨i, rfl⟩
      refine ⟨i * k, ?_⟩
      rw [hψ]; push_cast; field_simp
  constructor
  · rintro ⟨j, h1, h2, h3⟩
    obtain ⟨i, rfl⟩ := (key j).1 h3
    exact ⟨i, by rw [h1]; ring, by rw [h2]; ring⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨i * m, h1, h2, (key _).2 ⟨i, by ring⟩⟩

/-! ### Theorem 7.5 (3): irrational `t` -/

/-- **Theorem A 7.5 (3), first part.** If `ψ/π` is irrational, the circles `K(u)` are pairwise
distinct. -/
theorem same_circle_irrational {B : ℝ} (hB : 1 < B) (hirr : Irrational (psi B / Real.pi))
    (p q p' q' : ℤ) :
    (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ↔ p' = p ∧ q' = q := by
  rw [same_circle_iff _ hB]
  constructor
  · rintro ⟨j, h1, h2, K, hK⟩
    by_cases hj : j = 0
    · subst hj; exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩
    · exfalso
      apply hirr
      refine ⟨(K : ℚ) / j, ?_⟩
      have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      push_cast
      rw [div_eq_div_iff hj' Real.pi_pos.ne']
      linarith
  · rintro ⟨rfl, rfl⟩
    exact ⟨0, by ring, by ring, 0, by simp⟩

/-- `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
lemma norm_exp_sub_exp_le (a b : ℝ) :
    ‖exp (a * I) - exp (b * I)‖ ≤ |a - b| := by
  have : exp (a * I) - exp (b * I) = exp (b * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← exp_add]; push_cast; ring_nf
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The centers in polar form about `X`: `z(p,q) − X = B^{2p+q} e^{iqψ} (−X)`. -/
lemma zc_sub_X_polar {B : ℝ} (hB : 1 < B) (ψ : ℝ) (p q : ℤ) :
    zc B ψ p q - X B =
      ((B ^ (2 * p + q) : ℝ) : ℂ) * exp (((q : ℝ) * ψ : ℝ) * I) * (-(X B : ℂ)) := by
  rw [zc_sub_X ψ (by linarith : B ≠ 0)]
  push_cast
  rw [← exp_int_mul]
  ring_nf

/-- **Theorem A 7.5 (3), second part.** The centers lie on the circles `|z − X| = |X| B^s`,
`s = 2p + q`. -/
theorem center_norm {B : ℝ} (hB : 1 < B) (ψ : ℝ) (p q : ℤ) :
    ‖zc B ψ p q - X B‖ = |X B| * B ^ (2 * p + q) := by
  rw [zc_sub_X_polar hB, norm_mul, norm_mul, norm_exp_ofReal_mul_I, norm_neg, norm_real,
    norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (zpow_pos (by linarith : (0 : ℝ) < B) _)]
  ring

/-- Density of the angles `(s − 2p)ψ` modulo `2π` for irrational `ψ/π`. -/
lemma dense_angles {ψ : ℝ} (hirr : Irrational (ψ / Real.pi)) (s : ℤ) (θ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ p K : ℤ, |((s - 2 * p : ℤ) : ℝ) * ψ - θ - 2 * Real.pi * K| < δ := by
  have hirr' : Irrational ((2 * ψ) / (2 * Real.pi)) := by
    rwa [mul_div_mul_left _ _ (two_ne_zero)]
  have hd := dense_addSubgroupClosure_pair_iff.2 hirr'
  obtain ⟨g, hgd, hg⟩ := Metric.dense_iff.1 hd (θ - s * ψ) δ hδ
  obtain ⟨a, b, hab⟩ := AddSubgroup.mem_closure_pair.1 hg
  refine ⟨-a, -b, ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hgd
  simp only [zsmul_eq_mul] at hab
  rw [← hab] at hgd
  convert hgd using 2
  push_cast
  ring

/-- **Theorem A 7.5 (3), third part.** If `ψ/π` is irrational, the centers with `2p + q = s` are
dense on the circle `|z − X| = |X| B^s`: every point `X + B^s e^{iθ}(−X)` of it is a limit of
centers. -/
theorem centers_dense {B : ℝ} (hB : 1 < B) (hirr : Irrational (psi B / Real.pi)) (s : ℤ)
    (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℤ, 2 * p + q = s ∧
      ‖zc B (psi B) p q - (X B + ((B ^ s : ℝ) : ℂ) * exp (θ * I) * (-(X B : ℂ)))‖ < ε := by
  have hB0 : 0 < B := by linarith
  have hX : 0 < |X B| := abs_pos.2 (X_ne_zero hB)
  have hc : 0 < |X B| * B ^ s := mul_pos hX (zpow_pos hB0 s)
  obtain ⟨p, K, hpK⟩ := dense_angles hirr s θ (div_pos hε hc)
  refine ⟨p, s - 2 * p, by ring, ?_⟩
  have hsub : zc B (psi B) p (s - 2 * p) - (X B + ((B ^ s : ℝ) : ℂ) * exp (θ * I) * (-(X B : ℂ)))
      = ((B ^ s : ℝ) : ℂ) * (-(X B : ℂ)) *
        (exp ((((s - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) * I) - exp (θ * I)) := by
    have e : exp ((((s - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) * I) =
        exp ((((s - 2 * p : ℤ) : ℝ) * psi B : ℝ) * I) := by
      rw [show ((((s - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) : ℂ) * I =
        ((((s - 2 * p : ℤ) : ℝ) * psi B : ℝ) : ℂ) * I + (-K : ℤ) * (2 * Real.pi * I) by
          push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    rw [e, show zc B (psi B) p (s - 2 * p) = X B + (zc B (psi B) p (s - 2 * p) - X B) by ring,
      zc_sub_X_polar hB, show 2 * p + (s - 2 * p) = s by ring]
    ring
  rw [hsub, norm_mul, norm_mul, norm_real, norm_neg, norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (zpow_pos hB0 s)]
  calc B ^ s * |X B| * ‖exp ((((s - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) * I) -
        exp (θ * I)‖
      ≤ B ^ s * |X B| * |(((s - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K) - θ| := by
        gcongr; exact norm_exp_sub_exp_le _ _
    _ < B ^ s * |X B| * (ε / (|X B| * B ^ s)) := by
        gcongr; rw [show (((s - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K) - θ =
          ((s - 2 * p : ℤ) : ℝ) * psi B - θ - 2 * Real.pi * K by ring]; exact hpK
    _ = ε := by field_simp

/-- **Theorem A 7.5, last statement, case (3).** If `ψ/π` is irrational, some circle
`K(p, −2p)` with `p ≠ 0`, distinct from `K(0,0)` and of the same radius `1`, overlaps `K(0,0)`:
the distance of the centers is less than the sum of the radii. -/
theorem irrational_overlap {B : ℝ} (hB : 1 < B) (hirr : Irrational (psi B / Real.pi)) :
    ∃ p : ℤ, p ≠ 0 ∧ rad B p (-2 * p) = 1 ∧
      ‖zc B (psi B) p (-2 * p) - zc B (psi B) 0 0‖ < rad B 0 0 + rad B p (-2 * p) := by
  have hB0 : 0 < B := by linarith
  have hX : 0 < |X B| := abs_pos.2 (X_ne_zero hB)
  set δ := min 3 (1 / |X B|) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ3 : δ ≤ 3 := min_le_left _ _
  have hδX : δ * |X B| ≤ 1 := by
    have := min_le_right 3 (1 / |X B|); rw [← hδ] at this
    calc δ * |X B| ≤ 1 / |X B| * |X B| := by gcongr
      _ = 1 := by field_simp
  obtain ⟨p, K, hpK⟩ := dense_angles hirr 0 (δ / 2) (by positivity : 0 < δ / 4)
  have hrad : ∀ p : ℤ, rad B p (-2 * p) = 1 := fun p => by unfold rad; simp
  have hp : p ≠ 0 := by
    rintro rfl
    rw [show (((0 : ℤ) - 2 * 0 : ℤ) : ℝ) * psi B - δ / 2 - 2 * Real.pi * K =
      -(δ / 2) - 2 * Real.pi * K by push_cast; ring, abs_lt] at hpK
    have hpi := Real.pi_gt_three
    have h1 : (K : ℝ) < 0 := by
      by_contra h; push Not at h; nlinarith [Real.pi_pos]
    have h2 : (-1 : ℝ) < K := by nlinarith [Real.pi_pos]
    have : (-1 : ℤ) < K := by exact_mod_cast h2
    have : K < (0 : ℤ) := by exact_mod_cast h1
    omega
  refine ⟨p, hp, hrad p, ?_⟩
  rw [hrad p, show rad B 0 0 = 1 by unfold rad; simp]
  have e0 : zc B (psi B) 0 0 = 0 := by unfold zc; simp
  -- direct estimate
  have hsub : zc B (psi B) p (-2 * p) - zc B (psi B) 0 0 = (-(X B : ℂ)) *
      (exp ((((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) * I) - exp ((0 : ℝ) * I)) := by
    have e : exp ((((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) * I) =
        exp ((((-2 * p : ℤ) : ℝ) * psi B : ℝ) * I) := by
      rw [show ((((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) : ℂ) * I =
        ((((-2 * p : ℤ) : ℝ) * psi B : ℝ) : ℂ) * I + (-K : ℤ) * (2 * Real.pi * I) by
          push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    rw [e, e0, show zc B (psi B) p (-2 * p) = X B + (zc B (psi B) p (-2 * p) - X B) by ring,
      zc_sub_X_polar hB, show 2 * p + -2 * p = 0 by ring]
    simp
    ring
  rw [hsub, norm_mul, norm_neg, norm_real, Real.norm_eq_abs]
  have hb := norm_exp_sub_exp_le ((((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K)) 0
  have hlt : |(((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K) - 0| < δ := by
    rw [sub_zero]
    have := abs_sub_abs_le_abs_sub (((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K) (δ / 2)
    rw [show ((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K - δ / 2 =
      ((0 - 2 * p : ℤ) : ℝ) * psi B - δ / 2 - 2 * Real.pi * K by ring] at this
    rw [abs_of_pos (by positivity : 0 < δ / 2)] at this
    linarith
  calc |X B| * ‖exp ((((0 - 2 * p : ℤ) : ℝ) * psi B - 2 * Real.pi * K : ℝ) * I) -
        exp ((0 : ℝ) * I)‖ ≤ |X B| * δ := by gcongr; linarith
    _ ≤ 1 := by linarith
    _ < 1 + 1 := by norm_num

/-! ### Corollary 7.6: the golden configuration -/

/-- `2 cos ψ(φ) = (4√5 − 2)/5` is not an algebraic integer: otherwise `5x² + 4x = 76/5` would be. -/
theorem two_cosPsi_phi_not_integral : ¬ IsIntegral ℤ (2 * cosPsi φ) := by
  intro h
  set x := 2 * cosPsi φ with hx
  have hval : x = (4 * √5 - 2) / 5 := by rw [hx, cosPsi_phi]; ring
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hq : 5 * x ^ 2 + 4 * x = ((76 / 5 : ℚ) : ℝ) := by
    rw [hval]; push_cast; nlinarith [h5]
  have hint : IsIntegral ℤ (5 * x ^ 2 + 4 * x) := by
    have h5i : IsIntegral ℤ (5 : ℝ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := 5))
    have h4i : IsIntegral ℤ (4 : ℝ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := 4))
    exact (h5i.mul (h.pow 2)).add (h4i.mul h)
  obtain ⟨k, hk⟩ := (hint.exists_int_iff_exists_rat).1 ⟨76 / 5, hq⟩
  rw [hq] at hk
  have : (76 : ℝ) = 5 * k := by push_cast at hk; linarith
  have : (76 : ℤ) = 5 * k := by exact_mod_cast this
  omega

/-- **Corollary A 7.6, first part.** `ψ(φ)/π` is irrational. -/
theorem psi_phi_irrational : Irrational (psi φ / Real.pi) := by
  rintro ⟨r, hr⟩
  apply two_cosPsi_phi_not_integral
  have hψ : psi φ = r * Real.pi := by
    rw [hr]; field_simp
  rw [← cos_psi one_lt_phi, hψ]
  exact Real.isIntegral_two_mul_cos_rat_mul_pi r

/-- **Corollary A 7.6.** The golden configuration is in case (3): its circles are pairwise
distinct and its centers lie on the circles `|z + √5| = √5 φ^s`, densely on each. -/
theorem golden_case3 :
    (∀ p q p' q' : ℤ, (rad φ p' q' = rad φ p q ∧ zc φ (psi φ) p' q' = zc φ (psi φ) p q) ↔
        p' = p ∧ q' = q) ∧
      (∀ p q : ℤ, ‖zc φ (psi φ) p q + √5‖ = √5 * φ ^ (2 * p + q)) ∧
      (∀ (s : ℤ) (θ ε : ℝ), 0 < ε → ∃ p q : ℤ, 2 * p + q = s ∧
        ‖zc φ (psi φ) p q - (-√5 + ((φ ^ s : ℝ) : ℂ) * exp (θ * I) * √5)‖ < ε) := by
  refine ⟨same_circle_irrational one_lt_phi psi_phi_irrational, fun p q => ?_, fun s θ ε hε => ?_⟩
  · have := center_norm one_lt_phi (psi φ) p q
    rwa [X_phi, abs_neg, abs_of_pos (by positivity), ofReal_neg, sub_neg_eq_add] at this
  · have := centers_dense one_lt_phi psi_phi_irrational s θ hε
    simpa [X_phi] using this

/-- **Corollary A 7.6.** `3 < t(φ) < 4`: the golden configuration lies between the coherent
spirals `[3,6]` and `[4,8]`. -/
theorem t_phi_bounds : 3 < Real.pi / psi φ ∧ Real.pi / psi φ < 4 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h5p : 0 < √5 := by positivity
  have h2p : 0 < √2 := by positivity
  have hc := cosPsi_phi
  have hψ := psi_mem_Ioo one_lt_phi
  have hlo : cosPsi φ < √2 / 2 := by
    rw [hc]
    have h52 : 4 * √5 - 2 < 5 * √2 := by
      have : (4 * √5 - 2) ^ 2 < (5 * √2) ^ 2 := by nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
    linarith
  have hhi : 1 / 2 < cosPsi φ := by
    rw [hc]
    have : 7 < 4 * √5 := by nlinarith
    linarith
  have hmem := cosPsi_mem_Ioo one_lt_phi
  -- `π/4 < ψ(φ) < π/3`
  have a1 : Real.pi / 4 < psi φ := by
    unfold psi
    rw [← Real.cos_pi_div_four] at hlo
    have := Real.arccos_lt_arccos hmem.1.le hlo (by
      rw [Real.cos_pi_div_four]; nlinarith)
    rwa [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at this
  have a2 : psi φ < Real.pi / 3 := by
    unfold psi
    rw [← Real.cos_pi_div_three] at hhi
    have := Real.arccos_lt_arccos (by rw [Real.cos_pi_div_three]; norm_num) hhi hmem.2.le
    rwa [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at this
  have hpi := Real.pi_pos
  constructor
  · rw [lt_div_iff₀ hψ.1]; linarith
  · rw [div_lt_iff₀ hψ.1]; linarith

/-! ### Transcendence, from the Gelfond–Schneider theorem -/

/-- **The Gelfond–Schneider theorem** (not in Mathlib; used as a hypothesis): if `a ≠ 0, 1` and
`b` are algebraic and `b` is irrational, then `a^b` (principal value) is transcendental. -/
def GelfondSchneider : Prop :=
  ∀ a b : ℂ, IsAlgebraic ℤ a → IsAlgebraic ℤ b → a ≠ 0 → a ≠ 1 → (∀ r : ℚ, b ≠ r) →
    Transcendental ℤ (a ^ b)

lemma isAlgebraic_ofReal {x : ℝ} (h : IsAlgebraic ℤ x) : IsAlgebraic ℤ (x : ℂ) := by
  have := h.algebraMap (A := ℂ)
  simpa using this

lemma isAlgebraic_I : IsAlgebraic ℤ I :=
  IsAlgebraic.of_pow two_pos (by rw [I_sq]; exact isAlgebraic_one.neg)

/-- If `e^{iπρ}` is algebraic, then `ρ` is rational or transcendental (Gelfond–Schneider with
`a = −1`, `log(−1) = iπ`). -/
theorem rat_or_transcendental (hGS : GelfondSchneider) {ρ : ℝ}
    (h : IsAlgebraic ℤ (exp ((ρ * Real.pi : ℝ) * I))) :
    (∃ r : ℚ, ρ = r) ∨ Transcendental ℤ ρ := by
  by_contra hc
  push Not at hc
  obtain ⟨hirr, halg⟩ := hc
  have halg' : IsAlgebraic ℤ ((ρ : ℂ)) := isAlgebraic_ofReal (by
    by_contra h'; exact halg h')
  have hne : ∀ r : ℚ, (ρ : ℂ) ≠ r := by
    intro r hr
    apply hirr r
    exact_mod_cast hr
  have ht := hGS (-1) ρ (isAlgebraic_one.neg) halg' (by norm_num) (by norm_num) hne
  apply ht
  rw [cpow_def_of_ne_zero (by norm_num), log_neg_one]
  convert h using 2
  push_cast; ring

/-- `e^{iψ}` is algebraic when `cos ψ` is. -/
lemma isAlgebraic_exp_psi {B : ℝ} (hB : 1 < B) (hc : IsAlgebraic ℤ (cosPsi B)) :
    IsAlgebraic ℤ (exp ((psi B : ℝ) * I)) := by
  have hs : IsAlgebraic ℤ (Real.sin (psi B)) := by
    unfold psi
    rw [Real.sin_arccos]
    have hm := cosPsi_mem_Ioo hB
    exact isAlgebraic_sqrt (by nlinarith [hm.1, hm.2]) (isAlgebraic_one.sub (hc.pow 2))
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, cos_psi hB]
  exact (isAlgebraic_ofReal hc).add ((isAlgebraic_ofReal hs).mul isAlgebraic_I)

/-- **Corollary A 7.6, second part** (assuming Gelfond–Schneider). `ψ(φ)/π` is transcendental. -/
theorem psi_phi_transcendental (hGS : GelfondSchneider) : Transcendental ℤ (psi φ / Real.pi) := by
  have hc : IsAlgebraic ℤ (cosPsi φ) := by
    rw [cosPsi_phi]
    have h5 : IsAlgebraic ℤ (√5) := isAlgebraic_sqrt (by norm_num) (by
      simpa using isAlgebraic_nat 5)
    have := ((isAlgebraic_nat 2).mul h5 |>.sub isAlgebraic_one).mul (isAlgebraic_nat 5).inv
    simpa [div_eq_mul_inv] using this
  have he := isAlgebraic_exp_psi one_lt_phi hc
  rcases rat_or_transcendental hGS (ρ := psi φ / Real.pi) (by
    rwa [div_mul_cancel₀ _ Real.pi_pos.ne']) with ⟨r, hr⟩ | ht
  · exact absurd ⟨r, hr.symm⟩ psi_phi_irrational
  · exact ht

/-- **Corollary A 7.7** (assuming Gelfond–Schneider). If `B > 1` is algebraic, then
`t(B) = π/ψ(B)` is rational or transcendental. -/
theorem t_rat_or_transcendental (hGS : GelfondSchneider) {B : ℝ} (hB : 1 < B)
    (halg : IsAlgebraic ℤ B) :
    (∃ r : ℚ, Real.pi / psi B = r) ∨ Transcendental ℤ (Real.pi / psi B) := by
  have hB0 : 0 < B := by linarith
  have hη : IsAlgebraic ℤ (eta B) := by
    unfold eta
    have := ((isAlgebraic_nat 2).mul halg).mul ((halg.pow 2).add isAlgebraic_one).inv
    simpa [div_eq_mul_inv] using this
  have hc : IsAlgebraic ℤ (cosPsi B) := by
    rw [cosPsi_eq_eta]; exact ((hη.pow 2).add hη).sub isAlgebraic_one
  have hψ0 := (psi_mem_Ioo hB).1
  rcases rat_or_transcendental hGS (ρ := psi B / Real.pi) (by
    rw [div_mul_cancel₀ _ Real.pi_pos.ne']; exact isAlgebraic_exp_psi hB hc) with ⟨r, hr⟩ | ht
  · left
    refine ⟨r⁻¹, ?_⟩
    push_cast
    rw [← hr, inv_div]
  · right
    intro ha
    apply ht
    have := ha.inv
    rwa [inv_div] at this

end DoyleFormal
