/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.GeoPacking

/-!
# The center triangles of `D_B` cover `ℂ ∖ {X}` (Theorem B 7.2, tiling) — Phase 5g

The triangles of `D_B` are the upward triangles `(p,q), (p+1,q), (p,q+1)` and the downward
triangles `(p,q), (p,q+1), (p−1,q+1)`. All of them lie in the sectors between the rays from
`X` at angles `qψ` and `(q+1)ψ`. In such a sector, with `w − X = x e₀ + y e₁`
(`e₀ = e^{iqψ}`, `e₁ = e^{i(q+1)ψ}`), the triangles form a ladder whose rungs are the lines
`u/c + v/c' = 1` with nondecreasing `c, c'` (`u = x/|X|`, `v = y/(|X| B)`).

* `InTri w a b c`: `w` is a convex combination of `a, b, c`.
* `DB_cover` (**covering**): for every `B > 1`, every point `w ≠ X` lies in a closed upward or
  downward triangle of `D_B`.
-/

namespace DoyleFormal

open Complex

/-- `w` lies in the closed triangle `a, b, c`. -/
def InTri (w a b c : ℂ) : Prop :=
  ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
    w = (la : ℂ) * a + (lb : ℂ) * b + (lc : ℂ) * c

/-- `Im(conj a · b)`. -/
noncomputable def cross (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

lemma cramer (d e0 e1 : ℂ) :
    (cross e0 e1 : ℂ) * d = (cross d e1 : ℂ) * e0 + (cross e0 d : ℂ) * e1 := by
  apply Complex.ext <;> simp [cross] <;> ring

lemma cross_exp (s t : ℝ) : cross (exp (s * I)) (exp (t * I)) = Real.sin (t - s) := by
  simp only [cross, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_sub]
  ring

lemma cross_exp_polar (s r θ : ℝ) :
    cross (exp (s * I)) ((r : ℂ) * exp (θ * I)) = r * Real.sin (θ - s) := by
  simp only [cross, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Real.sin_sub]
  ring

lemma cross_polar_exp (s r θ : ℝ) :
    cross ((r : ℂ) * exp (θ * I)) (exp (s * I)) = r * Real.sin (s - θ) := by
  simp only [cross, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Real.sin_sub]
  ring

/-- The closed form with the factor `|X| B^{2p+q}` and the direction `e^{iqψ}`. -/
lemma zc_polar {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q : ℤ) :
    zc B ψ p q = X B + (((-X B) * B ^ (2 * p + q) : ℝ) : ℂ) * exp (((q * ψ : ℝ) : ℂ) * I) := by
  have hB0 : B ≠ 0 := by linarith
  have h := zc_sub_X ψ hB0 p q
  rw [exp_zpow_eq] at h
  rw [← sub_eq_iff_eq_add', h]
  push_cast; ring

/-- **The center triangles of `D_B` cover `ℂ ∖ {X}`.** -/
theorem DB_cover {B : ℝ} (hB : 1 < B) (w : ℂ) (hw : w ≠ X B) :
    ∃ p q : ℤ, InTri w (zc B (psi B) p q) (zc B (psi B) (p + 1) q) (zc B (psi B) p (q + 1)) ∨
      InTri w (zc B (psi B) p q) (zc B (psi B) p (q + 1)) (zc B (psi B) (p - 1) (q + 1)) := by
  set ψ := psi B with hψdef
  have hψ := psi_mem_Ioo hB
  have hB0 : 0 < B := by linarith
  set R0 := -X B with hR0def
  have hR0 : 0 < R0 := by simp only [R0]; linarith [X_neg hB]
  obtain ⟨d, hd⟩ : ∃ d, d = w - X B := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact sub_ne_zero.2 hw
  set θ := arg d
  set r := ‖d‖
  have hr : 0 < r := norm_pos_iff.2 hd0
  have hdpol : d = (r : ℂ) * exp (θ * I) := (norm_mul_exp_arg_mul_I d).symm
  -- the sector
  set q := ⌊θ / ψ⌋ with hq
  have hq1 : (q : ℝ) * ψ ≤ θ := by
    have := Int.floor_le (θ / ψ); rw [le_div_iff₀ hψ.1] at this; linarith
  have hq2 : θ < ((q : ℝ) + 1) * ψ := by
    have := Int.lt_floor_add_one (θ / ψ); rw [div_lt_iff₀ hψ.1] at this; linarith
  set e0 := exp (((q * ψ : ℝ) : ℂ) * I) with he0
  set e1 := exp ((((q + 1 : ℤ) * ψ : ℝ) : ℂ) * I) with he1
  have hsin : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hc01 : cross e0 e1 = Real.sin ψ := by
    rw [cross_exp]; congr 1; push_cast; ring
  -- coordinates in the sector
  set x := cross d e1 / Real.sin ψ
  set y := cross e0 d / Real.sin ψ
  have hx : 0 ≤ x := by
    apply div_nonneg _ hsin.le
    rw [hdpol, cross_polar_exp]
    apply mul_nonneg hr.le
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · push_cast; linarith
    · push_cast; linarith [hψ.2]
  have hy : 0 ≤ y := by
    apply div_nonneg _ hsin.le
    rw [hdpol, cross_exp_polar]
    apply mul_nonneg hr.le
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · nlinarith [hψ.2]
  have hdxy : d = (x : ℂ) * e0 + (y : ℂ) * e1 := by
    have h := cramer d e0 e1
    rw [hc01] at h
    have hs : ((Real.sin ψ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin.ne'
    apply mul_left_cancel₀ hs
    rw [h]
    simp only [x, y]
    rw [Complex.ofReal_div, Complex.ofReal_div]
    field_simp
  have hxy : 0 < x + y := by
    rcases (add_nonneg hx hy).lt_or_eq with h | h
    · exact h
    · exfalso
      have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by linarith
      rw [hx0, hy0, Complex.ofReal_zero, zero_mul, zero_mul, add_zero] at hdxy; exact hd0 hdxy
  -- rescaled coordinates and the rung
  set u := x / R0
  set v := y / (R0 * B)
  have hu : 0 ≤ u := div_nonneg hx hR0.le
  have hv : 0 ≤ v := div_nonneg hy (by positivity)
  have huv : 0 < u + v := by
    by_cases hx0 : 0 < x
    · have : 0 < u := div_pos hx0 hR0
      linarith
    · have hy0 : 0 < y := by linarith
      have : 0 < v := div_pos hy0 (mul_pos hR0 hB0)
      linarith
  have hBq : 0 < B ^ q := by positivity
  obtain ⟨p, hp1, hp2⟩ := exists_mem_Ico_zpow (div_pos huv hBq) (one_lt_pow₀ hB two_ne_zero)
  -- `c_k = B^{2k+q}`
  have hc : ∀ k : ℤ, B ^ (2 * k + q) = (B ^ 2) ^ k * B ^ q := by
    intro k
    rw [zpow_add₀ hB0.ne', zpow_mul, ← zpow_natCast]; norm_num
  set cp := B ^ (2 * p + q)
  set cp1 := B ^ (2 * (p + 1) + q)
  have hcp : 0 < cp := by positivity
  have hcp1 : cp1 = B ^ 2 * cp := by
    simp only [cp1, cp]
    rw [show 2 * (p + 1) + q = (2 * p + q) + 2 by ring, zpow_add₀ hB0.ne']; norm_num; ring
  have hB2 : 1 < B ^ 2 := one_lt_pow₀ hB two_ne_zero
  have hD : 0 < cp1 - cp := by rw [hcp1]; nlinarith
  have hcp1pos : 0 < cp1 := by linarith
  have hDne : cp1 - cp ≠ 0 := hD.ne'
  have hcpne : cp ≠ 0 := hcp.ne'
  have hcp1ne : cp1 ≠ 0 := hcp1pos.ne'
  have hcpe : cp = (B ^ 2) ^ p * B ^ q := hc p
  have hcp1e : cp1 = (B ^ 2) ^ (p + 1) * B ^ q := hc (p + 1)
  have hF1 : 1 ≤ (u + v) / cp := by
    rw [le_div_iff₀ hcp, one_mul, hcpe]
    exact (le_div_iff₀ hBq).1 hp1
  have hF2 : (u + v) / cp1 < 1 := by
    rw [div_lt_one (by positivity), hcp1e]
    exact (div_lt_iff₀ hBq).1 hp2
  -- the vertices
  have zA : zc B ψ p q = X B + ((R0 * cp : ℝ) : ℂ) * e0 := by rw [zc_polar ψ hB]
  have zC : zc B ψ (p + 1) q = X B + ((R0 * cp1 : ℝ) : ℂ) * e0 := by rw [zc_polar ψ hB]
  have zB : zc B ψ p (q + 1) = X B + ((R0 * (B * cp) : ℝ) : ℂ) * e1 := by
    rw [zc_polar ψ hB, he1, show 2 * p + (q + 1) = (2 * p + q) + 1 by ring, zpow_add₀ hB0.ne',
      zpow_one]
    simp only [cp, R0]; push_cast; ring
  have zB' : zc B ψ (p + 1) (q + 1) = X B + ((R0 * (B * cp1) : ℝ) : ℂ) * e1 := by
    rw [zc_polar ψ hB, he1, show 2 * (p + 1) + (q + 1) = (2 * (p + 1) + q) + 1 by ring,
      zpow_add₀ hB0.ne', zpow_one]
    simp only [cp1, R0]; push_cast; ring
  have hwXd : w = X B + (((R0 * u) : ℝ) : ℂ) * e0 + (((R0 * B * v) : ℝ) : ℂ) * e1 := by
    have : w = X B + d := by rw [hd]; ring
    have h1 : R0 * u = x := by simp only [u]; field_simp
    have h2 : R0 * B * v = y := by simp only [v]; field_simp
    rw [this, hdxy, h1, h2]; ring
  set G := u / cp1 + v / cp
  by_cases hG : G ≤ 1
  · -- the upward triangle `(p,q), (p+1,q), (p,q+1)`
    refine ⟨p, q, Or.inl ?_⟩
    refine ⟨(1 - G) * cp1 / (cp1 - cp), ((u + v) / cp - 1) * cp / (cp1 - cp), v / cp, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact div_nonneg (mul_nonneg (by linarith) (by positivity)) hD.le
    · exact div_nonneg (mul_nonneg (by linarith) hcp.le) hD.le
    · exact div_nonneg hv hcp.le
    · simp only [G]; field_simp; ring
    · rw [zA, zC, zB, hwXd]
      have hla : ((1 - G) * cp1 / (cp1 - cp)) * cp + (((u + v) / cp - 1) * cp / (cp1 - cp)) * cp1
          = u := by simp only [G]; field_simp; ring
      have hlb : (v / cp) * (B * cp) = B * v := by field_simp
      have hsum : (1 - G) * cp1 / (cp1 - cp) + ((u + v) / cp - 1) * cp / (cp1 - cp) + v / cp
          = 1 := by simp only [G]; field_simp; ring
      have hla' := congrArg (fun t : ℝ => (t : ℂ)) hla
      have hlb' := congrArg (fun t : ℝ => (t : ℂ)) hlb
      have hsum' := congrArg (fun t : ℝ => (t : ℂ)) hsum
      push_cast at hla' hlb' hsum' ⊢
      linear_combination (-(X B : ℂ)) * hsum' - (R0 : ℂ) * e0 * hla' - (R0 : ℂ) * e1 * hlb'
  · -- the downward triangle `(p+1,q), (p+1,q+1), (p,q+1)`
    refine ⟨p + 1, q, Or.inr ?_⟩
    push Not at hG
    refine ⟨u / cp1, cp * (G - 1) / (cp1 - cp), cp1 * (1 - (u + v) / cp1) / (cp1 - cp), ?_, ?_,
      ?_, ?_, ?_⟩
    · exact div_nonneg hu (by positivity)
    · exact div_nonneg (mul_nonneg hcp.le (by linarith)) hD.le
    · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) hD.le
    · simp only [G]; field_simp; ring
    · rw [show p + 1 - 1 = p by ring, zC, zB', zB, hwXd]
      have hla : (u / cp1) * cp1 = u := by field_simp
      have hlb : (cp * (G - 1) / (cp1 - cp)) * (B * cp1) +
          (cp1 * (1 - (u + v) / cp1) / (cp1 - cp)) * (B * cp) = B * v := by
        simp only [G]; field_simp; ring
      have hsum : u / cp1 + cp * (G - 1) / (cp1 - cp) + cp1 * (1 - (u + v) / cp1) / (cp1 - cp)
          = 1 := by simp only [G]; field_simp; ring
      have hla' := congrArg (fun t : ℝ => (t : ℂ)) hla
      have hlb' := congrArg (fun t : ℝ => (t : ℂ)) hlb
      have hsum' := congrArg (fun t : ℝ => (t : ℂ)) hsum
      push_cast at hla' hlb' hsum' ⊢
      linear_combination (-(X B : ℂ)) * hsum' - (R0 : ℂ) * e0 * hla' - (R0 : ℂ) * e1 * hlb'

/-! ### Disjointness for `B = B_n` -/

/-- The vertices of the upward (`up = true`) or downward triangle at `(p,q)`. -/
noncomputable def triV (B : ℝ) (up : Bool) (p q : ℤ) : ℂ × ℂ × ℂ :=
  if up then (zc B (psi B) p q, zc B (psi B) (p + 1) q, zc B (psi B) p (q + 1))
  else (zc B (psi B) p q, zc B (psi B) p (q + 1), zc B (psi B) (p - 1) (q + 1))

/-- `w` lies in the open triangle (all barycentric weights positive). -/
def InTriOpen (w : ℂ) (t : ℂ × ℂ × ℂ) : Prop :=
  ∃ la lb lc : ℝ, 0 < la ∧ 0 < lb ∧ 0 < lc ∧ la + lb + lc = 1 ∧
    w = (la : ℂ) * t.1 + (lb : ℂ) * t.2.1 + (lc : ℂ) * t.2.2

lemma cross_add_smul (a b : ℝ) (e0 e1 f : ℂ) :
    cross ((a : ℂ) * e0 + (b : ℂ) * e1) f = a * cross e0 f + b * cross e1 f := by
  simp [cross]; ring

lemma cross_self (e : ℂ) : cross e e = 0 := by simp [cross]; ring

lemma cross_anti (e f : ℂ) : cross f e = -cross e f := by simp [cross]; ring

/-- Coordinates with respect to two independent directions are unique. -/
lemma coords_unique {e0 e1 : ℂ} (h : cross e0 e1 ≠ 0) {a b a' b' : ℝ}
    (heq : (a : ℂ) * e0 + (b : ℂ) * e1 = (a' : ℂ) * e0 + (b' : ℂ) * e1) : a = a' ∧ b = b' := by
  have h1 := congrArg (fun z => cross z e1) heq
  have h0 := congrArg (fun z => cross z e0) heq
  simp only [cross_add_smul, cross_self, cross_anti e0 e1] at h1 h0
  constructor
  · have : (a - a') * cross e0 e1 = 0 := by linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h)
  · have : (b - b') * cross e0 e1 = 0 := by linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h)

/-- A positive combination of `1` and `e^{iψ}` has argument in `(0, ψ)`. -/
lemma arg_pos_comb {ψ x y : ℝ} (hψ0 : 0 < ψ) (hψ : ψ < Real.pi) (hx : 0 < x) (hy : 0 < y) :
    0 < arg ((x : ℂ) + (y : ℂ) * exp (ψ * I)) ∧ arg ((x : ℂ) + (y : ℂ) * exp (ψ * I)) < ψ := by
  set z := (x : ℂ) + (y : ℂ) * exp (ψ * I)
  have hsin : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ0 hψ
  have hzim : 0 < z.im := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith
  have h1 := arg_mem_Ioo_of_im_pos hzim
  refine ⟨h1.1, ?_⟩
  -- the angle from `z` to `e^{iψ}` is also in `(0, π)`, and the two add up to `ψ`
  have hz0 : z ≠ 0 := fun h => by rw [h] at hzim; simp at hzim
  set z' := exp (ψ * I) / z
  have hz'im : 0 < z'.im := by
    have : z' = exp (ψ * I) * (starRingEnd ℂ) z / (Complex.normSq z : ℂ) := by
      simp only [z']; rw [div_eq_mul_inv, Complex.inv_def]; push_cast; ring
    rw [this, Complex.div_ofReal_im]
    apply div_pos _ (Complex.normSq_pos.2 hz0)
    simp only [z, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re]
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  have h2 := arg_mem_Ioo_of_im_pos hz'im
  have hz'0 : z' ≠ 0 := fun h => by rw [h] at hz'im; simp at hz'im
  have hprod : z * z' = exp (ψ * I) := by simp only [z']; field_simp
  have hexp : exp (((arg z + arg z' : ℝ) : ℂ) * I) = exp ((ψ : ℂ) * I) := by
    have hn : ∀ t : ℂ, t ≠ 0 → exp ((arg t : ℂ) * I) = t / (‖t‖ : ℂ) := fun t ht => by
      have : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ht
      rw [eq_div_iff this, mul_comm]; exact norm_mul_exp_arg_mul_I t
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, hn z hz0, hn z' hz'0]
    have hnorm : ‖z‖ * ‖z'‖ = 1 := by
      rw [← norm_mul, hprod, Complex.norm_exp_ofReal_mul_I]
    rw [div_mul_div_comm, hprod, ← Complex.ofReal_mul, hnorm, Complex.ofReal_one, div_one]
  have := GeoHexPacking.S_eq_of_exp (by linarith [h1.1, h2.1]) (by linarith [h1.2, h2.2])
    hψ0 (by linarith [Real.pi_pos]) hexp
  linarith [h2.1]

section Resonant

variable {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n)
include hB hn hψn

/-- **Sectors are unique modulo `2n`.** -/
lemma sector_unique {w : ℂ} {q q' : ℤ} {x y x' y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hx' : 0 < x') (hy' : 0 < y')
    (h : w = (x : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
      (y : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I))
    (h' : w = (x' : ℂ) * exp (((q' * psi B : ℝ) : ℂ) * I) +
      (y' : ℂ) * exp ((((q' + 1 : ℤ) * psi B : ℝ) : ℂ) * I)) :
    ∃ k : ℤ, q' = q + 2 * k * n := by
  have hψ := psi_mem_Ioo hB
  set ψ := psi B
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- rotate both representations back to the first ray
  obtain ⟨a1, a2⟩ := arg_pos_comb hψ.1 hψ.2 hx hy
  obtain ⟨b1, b2⟩ := arg_pos_comb hψ.1 hψ.2 hx' hy'
  set z := (x : ℂ) + (y : ℂ) * exp (ψ * I)
  set z' := (x' : ℂ) + (y' : ℂ) * exp (ψ * I)
  have hz : w = z * exp (((q * ψ : ℝ) : ℂ) * I) := by
    rw [h]; simp only [z]
    rw [add_mul, mul_assoc, ← Complex.exp_add]; congr 3; push_cast; ring
  have hz' : w = z' * exp (((q' * ψ : ℝ) : ℂ) * I) := by
    rw [h']; simp only [z']
    rw [add_mul, mul_assoc, ← Complex.exp_add]; congr 3; push_cast; ring
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.arg_zero] at a1; exact lt_irrefl _ a1
  have hz'0 : z' ≠ 0 := fun h0 => by rw [h0, Complex.arg_zero] at b1; exact lt_irrefl _ b1
  -- `z' = z e^{i(q−q')ψ}`
  have hzz : z' = z * exp ((((q - q' : ℤ) * ψ : ℝ) : ℂ) * I) := by
    have e := hz'.symm.trans hz
    have hE : exp (((q' * ψ : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    rw [← mul_right_cancel₀ hE (show z' * exp (((q' * ψ : ℝ) : ℂ) * I) =
      z * exp ((((q - q' : ℤ) * ψ : ℝ) : ℂ) * I) * exp (((q' * ψ : ℝ) : ℂ) * I) by
        rw [e, mul_assoc, ← Complex.exp_add]; congr 3; push_cast; ring)]
  -- compare the arguments
  have hn' : ∀ t : ℂ, t ≠ 0 → exp ((arg t : ℂ) * I) = t / (‖t‖ : ℂ) := fun t ht => by
    have : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ht
    rw [eq_div_iff this, mul_comm]; exact norm_mul_exp_arg_mul_I t
  set θ : ℝ := ((q - q' : ℤ) : ℝ) * ψ with hθ
  have hE : ‖exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have h1 : exp ((arg z' : ℂ) * I) = exp ((arg z : ℂ) * I) * exp ((θ : ℂ) * I) := by
    rw [hn' z' hz'0, hn' z hz0, hzz, norm_mul, hE, mul_one]; ring
  have hexp : exp (((arg z' - arg z - θ : ℝ) : ℂ) * I) = 1 := by
    push_cast
    rw [sub_mul, sub_mul, Complex.exp_sub, Complex.exp_sub, h1]
    field_simp
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
  have hre : arg z' - arg z - θ = m * (2 * Real.pi) := by
    have := congrArg Complex.im hm; simpa using this
  simp only [hθ] at hre
  push_cast at hre
  -- `q − q' + 2nm` is an integer of modulus `< 1`
  have hψe : ψ = Real.pi / n := hψn
  have key : ((q - q' + 2 * m * n : ℤ) : ℝ) * ψ = arg z' - arg z := by
    push_cast
    have : (2 * m * n : ℝ) * ψ = m * (2 * Real.pi) := by rw [hψe]; field_simp
    linarith
  have hlt : |((q - q' + 2 * m * n : ℤ) : ℝ)| < 1 := by
    rw [abs_lt]
    constructor
    · by_contra hc; push Not at hc
      have : ((q - q' + 2 * m * n : ℤ) : ℝ) * ψ ≤ -1 * ψ := by
        exact mul_le_mul_of_nonneg_right hc hψ.1.le
      linarith
    · by_contra hc; push Not at hc
      have : 1 * ψ ≤ ((q - q' + 2 * m * n : ℤ) : ℝ) * ψ := by
        exact mul_le_mul_of_nonneg_right hc hψ.1.le
      linarith
  have h0 : q - q' + 2 * m * n = 0 := by
    have := abs_lt.1 hlt
    have h1 : -1 < q - q' + 2 * m * n := by exact_mod_cast this.1
    have h2 : q - q' + 2 * m * n < 1 := by exact_mod_cast this.2
    omega
  exact ⟨m, by linarith⟩

/-- Shifting a triangle by the coincidence lattice does not change its vertices. -/
lemma triV_shift (up : Bool) (p q k : ℤ) :
    triV B up p (q + 2 * k * n) = triV B up (p + k * n) q := by
  have hc : ∀ a b : ℤ, zc B (psi B) a (b + 2 * k * n) = zc B (psi B) (a + k * n) b := by
    intro a b
    have := (coherent_coincide_iff hB hn hψn (a + k * n) b (-(k * n)) (2 * (k * n))).2
      ⟨k, rfl, rfl⟩
    rw [show a + k * n + -(k * n) = a by ring, show b + 2 * (k * n) = b + 2 * k * n by ring]
      at this
    exact this.2
  cases up <;> simp only [triV, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [show q + 2 * k * n + 1 = q + 1 + 2 * k * n by ring, hc, hc, hc] <;>
    congr 2 <;> ring_nf

end Resonant

/-! ### The ladder in one sector -/

/-- `c_k = B^{2k+q}`. -/
noncomputable def cfun (B : ℝ) (q k : ℤ) : ℝ := B ^ (2 * k + q)

lemma cfun_pos {B : ℝ} (hB : 1 < B) (q k : ℤ) : 0 < cfun B q k := by
  unfold cfun; have : 0 < B := by linarith
  positivity

lemma cfun_succ {B : ℝ} (hB : 1 < B) (q k : ℤ) : cfun B q (k + 1) = B ^ 2 * cfun B q k := by
  unfold cfun
  rw [show 2 * (k + 1) + q = (2 * k + q) + 2 by ring, zpow_add₀ (by linarith)]
  norm_num; ring

lemma cfun_mono {B : ℝ} (hB : 1 < B) (q : ℤ) {k k' : ℤ} (h : k ≤ k') :
    cfun B q k ≤ cfun B q k' := by
  unfold cfun; exact zpow_le_zpow_right₀ hB.le (by omega)

lemma cfun_lt {B : ℝ} (hB : 1 < B) (q k : ℤ) : cfun B q k < cfun B q (k + 1) := by
  rw [cfun_succ hB]
  have := cfun_pos hB q k
  nlinarith [one_lt_pow₀ hB (two_ne_zero)]

/-- The rung quantities. -/
noncomputable def Fr (B : ℝ) (q : ℤ) (u v : ℝ) (k : ℤ) : ℝ := (u + v) / cfun B q k
noncomputable def Gr (B : ℝ) (q : ℤ) (u v : ℝ) (k : ℤ) : ℝ :=
  u / cfun B q (k + 1) + v / cfun B q k

section Ladder

variable {B : ℝ} (hB : 1 < B) (q : ℤ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
include hB hu hv

lemma Fr_anti {k k' : ℤ} (h : k ≤ k') : Fr B q u v k' ≤ Fr B q u v k :=
  div_le_div_of_nonneg_left (by linarith) (cfun_pos hB q k) (cfun_mono hB q h)

lemma Gr_anti {k k' : ℤ} (h : k ≤ k') : Gr B q u v k' ≤ Gr B q u v k := by
  unfold Gr
  have a := div_le_div_of_nonneg_left hu.le (cfun_pos hB q (k + 1))
    (cfun_mono hB q (show k + 1 ≤ k' + 1 by omega))
  have b := div_le_div_of_nonneg_left hv.le (cfun_pos hB q k) (cfun_mono hB q h)
  linarith

omit hv in
lemma Gr_lt_Fr (k : ℤ) : Gr B q u v k < Fr B q u v k := by
  unfold Gr Fr
  have h := div_lt_div_of_pos_left hu (cfun_pos hB q k) (cfun_lt hB q k)
  rw [add_div]; linarith

omit hu in
lemma Fr_succ_lt_Gr (k : ℤ) : Fr B q u v (k + 1) < Gr B q u v k := by
  unfold Gr Fr
  have h := div_lt_div_of_pos_left hv (cfun_pos hB q k) (cfun_lt hB q k)
  rw [add_div]; linarith

/-- In one sector, the open triangle containing a point is unique. -/
lemma ladder_up_up {k k' : ℤ} (h : 1 < Fr B q u v k ∧ Gr B q u v k < 1)
    (h' : 1 < Fr B q u v k' ∧ Gr B q u v k' < 1) : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hk | hk
  · have := Fr_anti hB q hu hv (show k + 1 ≤ k' by omega)
    linarith [Fr_succ_lt_Gr hB q (u := u) hv k]
  · have := Fr_anti hB q hu hv (show k' + 1 ≤ k by omega)
    linarith [Fr_succ_lt_Gr hB q (u := u) hv k']

lemma ladder_down_down {k k' : ℤ} (h : Fr B q u v k < 1 ∧ 1 < Gr B q u v (k - 1))
    (h' : Fr B q u v k' < 1 ∧ 1 < Gr B q u v (k' - 1)) : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hk | hk
  · have := Gr_anti hB q hu hv (show k ≤ k' - 1 by omega)
    linarith [Gr_lt_Fr hB q (v := v) hu k]
  · have := Gr_anti hB q hu hv (show k' ≤ k - 1 by omega)
    linarith [Gr_lt_Fr hB q (v := v) hu k']

lemma ladder_up_down {k k' : ℤ} (h : 1 < Fr B q u v k ∧ Gr B q u v k < 1)
    (h' : Fr B q u v k' < 1 ∧ 1 < Gr B q u v (k' - 1)) : False := by
  rcases le_or_gt k' k with hk | hk
  · have := Fr_anti hB q hu hv hk; linarith
  · have := Gr_anti hB q hu hv (show k ≤ k' - 1 by omega); linarith

end Ladder

/-! ### Coordinates of the open triangles -/

lemma zc_sector {B : ℝ} (hB : 1 < B) (p q : ℤ) :
    zc B (psi B) p q = X B + ((-X B * cfun B q p : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) ∧
    zc B (psi B) p (q + 1) = X B + ((-X B * B * cfun B q p : ℝ) : ℂ) *
      exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) := by
  have hB0 : B ≠ 0 := by linarith
  refine ⟨by rw [zc_polar _ hB]; rfl, ?_⟩
  rw [zc_polar _ hB, show 2 * p + (q + 1) = (2 * p + q) + 1 by ring, zpow_add₀ hB0, zpow_one]
  unfold cfun; push_cast; ring

/-- An open upward triangle in sector `q`: the coordinates and the rung inequalities. -/
lemma open_up {B : ℝ} (hB : 1 < B) {w : ℂ} {p q : ℤ} (h : InTriOpen w (triV B true p q)) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      w = X B + ((-X B * u : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v : ℝ) : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) ∧
      1 < Fr B q u v p ∧ Gr B q u v p < 1 := by
  obtain ⟨la, lb, lc, ha, hb, hc, hs, hw⟩ := h
  simp only [triV, ite_true] at hw
  have c0 := cfun_pos hB q p
  have c1 := cfun_pos hB q (p + 1)
  have hlt := cfun_lt hB q p
  refine ⟨la * cfun B q p + lb * cfun B q (p + 1), lc * cfun B q p, by positivity,
    by positivity, ?_, ?_, ?_⟩
  · rw [hw, (zc_sector hB p q).1, (zc_sector hB (p + 1) q).1, (zc_sector hB p q).2]
    have hs' : (la : ℂ) + lb + lc = 1 := by exact_mod_cast hs
    push_cast
    linear_combination (X B : ℂ) * hs'
  · unfold Fr
    rw [lt_div_iff₀ c0]
    nlinarith
  · unfold Gr
    rw [div_add_div _ _ c1.ne' c0.ne', div_lt_one (by positivity)]
    have hlc : lc = 1 - la - lb := by linarith
    rw [hlc]
    nlinarith [mul_pos (mul_pos ha c0) (sub_pos.2 hlt)]

/-- An open downward triangle in sector `q`: the coordinates and the rung inequalities. -/
lemma open_down {B : ℝ} (hB : 1 < B) {w : ℂ} {p q : ℤ} (h : InTriOpen w (triV B false p q)) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      w = X B + ((-X B * u : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v : ℝ) : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) ∧
      Fr B q u v p < 1 ∧ 1 < Gr B q u v (p - 1) := by
  obtain ⟨la, lb, lc, ha, hb, hc, hs, hw⟩ := h
  simp only [triV, Bool.false_eq_true, ite_false] at hw
  have c0 := cfun_pos hB q p
  have cm := cfun_pos hB q (p - 1)
  have hlt : cfun B q (p - 1) < cfun B q p := by
    have := cfun_lt hB q (p - 1); rwa [sub_add_cancel] at this
  refine ⟨la * cfun B q p, lb * cfun B q p + lc * cfun B q (p - 1), by positivity,
    by positivity, ?_, ?_, ?_⟩
  · rw [hw, (zc_sector hB p q).1, (zc_sector hB p q).2, (zc_sector hB (p - 1) q).2]
    have hs' : (la : ℂ) + lb + lc = 1 := by exact_mod_cast hs
    push_cast
    linear_combination (X B : ℂ) * hs'
  · unfold Fr
    rw [div_lt_one c0]
    nlinarith
  · unfold Gr
    rw [sub_add_cancel, div_add_div _ _ c0.ne' cm.ne', one_lt_div (by positivity)]
    have hla : la = 1 - lb - lc := by linarith
    rw [hla]
    nlinarith [mul_pos (mul_pos hb c0) (sub_pos.2 hlt)]

/-! ### Disjointness -/

/-- **The open center triangles of `D_{B_n}` are disjoint modulo `ℤ(−n, 2n)`.** If a point
lies in the interior of two triangles, they are of the same kind and their labels differ by a
multiple of `(−n, 2n)`. -/
theorem DBn_disjoint {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n)
    {w : ℂ} {up up' : Bool} {p q p' q' : ℤ} (h : InTriOpen w (triV B up p q))
    (h' : InTriOpen w (triV B up' p' q')) :
    up = up' ∧ ∃ k : ℤ, p' = p - k * n ∧ q' = q + 2 * k * n := by
  have hR0 : 0 < -X B := by linarith [X_neg hB]
  have hB0 : 0 < B := by linarith
  have hψ := psi_mem_Ioo hB
  have hsin : cross (exp (((q * psi B : ℝ) : ℂ) * I))
      (exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I)) ≠ 0 := by
    rw [cross_exp]
    have : ((q + 1 : ℤ) : ℝ) * psi B - q * psi B = psi B := by push_cast; ring
    rw [this]; exact (Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).ne'
  -- coordinates of `w` for the first triangle
  have hc1 : ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      w = X B + ((-X B * u : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v : ℝ) : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) := by
    cases up
    · obtain ⟨u, v, hu, hv, hw, -⟩ := open_down hB h; exact ⟨u, v, hu, hv, hw⟩
    · obtain ⟨u, v, hu, hv, hw, -⟩ := open_up hB h; exact ⟨u, v, hu, hv, hw⟩
  have hc2 : ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      w = X B + ((-X B * u : ℝ) : ℂ) * exp (((q' * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v : ℝ) : ℂ) * exp ((((q' + 1 : ℤ) * psi B : ℝ) : ℂ) * I) := by
    cases up'
    · obtain ⟨u, v, hu, hv, hw, -⟩ := open_down hB h'; exact ⟨u, v, hu, hv, hw⟩
    · obtain ⟨u, v, hu, hv, hw, -⟩ := open_up hB h'; exact ⟨u, v, hu, hv, hw⟩
  obtain ⟨u1, v1, hu1, hv1, hw1⟩ := hc1
  obtain ⟨u2, v2, hu2, hv2, hw2⟩ := hc2
  -- the sectors agree modulo `2n`
  obtain ⟨k, hk⟩ := sector_unique hB hn hψn (w := w - X B) (x := -X B * u1)
    (y := -X B * B * v1) (x' := -X B * u2) (y' := -X B * B * v2) (by positivity)
    (by positivity) (by positivity) (by positivity) (by rw [hw1]; ring) (by rw [hw2]; ring)
  refine ⟨?_, k, ?_, hk⟩ <;> (
  -- move the second triangle into sector `q`
  rw [hk, triV_shift hB hn hψn] at h'
  -- same coordinates in sector `q`
  have hco : ∀ {u v u' v' : ℝ},
      w = X B + ((-X B * u : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v : ℝ) : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) →
      w = X B + ((-X B * u' : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v' : ℝ) : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) →
      u = u' ∧ v = v' := by
    intro u v u' v' e e'
    have := coords_unique hsin (a := -X B * u) (b := -X B * B * v) (a' := -X B * u')
      (b' := -X B * B * v') (by linear_combination e'.symm.trans e |>.symm)
    exact ⟨mul_left_cancel₀ hR0.ne' this.1, mul_left_cancel₀ (by positivity) this.2⟩
  cases up <;> cases up'
  · obtain ⟨u, v, hu, hv, hw, hr⟩ := open_down hB h
    obtain ⟨u', v', -, -, hw', hr'⟩ := open_down hB h'
    obtain ⟨rfl, rfl⟩ := hco hw hw'
    have := ladder_down_down hB q hu hv hr hr'
    first | rfl | omega
  · obtain ⟨u, v, hu, hv, hw, hr⟩ := open_down hB h
    obtain ⟨u', v', -, -, hw', hr'⟩ := open_up hB h'
    obtain ⟨rfl, rfl⟩ := hco hw hw'
    exact (ladder_up_down hB q hu hv hr' hr).elim
  · obtain ⟨u, v, hu, hv, hw, hr⟩ := open_up hB h
    obtain ⟨u', v', -, -, hw', hr'⟩ := open_down hB h'
    obtain ⟨rfl, rfl⟩ := hco hw hw'
    exact (ladder_up_down hB q hu hv hr hr').elim
  · obtain ⟨u, v, hu, hv, hw, hr⟩ := open_up hB h
    obtain ⟨u', v', -, -, hw', hr'⟩ := open_up hB h'
    obtain ⟨rfl, rfl⟩ := hco hw hw'
    have := ladder_up_up hB q hu hv hr hr'
    first | rfl | omega)

/-- `X` lies in no closed center triangle. -/
lemma X_notin_tri {B : ℝ} (hB : 1 < B) (up : Bool) (p q : ℤ) :
    ¬ InTri (X B) (triV B up p q).1 (triV B up p q).2.1 (triV B up p q).2.2 := by
  rintro ⟨la, lb, lc, ha, hb, hc, hs, hw⟩
  have hR0 : 0 < -X B := by linarith [X_neg hB]
  have hψ := psi_mem_Ioo hB
  have hsin : cross (exp (((q * psi B : ℝ) : ℂ) * I))
      (exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I)) ≠ 0 := by
    rw [cross_exp]
    have : ((q + 1 : ℤ) : ℝ) * psi B - q * psi B = psi B := by push_cast; ring
    rw [this]; exact (Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).ne'
  have c0 := cfun_pos hB q p
  have hs' : (la : ℂ) + lb + lc = 1 := by exact_mod_cast hs
  cases up
  · simp only [triV, Bool.false_eq_true, ite_false] at hw
    rw [(zc_sector hB p q).1, (zc_sector hB p q).2, (zc_sector hB (p - 1) q).2] at hw
    have cm := cfun_pos hB q (p - 1)
    have := coords_unique hsin (a := -X B * (la * cfun B q p))
      (b := -X B * B * (lb * cfun B q p + lc * cfun B q (p - 1))) (a' := 0) (b' := 0)
      (by push_cast at hw ⊢; linear_combination hw.symm - (X B : ℂ) * hs')
    have h1 : la * cfun B q p = 0 := by
      rcases mul_eq_zero.1 this.1 with h | h
      · linarith
      · exact h
    have h2 : lb * cfun B q p + lc * cfun B q (p - 1) = 0 := by
      rcases mul_eq_zero.1 this.2 with h | h
      · nlinarith
      · exact h
    have : la = 0 := by nlinarith
    have : lb = 0 := by nlinarith [mul_nonneg hc cm.le]
    have : lc = 0 := by nlinarith [mul_nonneg hb c0.le]
    linarith
  · simp only [triV, ite_true] at hw
    rw [(zc_sector hB p q).1, (zc_sector hB (p + 1) q).1, (zc_sector hB p q).2] at hw
    have c1 := cfun_pos hB q (p + 1)
    have := coords_unique hsin (a := -X B * (la * cfun B q p + lb * cfun B q (p + 1)))
      (b := -X B * B * (lc * cfun B q p)) (a' := 0) (b' := 0)
      (by push_cast at hw ⊢; linear_combination hw.symm - (X B : ℂ) * hs')
    have h1 : la * cfun B q p + lb * cfun B q (p + 1) = 0 := by
      rcases mul_eq_zero.1 this.1 with h | h
      · linarith
      · exact h
    have h2 : lc * cfun B q p = 0 := by
      rcases mul_eq_zero.1 this.2 with h | h
      · nlinarith
      · exact h
    have : la = 0 := by nlinarith [mul_nonneg hb c1.le]
    have : lb = 0 := by nlinarith [mul_nonneg ha c0.le]
    have : lc = 0 := by nlinarith
    linarith

/-- **The center triangles of `D_{B_n}` tile `ℂ ∖ {X}`.** Every point `w ≠ X` lies in a closed
triangle, `X` lies in none, and two triangles whose interiors meet are the same triangle
modulo `ℤ(−n, 2n)`. -/
theorem DBn_tiles {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n) :
    (∀ w : ℂ, w ≠ (X B : ℂ) → ∃ up p q,
      InTri w (triV B up p q).1 (triV B up p q).2.1 (triV B up p q).2.2) ∧
    (∀ up p q, ¬ InTri (X B) (triV B up p q).1 (triV B up p q).2.1 (triV B up p q).2.2) ∧
    (∀ w up up' p q p' q', InTriOpen w (triV B up p q) → InTriOpen w (triV B up' p' q') →
      up = up' ∧ ∃ k : ℤ, p' = p - k * n ∧ q' = q + 2 * k * n) := by
  refine ⟨fun w hw => ?_, fun up p q => X_notin_tri hB up p q,
    fun w up up' p q p' q' h h' => DBn_disjoint hB hn hψn h h'⟩
  obtain ⟨p, q, h | h⟩ := DB_cover hB w hw
  · exact ⟨true, p, q, by simpa [triV] using h⟩
  · exact ⟨false, p, q, by simpa [triV] using h⟩

end DoyleFormal
