/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Tiling
import DoyleFormal.BdsClass

/-!
# The `k`-sheeted cover in case (2) of Theorem A 7.5

Let `B > 1` with `ψ(B) = πk/m`, `gcd(k, m) = 1`, i.e. `t = m/k`. Identify two center triangles
of `D_B` when they are of the same kind and their labels differ by a multiple of `m(−1, 2)`
(`Ident`); identified triangles are equal (`triV_shift_gen`, from `same_circle_rational`).

`k_sheeted`:
* every point `w ≠ X` lies in `k` closed center triangles, no two of them identified;
* among any `k + 1` open center triangles containing a point, two are identified.

So, away from the edges, every point of `ℂ ∖ {X}` is covered exactly `k` times by the
triangles modulo the identification: the center triangulation of `D_B` modulo `ℤ m(−1, 2)` is a
`k`-sheeted cover of `ℂ ∖ {X}` (`X` lies in no triangle, `X_notin_tri`).

The proof works with lifts `θ` of the direction of `w − X`: a lift determines the sector
`⌊θ/ψ⌋` (`DB_cover_lift`, `open_lift`), one sector contains one open triangle through `w`
(`same_sector`, the ladder of `Tiling.lean`), and the lifts `θ + 2πj`, `j = 0, …, k − 1`, give
sectors that are distinct modulo `2m`, while `θ` and `θ + 2πk` give sectors differing by `2m`.
-/

namespace DoyleFormal

open Complex

/-- **Cover with a prescribed lift.** `DB_cover` with any `θ` such that `w − X = |w − X| e^{iθ}`:
`w` lies in a closed triangle of sector `⌊θ/ψ⌋`. -/
theorem DB_cover_lift {B : ℝ} (hB : 1 < B) (w : ℂ) (hw : w ≠ X B) (θ : ℝ)
    (hθ : w - X B = (‖w - X B‖ : ℂ) * exp (θ * I)) :
    ∃ p : ℤ, InTri w (zc B (psi B) p ⌊θ / psi B⌋) (zc B (psi B) (p + 1) ⌊θ / psi B⌋)
        (zc B (psi B) p (⌊θ / psi B⌋ + 1)) ∨
      InTri w (zc B (psi B) p ⌊θ / psi B⌋) (zc B (psi B) p (⌊θ / psi B⌋ + 1))
        (zc B (psi B) (p - 1) (⌊θ / psi B⌋ + 1)) := by
  set ψ := psi B with hψdef
  have hψ := psi_mem_Ioo hB
  have hB0 : 0 < B := by linarith
  set R0 := -X B with hR0def
  have hR0 : 0 < R0 := by simp only [R0]; linarith [X_neg hB]
  obtain ⟨d, hd⟩ : ∃ d, d = w - X B := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact sub_ne_zero.2 hw
  set r := ‖d‖
  have hr : 0 < r := norm_pos_iff.2 hd0
  have hdpol : d = (r : ℂ) * exp (θ * I) := by simp only [r]; rw [hd]; exact hθ
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
    refine ⟨p, Or.inl ?_⟩
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
    refine ⟨p + 1, Or.inr ?_⟩
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


/-- An open triangle of sector `q` through `w` gives a lift of the direction of `w − X` strictly
inside `(qψ, (q + 1)ψ)`. -/
lemma open_lift {B : ℝ} (hB : 1 < B) {w : ℂ} {up : Bool} {p q : ℤ}
    (h : InTriOpen w (triV B up p q)) :
    ∃ θ : ℝ, w - X B = (‖w - X B‖ : ℂ) * exp (θ * I) ∧ q * psi B < θ ∧ θ < (q + 1) * psi B := by
  have hψ := psi_mem_Ioo hB
  have hR0 : 0 < -X B := by linarith [X_neg hB]
  have hB0 : 0 < B := by linarith
  have hc : ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      w = X B + ((-X B * u : ℝ) : ℂ) * exp (((q * psi B : ℝ) : ℂ) * I) +
        ((-X B * B * v : ℝ) : ℂ) * exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I) := by
    cases up
    · obtain ⟨u, v, hu, hv, hw, -⟩ := open_down hB h; exact ⟨u, v, hu, hv, hw⟩
    · obtain ⟨u, v, hu, hv, hw, -⟩ := open_up hB h; exact ⟨u, v, hu, hv, hw⟩
  obtain ⟨u, v, hu, hv, hw⟩ := hc
  have hx : 0 < -X B * u := mul_pos hR0 hu
  have hy : 0 < -X B * B * v := by positivity
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((-X B * u : ℝ) : ℂ) + ((-X B * B * v : ℝ) : ℂ) *
      exp ((psi B : ℂ) * I) := ⟨_, rfl⟩
  obtain ⟨ha1, ha2⟩ := arg_pos_comb hψ.1 hψ.2 hx hy
  rw [← hz] at ha1 ha2
  have hwz : w - X B = exp (((q * psi B : ℝ) : ℂ) * I) * z := by
    rw [hw, hz, show ((((q + 1 : ℤ) * psi B : ℝ)) : ℂ) * I =
      ((q * psi B : ℝ) : ℂ) * I + (psi B : ℂ) * I by push_cast; ring, exp_add]
    ring
  refine ⟨q * psi B + arg z, ?_, by linarith, by linarith⟩
  have hn : ‖w - X B‖ = ‖z‖ := by
    rw [hwz, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  rw [hn, hwz]
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [show ((q * psi B + arg z : ℝ) : ℂ) * I = ((q * psi B : ℝ) : ℂ) * I + (arg z : ℂ) * I by
    push_cast; ring, exp_add]
  ring

/-- Two lifts of the same direction differ by a multiple of `2π`. -/
lemma lift_diff {d : ℂ} (hd : d ≠ 0) {θ θ' : ℝ} (h : d = (‖d‖ : ℂ) * exp (θ * I))
    (h' : d = (‖d‖ : ℂ) * exp (θ' * I)) : ∃ n : ℤ, θ' = θ + n * (2 * Real.pi) := by
  have hn : (‖d‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hd)
  have e : exp (θ' * I) = exp (θ * I) := mul_left_cancel₀ hn (h'.symm.trans h)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- Identification of triangles: same kind, labels differing by a multiple of `m(−1, 2)`. -/
def Ident (m : ℕ) (T T' : Bool × ℤ × ℤ) : Prop :=
  T.1 = T'.1 ∧ ∃ i : ℤ, T'.2.1 = T.2.1 - i * m ∧ T'.2.2 = T.2.2 + 2 * i * m

section Sheets

variable {B : ℝ} (hB : 1 < B) {k m : ℕ} (hcop : Nat.Coprime k m)
  (hψkm : psi B = Real.pi * k / m)
include hB hcop hψkm

omit hcop in
lemma m_pos : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · have := (psi_mem_Ioo hB).1; rw [hψkm, h] at this; simp at this
  · exact h

/-- **Identified triangles are equal.** -/
lemma triV_shift_gen (up : Bool) (p q i : ℤ) :
    triV B up p (q + 2 * i * m) = triV B up (p + i * m) q := by
  have hm := m_pos hB hψkm
  have hc : ∀ a b : ℤ, zc B (psi B) a (b + 2 * i * m) = zc B (psi B) (a + i * m) b := by
    intro a b
    exact ((same_circle_rational hB hm hcop hψkm (a + i * m) b a (b + 2 * i * m)).2
      ⟨i, by ring, by ring⟩).2
  cases up <;> simp only [triV, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [show q + 2 * i * m + 1 = q + 1 + 2 * i * m by ring, hc, hc, hc] <;>
    congr 2 <;> ring_nf

end Sheets

/-- **One open triangle per sector**: two open triangles of the same sector through `w` are
equal. -/
lemma same_sector {B : ℝ} (hB : 1 < B) {w : ℂ} {up up' : Bool} {p p' q : ℤ}
    (h : InTriOpen w (triV B up p q)) (h' : InTriOpen w (triV B up' p' q)) :
    up = up' ∧ p = p' := by
  have hR0 : 0 < -X B := by linarith [X_neg hB]
  have hB0 : 0 < B := by linarith
  have hψ := psi_mem_Ioo hB
  have hsin : cross (exp (((q * psi B : ℝ) : ℂ) * I))
      (exp ((((q + 1 : ℤ) * psi B : ℝ) : ℂ) * I)) ≠ 0 := by
    rw [cross_exp]
    have : ((q + 1 : ℤ) : ℝ) * psi B - q * psi B = psi B := by push_cast; ring
    rw [this]; exact (Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).ne'
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
    exact ⟨rfl, ladder_down_down hB q hu hv hr hr'⟩
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
    exact ⟨rfl, ladder_up_up hB q hu hv hr hr'⟩

/-- Two integers whose unit intervals contain the same real are equal. -/
lemma int_eq_of_mem {a b : ℤ} {x : ℝ} (ha1 : (a : ℝ) < x) (ha2 : x < a + 1) (hb1 : (b : ℝ) < x)
    (hb2 : x < b + 1) : a = b := by
  have h1 : (a : ℝ) < b + 1 := by linarith
  have h2 : (b : ℝ) < a + 1 := by linarith
  have h1' : a < b + 1 := by exact_mod_cast h1
  have h2' : b < a + 1 := by exact_mod_cast h2
  omega

/-- The sectors of the lifts `θ₀ + 2πj`, `0 ≤ j < k`, are distinct modulo `2m`. -/
lemma sectors_distinct {k m : ℕ} {s c : ℝ} (hk : (1 : ℝ) ≤ k) (hkm : (k : ℝ) < m)
    (hc : c = 2 * m / k) {j j' : ℕ} (hj : j < k) (hj' : j' < k) (hne : j ≠ j') {i : ℤ}
    (h : (⌊s + j' * c⌋ : ℤ) = ⌊s + j * c⌋ + 2 * i * m) : False := by
  have hmR : (0 : ℝ) < m := by linarith
  have hgap : 1 ≤ c := by rw [hc, le_div_iff₀ (by linarith)]; linarith
  have hck : c * k = 2 * m := by rw [hc]; field_simp
  have f1 := Int.floor_le (s + j * c)
  have f2 := Int.lt_floor_add_one (s + j * c)
  have f3 := Int.floor_le (s + j' * c)
  have f4 := Int.lt_floor_add_one (s + j' * c)
  have hR : ((⌊s + j' * c⌋ : ℤ) : ℝ) = ⌊s + j * c⌋ + 2 * i * m := by exact_mod_cast h
  have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
  have hj'R : (j' : ℝ) + 1 ≤ k := by exact_mod_cast hj'
  have h0j : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h0j' : (0 : ℝ) ≤ j' := Nat.cast_nonneg j'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hlt' : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hlt
    -- `(j' − j) c − 1 < 2im < (j' − j) c + 1`, with `c ≤ (j' − j) c ≤ (k − 1) c = 2m − c`
    have a1 : (0 : ℝ) < 2 * i * m := by nlinarith
    have a2 : (2 * i * m : ℝ) < 2 * m := by nlinarith
    have b1 : (0 : ℝ) < i := by nlinarith
    have b2 : (i : ℝ) < 1 := by nlinarith
    have c1 : (0 : ℤ) < i := by exact_mod_cast b1
    have c2 : i < (1 : ℤ) := by exact_mod_cast b2
    omega
  · have hlt' : (j' : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    have a1 : (2 * i * m : ℝ) < 0 := by nlinarith
    have a2 : -(2 * m : ℝ) < 2 * i * m := by nlinarith
    have b1 : (i : ℝ) < 0 := by nlinarith
    have b2 : (-1 : ℝ) < i := by nlinarith
    have c1 : i < (0 : ℤ) := by exact_mod_cast b1
    have c2 : (-1 : ℤ) < i := by exact_mod_cast b2
    omega

/-- **Theorem A 7.5 (2): the `k`-sheeted cover.** For `ψ(B) = πk/m` in lowest terms:
every point `w ≠ X` lies in `k` closed center triangles, no two identified; and among any
`k + 1` open center triangles through a point, two are identified. -/
theorem k_sheeted {B : ℝ} (hB : 1 < B) {k m : ℕ} (hk : 1 ≤ k) (hcop : Nat.Coprime k m)
    (hψkm : psi B = Real.pi * k / m) :
    (∀ w : ℂ, w ≠ X B → ∃ T : Fin k → Bool × ℤ × ℤ,
      (∀ j, InTri w (triV B (T j).1 (T j).2.1 (T j).2.2).1 (triV B (T j).1 (T j).2.1 (T j).2.2).2.1
        (triV B (T j).1 (T j).2.1 (T j).2.2).2.2) ∧
      ∀ j j', j ≠ j' → ¬ Ident m (T j) (T j')) ∧
    (∀ (w : ℂ) (T : Fin (k + 1) → Bool × ℤ × ℤ),
      (∀ j, InTriOpen w (triV B (T j).1 (T j).2.1 (T j).2.2)) →
      ∃ j j', j ≠ j' ∧ Ident m (T j) (T j')) := by
  have hψ := psi_mem_Ioo hB
  have hm := m_pos hB hψkm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- `2π = (2m/k) ψ`, and `k < m`
  have h2pi : 2 * Real.pi = (2 * m / k) * psi B := by
    rw [hψkm]; field_simp
  have hkm : (k : ℝ) < m := by
    have := hψ.2; rw [hψkm, div_lt_iff₀ hmR] at this; nlinarith [Real.pi_pos]
  constructor
  · -- `k` sheets
    classical
    intro w hw
    obtain ⟨θ0, hθ0⟩ : ∃ θ0, θ0 = arg (w - X B) := ⟨_, rfl⟩
    have hlift : ∀ j : Fin k, w - X B =
        (‖w - X B‖ : ℂ) * exp (((θ0 + (j : ℕ) * (2 * Real.pi) : ℝ) : ℂ) * I) := by
      intro j
      rw [show (((θ0 + (j : ℕ) * (2 * Real.pi) : ℝ)) : ℂ) * I = (θ0 : ℂ) * I + (((j : ℕ) : ℤ) : ℂ) *
        (2 * Real.pi * I) by push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one, hθ0]
      exact (norm_mul_exp_arg_mul_I _).symm
    have hcov := fun j : Fin k => DB_cover_lift hB w hw _ (hlift j)
    choose pf hpf using hcov
    let qf : Fin k → ℤ := fun j => ⌊(θ0 + (j : ℕ) * (2 * Real.pi)) / psi B⌋
    let T : Fin k → Bool × ℤ × ℤ := fun j =>
      if InTri w (zc B (psi B) (pf j) (qf j)) (zc B (psi B) (pf j + 1) (qf j))
          (zc B (psi B) (pf j) (qf j + 1)) then (true, pf j, qf j) else (false, pf j, qf j)
    refine ⟨T, fun j => ?_, fun j j' hjj' hid => ?_⟩
    · by_cases hj : InTri w (zc B (psi B) (pf j) (qf j)) (zc B (psi B) (pf j + 1) (qf j))
          (zc B (psi B) (pf j) (qf j + 1))
      · simp only [T, hj, triV, ite_true]
      · simp only [T, hj, triV, Bool.false_eq_true, ite_false]
        exact (hpf j).resolve_left hj
    · obtain ⟨-, i, -, hq⟩ := hid
      have hqj : ∀ j : Fin k, (T j).2.2 = qf j := by
        intro j; dsimp only [T]; split <;> rfl
      rw [hqj, hqj] at hq
      have e : ∀ j : ℕ, (θ0 + j * (2 * Real.pi)) / psi B = θ0 / psi B + j * (2 * m / k) := by
        intro j; have hψne := hψ.1.ne'; rw [add_div, h2pi]; congr 1; field_simp
      simp only [qf, e] at hq
      exact sectors_distinct hkR hkm rfl j.isLt j'.isLt (fun h => hjj' (Fin.ext h)) hq
  · -- at most `k` sheets
    intro w T hT
    rcases eq_or_ne w (X B) with hwX | hwX
    · exfalso
      obtain ⟨la, lb, lc, ha, hb, hc, hs, hw⟩ := hT 0
      exact X_notin_tri hB (T 0).1 (T 0).2.1 (T 0).2.2
        ⟨la, lb, lc, ha.le, hb.le, hc.le, hs, by rw [← hwX]; exact hw⟩
    have hd : w - X B ≠ 0 := sub_ne_zero.2 hwX
    have h0 : w - X B = (‖w - X B‖ : ℂ) * exp ((arg (w - X B) : ℂ) * I) :=
      (norm_mul_exp_arg_mul_I _).symm
    have hl := fun j => open_lift hB (hT j)
    choose θf hθf hθ1 hθ2 using hl
    have hn := fun j => lift_diff hd h0 (hθf j)
    choose nf hnf using hn
    have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
    let f : Fin (k + 1) → Fin k := fun j =>
      ⟨Int.toNat (nf j % k), by
        have h1 := Int.emod_nonneg (nf j) hk0.ne'
        have h2 := Int.emod_lt_of_pos (nf j) hk0
        omega⟩
    obtain ⟨j, j', hjj', hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    refine ⟨j, j', hjj', ?_⟩
    have hmod : nf j % k = nf j' % k := by
      have := congrArg Fin.val hf
      simp only [f] at this
      have h1 := Int.emod_nonneg (nf j) hk0.ne'
      have h2 := Int.emod_nonneg (nf j') hk0.ne'
      omega
    obtain ⟨i, hi⟩ : (k : ℤ) ∣ nf j' - nf j := Int.ModEq.dvd hmod
    have hiR : ((nf j' : ℤ) : ℝ) = nf j + k * i := by
      have : nf j' = nf j + k * i := by linarith
      exact_mod_cast this
    have hθ' : θf j' = θf j + ((2 * i * m : ℤ) : ℝ) * psi B := by
      rw [hnf j', hnf j, hiR]
      have : (k : ℝ) * i * (2 * Real.pi) = ((2 * i * m : ℤ) : ℝ) * psi B := by
        rw [h2pi]; push_cast; field_simp
      linear_combination this
    have hψ0 := hψ.1
    have g1 : (((T j).2.2 : ℤ) : ℝ) < θf j / psi B := by
      rw [lt_div_iff₀ hψ0]; exact hθ1 j
    have g2 : θf j / psi B < (((T j).2.2 : ℤ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hψ0]; exact hθ2 j
    have f1 : (((T j').2.2 - 2 * i * m : ℤ) : ℝ) < θf j / psi B := by
      rw [lt_div_iff₀ hψ0]
      have := hθ1 j'
      rw [hθ'] at this
      push_cast at this ⊢
      linarith
    have f2 : θf j / psi B < (((T j').2.2 - 2 * i * m : ℤ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hψ0]
      have := hθ2 j'
      rw [hθ'] at this
      push_cast at this ⊢
      linarith
    have hq : (T j').2.2 = (T j).2.2 + 2 * i * m := by
      have := int_eq_of_mem f1 f2 g1 g2
      omega
    have h' := hT j'
    rw [hq, triV_shift_gen hB hcop hψkm] at h'
    obtain ⟨hup, hp⟩ := same_sector hB (hT j) h'
    exact ⟨hup, i, by linarith, hq⟩

end DoyleFormal
