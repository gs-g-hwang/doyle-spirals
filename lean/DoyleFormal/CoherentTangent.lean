/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Coherent
import DoyleFormal.FirstOverlap

/-!
# Tangency in the resonant spirals (paper B, Proposition 5.3, last sentence) — Phase 4h

For `ψ(B) = π/n`, `n ≥ 2`: the circles at `u` and `u + w` are tangent iff `w` is a lattice
direction modulo `ℤ(−n, 2n)` (`coherent_tangent_iff`). Together with `coherent_coincide_iff`
and `coherent_no_overlap` this is Proposition B 5.3.
-/

namespace DoyleFormal

open Complex

/-- The six lattice directions. -/
def IsUnitDir (x y : ℤ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨
    (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1)

/-- Tangency criterion for `K(p,q)` and `K(p+a,q+b)`. -/
lemma tangent_iff_alg {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ = rad B (p + a) (q + b) + rad B p q ↔
      X B ^ 2 * ((B ^ (2 * a + b)) ^ 2 + 1 - 2 * B ^ (2 * a + b) * Real.cos (b * ψ))
        = (1 + B ^ (2 * a + b)) ^ 2 := by
  have hB0 : 0 < B := by linarith
  have hr : 0 < rad B p q := by unfold rad; exact zpow_pos hB0 _
  have hd := dist_sq ψ hB p q a b
  rw [rad_add hB0 p q a b]
  set ρ := B ^ (2 * a + b) with hρdef
  have hρ : 0 < ρ := zpow_pos hB0 _
  constructor
  · intro h
    rw [h] at hd
    have h2 : rad B p q ^ 2 *
        (X B ^ 2 * (ρ ^ 2 + 1 - 2 * ρ * Real.cos (b * ψ)) - (1 + ρ) ^ 2) = 0 := by
      linear_combination -hd
    have := (mul_eq_zero.1 h2).resolve_left (by positivity)
    linarith
  · intro h
    refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [hd]
    linear_combination rad B p q ^ 2 * h

/-- Tangency is symmetric in the two circles. -/
lemma tangent_symm {B ψ : ℝ} (p q a b : ℤ) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ = rad B (p + a) (q + b) + rad B p q ↔
      ‖zc B ψ (p + a + -a) (q + b + -b) - zc B ψ (p + a) (q + b)‖
        = rad B (p + a + -a) (q + b + -b) + rad B (p + a) (q + b) := by
  rw [show p + a + -a = p by ring, show q + b + -b = q by ring,
    norm_sub_rev (zc B ψ p q) (zc B ψ (p + a) (q + b)),
    add_comm (rad B p q) (rad B (p + a) (q + b))]

/-- `|s| ≥ 3`: never tangent. -/
lemma not_tangent_far {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) (hs : 3 ≤ |2 * a + b|) :
    ¬ ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ = rad B (p + a) (q + b) + rad B p q := by
  rw [tangent_iff_alg ψ hB p q a b]
  have hB0 : 0 < B := by linarith
  set ρ := B ^ (2 * a + b) with hρdef
  have hρ0 : 0 < ρ := zpow_pos hB0 _
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have hfac : X B ^ 2 * (ρ - 1) ^ 2 - (1 + ρ) ^ 2
      = 4 * (ρ - B ^ 2) * (B ^ 2 * ρ - 1) / (B ^ 2 - 1) ^ 2 := by
    unfold X; field_simp; ring
  have hprod : 0 < (ρ - B ^ 2) * (B ^ 2 * ρ - 1) := by
    rcases le_abs'.1 hs with h | h
    · have hle : ρ ≤ B ^ (-3 : ℤ) := zpow_le_zpow_right₀ hB.le h
      have h3 : B ^ (-3 : ℤ) = (B ^ 3)⁻¹ := by rw [zpow_neg, zpow_ofNat]
      have hB3 : 1 < B ^ 3 := one_lt_pow₀ hB (by norm_num)
      have hρ1 : ρ < 1 := by
        rw [h3] at hle; exact lt_of_le_of_lt hle (inv_lt_one_of_one_lt₀ hB3)
      have hB2ρ : B ^ 2 * ρ < 1 := by
        have : B ^ 2 * ρ ≤ B ^ 2 * (B ^ 3)⁻¹ := by rw [h3] at hle; gcongr
        have e : B ^ 2 * (B ^ 3)⁻¹ = B⁻¹ := by field_simp
        rw [e] at this
        exact lt_of_le_of_lt this (inv_lt_one_of_one_lt₀ hB)
      have hB2 : 1 < B ^ 2 := one_lt_pow₀ hB (by norm_num)
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · have hle : B ^ (3 : ℤ) ≤ ρ := zpow_le_zpow_right₀ hB.le h
      rw [zpow_ofNat] at hle
      have hB23 : B ^ 2 < B ^ 3 := pow_lt_pow_right₀ hB (by norm_num)
      have hB2 : 1 < B ^ 2 := one_lt_pow₀ hB (by norm_num)
      have : 1 < B ^ 2 * ρ := by nlinarith
      exact mul_pos (by linarith) (by linarith)
  have hpos : 0 < 4 * (ρ - B ^ 2) * (B ^ 2 * ρ - 1) / (B ^ 2 - 1) ^ 2 := by
    apply div_pos _ (by positivity); linarith
  have hc := Real.cos_le_one (b * ψ)
  have hX2 : 0 ≤ X B ^ 2 := sq_nonneg _
  have hextra : 0 ≤ X B ^ 2 * (2 * ρ * (1 - Real.cos (b * ψ))) :=
    mul_nonneg hX2 (mul_nonneg (by positivity) (by linarith))
  intro h
  have : X B ^ 2 * (ρ ^ 2 + 1 - 2 * ρ * Real.cos (b * ψ))
      = X B ^ 2 * (ρ - 1) ^ 2 + X B ^ 2 * (2 * ρ * (1 - Real.cos (b * ψ))) := by ring
  linarith

/-- `|s| = 2`: tangent iff `cos(bψ) = 1`. -/
lemma tangent_s2 {B : ℝ} (ψ : ℝ) (hB : 1 < B) (p q a b : ℤ) (hs : |2 * a + b| = 2) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ = rad B (p + a) (q + b) + rad B p q ↔
      Real.cos (b * ψ) = 1 := by
  rw [tangent_iff_alg ψ hB p q a b]
  have hB0 : 0 < B := by linarith
  set ρ := B ^ (2 * a + b) with hρdef
  have hρ0 : 0 < ρ := zpow_pos hB0 _
  have h2 : B ^ 2 - 1 ≠ 0 := by nlinarith
  have hzero : (ρ - B ^ 2) * (B ^ 2 * ρ - 1) = 0 := by
    rcases abs_choice (2 * a + b) with h | h <;> rw [h] at hs
    · rw [hρdef, hs, zpow_ofNat]; ring
    · have hs' : 2 * a + b = -2 := by omega
      rw [hρdef, hs', zpow_neg, zpow_ofNat]
      have : B ^ 2 ≠ 0 := by positivity
      field_simp; ring
  have hfac : X B ^ 2 * (ρ ^ 2 + 1 - 2 * ρ * Real.cos (b * ψ)) - (1 + ρ) ^ 2
      = 4 * ((ρ - B ^ 2) * (B ^ 2 * ρ - 1)) / (B ^ 2 - 1) ^ 2
        + X B ^ 2 * (2 * ρ) * (1 - Real.cos (b * ψ)) := by
    unfold X; field_simp; ring
  rw [hzero, mul_zero, zero_div, zero_add] at hfac
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  have hk : 0 < X B ^ 2 * (2 * ρ) := by positivity
  constructor
  · intro h
    have : X B ^ 2 * (2 * ρ) * (1 - Real.cos (b * ψ)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hk.ne'
    linarith
  · intro h
    rw [h, sub_self, mul_zero] at hfac
    rw [h]
    linarith

/-- `s = 1`: tangent iff `cos(bψ) = cos ψ` (for `cos ψ = cosPsi B`). -/
lemma tangent_s1 {B ψ : ℝ} (hB : 1 < B) (hcos : Real.cos ψ = cosPsi B) (p q a b : ℤ)
    (hs : 2 * a + b = 1) :
    ‖zc B ψ (p + a) (q + b) - zc B ψ p q‖ = rad B (p + a) (q + b) + rad B p q ↔
      Real.cos (b * ψ) = Real.cos ψ := by
  rw [tangent_iff_alg ψ hB p q a b, hs, zpow_one, hcos]
  have key := X_sq_mul hB
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  have hk : 0 < X B ^ 2 * (2 * B) := mul_pos hX2 (by linarith)
  have e : X B ^ 2 * (B ^ 2 + 1 - 2 * B * Real.cos (b * ψ)) - (1 + B) ^ 2
      = X B ^ 2 * (2 * B) * (cosPsi B - Real.cos (b * ψ)) := by linear_combination key
  constructor
  · intro h
    have : X B ^ 2 * (2 * B) * (cosPsi B - Real.cos (b * ψ)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hk.ne'
    linarith
  · intro h
    rw [h]
    exact key

/-- `1 < X² sin²ψ` when `ψ = psi B ≤ π/2`. -/
lemma one_lt_X_sq_sin_sq {B : ℝ} (hB : 1 < B) (h2 : psi B ≤ Real.pi / 2) :
    1 < X B ^ 2 * Real.sin (psi B) ^ 2 := by
  have hψ := psi_mem_Ioo hB
  have hc0 : 0 ≤ Real.cos (psi B) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hψ.1], h2⟩
  have e1 := eta_lt_one hB
  have e0 := eta_pos (by linarith : (0 : ℝ) < B)
  have hceta : Real.cos (psi B) < eta B := by
    rw [cos_psi hB, cosPsi_eq_eta]; nlinarith
  have hsq : Real.cos (psi B) ^ 2 < eta B ^ 2 := by nlinarith
  have hsin2 : Real.sin (psi B) ^ 2 = 1 - Real.cos (psi B) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (psi B); linarith
  have key := X_sq_one_sub_eta_sq hB
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  have : X B ^ 2 * (1 - eta B ^ 2) < X B ^ 2 * Real.sin (psi B) ^ 2 :=
    mul_lt_mul_of_pos_left (by rw [hsin2]; linarith) hX2
  linarith

/-- Odd `b` with `sin²(bπ/(2n)) = sin²(π/(2n))` is `≡ ±1 (mod 2n)`. -/
lemma odd_eq_case {n : ℕ} (hn : 2 ≤ n) (b : ℤ) (hodd : b % 2 = 1)
    (h : Real.sin (b * Real.pi / (2 * n)) ^ 2 = Real.sin (Real.pi / (2 * n)) ^ 2) :
    b % (2 * n) = 1 ∨ b % (2 * n) = 2 * n - 1 := by
  have hN : (0 : ℤ) < 2 * n := by omega
  set ρ := b % (2 * (n : ℤ)) with hρdef
  set K := b / (2 * (n : ℤ)) with hKdef
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg b (by omega)
  have hρN : ρ < 2 * n := Int.emod_lt_of_pos b hN
  have hdec : b = 2 * (n * K) + ρ := by
    have := Int.mul_ediv_add_emod b (2 * (n : ℤ)); rw [← hρdef, ← hKdef] at this; linarith
  have hρodd : ρ % 2 = 1 := by
    generalize n * K = M at hdec; omega
  by_contra hcon
  rw [not_or] at hcon
  have h3 : 3 ≤ ρ := by omega
  have h4 : ρ ≤ 2 * n - 3 := by omega
  -- reduce `b` to `ρ`
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx : (b : ℝ) * Real.pi / (2 * n) = (ρ : ℝ) * Real.pi / (2 * n) + (K : ℝ) * Real.pi := by
    have : (b : ℝ) = 2 * (n * K) + ρ := by exact_mod_cast hdec
    rw [this]; field_simp; ring
  rw [hx, sin_sq_add_int_mul_pi] at h
  have hpi := Real.pi_pos
  have hN2 : (0 : ℝ) < 2 * n := by positivity
  have h3' : (3 : ℝ) ≤ ρ := by exact_mod_cast h3
  have h4' : (ρ : ℝ) ≤ 2 * n - 3 := by exact_mod_cast h4
  have hlt := sin_lt_sin_of_mem (ψ := Real.pi / (2 * n)) (x := (ρ : ℝ) * Real.pi / (2 * n))
    (by positivity) (by rw [div_le_div_iff₀ hN2 (by norm_num)]; nlinarith)
    (by rw [div_lt_div_iff_of_pos_right hN2]; nlinarith)
    (by
      rw [show Real.pi - Real.pi / (2 * n) = (2 * n - 1) * Real.pi / (2 * n) by field_simp,
        div_lt_div_iff_of_pos_right hN2]
      nlinarith)
  have hpos : 0 < Real.sin (Real.pi / (2 * n)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hN2]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact (lt_mul_iff_one_lt_right hpi).2 (by linarith)
  have := mul_self_lt_mul_self hpos.le hlt
  rw [sq, sq] at h
  linarith

/-- **Proposition B 5.3, tangency.** For `ψ(B) = π/n`, `n ≥ 2`, the circles at `u` and `u + w`
are tangent iff `w` is a lattice direction modulo `ℤ(−n, 2n)`. -/
theorem coherent_tangent_iff {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n)
    (hψn : psi B = Real.pi / n) (p q a b : ℤ) :
    ‖zc B (psi B) (p + a) (q + b) - zc B (psi B) p q‖
        = rad B (p + a) (q + b) + rad B p q ↔
      ∃ k : ℤ, IsUnitDir (a + k * n) (b - 2 * k * n) := by
  have hcos := cos_psi hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hB0 : 0 < B := by linarith
  constructor
  · intro ht
    have hs : 3 ≤ |2 * a + b| ∨ |2 * a + b| = 2 ∨ 2 * a + b = 0 ∨ 2 * a + b = 1 ∨
        2 * a + b = -1 := by
      have h0 := abs_nonneg (2 * a + b)
      rcases abs_choice (2 * a + b) with h | h <;> rw [h] at h0 ⊢ <;> omega
    rcases hs with hs | hs | hs | hs | hs
    · exact absurd ht (not_tangent_far _ hB p q a b hs)
    · -- `|s| = 2`: `cos(bψ) = 1`, so `2n ∣ b`
      have hc := (tangent_s2 _ hB p q a b hs).1 ht
      rw [hψn] at hc
      obtain ⟨m, hm⟩ := Real.cos_eq_one_iff _ |>.1 hc
      have hbm : (b : ℝ) = 2 * n * m := by
        field_simp at hm; nlinarith [Real.pi_pos]
      have hbm' : b = 2 * n * m := by exact_mod_cast hbm
      refine ⟨m, ?_⟩
      unfold IsUnitDir
      rcases abs_choice (2 * a + b) with h | h
      · have hs2 : 2 * a + b = 2 := by rw [← h]; exact hs
        left; constructor <;> linarith
      · have hs2 : 2 * a + b = -2 := by
          have : -(2 * a + b) = 2 := by rw [← h]; exact hs
          linarith
        right; left; constructor <;> linarith
    · -- `s = 0`: impossible
      exfalso
      obtain ⟨j, rfl, rfl⟩ : ∃ j, a = -j ∧ b = 2 * j := ⟨-a, by ring, by omega⟩
      by_cases hj : (n : ℤ) ∣ j
      · obtain ⟨k, hk⟩ := hj
        have hco := (coherent_coincide_iff hB hn hψn p q (-j) (2 * j)).2
          ⟨k, by rw [hk]; ring, by rw [hk]; ring⟩
        rw [hco.2, sub_self, norm_zero, hco.1] at ht
        have : 0 < rad B p q := by unfold rad; exact zpow_pos hB0 _
        linarith
      · rw [tangent_iff_alg _ hB, show 2 * -j + 2 * j = 0 by ring, zpow_zero] at ht
        have hc := cos_eq_one_sub_two_sin_sq (((2 * j : ℤ) : ℝ) * psi B)
        rw [show ((2 * j : ℤ) : ℝ) * psi B / 2 = j * psi B by push_cast; ring] at hc
        rw [hc] at ht
        have h1 := one_lt_X_sq_sin_sq hB (by
          rw [hψn, div_le_div_iff₀ hn0 (by norm_num)]
          have : (2 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [Real.pi_pos])
        have h2 := sin_sq_le_of_not_dvd (N := (n : ℤ)) (by exact_mod_cast hn) j hj
        push_cast at h2
        rw [hψn] at h1 ht
        rw [show (j : ℝ) * (Real.pi / n) = j * Real.pi / n by ring] at ht
        have h3 : X B ^ 2 * Real.sin (Real.pi / n) ^ 2
            ≤ X B ^ 2 * Real.sin (j * Real.pi / n) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        have h4 : X B ^ 2 * Real.sin (j * Real.pi / n) ^ 2 = 1 := by linear_combination ht / 4
        linarith
    all_goals
      -- `s = ±1`: `cos(bψ) = cos ψ`, so `b ≡ ±1 (mod 2n)`
      have hcb : Real.cos (b * psi B) = Real.cos (psi B) := by
        first
          | exact (tangent_s1 hB hcos p q a b hs).1 ht
          | (have ht' := (tangent_symm p q a b).1 ht
             have := (tangent_s1 hB hcos (p + a) (q + b) (-a) (-b) (by omega)).1 ht'
             push_cast at this; rwa [neg_mul, Real.cos_neg] at this)
      rw [cos_eq_one_sub_two_sin_sq (b * psi B), cos_eq_one_sub_two_sin_sq (psi B), hψn] at hcb
      have hsq : Real.sin (b * Real.pi / (2 * n)) ^ 2 = Real.sin (Real.pi / (2 * n)) ^ 2 := by
        rw [show (b : ℝ) * Real.pi / (2 * n) = b * (Real.pi / n) / 2 by ring,
          show Real.pi / (2 * n) = Real.pi / n / 2 by ring]
        linarith
      have hodd : b % 2 = 1 := by omega
      have hρ := odd_eq_case hn b hodd hsq
      set K := b / (2 * (n : ℤ)) with hKdef
      have hdec : b = 2 * n * K + b % (2 * n) := by
        have := Int.mul_ediv_add_emod b (2 * (n : ℤ)); rw [← hKdef] at this; linarith
      unfold IsUnitDir
      rcases hρ with hρ | hρ <;> rw [hρ] at hdec
      · refine ⟨K, ?_⟩
        first
          | (right; right; left; constructor <;> linarith)
          | (right; right; right; right; right; constructor <;> linarith)
      · refine ⟨K + 1, ?_⟩
        first
          | (right; right; right; right; left; constructor <;> linarith)
          | (right; right; right; left; constructor <;> linarith)
  · rintro ⟨k, hdir⟩
    -- move to the representative `w' = w + k(n, −2n)`
    set a' := a + k * n with ha'
    set b' := b - 2 * k * n with hb'
    have hco := (coherent_coincide_iff hB hn hψn (p + a') (q + b') (a - a') (b - b')).2
      ⟨k, by rw [ha']; ring, by rw [hb']; ring⟩
    rw [show p + a' + (a - a') = p + a by ring, show q + b' + (b - b') = q + b by ring] at hco
    rw [hco.1, hco.2]
    have h10 := edge_10 (psi B) hB
    have h01 := edge_01 hB hcos
    have hm11 := edge_m11 hB hcos
    unfold IsUnitDir at hdir
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2]
    · simpa using h10 p q
    · have := h10 (p + -1) q
      rw [show p + -1 + 1 = p by ring, norm_sub_rev, add_comm (rad B p q)] at this
      rw [add_zero]; exact this
    · simpa using h01 p q
    · have := h01 p (q + -1)
      rw [show q + -1 + 1 = q by ring, norm_sub_rev, add_comm (rad B p q)] at this
      rw [add_zero]; exact this
    · have := hm11 (p + 1) (q + -1)
      rw [show p + 1 + -1 = p by ring, show q + -1 + 1 = q by ring, norm_sub_rev,
        add_comm (rad B p q)] at this
      exact this
    · exact hm11 p q

end DoyleFormal
