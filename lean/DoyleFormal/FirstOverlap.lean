/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Overlap

/-!
# Theorem B 5.2 (first overlap) — Phase 4e

The `m`-ring ball is `{u : ‖u‖ ≤ m}` for the hexagonal norm `‖(p,q)‖ = max(|p|,|q|,|p+q|)`.
`OverlapWithin B m` says that two circles of `D_B` at non-adjacent lattice points of the
`m`-ring ball (`‖u'−u‖ ≥ 2`), which are not the same circle, overlap.

`first_overlap` (Theorem B 5.2): for `B > 1` not resonant (`r = t − ⌊t⌋ > 0`, `t = π/ψ`),
the least such `m` is `⌊t⌋` if `sin(rψ) < tanh log B`, and `⌊t⌋ + 1` otherwise.
-/

namespace DoyleFormal

open Complex

/-- The hexagonal norm of the triangular lattice. -/
def hnorm (p q : ℤ) : ℤ := max |p| (max |q| |p + q|)

lemma hnorm_le_iff (p q m : ℤ) :
    hnorm p q ≤ m ↔ (-m ≤ p ∧ p ≤ m) ∧ (-m ≤ q ∧ q ≤ m) ∧ (-m ≤ p + q ∧ p + q ≤ m) := by
  simp only [hnorm, max_le_iff, abs_le]

lemma two_le_hnorm_iff (p q : ℤ) :
    2 ≤ hnorm p q ↔ (p ≤ -2 ∨ 2 ≤ p) ∨ (q ≤ -2 ∨ 2 ≤ q) ∨ (p + q ≤ -2 ∨ 2 ≤ p + q) := by
  simp only [hnorm, le_max_iff, le_abs']

/-- Two circles of `D_B` at non-adjacent points of the `m`-ring ball overlap. -/
def OverlapWithin (B : ℝ) (m : ℤ) : Prop :=
  ∃ p q p' q' : ℤ, hnorm p q ≤ m ∧ hnorm p' q' ≤ m ∧ 2 ≤ hnorm (p' - p) (q' - q) ∧
    ¬ (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ∧
    ‖zc B (psi B) p' q' - zc B (psi B) p q‖ < rad B p' q' + rad B p q

/-- The first-overlap ring predicted by Theorem B 5.2. -/
noncomputable def mFirst (B : ℝ) : ℤ :=
  if Real.sin (Int.fract (Real.pi / psi B) * psi B) < Real.tanh (Real.log B)
  then ⌊Real.pi / psi B⌋ else ⌊Real.pi / psi B⌋ + 1

lemma X_sq_sin_lt_one_iff {B : ℝ} (hB : 1 < B) (x : ℝ) :
    X B ^ 2 * Real.sin x ^ 2 < 1 ↔ |Real.sin x| < Real.tanh (Real.log B) := by
  have ht : 0 < Real.tanh (Real.log B) := by
    rw [tanh_log_eq hB]; apply div_pos <;> nlinarith
  have key := X_sq_mul_tanh_sq hB
  have hX2 : 0 < X B ^ 2 := by nlinarith [X_neg hB]
  rw [← abs_of_pos ht, ← sq_lt_sq]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma sin_sq_int_abs (j : ℤ) (ψ : ℝ) :
    Real.sin (j * ψ) ^ 2 = Real.sin (((|j| : ℤ) : ℝ) * ψ) ^ 2 := by
  rcases abs_choice j with h | h <;> rw [h]
  push_cast; rw [neg_mul, Real.sin_neg]; ring

lemma cos_int_abs (b : ℤ) (ψ : ℝ) : Real.cos (b * ψ) = Real.cos (((|b| : ℤ) : ℝ) * ψ) := by
  rcases abs_choice b with h | h <;> rw [h]
  push_cast; rw [neg_mul, Real.cos_neg]

/-- **No overlap below the predicted ring.** -/
theorem no_overlap_below {B : ℝ} (hB : 1 < B) (hr : 0 < Int.fract (Real.pi / psi B)) (m : ℤ)
    (hm : m < mFirst B) : ¬ OverlapWithin B m := by
  have hψ := psi_mem_Ioo hB
  have hcos := cos_psi hB
  set ψ := psi B with hψdef
  set n := ⌊Real.pi / ψ⌋ with hndef
  set r := Int.fract (Real.pi / ψ) with hrdef
  have htψ : Real.pi / ψ * ψ = Real.pi := div_mul_cancel₀ _ hψ.1.ne'
  have hnt : (n : ℝ) ≤ Real.pi / ψ := Int.floor_le _
  have hM : mFirst B ≤ n + 1 := by unfold mFirst; split_ifs <;> simp [← hψdef, ← hndef]
  rintro ⟨p, q, p', q', hu, hv, h2, -, hov⟩
  obtain ⟨a, rfl⟩ : ∃ a, p' = p + a := ⟨p' - p, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, q' = q + b := ⟨q' - q, by ring⟩
  simp only [add_sub_cancel_left] at h2
  rw [hnorm_le_iff] at hu hv
  rw [two_le_hnorm_iff] at h2
  -- `|s| ≤ 1`
  have hs : 2 * a + b = 0 ∨ 2 * a + b = 1 ∨ 2 * a + b = -1 := by
    by_contra hc
    exact no_overlap_far ψ hB p q a b (by rw [le_abs']; omega) hov
  rcases hs with hs | hs | hs
  · -- type (E): `w = j(−1,2)`
    obtain ⟨j, rfl, rfl⟩ : ∃ j, a = -j ∧ b = 2 * j := ⟨-a, by ring, by omega⟩
    have hov' := (overlap_s0 ψ hB p q j).1 hov
    rw [sin_sq_int_abs] at hov'
    set k := |j| with hk
    have hk1 : 1 ≤ k := by have := abs_nonneg j; rcases abs_choice j with h | h <;> omega
    have hkm : k ≤ m := by have := abs_nonneg j; rcases abs_choice j with h | h <;> omega
    by_cases hkn : k ≤ n - 1
    · apply E_no_overlap_before hB k hk1 _ hov'
      have : ((k : ℝ) + 1) ≤ Real.pi / ψ := by
        have : ((k + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast (by omega : k + 1 ≤ n)
        push_cast at this; linarith
      calc ((k : ℝ) + 1) * ψ ≤ Real.pi / ψ * ψ := mul_le_mul_of_nonneg_right this hψ.1.le
        _ = Real.pi := htψ
    · -- `k = n` and the condition of `mFirst` fails
      have hkn' : k = n := by omega
      have hcond : ¬ Real.sin (r * ψ) < Real.tanh (Real.log B) := by
        intro hc
        have : mFirst B = n := by
          unfold mFirst; split_ifs with h
          · rfl
          · exact absurd hc h
        omega
      apply hcond
      have hsf := sin_floor_mul hψ.1
      rw [← hndef, ← hrdef] at hsf
      rw [hkn', hsf, X_sq_sin_lt_one_iff hB] at hov'
      exact lt_of_le_of_lt (le_abs_self _) hov'
  · -- type (O), `s = 1`
    have hov' := (overlap_s1 hB hcos p q a b hs).1 hov
    rw [cos_int_abs] at hov'
    set c := |b| with hc
    have hc3 : 3 ≤ c := by have := abs_nonneg b; rcases abs_choice b with h | h <;> omega
    have hcm : c ≤ 2 * m := by have := abs_nonneg b; rcases abs_choice b with h | h <;> omega
    have hcodd : c % 2 = 1 := by have := abs_nonneg b; rcases abs_choice b with h | h <;> omega
    by_cases hcn : c ≤ 2 * n - 3
    · refine absurd hov' (not_lt.2 (O_no_overlap_before hB c hc3 ?_).le)
      have : ((c : ℝ) + 3) ≤ 2 * (Real.pi / ψ) := by
        have : ((c + 3 : ℤ) : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : c + 3 ≤ 2 * n)
        push_cast at this; linarith
      calc ((c : ℝ) + 3) * ψ ≤ 2 * (Real.pi / ψ) * ψ := mul_le_mul_of_nonneg_right this hψ.1.le
        _ = 2 * Real.pi := by rw [mul_assoc, htψ]
    · have hc' : c = 2 * n - 1 := by omega
      have := O_no_overlap_floor hB (by rw [← hψdef, ← hndef]; omega) hr
      rw [← hψdef, ← hndef, ← hc'] at this
      linarith
  · -- type (O), `s = −1`
    have hov' := (overlap_sm1 hB hcos p q a b hs).1 hov
    rw [cos_int_abs] at hov'
    set c := |b| with hc
    have hc3 : 3 ≤ c := by have := abs_nonneg b; rcases abs_choice b with h | h <;> omega
    have hcm : c ≤ 2 * m := by have := abs_nonneg b; rcases abs_choice b with h | h <;> omega
    have hcodd : c % 2 = 1 := by have := abs_nonneg b; rcases abs_choice b with h | h <;> omega
    by_cases hcn : c ≤ 2 * n - 3
    · refine absurd hov' (not_lt.2 (O_no_overlap_before hB c hc3 ?_).le)
      have : ((c : ℝ) + 3) ≤ 2 * (Real.pi / ψ) := by
        have : ((c + 3 : ℤ) : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : c + 3 ≤ 2 * n)
        push_cast at this; linarith
      calc ((c : ℝ) + 3) * ψ ≤ 2 * (Real.pi / ψ) * ψ := mul_le_mul_of_nonneg_right this hψ.1.le
        _ = 2 * Real.pi := by rw [mul_assoc, htψ]
    · have hc' : c = 2 * n - 1 := by omega
      have := O_no_overlap_floor hB (by rw [← hψdef, ← hndef]; omega) hr
      rw [← hψdef, ← hndef, ← hc'] at this
      linarith

/-- **Overlap at the predicted ring.** -/
theorem overlap_at_mFirst {B : ℝ} (hB : 1 < B) (hr : 0 < Int.fract (Real.pi / psi B)) :
    OverlapWithin B (mFirst B) := by
  have hψ := psi_mem_Ioo hB
  have hcos := cos_psi hB
  set ψ := psi B with hψdef
  set n := ⌊Real.pi / ψ⌋ with hndef
  set r := Int.fract (Real.pi / ψ) with hrdef
  have ht1 : 1 < Real.pi / ψ := by rw [one_lt_div hψ.1]; exact hψ.2
  have hn1 : 1 ≤ n := Int.le_floor.2 (by push_cast; linarith)
  have hr1 : r < 1 := Int.fract_lt_one _
  have hnψ : (n : ℝ) * ψ = Real.pi - r * ψ := by
    have := Int.floor_add_fract (Real.pi / ψ)
    have h2 : (n : ℝ) = Real.pi / ψ - r := by linarith
    rw [h2, sub_mul, div_mul_cancel₀ _ hψ.1.ne']
  change OverlapWithin B (if Real.sin (r * ψ) < Real.tanh (Real.log B) then n else n + 1)
  split_ifs with hc
  · -- type (E) at ring `n`: `u = (n, −n)`, `u' = u + n(−1,2)`
    refine ⟨n, -n, n + -n, -n + 2 * n, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnorm_le_iff]; omega
    · rw [hnorm_le_iff]; omega
    · rw [two_le_hnorm_iff]; omega
    · rintro hsame
      obtain ⟨j, hj1, -, k, hk⟩ := (same_circle_iff ψ hB n (-n) (n + -n) (-n + 2 * n)).1 hsame
      have hj : j = n := by omega
      rw [hj] at hk
      have hpos : 0 < (n : ℝ) * ψ := by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : (0 : ℤ) < n)
        exact mul_pos this hψ.1
      have hlt : (n : ℝ) * ψ < Real.pi := by rw [hnψ]; nlinarith [hψ.1]
      rw [hk] at hpos hlt
      have k0 : (0 : ℝ) < k := by
        by_contra h; rw [not_lt] at h; nlinarith [Real.pi_pos]
      have k1 : (k : ℝ) < 1 := by
        by_contra h; rw [not_lt] at h; nlinarith [Real.pi_pos]
      have : (0 : ℤ) < k := by exact_mod_cast k0
      have : k < (1 : ℤ) := by exact_mod_cast k1
      omega
    · have hsf := sin_floor_mul hψ.1
      rw [← hndef, ← hrdef] at hsf
      rw [overlap_s0_tanh ψ hB, hsf]
      have : 0 ≤ Real.sin (r * ψ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Int.fract_nonneg _) hψ.1.le)
          (by nlinarith [hψ.1, hψ.2])
      rwa [abs_of_nonneg this]
  · -- type (O) at ring `n + 1`: `u = (n, −n)`, `u' = u + (−n, 2n+1)`
    refine ⟨n, -n, n + -n, -n + (2 * n + 1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnorm_le_iff]; omega
    · rw [hnorm_le_iff]; omega
    · rw [two_le_hnorm_iff]; omega
    · rintro ⟨hrad, -⟩
      have hB0 : 0 < B := by linarith
      rw [rad_add hB0, show 2 * -n + (2 * n + 1) = 1 by ring, zpow_one] at hrad
      have hr0 : 0 < rad B n (-n) := by unfold rad; exact zpow_pos hB0 _
      nlinarith
    · rw [overlap_s1 hB hcos n (-n) (-n) (2 * n + 1) (by ring)]
      have := O_overlap_ceil hB hr
      rwa [← hψdef, ← hndef] at this

/-- **Theorem B 5.2 (first overlap).** For non-resonant `B > 1`, `mFirst B` is the least `m`
such that two circles at non-adjacent points of the `m`-ring ball overlap. -/
theorem first_overlap {B : ℝ} (hB : 1 < B) (hr : 0 < Int.fract (Real.pi / psi B)) :
    IsLeast {m : ℤ | OverlapWithin B m} (mFirst B) := by
  refine ⟨overlap_at_mFirst hB hr, fun m hm => ?_⟩
  by_contra h
  exact no_overlap_below hB hr m (lt_of_not_ge h) hm

end DoyleFormal
