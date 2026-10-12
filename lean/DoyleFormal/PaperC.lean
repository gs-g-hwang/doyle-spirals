/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.RegularGeo

/-!
# Paper C, appendix and the lower bounds (Phase C1)

* `ball_pair` (**Lemma C A.1**): two points of the `k`-ring ball differ by `w` for some position
  iff `‖w‖ ≤ 2k`.
* `sin_gt_tanh` (**Lemma C A.3**): `ψ ≤ π/2 ⇒ sin ψ > tanh λ`.
* `patch_univalent` (**Proposition C A.4**): under (i) `t ≥ k+1`, or (ii) `k < t < k+1` and
  `sin((t−k)ψ) > tanh λ`, no two circles of the `k`-ring patch of `D_B` coincide or overlap.
  (Lemma C A.2 is Lemma B 5.1, `overlap_iff_Omega`.)
* `Bstar_spec` (**Proposition C 3.1 (a), `k ≥ 2`**): `B*_k`, the smallest zero of
  `sin(kψ(B)) − tanh log B` in `[B_{k+1}, B_k]`, exists, lies in `(B_{k+1}, B_k)`, and the
  function is positive on `[B_{k+1}, B*_k)`.
* `patch_univalent_lower` (**Proposition C 3.1 (b), `k ≥ 2`**): for `B ∈ [B_{k+1}, B*_k)` the
  `k`-ring patch of `D_B` has no coinciding and no overlapping circles.
-/

namespace DoyleFormal

open Real

/-- **Lemma C A.1.** -/
theorem ball_pair (k a b : ℤ) :
    (∃ p q : ℤ, hnorm p q ≤ k ∧ hnorm (p + a) (q + b) ≤ k) ↔ hnorm a b ≤ 2 * k := by
  simp only [hnorm_le_iff]
  constructor
  · rintro ⟨p, q, h1, h2⟩; omega
  · intro h
    refine ⟨-(a / 2), -((a + b) / 2 - a / 2), ?_, ?_⟩ <;> omega

/-- **Lemma C A.3.** -/
theorem sin_gt_tanh {B : ℝ} (hB : 1 < B) (hψ : psi B ≤ π / 2) :
    tanh (log B) < sin (psi B) := by
  have hB0 : 0 < B := by linarith
  have hψ0 := psi_mem_Ioo hB
  have hcos := cos_psi hB
  rw [cosPsi_eq_eta] at hcos
  set η := eta B with hη
  have hη0 : 0 < η := eta_pos hB0
  have hη1 : η < 1 := eta_lt_one hB
  have hcos0 : 0 ≤ cos (psi B) := cos_nonneg_of_mem_Icc ⟨by linarith [hψ0.1], hψ⟩
  have ht : tanh (log B) ^ 2 = 1 - η ^ 2 := by
    rw [tanh_log_eq hB, hη]; unfold eta; field_simp; ring
  have hs : sin (psi B) ^ 2 = 1 - (η ^ 2 + η - 1) ^ 2 := by
    rw [← hcos]; linarith [sin_sq_add_cos_sq (psi B)]
  have hspos : 0 < sin (psi B) := sin_pos_of_pos_of_lt_pi hψ0.1 hψ0.2
  have htpos : 0 < tanh (log B) := by
    rw [tanh_log_eq hB]; apply div_pos <;> nlinarith
  have hkey : tanh (log B) ^ 2 < sin (psi B) ^ 2 := by
    rw [ht, hs]
    have : 0 ≤ η ^ 2 + η - 1 := by rw [← hcos]; exact hcos0
    nlinarith
  nlinarith

lemma hnorm_one_dir {a b : ℤ} (h : hnorm a b = 1) : ∃ i : Fin 6, (a, b) = ldir i := by
  have h' : hnorm a b ≤ 1 := h.le
  rw [hnorm_le_iff] at h'
  have h2 : ¬ hnorm a b ≤ 0 := by omega
  rw [hnorm_le_iff] at h2
  have ha : -1 ≤ a ∧ a ≤ 1 := by omega
  have hb : -1 ≤ b ∧ b ≤ 1 := by omega
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> first | decide | (exfalso; omega)

/-- **Proposition C A.4.** Under (i) or (ii), no two circles of the `k`-ring patch of `D_B`
coincide, and no two overlap. -/
theorem patch_univalent {B : ℝ} (hB : 1 < B) {k : ℕ} (hk : 1 ≤ k)
    (h : ((k : ℝ) + 1 ≤ π / psi B) ∨
      ((k : ℝ) < π / psi B ∧ π / psi B < k + 1 ∧
        tanh (log B) < sin ((π / psi B - k) * psi B)))
    (p q p' q' : ℤ) (hu : hnorm p q ≤ k) (hu' : hnorm p' q' ≤ k) (hne : (p, q) ≠ (p', q')) :
    ¬ (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ∧
      ¬ ‖zc B (psi B) p' q' - zc B (psi B) p q‖ < rad B p' q' + rad B p q := by
  have hψ := psi_mem_Ioo hB
  set ψ := psi B with hψdef
  set t := π / ψ with ht
  have htk : (k : ℝ) < t := by
    rcases h with h | h
    · linarith
    · exact h.1
  have hdiff : hnorm (p' - p) (q' - q) ≤ 2 * k := by
    rw [hnorm_le_iff] at hu hu' ⊢; omega
  -- no coincidences
  have hnc : ¬ (rad B p' q' = rad B p q ∧ zc B ψ p' q' = zc B ψ p q) := by
    rw [same_circle_iff ψ hB]
    rintro ⟨j, hj1, hj2, m, hm⟩
    have hj0 : j ≠ 0 := by intro h0; subst h0; exact hne (by simp_all)
    have hjk : |j| ≤ k := by
      rw [hnorm_le_iff] at hdiff
      have : q' - q = 2 * j := by omega
      rw [abs_le]; omega
    -- `|j| ψ = |m| π ≥ π`, so `|j| ≥ t > k`
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hm
      simp only [Int.cast_zero, zero_mul, mul_eq_zero] at hm
      rcases hm with h1 | h1
      · exact hj0 (by exact_mod_cast h1)
      · linarith [hψ.1]
    have h1 : π ≤ |(j : ℝ)| * ψ := by
      have : |(j : ℝ) * ψ| = |(m : ℝ)| * π := by rw [hm, abs_mul, abs_of_pos pi_pos]
      rw [abs_mul, abs_of_pos hψ.1] at this
      rw [this]
      have : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
      nlinarith [pi_pos]
    have h2 : t ≤ |(j : ℝ)| := by
      rw [ht, div_le_iff₀ hψ.1]; exact h1
    have h3 : |(j : ℝ)| ≤ k := by rw [← Int.cast_abs]; exact_mod_cast hjk
    linarith
  refine ⟨hnc, fun hov => ?_⟩
  -- adjacent circles are tangent
  by_cases hadj : hnorm (p' - p) (q' - q) ≤ 1
  · have h1 : hnorm (p' - p) (q' - q) = 1 := by
      have : ¬ hnorm (p' - p) (q' - q) ≤ 0 := by
        rw [hnorm_le_iff]; intro h0; exact hne (by ext <;> simp <;> omega)
      omega
    obtain ⟨i, hi⟩ := hnorm_one_dir h1
    have he := (zc_isConfig hB).edge (p, q) i
    have hpq : (p, q) + ldir i = (p', q') := by rw [← hi]; ext <;> simp
    rw [hpq] at he
    simp only at he
    linarith
  push Not at hadj
  have h2 : 2 ≤ hnorm (p' - p) (q' - q) := hadj
  -- the resonant case
  by_cases hfr : Int.fract t = 0
  · have hfl : t = ⌊t⌋ := by have := Int.self_sub_floor t; rw [hfr] at this; linarith
    set n := ⌊t⌋ with hn
    have hnk : (k : ℤ) + 1 ≤ n := by
      rcases h with h | ⟨h1, h2, -⟩
      · have : ((k : ℤ) + 1 : ℝ) ≤ n := by rw [← hfl]; push_cast; exact h
        exact_mod_cast this
      · exfalso
        have a1 : (k : ℝ) < n := by rw [← hfl]; exact h1
        have a2 : (n : ℝ) < k + 1 := by rw [← hfl]; exact h2
        have b1 : (k : ℤ) < n := by exact_mod_cast a1
        have b2 : n < (k : ℤ) + 1 := by exact_mod_cast a2
        omega
    have hn2 : 2 ≤ n.toNat := by omega
    have hψn : psi B = π / (n.toNat : ℕ) := by
      have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [this, ← hfl, ht]; field_simp; rfl
    have hw : ¬ ∃ j : ℤ, p' - p = -(j * (n.toNat : ℕ)) ∧ q' - q = 2 * (j * (n.toNat : ℕ)) := by
      rintro ⟨j, hj1, hj2⟩
      have hj0 : j ≠ 0 := by intro h0; subst h0; exact hne (by ext <;> simp <;> omega)
      have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
      rw [hcast] at hj1 hj2
      rw [hnorm_le_iff] at hdiff
      rcases lt_or_gt_of_ne hj0 with hj | hj
      · nlinarith
      · nlinarith
    have := coherent_no_overlap hB hn2 hψn p q (p' - p) (q' - q) hw
    simp only [add_sub_cancel] at this
    exact this hov
  -- the non-resonant case: the first overlap is beyond the `k`-ring ball
  · have hr : 0 < Int.fract t := lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm hfr)
    have hm : (k : ℤ) < mFirst B := by
      unfold mFirst
      rw [← hψdef, ← ht]
      rcases h with h | ⟨h1, h2, h3⟩
      · have : (k : ℤ) + 1 ≤ ⌊t⌋ := by
          rw [Int.le_floor]; push_cast; exact h
        split_ifs <;> omega
      · have hfl : ⌊t⌋ = (k : ℤ) := by
          rw [Int.floor_eq_iff]; push_cast; exact ⟨h1.le, h2⟩
        have hfr' : Int.fract t = t - k := by
          rw [Int.fract, hfl]; push_cast; ring
        have hnot : ¬ sin ((t - k) * ψ) < tanh (log B) := by linarith
        simp only [hfr', hnot, ↓reduceIte, hfl]
        omega
    exact no_overlap_below hB hr k hm ⟨p, q, p', q', hu, hu', h2, hnc, hov⟩

/-! ### Proposition C 3.1 (a), (b) for `k ≥ 2` -/

/-- The resonant parameter `B_n` (`n ≥ 2`). -/
noncomputable def Bres (n : ℕ) : ℝ :=
  if h : 2 ≤ n then Classical.choose (resonant n h).exists else 2

lemma Bres_spec {n : ℕ} (hn : 2 ≤ n) : 1 < Bres n ∧ psi (Bres n) = π / n := by
  unfold Bres; simp only [hn, ↓reduceDIte]
  exact Classical.choose_spec (resonant n hn).exists

lemma continuous_psi : Continuous psi := by
  unfold psi cosPsi
  apply continuous_arccos.comp
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x; positivity

/-- The function whose smallest zero is `B*_k`; for `B > 1`, `(B²−1)/(B²+1) = tanh log B`. -/
noncomputable def gk (k : ℕ) (B : ℝ) : ℝ := sin (k * psi B) - (B ^ 2 - 1) / (B ^ 2 + 1)

lemma continuous_gk (k : ℕ) : Continuous (gk k) := by
  unfold gk
  apply Continuous.sub
  · exact continuous_sin.comp (continuous_const.mul continuous_psi)
  · apply Continuous.div (by fun_prop) (by fun_prop); intro x; positivity

lemma Bres_lt {k : ℕ} (hk : 2 ≤ k) : Bres (k + 1) < Bres k := by
  obtain ⟨h1, h1'⟩ := Bres_spec (show 2 ≤ k + 1 by omega)
  obtain ⟨h2, h2'⟩ := Bres_spec hk
  by_contra hc; push Not at hc
  rcases eq_or_lt_of_le hc with h | h
  · rw [h] at h2'; rw [h2'] at h1'
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    field_simp at h1'; push_cast at h1'; linarith [pi_pos]
  · have := psi_strictMonoOn h2 h1 h
    rw [h1', h2'] at this
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have : π / (k : ℝ) < π / ((k + 1 : ℕ) : ℝ) := this
    rw [div_lt_div_iff_of_pos_left pi_pos (by positivity) (by positivity)] at this
    push_cast at this; linarith

/-- `B*_k`: the smallest zero of `gk k` in `[B_{k+1}, B_k]`. -/
noncomputable def Bstar (k : ℕ) : ℝ := sInf {B ∈ Set.Icc (Bres (k + 1)) (Bres k) | gk k B = 0}

/-- **Proposition C 3.1 (a).** For `k ≥ 2`, `B*_k ∈ (B_{k+1}, B_k)` is a zero of
`sin(kψ(B)) − tanh log B`, and this function is positive on `[B_{k+1}, B*_k)`. -/
theorem Bstar_spec {k : ℕ} (hk : 2 ≤ k) :
    Bres (k + 1) < Bstar k ∧ Bstar k < Bres k ∧ gk k (Bstar k) = 0 ∧
      ∀ B, Bres (k + 1) ≤ B → B < Bstar k → 0 < gk k B := by
  obtain ⟨h1, h1'⟩ := Bres_spec (show 2 ≤ k + 1 by omega)
  obtain ⟨h2, h2'⟩ := Bres_spec hk
  have hlt := Bres_lt hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- the signs at the ends
  have hg1 : 0 < gk k (Bres (k + 1)) := by
    unfold gk
    rw [h1', ← tanh_log_eq h1]
    have : sin (k * (π / ((k + 1 : ℕ) : ℝ))) = sin (psi (Bres (k + 1))) := by
      rw [h1']; push_cast
      rw [show (k : ℝ) * (π / (k + 1)) = π - π / (k + 1) by field_simp; ring, sin_pi_sub]
    rw [this]
    have hle : psi (Bres (k + 1)) ≤ π / 2 := by
      rw [h1']; push_cast
      exact div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by linarith)
    linarith [sin_gt_tanh h1 hle]
  have hg2 : gk k (Bres k) < 0 := by
    unfold gk
    rw [h2', show (k : ℝ) * (π / k) = π by field_simp, sin_pi]
    have : 0 < (Bres k ^ 2 - 1) / (Bres k ^ 2 + 1) := by apply div_pos <;> nlinarith
    linarith
  -- the zero set is nonempty, closed and bounded
  set S := {B ∈ Set.Icc (Bres (k + 1)) (Bres k) | gk k B = 0}
  have hS : S.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hlt.le (continuous_gk k).continuousOn
      ⟨hg2.le, hg1.le⟩
    exact ⟨c, hc, hc0⟩
  have hSc : IsClosed S :=
    isClosed_Icc.inter (isClosed_eq (continuous_gk k) continuous_const)
  have hSb : BddBelow S := ⟨Bres (k + 1), fun x hx => hx.1.1⟩
  have hmem : Bstar k ∈ S := hSc.csInf_mem hS hSb
  have hne1 : Bstar k ≠ Bres (k + 1) := fun h => by
    have := hmem.2; rw [h] at this; linarith
  have hne2 : Bstar k ≠ Bres k := fun h => by
    have := hmem.2; rw [h] at this; linarith
  refine ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm hne1), lt_of_le_of_ne hmem.1.2 hne2, hmem.2,
    fun B hB1 hB2 => ?_⟩
  -- positivity before the first zero
  by_contra hc; push Not at hc
  obtain ⟨c, hc1, hc0⟩ := intermediate_value_Icc' hB1 (continuous_gk k).continuousOn
    ⟨hc, hg1.le⟩
  have hcS : c ∈ S := ⟨⟨hc1.1, by linarith [hc1.2, hmem.1.2]⟩, hc0⟩
  have := csInf_le hSb hcS
  change Bstar k ≤ c at this
  linarith [hc1.2]

/-- **Proposition C 3.1 (b).** For `k ≥ 2` and `B ∈ [B_{k+1}, B*_k)`, no two circles of the
`k`-ring patch of `D_B` coincide or overlap. -/
theorem patch_univalent_lower {k : ℕ} (hk : 2 ≤ k) {B : ℝ} (hB1 : Bres (k + 1) ≤ B)
    (hB2 : B < Bstar k) (p q p' q' : ℤ) (hu : hnorm p q ≤ k) (hu' : hnorm p' q' ≤ k)
    (hne : (p, q) ≠ (p', q')) :
    ¬ (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ∧
      ¬ ‖zc B (psi B) p' q' - zc B (psi B) p q‖ < rad B p' q' + rad B p q := by
  obtain ⟨hs1, hs2, -, hpos⟩ := Bstar_spec hk
  obtain ⟨h1, h1'⟩ := Bres_spec (show 2 ≤ k + 1 by omega)
  obtain ⟨h2, h2'⟩ := Bres_spec hk
  have hB : 1 < B := by linarith
  have hψ := psi_mem_Ioo hB
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  -- `π/(k+1) ≤ ψ(B) < π/k`
  have hψ1 : π / ((k : ℝ) + 1) ≤ psi B := by
    rcases eq_or_lt_of_le hB1 with h | h
    · rw [← h, h1']; push_cast; rfl
    · have := psi_strictMonoOn h1 hB h; rw [h1'] at this; push_cast at this; linarith
  have hψ2 : psi B < π / k := by
    have := psi_strictMonoOn hB h2 (by linarith); rw [h2'] at this; exact this
  have ht1 : π / psi B ≤ k + 1 := by
    rw [div_le_iff₀ hψ.1]; rw [div_le_iff₀ (by positivity)] at hψ1; linarith
  have ht2 : (k : ℝ) < π / psi B := by
    rw [lt_div_iff₀ hψ.1]; rw [lt_div_iff₀ hk0] at hψ2; linarith
  refine patch_univalent hB (by omega) ?_ p q p' q' hu hu' hne
  rcases eq_or_lt_of_le ht1 with h | h
  · left; rw [h]
  · right
    refine ⟨ht2, h, ?_⟩
    have hg := hpos B hB1 hB2
    unfold gk at hg
    rw [← tanh_log_eq hB] at hg
    have : sin ((π / psi B - k) * psi B) = sin (k * psi B) := by
      rw [sub_mul, div_mul_cancel₀ _ hψ.1.ne', sin_pi_sub]
    rw [this]; linarith

end DoyleFormal
