/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Fibres

/-!
# Paper C: the near-period corollary of Lemma 2.2 and the case `k = 1` of Proposition 3.1

* `norm_exp_sub_one_le_mul_exp`: `|e^w − 1| ≤ |w| e^{|w|}`.
* `near_period` (**Lemma C 2.2, second statement**): if `|ℓ − 2πim| ≤ ε` and
  `ε e^ε < 2κ e^{−ε}`, then `|e^ℓ − 1| < κ(1 + |e^ℓ|)`; with `doyle_overlap_iff`, the circles
  `K(u)`, `K(u+v)` with `α^v = e^ℓ` overlap or coincide (`near_period_overlap`).
* `Bstar1_spec`, `patch_univalent_lower1` (**Proposition C 3.1 for `k = 1`**, `B₁ = ∞`): `B*_1`
  exists in `(B₂, ∞)`, and the `1`-ring patch of `D_B` has no coinciding or overlapping
  circles for `B ∈ [B₂, B*_1)`.
-/

namespace DoyleFormal

open Real Filter Topology

/-- `|e^w − 1| ≤ |w| e^{|w|}`. -/
theorem norm_exp_sub_one_le_mul_exp (w : ℂ) : ‖Complex.exp w - 1‖ ≤ ‖w‖ * exp ‖w‖ := by
  -- for every `N ≥ ‖w‖ + 1`: telescoping over `N` steps
  have hN : ∀ N : ℕ, ‖w‖ ≤ N → 0 < N →
      ‖Complex.exp w - 1‖ ≤ exp ‖w‖ * (‖w‖ + ‖w‖ ^ 2 / N) := by
    intro N hwN hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set x := w / N
    have hx : ‖x‖ ≤ 1 := by
      simp only [x, norm_div, Complex.norm_natCast]; rw [div_le_one hN0]; exact hwN
    have htel : Complex.exp w - 1 =
        ∑ k ∈ Finset.range N, Complex.exp (k * x) * (Complex.exp x - 1) := by
      have : ∀ k : ℕ, Complex.exp (k * x) * (Complex.exp x - 1) =
          Complex.exp ((k + 1 : ℕ) * x) - Complex.exp (k * x) := by
        intro k; push_cast; rw [add_mul, one_mul, Complex.exp_add]; ring
      simp only [this]
      rw [Finset.sum_range_sub (fun k : ℕ => Complex.exp (k * x))]
      simp only [x, Nat.cast_zero, zero_mul, Complex.exp_zero]
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      congr 2; field_simp
    have hterm : ∀ k ∈ Finset.range N, ‖Complex.exp (k * x) * (Complex.exp x - 1)‖ ≤
        exp ‖w‖ * (‖x‖ + ‖x‖ ^ 2) := by
      intro k hk
      rw [norm_mul]
      have h1 : ‖Complex.exp (k * x)‖ ≤ exp ‖w‖ := by
        refine (Complex.norm_exp_le_exp_norm _).trans (exp_le_exp.2 ?_)
        rw [norm_mul, Complex.norm_natCast]
        simp only [x, norm_div, Complex.norm_natCast]
        have hk' : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hk).le
        rw [mul_div_assoc', div_le_iff₀ hN0]; nlinarith [norm_nonneg w]
      have h2 : ‖Complex.exp x - 1‖ ≤ ‖x‖ + ‖x‖ ^ 2 := by
        have := Complex.norm_exp_sub_one_sub_id_le hx
        calc ‖Complex.exp x - 1‖ = ‖(Complex.exp x - 1 - x) + x‖ := by ring_nf
          _ ≤ ‖Complex.exp x - 1 - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ ‖x‖ + ‖x‖ ^ 2 := by linarith
      exact mul_le_mul h1 h2 (norm_nonneg _) (exp_pos _).le
    rw [htel]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, x, norm_div,
      Complex.norm_natCast]
    field_simp
  -- let `N → ∞`
  have hlim : Tendsto (fun N : ℕ => exp ‖w‖ * (‖w‖ + ‖w‖ ^ 2 / N)) atTop
      (𝓝 (exp ‖w‖ * (‖w‖ + 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop))
  rw [add_zero, mul_comm] at hlim
  refine ge_of_tendsto hlim ?_
  obtain ⟨M, hM⟩ := exists_nat_ge (‖w‖ + 1)
  filter_upwards [eventually_ge_atTop M] with N hNM
  have hNr : (M : ℝ) ≤ N := by exact_mod_cast hNM
  exact hN N (by linarith) (by exact_mod_cast (show 0 < (N : ℝ) by linarith [norm_nonneg w]))

/-- **Lemma C 2.2, second statement (near-periods).** -/
theorem near_period {ℓ : ℂ} {m : ℤ} {ε κ : ℝ}
    (h : ‖ℓ - 2 * π * Complex.I * m‖ ≤ ε) (hεκ : ε * exp ε < 2 * κ * exp (-ε)) :
    ‖Complex.exp ℓ - 1‖ < κ * (1 + ‖Complex.exp ℓ‖) := by
  set ℓ' := ℓ - 2 * π * Complex.I * m
  have hε : 0 ≤ ε := (norm_nonneg _).trans h
  have hper : Complex.exp ℓ = Complex.exp ℓ' := by
    simp only [ℓ']
    rw [Complex.exp_sub, show 2 * (π : ℂ) * Complex.I * m = m * (2 * π * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, div_one]
  have hκ : 0 < κ := by
    by_contra hk; push Not at hk
    have : 2 * κ * exp (-ε) ≤ 0 := by
      have := exp_pos (-ε); nlinarith
    nlinarith [mul_nonneg hε (exp_pos ε).le]
  -- `|e^ℓ − 1| ≤ ε e^ε`
  have h1 : ‖Complex.exp ℓ - 1‖ ≤ ε * exp ε := by
    rw [hper]
    refine (norm_exp_sub_one_le_mul_exp ℓ').trans ?_
    exact mul_le_mul h (exp_le_exp.2 h) (exp_pos _).le hε
  -- `1 + |e^ℓ| ≥ 2 e^{−ε}`
  have h2 : 2 * exp (-ε) ≤ 1 + ‖Complex.exp ℓ‖ := by
    rw [hper, Complex.norm_exp]
    have a : exp (-ε) ≤ exp ℓ'.re := by
      apply exp_le_exp.2
      have := Complex.abs_re_le_norm ℓ'
      rw [abs_le] at this; linarith
    have b : exp (-ε) ≤ 1 := by rw [exp_le_one_iff]; linarith
    linarith
  calc ‖Complex.exp ℓ - 1‖ ≤ ε * exp ε := h1
    _ < 2 * κ * exp (-ε) := hεκ
    _ ≤ κ * (1 + ‖Complex.exp ℓ‖) := by nlinarith

/-- With the structure of `doyle_structure`: a near-period gives overlapping or coinciding
circles. -/
theorem near_period_overlap {A B : ℝ} {z : ℤ → ℤ → ℂ} {X α₀ α₁ : ℂ} (hα₀ : α₀ ≠ 0)
    (hα₁ : α₁ ≠ 0) (hX : z 0 0 ≠ X)
    (hexp : ∀ p q : ℤ, z p q - X = α₀ ^ p * α₁ ^ q * (z 0 0 - X))
    (hrad : ∀ p q : ℤ, A ^ p * B ^ q = ‖z p q - X‖ / ‖z 0 0 - X‖) (p q a b : ℤ) {ℓ : ℂ}
    (hℓ : Complex.exp ℓ = α₀ ^ a * α₁ ^ b) {m : ℤ} {ε : ℝ}
    (h : ‖ℓ - 2 * π * Complex.I * m‖ ≤ ε)
    (hεκ : ε * exp ε < 2 * (1 / ‖z 0 0 - X‖) * exp (-ε)) :
    ‖z (p + a) (q + b) - z p q‖ < A ^ (p + a) * B ^ (q + b) + A ^ p * B ^ q := by
  rw [doyle_overlap_iff hα₀ hα₁ hX hexp hrad, ← hℓ]
  exact near_period h hεκ

/-! ### Proposition C 3.1 for `k = 1` -/

lemma cosPsi_six : cosPsi 6 = -781 / 1369 := by unfold cosPsi; norm_num

lemma psi_six_gt : π / 2 < psi 6 := by
  unfold psi
  rw [cosPsi_six, arccos_eq_pi_div_two_sub_arcsin]
  have : arcsin (-781 / 1369) < 0 := arcsin_lt_zero.2 (by norm_num)
  linarith

lemma Bres_two_lt_six : Bres 2 < 6 := by
  obtain ⟨h1, h1'⟩ := Bres_spec (le_refl 2)
  by_contra hc; push Not at hc
  rcases eq_or_lt_of_le hc with h | h
  · have := psi_six_gt; rw [h, h1'] at this; norm_num at this
  · have := psi_strictMonoOn (by norm_num : (1 : ℝ) < 6) h1 h
    rw [h1'] at this; have := psi_six_gt; norm_num at *; linarith

lemma gk_one_six : gk 1 6 < 0 := by
  unfold gk
  have hψ := psi_mem_Ioo (by norm_num : (1 : ℝ) < 6)
  have hs : 0 ≤ sin (psi 6) := (sin_pos_of_pos_of_lt_pi hψ.1 hψ.2).le
  have hc := cos_psi (by norm_num : (1 : ℝ) < 6)
  rw [cosPsi_six] at hc
  have hsq : sin (psi 6) ^ 2 = 1 - (781 / 1369) ^ 2 := by
    rw [sin_sq, hc]; ring
  have : sin (psi 6) < 35 / 37 := by nlinarith
  norm_num; linarith

/-- `B*_1`: the smallest zero of `sin ψ(B) − tanh log B` beyond `B₂` (`B₁ = ∞`). -/
noncomputable def Bstar1 : ℝ := sInf {B ∈ Set.Icc (Bres 2) 6 | gk 1 B = 0}

/-- **Proposition C 3.1 (a) for `k = 1`.** -/
theorem Bstar1_spec :
    Bres 2 < Bstar1 ∧ gk 1 Bstar1 = 0 ∧ ∀ B, Bres 2 ≤ B → B < Bstar1 → 0 < gk 1 B := by
  obtain ⟨h1, h1'⟩ := Bres_spec (le_refl 2)
  have hlt := Bres_two_lt_six
  have hg1 : 0 < gk 1 (Bres 2) := by
    unfold gk
    rw [h1', show ((1 : ℕ) : ℝ) * (π / ((2 : ℕ) : ℝ)) = π / 2 by push_cast; ring, sin_pi_div_two]
    have : (Bres 2 ^ 2 - 1) / (Bres 2 ^ 2 + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  have hg2 := gk_one_six
  set S := {B ∈ Set.Icc (Bres 2) 6 | gk 1 B = 0}
  have hS : S.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hlt.le (continuous_gk 1).continuousOn
      ⟨hg2.le, hg1.le⟩
    exact ⟨c, hc, hc0⟩
  have hSc : IsClosed S :=
    isClosed_Icc.inter (isClosed_eq (continuous_gk 1) continuous_const)
  have hSb : BddBelow S := ⟨Bres 2, fun x hx => hx.1.1⟩
  have hmem : Bstar1 ∈ S := hSc.csInf_mem hS hSb
  have hne1 : Bstar1 ≠ Bres 2 := fun h => by
    have := hmem.2; rw [h] at this; linarith
  refine ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm hne1), hmem.2, fun B hB1 hB2 => ?_⟩
  by_contra hc; push Not at hc
  obtain ⟨c, hc1, hc0⟩ := intermediate_value_Icc' hB1 (continuous_gk 1).continuousOn
    ⟨hc, hg1.le⟩
  have hcS : c ∈ S := ⟨⟨hc1.1, by linarith [hc1.2, hmem.1.2]⟩, hc0⟩
  have := csInf_le hSb hcS
  change Bstar1 ≤ c at this
  linarith [hc1.2]

/-- **Proposition C 3.1 (b) for `k = 1`.** -/
theorem patch_univalent_lower1 {B : ℝ} (hB1 : Bres 2 ≤ B) (hB2 : B < Bstar1)
    (p q p' q' : ℤ) (hu : hnorm p q ≤ 1) (hu' : hnorm p' q' ≤ 1) (hne : (p, q) ≠ (p', q')) :
    ¬ (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ∧
      ¬ ‖zc B (psi B) p' q' - zc B (psi B) p q‖ < rad B p' q' + rad B p q := by
  obtain ⟨-, -, hpos⟩ := Bstar1_spec
  obtain ⟨h1, h1'⟩ := Bres_spec (le_refl 2)
  have hB : 1 < B := by linarith
  have hψ := psi_mem_Ioo hB
  have hψ1 : π / 2 ≤ psi B := by
    rcases eq_or_lt_of_le hB1 with h | h
    · rw [← h, h1']; push_cast; rfl
    · have := psi_strictMonoOn h1 hB h; rw [h1'] at this; push_cast at this; linarith
  have ht1 : π / psi B ≤ (1 : ℕ) + 1 := by
    rw [div_le_iff₀ hψ.1]; push_cast; linarith
  have ht2 : ((1 : ℕ) : ℝ) < π / psi B := by
    rw [lt_div_iff₀ hψ.1]; push_cast; linarith [hψ.2]
  refine patch_univalent hB (le_refl 1) ?_ p q p' q' hu hu' hne
  rcases eq_or_lt_of_le ht1 with h | h
  · left; rw [h]
  · right
    refine ⟨ht2, h, ?_⟩
    have hg := hpos B hB1 hB2
    unfold gk at hg
    rw [← tanh_log_eq hB] at hg
    have : sin ((π / psi B - ((1 : ℕ) : ℝ)) * psi B) = sin (((1 : ℕ) : ℝ) * psi B) := by
      rw [sub_mul, div_mul_cancel₀ _ hψ.1.ne']; push_cast; rw [one_mul, sin_pi_sub]
    rw [this]; linarith

/-! ### The additive map `ℒ` of Proposition C 2.1 -/

/-- `ℒ(p,q) = p log α₀ + q log α₁` satisfies `e^{ℒ(p,q)} = α₀^p α₁^q`. -/
theorem lattice_log {α₀ α₁ : ℂ} (h0 : α₀ ≠ 0) (h1 : α₁ ≠ 0) (p q : ℤ) :
    Complex.exp (p * Complex.log α₀ + q * Complex.log α₁) = α₀ ^ p * α₁ ^ q := by
  rw [Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, Complex.exp_log h0,
    Complex.exp_log h1]

/-- **Uniqueness of `ℒ` up to `2πi ℓ`.** Two additive maps `ℤ² → ℂ` with the same exponentials
differ by `2πi ℓ` for an additive `ℓ : ℤ² → ℤ`. -/
theorem lattice_log_unique (L L' : ℤ × ℤ →+ ℂ)
    (h : ∀ u, Complex.exp (L u) = Complex.exp (L' u)) :
    ∃ ℓ : ℤ × ℤ →+ ℤ, ∀ u, L u = L' u + 2 * π * Complex.I * ℓ u := by
  have hk : ∀ u, ∃ n : ℤ, L u - L' u = n * (2 * π * Complex.I) := fun u =>
    Complex.exp_eq_one_iff.1 (by rw [Complex.exp_sub, h u, div_self (Complex.exp_ne_zero _)])
  choose n hn using hk
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hadd : ∀ u v, n (u + v) = n u + n v := by
    intro u v
    have e := hn (u + v)
    rw [map_add, map_add, show L u + L v - (L' u + L' v) = (L u - L' u) + (L v - L' v) by ring,
      hn u, hn v] at e
    have : ((n (u + v) : ℂ) - (n u + n v)) * (2 * π * Complex.I) = 0 := by
      linear_combination -e
    have := (mul_eq_zero.1 this).resolve_right h2pi
    exact_mod_cast (sub_eq_zero.1 this)
  have hzero : n 0 = 0 := by
    have := hadd 0 0; simp only [add_zero] at this; omega
  refine ⟨⟨⟨n, hzero⟩, hadd⟩, fun u => ?_⟩
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  linear_combination hn u

end DoyleFormal
