/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.HexExp

/-!
# Paper C, Proposition 3.1: the asymptotics of `B_n` (Phase C2)

* `Bres_tendsto_one`: `B_n → 1`.
* `Bres_sub_one`: `B_n − 1 = sin(π/(2n)) (B_n² + 1)/√(B_n² + B_n + 1)` (from
  `sin²(ψ/2) = (1 − η)(2 + η)/2`).
* `Bres_asymp` (**Proposition C 3.1, last part**): `k (B_{k+1}² − 1) → 2π/√3`.
-/

namespace DoyleFormal

open Real Filter Topology

lemma Bres_tendsto_one : Tendsto Bres atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB1 : 1 < 1 + ε := by linarith
  have hψ := (psi_mem_Ioo hB1).1
  obtain ⟨N, hN⟩ := exists_nat_gt (max 2 (π / psi (1 + ε)))
  refine ⟨N, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) < n :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) (by exact_mod_cast hn)
    exact_mod_cast this.le
  obtain ⟨h1, h1'⟩ := Bres_spec hn2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : psi (Bres n) < psi (1 + ε) := by
    rw [h1', div_lt_iff₀ hn0]
    have : π / psi (1 + ε) < n :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) (by exact_mod_cast hn)
    rw [div_lt_iff₀ hψ] at this; linarith
  have hB : Bres n < 1 + ε := by
    by_contra hc; push Not at hc
    rcases eq_or_lt_of_le hc with h | h
    · rw [h] at hlt; exact lt_irrefl _ hlt
    · linarith [psi_strictMonoOn hB1 h1 h]
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

lemma Bres_sub_one {n : ℕ} (hn : 2 ≤ n) :
    Bres n - 1 = sin (π / (2 * n)) * ((Bres n ^ 2 + 1) / √(Bres n ^ 2 + Bres n + 1)) := by
  obtain ⟨h1, h1'⟩ := Bres_spec hn
  set B := Bres n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : sin (π / (2 * n)) ^ 2 = (B - 1) ^ 2 * (B ^ 2 + B + 1) / (B ^ 2 + 1) ^ 2 := by
    rw [← sin_sq_half_eta, show π / (2 * n) = psi B / 2 by rw [h1']; field_simp]
    have := cos_psi h1
    rw [cosPsi_eq_eta] at this
    rw [sin_sq_eq_half_sub, show 2 * (psi B / 2) = psi B by ring, this]; ring
  have hspos : 0 < sin (π / (2 * n)) := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hq : 0 < B ^ 2 + B + 1 := by positivity
  have hsq : sin (π / (2 * n)) = (B - 1) * √(B ^ 2 + B + 1) / (B ^ 2 + 1) := by
    have hpos : 0 ≤ (B - 1) * √(B ^ 2 + B + 1) / (B ^ 2 + 1) := by
      apply div_nonneg (mul_nonneg (by linarith) (sqrt_nonneg _)) (by positivity)
    rw [← sqrt_sq hspos.le, ← sqrt_sq hpos, hs]
    congr 1
    rw [div_pow, mul_pow, sq_sqrt hq.le]
  rw [hsq]
  have : √(B ^ 2 + B + 1) ≠ 0 := (sqrt_pos.2 hq).ne'
  field_simp

lemma n_sin_tendsto : Tendsto (fun n : ℕ => (n : ℝ) * sin (π / (2 * n))) atTop (𝓝 (π / 2)) := by
  have hlow : Tendsto (fun n : ℕ => π / 2 - (π / 2) ^ 3 / 6 / (n : ℝ) ^ 2) atTop (𝓝 (π / 2)) := by
    have : Tendsto (fun n : ℕ => (π / 2) ^ 3 / 6 / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hx : 0 < π / (2 * n) := by positivity
    have := sin_gt_sub_cube hx
    have e : (n : ℝ) * (π / (2 * n) - (π / (2 * n)) ^ 3 / 6) = π / 2 - (π / 2) ^ 3 / 6 / n ^ 2 := by
      field_simp
    rw [← e]
    exact (mul_le_mul_of_nonneg_left this.le hn0.le)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := sin_le (show 0 ≤ π / (2 * n) by positivity)
    calc (n : ℝ) * sin (π / (2 * n)) ≤ n * (π / (2 * n)) := mul_le_mul_of_nonneg_left this hn0.le
      _ = π / 2 := by field_simp

/-- **Proposition C 3.1, asymptotics.** `k (B_{k+1}² − 1) → 2π/√3`. -/
theorem Bres_asymp :
    Tendsto (fun k : ℕ => (k : ℝ) * (Bres (k + 1) ^ 2 - 1)) atTop (𝓝 (2 * π / √3)) := by
  -- `n (B_n − 1) → π/√3`
  set g : ℝ → ℝ := fun B => (B ^ 2 + 1) / √(B ^ 2 + B + 1)
  have hg : Continuous g := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x; exact (sqrt_pos.2 (by nlinarith [sq_nonneg (x + 1 / 2)])).ne'
  have hg1 : g 1 = 2 / √3 := by simp only [g]; norm_num
  have hf : Tendsto (fun n : ℕ => (n : ℝ) * (Bres n - 1)) atTop (𝓝 (π / 2 * (2 / √3))) := by
    have h := n_sin_tendsto.mul ((hg.tendsto 1).comp Bres_tendsto_one)
    rw [hg1] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp only [Function.comp, g]
    rw [Bres_sub_one hn]; ring
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) * (Bres n ^ 2 - 1)) atTop (𝓝 (2 * π / √3)) := by
    have h := hf.mul (Bres_tendsto_one.add tendsto_const_nhds (b := (1 : ℝ)))
    have : π / 2 * (2 / √3) * (1 + 1) = 2 * π / √3 := by ring
    rw [this] at h
    refine h.congr' (Eventually.of_forall fun n => ?_)
    ring
  -- shift `n = k + 1`
  have hshift := hsq.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto (fun k : ℕ => Bres (k + 1) ^ 2 - 1) atTop (𝓝 0) := by
    have := ((Bres_tendsto_one.pow 2).sub_const 1).comp (tendsto_add_atTop_nat 1)
    simp only [one_pow, sub_self] at this
    exact this
  have := hshift.sub hsmall
  simp only [sub_zero] at this
  refine this.congr' (Eventually.of_forall fun k => ?_)
  simp only [Function.comp]; push_cast; ring

end DoyleFormal
