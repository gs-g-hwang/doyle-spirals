/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.OneShapeConfig

/-!
# Non-vacuity checks — Phase 4q

* `oneshape_case3_nonvacuous`: `ℓ(p,q) = 2p + q` satisfies the hypotheses of
  `oneshape_case3` (every pair is admissible and the angles at every vertex sum to `2π`).
* `rad_locUniv`: the radius function `B^{2p+q}` of `D_B` has closing flowers (`LocUniv`), by
  Corollary A 3.2 (`flower_angle_sum`). So the hypotheses of `oneshape_config` are met by
  `D_B` itself.
-/

namespace DoyleFormal

open Real

lemma ldir_exp (u : ℤ × ℤ) (i : Fin 6) :
    2 * (u + ldir i).1 + (u + ldir i).2 - (2 * u.1 + u.2) = Ppat i := by
  fin_cases i <;> simp [ldir, Ppat] <;> ring

/-- `ℓ = 2p + q` satisfies the hypotheses of `oneshape_case3`. -/
theorem oneshape_case3_nonvacuous {B : ℝ} (hB : 1 < B) :
    let ℓ : ℤ × ℤ → ℤ := fun u => 2 * u.1 + u.2
    (∀ u i, PairOK (ℓ (u + ldir i) - ℓ u) (ℓ (u + ldir (i + 1)) - ℓ u)) ∧
      ∀ u, ∑ i, angOf (angleAt 1 B (B ^ 2)) (angleAt B (B ^ 2) 1) (angleAt (B ^ 2) 1 B)
        (ℓ (u + ldir i) - ℓ u) (ℓ (u + ldir (i + 1)) - ℓ u) = 2 * π := by
  intro ℓ
  have hd : ∀ u i, ℓ (u + ldir i) - ℓ u = Ppat i := fun u i => ldir_exp u i
  refine ⟨fun u i => ?_, fun u => ?_⟩
  · rw [hd, hd]
    fin_cases i <;> simp [Ppat, PairOK]
  · simp only [hd]
    rw [Fin.sum_univ_six]
    obtain ⟨-, -, hsum, -⟩ := cell_angles hB
    norm_num [Ppat, angOf]
    linarith

/-- The radius function of `D_B` has closing flowers. -/
theorem rad_locUniv {B : ℝ} (hB : 0 < B) : LocUniv (rad B) := by
  intro u
  have hA : 0 < B ^ 2 := by positivity
  have hfl := flower_angle_sum hA hB
  rw [← hfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : ∀ j : Fin 6, rad B (u + ldir j).1 (u + ldir j).2 =
      rad B u.1 u.2 * rho (B ^ 2) B j := by
    intro j
    have hB0 : B ≠ 0 := hB.ne'
    unfold rad
    rw [show 2 * (u + ldir j).1 + (u + ldir j).2 = (2 * u.1 + u.2) + Ppat j by
      have := ldir_exp u j; linarith, zpow_add₀ hB0]
    congr 1
    fin_cases j <;> simp [Ppat, rho] <;> field_simp
  rw [hr, hr]
  have hu : 0 < rad B u.1 u.2 := by unfold rad; positivity
  have hrho : ∀ j : Fin 6, 0 < rho (B ^ 2) B j := by
    intro j
    fin_cases j <;>
      simp only [rho, Fin.reduceFinMk, one_div, Matrix.cons_val, inv_pos] <;>
      positivity
  unfold theta
  have h := angleAt_smul hu one_pos (hrho i) (hrho (i + 1))
  rw [mul_one] at h
  exact h

end DoyleFormal
