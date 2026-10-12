/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Flower

/-!
# The flower in the plane (paper A, Section 2.1 and Corollary 3.2) — Phase 4

The petal centers are placed in polar form, `Pₙ = (1 + ρₙ) e^{i φₙ}`, where `φₙ = θ₀ + ⋯ + θₙ₋₁`.
For all `A, B > 0`:

* `petal_norm`     : `|Pₙ| = 1 + ρₙ`, so every petal touches the unit circle `K₀`;
* `petal_tangent`  : `|Pₙ − Pₙ₊₁| = ρₙ + ρₙ₊₁`, so consecutive petals touch;
* `petal_closes`   : `P₆ = P₀`, so the six circles close up exactly around `K₀`
  (Corollary A 3.2).

The key identity is `cos_angleAt`: `cos(angleAt x y z)` is the law-of-cosines value
(A, eq. (2.4)).
-/

namespace DoyleFormal

open Real Complex

/-- `cos(angleAt x y z)` is the law-of-cosines value for sides `x+y`, `x+z`, `y+z`. -/
theorem cos_angleAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.cos (angleAt x y z)
      = ((x + y) ^ 2 + (x + z) ^ 2 - (y + z) ^ 2) / (2 * (x + y) * (x + z)) := by
  set t := 1 / (nu x y z * x) with ht
  have hc : 0 < Real.cos (arctan t) := cos_arctan_pos t
  have h := cos_eq_of_tan_half (x := angleAt x y z) (by
    unfold angleAt; rw [show 2 * arctan t / 2 = arctan t by ring]; exact hc.ne')
  unfold angleAt at h ⊢
  rw [show 2 * arctan t / 2 = arctan t by ring, Real.tan_arctan] at h
  rw [h]
  have ht2 : t ^ 2 = y * z / (x * (x + y + z)) := by
    rw [ht]; unfold nu
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [ht2]
  field_simp
  ring

/-- `|a e^{iα} − b e^{iβ}|² = a² + b² − 2ab cos(β − α)`. -/
lemma norm_sub_polar_sq (a b α β : ℝ) :
    ‖(a : ℂ) * exp (α * I) - (b : ℂ) * exp (β * I)‖ ^ 2
      = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (β - α) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
  rw [Real.cos_sub]
  linear_combination a ^ 2 * Real.sin_sq_add_cos_sq α + b ^ 2 * Real.sin_sq_add_cos_sq β

/-- `n mod 6` as an element of `Fin 6`. -/
def fin6 (n : ℕ) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩

lemma fin6_succ (n : ℕ) : fin6 n + 1 = fin6 (n + 1) := by
  ext
  simp only [fin6, Fin.val_add, Fin.val_one]
  omega

/-- Petal radii indexed by `ℕ` (mod 6). -/
noncomputable def rhoN (A B : ℝ) (n : ℕ) : ℝ := rho A B (fin6 n)

/-- Polar angle of the `n`-th petal center: `φₙ = θ₀ + ⋯ + θₙ₋₁`. -/
noncomputable def phiN (A B : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, theta A B (fin6 k)

/-- Petal centers `Pₙ = (1 + ρₙ) e^{i φₙ}`. -/
noncomputable def petal (A B : ℝ) (n : ℕ) : ℂ := ((1 + rhoN A B n : ℝ) : ℂ) * exp (phiN A B n * I)

lemma rho_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (i : Fin 6) : 0 < rho A B i := by
  fin_cases i
  exacts [hA, hB, div_pos hB hA, one_div_pos.2 hA, one_div_pos.2 hB, div_pos hA hB]

lemma rhoN_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) : 0 < rhoN A B n :=
  rho_pos hA hB _

/-- Every petal touches the unit circle: `|Pₙ| = 1 + ρₙ`. -/
theorem petal_norm {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    ‖petal A B n‖ = 1 + rhoN A B n := by
  have := rhoN_pos hA hB n
  unfold petal
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

/-- Consecutive petals touch: `|Pₙ − Pₙ₊₁| = ρₙ + ρₙ₊₁`. -/
theorem petal_tangent {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    ‖petal A B n - petal A B (n + 1)‖ = rhoN A B n + rhoN A B (n + 1) := by
  have hy := rhoN_pos hA hB n
  have hz := rhoN_pos hA hB (n + 1)
  have hphi : phiN A B (n + 1) - phiN A B n = theta A B (fin6 n) := by
    unfold phiN; rw [Finset.sum_range_succ]; ring
  have hth : theta A B (fin6 n) = angleAt 1 (rhoN A B n) (rhoN A B (n + 1)) := by
    unfold theta rhoN; rw [fin6_succ]
  have hsq : ‖petal A B n - petal A B (n + 1)‖ ^ 2 = (rhoN A B n + rhoN A B (n + 1)) ^ 2 := by
    unfold petal
    rw [norm_sub_polar_sq, hphi, hth, cos_angleAt one_pos hy hz]
    field_simp
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by linarith)).1 hsq

/-- **Corollary A 3.2, geometric form.** The sixth petal coincides with the first:
the six circles close up exactly around the unit circle. -/
theorem petal_closes {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : petal A B 6 = petal A B 0 := by
  have h6 : phiN A B 6 = 2 * π := by
    rw [← flower_angle_sum hA hB, Fin.sum_univ_six]
    unfold phiN
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rfl
  unfold petal
  rw [h6, show rhoN A B 6 = rhoN A B 0 from rfl]
  have h0 : phiN A B 0 = 0 := by simp [phiN]
  rw [h0]
  push_cast
  rw [show (2 * (π : ℂ)) * I = 2 * π * I by ring, Complex.exp_two_pi_mul_I, zero_mul,
    Complex.exp_zero]

end DoyleFormal
