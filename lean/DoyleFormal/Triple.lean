/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.TurningAngle
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Tangent triples (paper A, Lemma 3.3 and Remark 3.9)

Three mutually externally tangent circles with radii `x, y, z` have centers `U, V, W` with
`|UV| = x + y`, `|VW| = y + z`, `|WU| = z + x`. In any Euclidean space:

* `tangent_triple_tan_half` (Lemma A 3.3, eq. (3.2)): the angle `θ_U` at `U` satisfies
  `tan(θ_U/2) = 1/(ν x)` with `ν = √((x+y+z)/(xyz))`, i.e. `cot(θ_U/2) = ν x`.
* `cell_triangle_turning`: for the cell triangle `O, P₁, P₀` of `D_B` (radii `1, B, B²`),
  `cos(θ_O − θ_{P₀}) = cosPsi B`. This removes the half-angle hypotheses from
  `turning_angle` (Remark A 3.9). What remains assumed is only `ψ = θ_O − θ_{P₀}`.
-/

namespace DoyleFormal

open Real EuclideanGeometry

/-- `ν = √((x + y + z)/(xyz))`, the reciprocal of the inradius. -/
noncomputable def nu (x y z : ℝ) : ℝ := √((x + y + z) / (x * y * z))

lemma nu_pos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < nu x y z := by
  unfold nu; apply Real.sqrt_pos.2; positivity

/-- Half-angle from the law-of-cosines value of a tangent triple. -/
theorem tan_half_of_cos {θ x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π)
    (hc : cos θ = ((x + y) ^ 2 + (z + x) ^ 2 - (y + z) ^ 2) / (2 * (x + y) * (z + x))) :
    tan (θ / 2) = 1 / (nu x y z * x) := by
  have hD : 0 < (x + y) * (z + x) := by positivity
  have h1m : 1 - cos θ = 2 * y * z / ((x + y) * (z + x)) := by
    rw [hc]; field_simp; ring
  have h1p : 1 + cos θ = 2 * x * (x + y + z) / ((x + y) * (z + x)) := by
    rw [hc]; field_simp; ring
  have hcl : cos θ < 1 := by
    have : 0 < 1 - cos θ := by rw [h1m]; positivity
    linarith
  have hcg : -1 < cos θ := by
    have : 0 < 1 + cos θ := by rw [h1p]; positivity
    linarith
  have hθ0' : 0 < θ := by
    rcases hθ0.lt_or_eq with h | h
    · exact h
    · rw [← h, cos_zero] at hcl; exact absurd hcl (lt_irrefl 1)
  have hθπ' : θ < π := by
    rcases hθπ.lt_or_eq with h | h
    · exact h
    · rw [h, cos_pi] at hcg; exact absurd hcg (lt_irrefl _)
  have hcos2 : 0 < cos (θ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin2 : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have ht : 0 < tan (θ / 2) := by rw [tan_eq_sin_div_cos]; positivity
  have hr : 0 < 1 / (nu x y z * x) := by have := nu_pos hx hy hz; positivity
  -- tan²(θ/2) = (1 − cos θ)/(1 + cos θ)
  have hhalf := cos_eq_of_tan_half (x := θ) hcos2.ne'
  have ht2 : tan (θ / 2) ^ 2 = y * z / (x * (x + y + z)) := by
    have h1 : tan (θ / 2) ^ 2 * (1 + cos θ) = 1 - cos θ := by
      have hpos : 0 < 1 + tan (θ / 2) ^ 2 := by positivity
      rw [hhalf]; field_simp; ring
    rw [h1p, h1m] at h1
    have : 0 < x * (x + y + z) := by positivity
    field_simp at h1 ⊢
    nlinarith [h1]
  have hr2 : (1 / (nu x y z * x)) ^ 2 = y * z / (x * (x + y + z)) := by
    unfold nu
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  exact (sq_eq_sq₀ ht.le hr.le).1 (by rw [ht2, hr2])

/-- **Lemma A 3.3, eq. (3.2).** For three mutually tangent circles with centers `U, V, W`
and radii `x, y, z`, the angle at `U` satisfies `tan(θ_U/2) = 1/(ν x)`. -/
theorem tangent_triple_tan_half {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (U V' W : P) (hUV : dist U V' = x + y) (hVW : dist V' W = y + z) (hWU : dist W U = z + x) :
    tan (∠ V' U W / 2) = 1 / (nu x y z * x) := by
  apply tan_half_of_cos hx hy hz (angle_nonneg _ _ _) (angle_le_pi _ _ _)
  have hlaw := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle V' U W
  rw [dist_comm V' U, hUV, hVW, hWU] at hlaw
  have hD : 2 * (x + y) * (z + x) ≠ 0 := by positivity
  rw [eq_div_iff hD]
  linarith

lemma nu_quadratic {B : ℝ} (hB : 0 < B) :
    nu 1 B (B ^ 2) ^ 2 * B ^ 3 = 1 + B + B ^ 2 := by
  unfold nu
  rw [Real.sq_sqrt (by positivity)]
  field_simp

lemma nu_perm (x y z : ℝ) : nu z x y = nu x y z := by
  unfold nu; congr 1; ring

/-- An angle in `[0, π/2]` with positive tangent lies in `(0, π/2)`. -/
lemma mem_Ioo_of_tan_pos {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ π / 2) (ht : 0 < tan α) :
    α ∈ Set.Ioo 0 (π / 2) := by
  refine ⟨?_, ?_⟩
  · rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h, tan_zero] at ht; exact absurd ht (lt_irrefl 0)
  · rcases h1.lt_or_eq with h | h
    · exact h
    · rw [h, tan_pi_div_two] at ht; exact absurd ht (lt_irrefl 0)

/-- **Remark A 3.9 + Proposition A 7.1 (analytic part), without hypotheses on angles.**
For the cell triangle of `D_B` (centers `O, P₁, P₀`, radii `1, B, B²`), the difference of
the angles at `O` and at `P₀` has cosine `cosPsi B`. -/
theorem cell_triangle_turning {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {B : ℝ} (hB : 0 < B) (O P₁ P₀ : P)
    (hOP₁ : dist O P₁ = 1 + B) (hP₁P₀ : dist P₁ P₀ = B + B ^ 2)
    (hP₀O : dist P₀ O = B ^ 2 + 1) :
    cos (∠ P₁ O P₀ - ∠ O P₀ P₁) = cosPsi B := by
  have hB2 : 0 < B ^ 2 := by positivity
  set ν := nu 1 B (B ^ 2) with hν
  have hνpos : 0 < ν := nu_pos one_pos hB hB2
  -- angle at O: x = 1, y = B, z = B²
  have htO : tan (∠ P₁ O P₀ / 2) = 1 / ν := by
    have := tangent_triple_tan_half one_pos hB hB2 O P₁ P₀ hOP₁ hP₁P₀ hP₀O
    rw [this, mul_one]
  -- angle at P₀: x = B², y = 1, z = B
  have htP : tan (∠ O P₀ P₁ / 2) = 1 / (ν * B ^ 2) := by
    have := tangent_triple_tan_half hB2 one_pos hB P₀ O P₁
      (by rw [hP₀O]) (by rw [hOP₁]) (by rw [hP₁P₀])
    rw [this, nu_perm]
  have hαO := mem_Ioo_of_tan_pos (α := ∠ P₁ O P₀ / 2) (by linarith [angle_nonneg P₁ O P₀])
    (by linarith [angle_le_pi P₁ O P₀]) (by rw [htO]; positivity)
  have hαP := mem_Ioo_of_tan_pos (α := ∠ O P₀ P₁ / 2) (by linarith [angle_nonneg O P₀ P₁])
    (by linarith [angle_le_pi O P₀ P₁]) (by rw [htP]; positivity)
  have h := (turning_angle hB hνpos (nu_quadratic hB) hαO hαP htO htP).2
  rw [show 2 * (∠ P₁ O P₀ / 2) - 2 * (∠ O P₀ P₁ / 2) = ∠ P₁ O P₀ - ∠ O P₀ P₁ by ring] at h
  exact h

end DoyleFormal
