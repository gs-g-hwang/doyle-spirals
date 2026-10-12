/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Triple
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.BigOperators.Fin

/-!
# The flower and the classification (paper A, Section 3) — Phase 4

The angle of a tangent triple with radii `x, y, z` at the vertex of radius `x` is
`angleAt x y z = 2 arctan (1/(ν x))` (`angleAt_eq_angle`: this is the Euclidean angle).

* `angle_sum`         : `angleAt x y z + angleAt y z x + angleAt z x y = π`.
* `angleAt_smul`      : the angle depends only on the radii up to scaling (Lemma A 3.3).
* `sides_prop_iff`    : sides are proportional iff radii are (Lemma A 3.3, first part).
* `theta_two`, `theta_four`, `theta_three`, `theta_five`: Proposition A 3.1 in angle form.
* `flower_angle_sum`  : **Corollary A 3.2**, `θ₀ + ⋯ + θ₅ = 2π` for all `A, B > 0`.
* `classification`    : **Theorem A 3.4**, `Δ₁ ∼ Δ₀ ⇔ A = B² ∨ B = A² ∨ AB = 1`.
* `relabel_*`, `branches_meet`: the rest of Theorem A 3.4.
* `anglesum_axis`     : **Corollary A 3.8**, `θ₀ + θ₁ + θ₂ = π` when `A = B²`.
-/

namespace DoyleFormal

open Real EuclideanGeometry

/-! ### The angle function of a tangent triple -/

/-- Angle at the vertex of radius `x` of the triangle of centers of three mutually
tangent circles with radii `x, y, z`. -/
noncomputable def angleAt (x y z : ℝ) : ℝ := 2 * arctan (1 / (nu x y z * x))

lemma nu_swap (x y z : ℝ) : nu x z y = nu x y z := by
  unfold nu; congr 1; ring

lemma nu_sq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    nu x y z ^ 2 * (x * y * z) = x + y + z := by
  unfold nu
  rw [Real.sq_sqrt (by positivity)]
  field_simp

lemma angleAt_swap (x y z : ℝ) : angleAt x z y = angleAt x y z := by
  unfold angleAt; rw [nu_swap]

lemma arctan_sum_core {x y z ν : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hν : 0 < ν)
    (hν2 : ν ^ 2 * (x * y * z) = x + y + z) :
    arctan (1 / (ν * x)) + arctan (1 / (ν * y)) + arctan (1 / (ν * z)) = π / 2 := by
  have hxy : 1 < ν ^ 2 * (x * y) := by
    by_contra h
    push Not at h
    have : ν ^ 2 * (x * y) * z ≤ 1 * z := mul_le_mul_of_nonneg_right h hz.le
    nlinarith
  have hab : 1 / (ν * x) * (1 / (ν * y)) < 1 := by
    rw [div_mul_div_comm, one_mul, div_lt_one (by positivity)]
    nlinarith
  have hne : 1 - 1 / (ν * x) * (1 / (ν * y)) ≠ 0 := by linarith
  rw [arctan_add hab]
  have key : (1 / (ν * x) + 1 / (ν * y)) / (1 - 1 / (ν * x) * (1 / (ν * y)))
      = (1 / (ν * z))⁻¹ := by
    rw [div_eq_iff hne]
    field_simp
    linear_combination (-1 : ℝ) * hν2
  rw [key, arctan_inv_of_pos (by positivity)]
  ring

/-- Angle sum of a tangent triple: `π`. -/
theorem angle_sum {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    angleAt x y z + angleAt y z x + angleAt z x y = π := by
  unfold angleAt
  rw [show nu y z x = nu x y z from (nu_perm y z x).symm, nu_perm x y z]
  have := arctan_sum_core hx hy hz (nu_pos hx hy hz) (nu_sq hx hy hz)
  linarith

lemma nu_smul {μ x y z : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    nu (μ * x) (μ * y) (μ * z) * μ = nu x y z := by
  unfold nu
  rw [show (μ * x + μ * y + μ * z) / (μ * x * (μ * y) * (μ * z))
      = (x + y + z) / (x * y * z) / μ ^ 2 by field_simp,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hμ.le]
  field_simp

/-- **Lemma A 3.3 (angles depend only on the radii up to scaling).** -/
theorem angleAt_smul {μ x y z : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    angleAt (μ * x) (μ * y) (μ * z) = angleAt x y z := by
  unfold angleAt
  rw [show nu (μ * x) (μ * y) (μ * z) * (μ * x) = (nu (μ * x) (μ * y) (μ * z) * μ) * x by ring,
    nu_smul hμ hx hy hz]

/-- **Lemma A 3.3, first part.** For tangent triples, the side triples
`(y+z, z+x, x+y)` are proportional with factor `μ` iff the radius triples are. -/
theorem sides_prop_iff (μ x y z x' y' z' : ℝ) :
    (y' + z' = μ * (y + z) ∧ z' + x' = μ * (z + x) ∧ x' + y' = μ * (x + y)) ↔
      (x' = μ * x ∧ y' = μ * y ∧ z' = μ * z) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨by ring, by ring, by ring⟩

/-- `angleAt` is the Euclidean angle of the triangle of centers. -/
theorem angleAt_eq_angle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (U V' W : P) (hUV : dist U V' = x + y) (hVW : dist V' W = y + z) (hWU : dist W U = z + x) :
    ∠ V' U W = angleAt x y z := by
  have ht := tangent_triple_tan_half hx hy hz U V' W hUV hVW hWU
  have hmem := mem_Ioo_of_tan_pos (α := ∠ V' U W / 2) (by linarith [angle_nonneg V' U W])
    (by linarith [angle_le_pi V' U W]) (by rw [ht]; have := nu_pos hx hy hz; positivity)
  have := arctan_tan (x := ∠ V' U W / 2) (by linarith [hmem.1, pi_pos]) hmem.2
  rw [ht] at this
  unfold angleAt
  linarith

/-! ### The flower -/

/-- Ring-one radii `ρ₀, …, ρ₅ = A, B, B/A, 1/A, 1/B, A/B` (A, eq. (2.2)). -/
noncomputable def rho (A B : ℝ) : Fin 6 → ℝ := ![A, B, B / A, 1 / A, 1 / B, A / B]

/-- Angle at `O` of the cell triangle `Δᵢ = O Pᵢ Pᵢ₊₁` (A, eq. (2.4)). -/
noncomputable def theta (A B : ℝ) (i : Fin 6) : ℝ := angleAt 1 (rho A B i) (rho A B (i + 1))

lemma theta_zero (A B : ℝ) : theta A B 0 = angleAt 1 A B := rfl
lemma theta_one (A B : ℝ) : theta A B 1 = angleAt 1 B (B / A) := rfl
lemma theta_two' (A B : ℝ) : theta A B 2 = angleAt 1 (B / A) (1 / A) := rfl
lemma theta_three' (A B : ℝ) : theta A B 3 = angleAt 1 (1 / A) (1 / B) := rfl
lemma theta_four' (A B : ℝ) : theta A B 4 = angleAt 1 (1 / B) (A / B) := rfl
lemma theta_five' (A B : ℝ) : theta A B 5 = angleAt 1 (A / B) A := rfl

/-- Proposition A 3.1: angle of `Δ₂` at `O` = angle of `Δ₀` at `P₀` (ratio `1/A`). -/
theorem theta_two {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : theta A B 2 = angleAt A B 1 := by
  rw [theta_two', ← angleAt_smul (inv_pos.2 hA) hA hB one_pos]
  congr 1 <;> field_simp

/-- Proposition A 3.1: angle of `Δ₄` at `O` = angle of `Δ₀` at `P₁` (ratio `1/B`). -/
theorem theta_four {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : theta A B 4 = angleAt B 1 A := by
  rw [theta_four', ← angleAt_smul (inv_pos.2 hB) hB one_pos hA]
  congr 1 <;> field_simp

/-- Proposition A 3.1: angle of `Δ₃` at `O` = angle of `Δ₁` at `P₁` (ratio `1/B`). -/
theorem theta_three {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    theta A B 3 = angleAt B (B / A) 1 := by
  rw [theta_three', ← angleAt_smul (inv_pos.2 hB) hB (by positivity) one_pos]
  congr 1 <;> field_simp

/-- Proposition A 3.1: angle of `Δ₅` at `O` = angle of `Δ₁` at `P₂` (ratio `A/B`). -/
theorem theta_five {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    theta A B 5 = angleAt (B / A) 1 B := by
  rw [theta_five', ← angleAt_smul (div_pos hA hB) (by positivity) one_pos hB]
  congr 1 <;> field_simp

/-- **Corollary A 3.2 (closure of the flower).** For all `A, B > 0`, `∑ θᵢ = 2π`. -/
theorem flower_angle_sum {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∑ i, theta A B i = 2 * π := by
  rw [Fin.sum_univ_six, theta_zero, theta_one, theta_two hA hB, theta_three hA hB,
    theta_four hA hB, theta_five hA hB]
  have h0 := angle_sum one_pos hA hB
  have h1 := angle_sum one_pos hB (div_pos hB hA)
  linarith

/-! ### Classification of total similarity (Theorem A 3.4) -/

/-- The six orderings of a triple. -/
def perms3 {α : Type*} (a b c : α) : List (α × α × α) :=
  [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)]

/-- Two tangent triples are similar (some vertex bijection, some ratio `μ`). By
Lemma A 3.3 (`sides_prop_iff`), this is similarity of the triangles of centers. -/
def SimTriple (t s : ℝ × ℝ × ℝ) : Prop :=
  ∃ μ > 0, ∃ s' ∈ perms3 s.1 s.2.1 s.2.2, t = (μ * s'.1, μ * s'.2.1, μ * s'.2.2)

/-- **Theorem A 3.4.** With radii `(1, B, B/A)` at `(O, P₁, P₂)` of `Δ₁` and `(A, B, 1)`
at `(P₀, P₁, O)` of `Δ₀`: `Δ₁ ∼ Δ₀` iff `A = B² ∨ B = A² ∨ AB = 1`. (By Proposition
A 3.1, `Δ₁ ∼ Δ₀` is equivalent to all six cell triangles being similar.) -/
theorem classification {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    SimTriple (1, B, B / A) (A, B, 1) ↔ A = B ^ 2 ∨ B = A ^ 2 ∨ A * B = 1 := by
  have hA' : A ≠ 0 := hA.ne'
  have hB' : B ≠ 0 := hB.ne'
  constructor
  · rintro ⟨μ, hμ, s', hs', ht⟩
    simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prod.mk.injEq] at ht <;> obtain ⟨h1, h2, h3⟩ := ht
    · -- (A, B, 1): A = B = 1
      have hμ1 : μ = 1 := by
        have : B * (1 - μ) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hB'
        · linarith
      subst hμ1
      left
      have hA1 : A = 1 := by linarith
      subst hA1
      field_simp at h3
      rw [h3]; norm_num
    · -- (A, 1, B): AB = 1
      right; right
      rw [h2]; linear_combination -h1
    · -- (B, A, 1): A = B²
      left
      have hμ : μ = 1 / B := by field_simp; linarith
      rw [hμ] at h2
      field_simp at h2
      linarith
    · -- (B, 1, A): A = B = 1
      have hB1 : B = 1 := by
        have hμ' : μ = B := by linarith
        rw [hμ'] at h1
        nlinarith
      subst hB1
      have hμ1 : μ = 1 := by linarith
      subst hμ1
      field_simp at h3
      left; nlinarith
    · -- (1, A, B): A = B = 1
      have hμ1 : μ = 1 := by linarith
      subst hμ1
      have hAB : B = A := by linarith
      subst hAB
      field_simp at h3
      left; nlinarith
    · -- (1, B, A): B = A²
      have hμ1 : μ = 1 := by linarith
      subst hμ1
      right; left
      field_simp at h3
      nlinarith
  · rintro (h | h | h)
    · -- case (iii): μ = 1/B, image (B, A, 1)
      refine ⟨1 / B, by positivity, (B, A, 1), by simp [perms3], ?_⟩
      simp only [Prod.mk.injEq]
      refine ⟨by field_simp, by rw [h]; field_simp, by rw [h]; field_simp⟩
    · -- case (vi): μ = 1, image (1, B, A)
      refine ⟨1, one_pos, (1, B, A), by simp [perms3], ?_⟩
      simp only [Prod.mk.injEq]
      refine ⟨by ring, by ring, by rw [h]; field_simp⟩
    · -- case (ii): μ = 1/A, image (A, 1, B)
      refine ⟨1 / A, by positivity, (A, 1, B), by simp [perms3], ?_⟩
      simp only [Prod.mk.injEq]
      have hB1 : B = 1 / A := by field_simp; linarith
      refine ⟨by field_simp, by rw [hB1]; ring, by field_simp⟩

/-- The relabelings `R(A,B) = (B, B/A)` and `M(A,B) = (B, A)` carry the branch `A = B²`
to the branches `AB = 1` and `B = A²` (Theorem A 3.4). -/
theorem relabel_branches {B : ℝ} (hB : 0 < B) :
    (B * (B / B ^ 2) = 1) ∧ (B ^ 2 = B ^ 2) := by
  refine ⟨?_, rfl⟩
  field_simp

/-- The three branches meet only at `A = B = 1` (Theorem A 3.4). -/
theorem branches_meet {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ((A = B ^ 2 ∧ A * B = 1) ∨ (A = B ^ 2 ∧ B = A ^ 2) ∨ (B = A ^ 2 ∧ A * B = 1)) →
      A = 1 ∧ B = 1 := by
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · subst h1
    have hB1 : B ^ 3 = 1 := by linarith [h2]
    have : B = 1 := by
      have := pow_eq_one_iff_of_nonneg hB.le (by norm_num : (3 : ℕ) ≠ 0) |>.1 hB1
      exact this
    subst this; norm_num
  · subst h1
    have hB3 : B * (B ^ 3 - 1) = 0 := by nlinarith [h2]
    rcases mul_eq_zero.mp hB3 with h | h
    · exact absurd h hB.ne'
    · have hB1 : B ^ 3 = 1 := by linarith
      have : B = 1 :=
        pow_eq_one_iff_of_nonneg hB.le (by norm_num : (3 : ℕ) ≠ 0) |>.1 hB1
      subst this; norm_num
  · subst h1
    have hA1 : A ^ 3 = 1 := by linarith [h2]
    have : A = 1 := pow_eq_one_iff_of_nonneg hA.le (by norm_num : (3 : ℕ) ≠ 0) |>.1 hA1
    subst this; norm_num

/-- **Corollary A 3.6 (second-neighbor form).** The branches are exactly where one of the
second-neighbor multipliers `AB`, `B²/A`, `A²/B` equals `1`. -/
theorem second_neighbor {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A = B ^ 2 ∨ B = A ^ 2 ∨ A * B = 1) ↔ (A * B = 1 ∨ B ^ 2 / A = 1 ∨ A ^ 2 / B = 1) := by
  rw [div_eq_one_iff_eq hA.ne', div_eq_one_iff_eq hB.ne']
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
    · exact Or.inl h
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)

/-- **Corollary A 3.8 (angle sum on the axis).** For `A = B²`, `θ₀ + θ₁ + θ₂ = π`
and `θ₃ + θ₄ + θ₅ = π`. -/
theorem anglesum_axis {B : ℝ} (hB : 0 < B) :
    theta (B ^ 2) B 0 + theta (B ^ 2) B 1 + theta (B ^ 2) B 2 = π ∧
      theta (B ^ 2) B 3 + theta (B ^ 2) B 4 + theta (B ^ 2) B 5 = π := by
  have hA : 0 < B ^ 2 := by positivity
  -- θ₁ = angle of Δ₀ at P₁ (correspondence (P₀,P₁,O) ↦ (P₁,O,P₂), ratio 1/B)
  have h1 : theta (B ^ 2) B 1 = angleAt B 1 (B ^ 2) := by
    rw [theta_one, ← angleAt_smul (inv_pos.2 hB) hB one_pos hA, angleAt_swap]
    congr 1 <;> field_simp
  have h0 := angle_sum one_pos hA hB
  have hs := flower_angle_sum hA hB
  rw [Fin.sum_univ_six] at hs
  have h01 : theta (B ^ 2) B 0 + theta (B ^ 2) B 1 + theta (B ^ 2) B 2 = π := by
    rw [theta_zero, h1, theta_two hA hB]
    have := angle_sum one_pos hA hB
    linarith
  exact ⟨h01, by linarith⟩

end DoyleFormal
