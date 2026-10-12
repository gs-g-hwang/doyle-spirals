/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.MirrorAll

/-!
# Theorem A 8.1, Case 3: the radius exponent is affine — Phase 4m

In Case 3 of Theorem A 8.1 every center triangle is similar to the triangle with radii
`1, B, B²` (`B > 1`), and the radii are `r(u) = c B^{ℓ(u)}` with `ℓ : ℤ² → ℤ`. Then the three
values of `ℓ` on every center triangle are `k, k+1, k+2`. With `n_i = ℓ(v + d_i) − ℓ(v)` for
the six directions `d_0, …, d_5` in cyclic order, each consecutive pair `(n_i, n_{i+1})` is
`{1,2}`, `{−1,1}` or `{−2,−1}` (`PairOK`), according as `v` is the smallest, middle or
largest vertex of that triangle, where its angle is `θ_O`, `θ_{P₁}` or `θ_{P₀}` (`angOf`).

* `cell_angles`: for `B > 1`, `θ_{P₀} < θ_{P₁} < θ_O`, `θ_O + θ_{P₁} + θ_{P₀} = π` and
  `θ_{P₁} ≠ π/3`.
* `vertex_pattern`: if the angles at `v` sum to `2π`, then `(n_0, …, n_5)` is a rotation of
  `(2, 1, −1, −2, −1, 1)` (the axis pattern).
* `pattern_consistent`, `axis_const`: the axis is the same at adjacent vertices.
* `exponent_affine`: hence `ℓ(p,q) = ℓ(0,0) + p·a + q·b` with `(a,b)` one of the six
  rotations of `(2,1)`; after the lattice rotation taking the axis to `(1,0)`,
  `ℓ(p,q) = ℓ(0,0) + 2p + q`.
* `oneshape_case3`: the combination for the triangle `1, B, B²`.

Not formalized here: the angle sum `2π` around each vertex of a configuration, Lemma A 3.3's
reduction to roles, and Cases 1 and 2 of Theorem A 8.1 (these are hypotheses of
`oneshape_case3`).
-/

namespace DoyleFormal

open Real

/-! ### The angles of the triangle `1, B, B²` -/

/-- For `B > 1` the angles of the triangle with radii `1, B, B²` at the vertices of radius
`B²`, `B`, `1` are strictly increasing, sum to `π`, and the middle one is not `π/3`. -/
theorem cell_angles {B : ℝ} (hB : 1 < B) :
    angleAt (B ^ 2) 1 B < angleAt B (B ^ 2) 1 ∧ angleAt B (B ^ 2) 1 < angleAt 1 B (B ^ 2) ∧
      angleAt 1 B (B ^ 2) + angleAt B (B ^ 2) 1 + angleAt (B ^ 2) 1 B = π ∧
      angleAt B (B ^ 2) 1 ≠ π / 3 := by
  have hB0 : 0 < B := by linarith
  have hB2 : 0 < B ^ 2 := by positivity
  set ν := nu 1 B (B ^ 2) with hν
  have hν0 : 0 < ν := nu_pos one_pos hB0 hB2
  have e1 : nu B (B ^ 2) 1 = ν := (nu_perm B (B ^ 2) 1).symm
  have e2 : nu (B ^ 2) 1 B = ν := nu_perm 1 B (B ^ 2)
  have hsq : ν ^ 2 * (1 * B * B ^ 2) = 1 + B + B ^ 2 := nu_sq one_pos hB0 hB2
  unfold angleAt
  rw [e1, e2]
  have hlt1 : B < B ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : 1 / (ν * B ^ 2) < 1 / (ν * B) :=
      one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    linarith [arctan_strictMono this]
  · have : 1 / (ν * B) < 1 / (ν * 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    linarith [arctan_strictMono this]
  · have h := angle_sum one_pos hB0 hB2
    unfold angleAt at h
    rwa [e1, e2] at h
  · intro h
    have ha : arctan (1 / (ν * B)) = π / 6 := by linarith
    have ht : 1 / (ν * B) = 1 / √3 := by
      rw [← Real.tan_pi_div_six, ← ha, Real.tan_arctan]
    have h3 : ν * B = √3 := by
      have := ht
      field_simp at this
      linarith
    have h9 : (ν * B) ^ 2 = 3 := by rw [h3, Real.sq_sqrt (by norm_num)]
    have : (B - 1) ^ 2 = 0 := by nlinarith
    have : B = 1 := by nlinarith
    linarith

/-! ### The pattern at one vertex -/

/-- The three values on a center triangle through `v` are `k, k+1, k+2`: the differences
`(x, y)` to the other two vertices are `{1,2}`, `{−1,1}` or `{−2,−1}`. -/
def PairOK (x y : ℤ) : Prop :=
  (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = -1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) ∨
    (x = -2 ∧ y = -1) ∨ (x = -1 ∧ y = -2)

/-- The angle at `v`: `θ_O` if `v` is the smallest vertex (`x + y = 3`), `θ_{P₁}` if it is
the middle one (`x + y = 0`), `θ_{P₀}` otherwise. -/
noncomputable def angOf (θO θM θL : ℝ) (x y : ℤ) : ℝ :=
  if x + y = 3 then θO else if x + y = 0 then θM else θL

/-- The axis pattern `(2, 1, −1, −2, −1, 1)`. -/
def Ppat : Fin 6 → ℤ := ![2, 1, -1, -2, -1, 1]

/-- **The pattern at a vertex.** If every consecutive pair is admissible and the angles at
the vertex sum to `2π`, the six differences are a rotation of `(2, 1, −1, −2, −1, 1)`. -/
theorem vertex_pattern {θO θM θL : ℝ} (hsum : θO + θM + θL = π) (hLM : θL < θM)
    (hMO : θM < θO) (hM : θM ≠ π / 3) (n : Fin 6 → ℤ) (hp : ∀ i, PairOK (n i) (n (i + 1)))
    (hang : ∑ i, angOf θO θM θL (n i) (n (i + 1)) = 2 * π) :
    ∃ k : Fin 6, ∀ i, n i = Ppat (i - k) := by
  rw [Fin.sum_univ_six] at hang
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2
  have h3 := hp 3; have h4 := hp 4; have h5 := hp 5
  simp only [show (0 : Fin 6) + 1 = 1 by decide, show (1 : Fin 6) + 1 = 2 by decide,
    show (2 : Fin 6) + 1 = 3 by decide, show (3 : Fin 6) + 1 = 4 by decide,
    show (4 : Fin 6) + 1 = 5 by decide, show (5 : Fin 6) + 1 = 0 by decide]
    at h0 h1 h2 h3 h4 h5 hang
  suffices H : ∃ k : Fin 6, n 0 = Ppat (0 - k) ∧ n 1 = Ppat (1 - k) ∧ n 2 = Ppat (2 - k) ∧
      n 3 = Ppat (3 - k) ∧ n 4 = Ppat (4 - k) ∧ n 5 = Ppat (5 - k) by
    obtain ⟨k, e0, e1, e2, e3, e4, e5⟩ := H
    exact ⟨k, fun i => by fin_cases i <;> assumption⟩
  generalize n 0 = a0 at *
  generalize n 1 = a1 at *
  generalize n 2 = a2 at *
  generalize n 3 = a3 at *
  generalize n 4 = a4 at *
  generalize n 5 = a5 at *
  have hM' : θM < π / 3 ∨ π / 3 < θM := lt_or_gt_of_ne hM
  unfold PairOK at h0 h1 h2 h3 h4 h5
  rcases h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h1 with ⟨h1a, rfl⟩ | ⟨h1a, rfl⟩ | ⟨h1a, rfl⟩ | ⟨h1a, rfl⟩ | ⟨h1a, rfl⟩ |
      ⟨h1a, rfl⟩ <;> norm_num at h1a <;>
    rcases h2 with ⟨h2a, rfl⟩ | ⟨h2a, rfl⟩ | ⟨h2a, rfl⟩ | ⟨h2a, rfl⟩ | ⟨h2a, rfl⟩ |
      ⟨h2a, rfl⟩ <;> norm_num at h2a <;>
    rcases h3 with ⟨h3a, rfl⟩ | ⟨h3a, rfl⟩ | ⟨h3a, rfl⟩ | ⟨h3a, rfl⟩ | ⟨h3a, rfl⟩ |
      ⟨h3a, rfl⟩ <;> norm_num at h3a <;>
    rcases h4 with ⟨h4a, rfl⟩ | ⟨h4a, rfl⟩ | ⟨h4a, rfl⟩ | ⟨h4a, rfl⟩ | ⟨h4a, rfl⟩ |
      ⟨h4a, rfl⟩ <;> norm_num at h4a <;>
    norm_num at h5 <;>
    norm_num [angOf] at hang <;>
    first
      | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩ | exact ⟨4, by decide⟩ | exact ⟨5, by decide⟩
      | (exfalso; rcases hM' with hM' | hM' <;> linarith)

/-! ### The axis is the same at every vertex -/

/-- The six lattice directions in cyclic order. -/
def ldir : Fin 6 → ℤ × ℤ := ![(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

lemma ldir_add_two (j : Fin 6) : ldir j + ldir (j + 2) = ldir (j + 1) := by
  fin_cases j <;> decide

lemma ldir_sub_two (j : Fin 6) : ldir j + ldir (j - 2) = ldir (j - 1) := by
  fin_cases j <;> decide

lemma ldir_add_three (j : Fin 6) : ldir j + ldir (j + 3) = 0 := by
  fin_cases j <;> decide

/-- **Consistency of the pattern** along an edge `v → v + d_j` (a finite check). -/
lemma pattern_consistent (j k k' : Fin 6) (h0 : Ppat (j - k) + Ppat (j + 3 - k') = 0)
    (h1 : Ppat (j + 1 - k) = Ppat (j - k) + Ppat (j + 2 - k'))
    (h2 : Ppat (j - 1 - k) = Ppat (j - k) + Ppat (j - 2 - k')) : k = k' := by
  revert j k k'
  decide

section Axis

variable {ℓ : ℤ × ℤ → ℤ}

/-- The pattern at `u`: `ℓ(u + d_i) − ℓ(u) = Ppat(i − k)`. -/
def HasAxis (ℓ : ℤ × ℤ → ℤ) (u : ℤ × ℤ) (k : Fin 6) : Prop :=
  ∀ i, ℓ (u + ldir i) - ℓ u = Ppat (i - k)

lemma axis_const {u : ℤ × ℤ} {j k k' : Fin 6} (hu : HasAxis ℓ u k)
    (hv : HasAxis ℓ (u + ldir j) k') : k = k' := by
  refine pattern_consistent j k k' ?_ ?_ ?_
  · have a := hu j
    have b := hv (j + 3)
    rw [add_assoc, ldir_add_three, add_zero] at b
    linarith
  · have a := hu (j + 1)
    have b := hv (j + 2)
    have c := hu j
    rw [add_assoc, ldir_add_two] at b
    linarith
  · have a := hu (j - 1)
    have b := hv (j - 2)
    have c := hu j
    rw [add_assoc, ldir_sub_two] at b
    linarith

/-- **The radius exponent is affine.** If every vertex has the axis pattern, then
`ℓ(p,q) = ℓ(0,0) + p·Ppat(−k) + q·Ppat(1−k)` for one `k`. -/
theorem exponent_affine (h : ∀ u, ∃ k, HasAxis ℓ u k) :
    ∃ k : Fin 6, ∀ p q : ℤ, ℓ (p, q) = ℓ (0, 0) + p * Ppat (0 - k) + q * Ppat (1 - k) := by
  choose κ hκ using h
  have step : ∀ u (j : Fin 6), κ (u + ldir j) = κ u := fun u j =>
    (axis_const (hκ u) (hκ (u + ldir j))).symm
  have e0 : ∀ p q : ℤ, (p, q) + ldir 0 = (p + 1, q) := fun p q => by simp [ldir]
  have e1 : ∀ p q : ℤ, (p, q) + ldir 1 = (p, q + 1) := fun p q => by simp [ldir]
  have e3 : ∀ p q : ℤ, (p, q) + ldir 3 = (p - 1, q) := fun p q => by
    simp [ldir, sub_eq_add_neg]
  have e4 : ∀ p q : ℤ, (p, q) + ldir 4 = (p, q - 1) := fun p q => by
    simp [ldir, sub_eq_add_neg]
  -- the axis index is constant
  have hrow : ∀ p : ℤ, κ (p, 0) = κ (0, 0) := by
    intro p
    induction p using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [← ih, ← step (n, 0) 0, e0]
    | pred n ih => rw [← ih, ← step (-(n : ℤ), 0) 3, e3]
  have hall : ∀ p q : ℤ, κ (p, q) = κ (0, 0) := by
    intro p q
    induction q using Int.induction_on with
    | zero => exact hrow p
    | succ n ih => rw [← ih, ← step (p, n) 1, e1]
    | pred n ih => rw [← ih, ← step (p, -(n : ℤ)) 4, e4]
  set k := κ (0, 0)
  have dp : ∀ p q : ℤ, ℓ (p + 1, q) - ℓ (p, q) = Ppat (0 - k) := fun p q => by
    rw [← e0, hκ (p, q) 0, hall]
  have dq : ∀ p q : ℤ, ℓ (p, q + 1) - ℓ (p, q) = Ppat (1 - k) := fun p q => by
    rw [← e1, hκ (p, q) 1, hall]
  refine ⟨k, fun p q => ?_⟩
  have hp : ∀ p : ℤ, ℓ (p, 0) = ℓ (0, 0) + p * Ppat (0 - k) := by
    intro p
    induction p using Int.induction_on with
    | zero => simp
    | succ n ih => have := dp n 0; linarith
    | pred n ih =>
      have := dp (-(n : ℤ) - 1) 0
      rw [sub_add_cancel] at this
      linarith
  induction q using Int.induction_on with
  | zero => simpa using hp p
  | succ n ih => have := dq p n; linarith
  | pred n ih =>
    have := dq p (-(n : ℤ) - 1)
    rw [sub_add_cancel] at this
    linarith

end Axis

/-- The six possible gradients `(Ppat(−k), Ppat(1−k))` are the rotations of `(2,1)`; `k = 0`
gives `ℓ(p,q) = ℓ(0,0) + 2p + q`. -/
lemma gradient_zero : (Ppat (0 - 0), Ppat (1 - 0)) = (2, 1) := by decide

/-- **Theorem A 8.1, Case 3 (combinatorial core).** Let `B > 1` and `ℓ : ℤ² → ℤ`. Suppose
that on every center triangle through every vertex the values of `ℓ` are `k, k+1, k+2`
(`PairOK`), and that at every vertex the angles of the triangle `1, B, B²` sum to `2π`. Then
`ℓ` is affine: `ℓ(p,q) = ℓ(0,0) + p·a + q·b` with `(a,b)` a rotation of `(2,1)`. -/
theorem oneshape_case3 {B : ℝ} (hB : 1 < B) (ℓ : ℤ × ℤ → ℤ)
    (hp : ∀ u i, PairOK (ℓ (u + ldir i) - ℓ u) (ℓ (u + ldir (i + 1)) - ℓ u))
    (hang : ∀ u, ∑ i, angOf (angleAt 1 B (B ^ 2)) (angleAt B (B ^ 2) 1) (angleAt (B ^ 2) 1 B)
      (ℓ (u + ldir i) - ℓ u) (ℓ (u + ldir (i + 1)) - ℓ u) = 2 * π) :
    ∃ k : Fin 6, ∀ p q : ℤ, ℓ (p, q) = ℓ (0, 0) + p * Ppat (0 - k) + q * Ppat (1 - k) := by
  obtain ⟨hLM, hMO, hsum, hM⟩ := cell_angles hB
  refine exponent_affine fun u => ?_
  exact vertex_pattern hsum hLM hMO hM (fun i => ℓ (u + ldir i) - ℓ u) (hp u) (hang u)

end DoyleFormal
