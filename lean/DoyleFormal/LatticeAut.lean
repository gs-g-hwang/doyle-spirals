/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Symmetry

/-!
# The indirect lattice automorphism (paper A, Theorem 4.1, `⇒`) — Phase 4i

Lattice points are `(p,q) ∈ ℤ²`, with the six directions `(1,0), (0,1), (−1,1), (−1,0),
(0,−1), (1,−1)`; in these coordinates a positively oriented lattice triangle has
determinant `+1`.

* `IsIndirectAut τ`: `τ` maps the three edges of every upward and downward lattice triangle
  to lattice edges and reverses the orientation of these triangles. Every indirect lattice
  automorphism in the sense of Theorem A 4.1 has these properties (bijectivity is not used).
* `indirect_aut_unique`: if moreover `τ(0,0) = (0,0)` and `τ(1,0) = (1,0)`, then
  `τ(p,q) = (p+q, −q)`. This is the uniqueness step of Theorem A 4.1 (`⇒`).
* `mirror_converse`: if the radius function `A^p B^q` is invariant under such a `τ`, then
  `A = B²`. (That conjugation invariance of the circles gives an indirect `τ` with
  `r ∘ τ = r` is the first step of the paper's proof; the general `(A,B)` configuration is
  not formalized.)
-/

namespace DoyleFormal

/-- The six lattice directions. -/
def IsDir (x : ℤ × ℤ) : Prop :=
  x = (1, 0) ∨ x = (0, 1) ∨ x = (-1, 1) ∨ x = (-1, 0) ∨ x = (0, -1) ∨ x = (1, -1)

/-- Determinant of two lattice vectors (orientation in lattice coordinates). -/
def ldet (x y : ℤ × ℤ) : ℤ := x.1 * y.2 - x.2 * y.1

/-- Rotation by `−60°` in lattice coordinates. -/
def rotm (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + x.2, -x.1)

lemma IsDir.neg {x : ℤ × ℤ} (h : IsDir x) : IsDir (-x) := by
  unfold IsDir at *
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- In a negatively oriented lattice triangle the third edge is the first one rotated by
`−60°`. (The condition `y − x ∈ dirs` excludes the angle `−120°`.) -/
lemma rotm_of_ldet {x y : ℤ × ℤ} (hx : IsDir x) (hy : IsDir y) (hxy : IsDir (y - x))
    (hd : ldet x y = -1) : y = rotm x := by
  unfold IsDir at hx hy hxy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [ldet, rotm]

/-- **Indirect lattice automorphism** (the properties used in Theorem A 4.1): edges in the
three directions `(1,0), (0,1), (−1,1)` go to lattice edges, and upward and downward lattice
triangles are mapped to negatively oriented triangles. -/
structure IsIndirectAut (τ : ℤ → ℤ → ℤ × ℤ) : Prop where
  t10 : ∀ p q, IsDir (τ (p + 1) q - τ p q)
  t01 : ∀ p q, IsDir (τ p (q + 1) - τ p q)
  tm11 : ∀ p q, IsDir (τ (p - 1) (q + 1) - τ p q)
  up : ∀ p q, ldet (τ (p + 1) q - τ p q) (τ p (q + 1) - τ p q) = -1
  down : ∀ p q, ldet (τ p (q + 1) - τ p q) (τ (p - 1) (q + 1) - τ p q) = -1

/-- The lattice reflection `τ(p,q) = (p+q, −q)` of Theorem A 4.1. -/
def mirrorAut (p q : ℤ) : ℤ × ℤ := (p + q, -q)

theorem mirrorAut_isIndirectAut : IsIndirectAut mirrorAut where
  t10 p q := by unfold IsDir mirrorAut; left; ext <;> simp
  t01 p q := by unfold IsDir mirrorAut; right; right; right; right; right; ext <;> simp
  tm11 p q := by unfold IsDir mirrorAut; right; right; right; right; left; ext <;> simp
  up p q := by simp [ldet, mirrorAut]
  down p q := by simp [ldet, mirrorAut]

/-- Two triangles with `c − a = rotm (b − a)`: any two corresponding vertices determine the
third. -/
lemma rotm_tri_agree {a b c a' b' c' : ℤ × ℤ} (h : c - a = rotm (b - a))
    (h' : c' - a' = rotm (b' - a')) :
    (a = a' → b = b' → c = c') ∧ (b = b' → c = c' → a = a') ∧
      (c = c' → a = a' → b = b') := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  obtain ⟨a1', a2'⟩ := a'; obtain ⟨b1', b2'⟩ := b'; obtain ⟨c1', c2'⟩ := c'
  simp only [rotm, Prod.mk_sub_mk, Prod.mk.injEq] at h h' ⊢
  refine ⟨?_, ?_, ?_⟩ <;> intro e1 e2 <;> obtain ⟨e1a, e1b⟩ := e1 <;>
    obtain ⟨e2a, e2b⟩ := e2 <;> constructor <;> omega

section Agree

variable {τ ρ : ℤ → ℤ → ℤ × ℤ}

lemma IsIndirectAut.up_rel (hτ : IsIndirectAut τ) (p q : ℤ) :
    τ p (q + 1) - τ p q = rotm (τ (p + 1) q - τ p q) := by
  refine rotm_of_ldet (hτ.t10 p q) (hτ.t01 p q) ?_ (hτ.up p q)
  have h := hτ.tm11 (p + 1) q
  rw [add_sub_cancel_right] at h
  simpa using h

lemma IsIndirectAut.down_rel (hτ : IsIndirectAut τ) (p q : ℤ) :
    τ (p - 1) (q + 1) - τ p q = rotm (τ p (q + 1) - τ p q) := by
  refine rotm_of_ldet (hτ.t01 p q) (hτ.tm11 p q) ?_ (hτ.down p q)
  have h := (hτ.t10 (p - 1) (q + 1)).neg
  rw [sub_add_cancel] at h
  simpa using h

lemma aut_up_agree (hτ : IsIndirectAut τ) (hρ : IsIndirectAut ρ) (p q : ℤ) :
    (τ p q = ρ p q → τ (p + 1) q = ρ (p + 1) q → τ p (q + 1) = ρ p (q + 1)) ∧
    (τ (p + 1) q = ρ (p + 1) q → τ p (q + 1) = ρ p (q + 1) → τ p q = ρ p q) ∧
    (τ p (q + 1) = ρ p (q + 1) → τ p q = ρ p q → τ (p + 1) q = ρ (p + 1) q) :=
  rotm_tri_agree (hτ.up_rel p q) (hρ.up_rel p q)

lemma aut_down_agree (hτ : IsIndirectAut τ) (hρ : IsIndirectAut ρ) (p q : ℤ) :
    (τ p q = ρ p q → τ p (q + 1) = ρ p (q + 1) → τ (p - 1) (q + 1) = ρ (p - 1) (q + 1)) ∧
    (τ p (q + 1) = ρ p (q + 1) → τ (p - 1) (q + 1) = ρ (p - 1) (q + 1) → τ p q = ρ p q) ∧
    (τ (p - 1) (q + 1) = ρ (p - 1) (q + 1) → τ p q = ρ p q → τ p (q + 1) = ρ p (q + 1)) :=
  rotm_tri_agree (hτ.down_rel p q) (hρ.down_rel p q)

/-- Two indirect lattice automorphisms that agree at `(0,0)` and `(1,0)` agree everywhere
(the same propagation as in `rigidity`). -/
theorem aut_rigidity (hτ : IsIndirectAut τ) (hρ : IsIndirectAut ρ) (h0 : τ 0 0 = ρ 0 0)
    (h1 : τ 1 0 = ρ 1 0) : ∀ p q, τ p q = ρ p q := by
  -- the axis row `q = 0`
  have row0 : ∀ p : ℤ, τ p 0 = ρ p 0 ∧ τ (p + 1) 0 = ρ (p + 1) 0 := by
    intro p
    induction p using Int.induction_on with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ n ih =>
      have c1 := (aut_up_agree hτ hρ n 0).1 ih.1 ih.2
      have c2 := (aut_down_agree hτ hρ (n + 1) 0).2.2 (by rw [add_sub_cancel_right]; exact c1)
        ih.2
      have c3 := (aut_up_agree hτ hρ (n + 1) 0).2.2 c2 ih.2
      exact ⟨ih.2, c3⟩
    | pred n ih =>
      have hA := ih.1
      have hB := ih.2
      have d1 := (aut_down_agree hτ hρ (-(n : ℤ) + 1) (-1)).2.1 (by simpa using hB)
        (by simpa using hA)
      have u1 := (aut_up_agree hτ hρ (-(n : ℤ)) (-1)).2.1 d1 (by simpa using hA)
      have d2 := (aut_down_agree hτ hρ (-(n : ℤ)) (-1)).1 u1 (by simpa using hA)
      refine ⟨by simpa using d2, by simpa using hA⟩
  -- all rows, upward and downward
  intro p q
  induction q using Int.induction_on generalizing p with
  | zero => exact (row0 p).1
  | succ n ih => exact (aut_up_agree hτ hρ p n).1 (ih p) (ih (p + 1))
  | pred n ih =>
    exact (aut_down_agree hτ hρ p (-(n : ℤ) - 1)).2.1 (by simpa using ih p)
      (by simpa using ih (p - 1))

end Agree

/-- **Theorem A 4.1 (`⇒`), uniqueness of `τ`.** An indirect lattice automorphism fixing
`(0,0)` and `(1,0)` is `τ(p,q) = (p+q, −q)`. -/
theorem indirect_aut_unique {τ : ℤ → ℤ → ℤ × ℤ} (hτ : IsIndirectAut τ) (h0 : τ 0 0 = (0, 0))
    (h1 : τ 1 0 = (1, 0)) (p q : ℤ) : τ p q = (p + q, -q) :=
  aut_rigidity hτ mirrorAut_isIndirectAut (by simp [h0, mirrorAut])
    (by simp [h1, mirrorAut]) p q

/-- **Theorem A 4.1 (`⇒`), radius part.** If the radius function `A^p B^q` (`A, B > 0`) is
invariant under an indirect lattice automorphism fixing `(0,0)` and `(1,0)`, then
`A = B²`. -/
theorem mirror_converse {A B : ℝ} (hB : 0 < B) {τ : ℤ → ℤ → ℤ × ℤ} (hτ : IsIndirectAut τ)
    (h0 : τ 0 0 = (0, 0)) (h1 : τ 1 0 = (1, 0))
    (hr : ∀ p q, A ^ (τ p q).1 * B ^ (τ p q).2 = A ^ p * B ^ q) : A = B ^ 2 := by
  have h := hr 0 1
  rw [indirect_aut_unique hτ h0 h1] at h
  simp only [zero_add, zpow_one, zpow_zero, one_mul, zpow_neg] at h
  exact (mirror_radius hB).1 (by rw [div_eq_mul_inv]; exact h)

end DoyleFormal
