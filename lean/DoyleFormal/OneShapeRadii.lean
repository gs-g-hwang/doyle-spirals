/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.FlowerWinding

/-!
# Theorem A 8.1 for the radius function — Phase 4o

Let `r > 0` be a radius function on `ℤ²` whose flowers close up (`LocUniv`) and whose center
triangles are all similar to one triangle with radii `(a, b, c)` (`SimTriple`, Lemma A 3.3).
Following the proof of Theorem A 8.1 with the shape sorted, `a ≤ b ≤ c`:

* `case_generic` (Case 1, `a < b < c`, `b² ≠ ac`): the role of a vertex is the same in all six
  triangles around it, which forces an angle `π/3` at two different roles — impossible.
* `case_isosceles` (Case 2, two equal radii, the third different): being the apex is the same
  in all six triangles around a vertex — impossible.
* `case_gp` (Case 3, `b² = ac`, `a < b`): `r = r(0,0) B^{ℓ}` with `ℓ` affine (`OneShape`).
* `oneshape_radii` (**Theorem A 8.1, radius part**): either the radii agree at adjacent
  points (all triangles equilateral), or `r(p,q) = r(0,0) B^{p a + q b}` with `B > 1` and
  `(a, b)` one of the six rotations of `(2, 1)`.
-/

namespace DoyleFormal

open Real

/-! ### Shapes and roles -/

lemma perms3_mem {a b c x y w : ℝ} :
    (x, y, w) ∈ perms3 a b c ↔ (x = a ∧ y = b ∧ w = c) ∨ (x = a ∧ y = c ∧ w = b) ∨
      (x = b ∧ y = a ∧ w = c) ∨ (x = b ∧ y = c ∧ w = a) ∨ (x = c ∧ y = a ∧ w = b) ∨
        (x = c ∧ y = b ∧ w = a) := by
  simp [perms3]

lemma simTriple_iff {p q s a b c : ℝ} :
    SimTriple (p, q, s) (a, b, c) ↔
      ∃ μ > 0, ∃ x y w, (x, y, w) ∈ perms3 a b c ∧ p = μ * x ∧ q = μ * y ∧ s = μ * w := by
  constructor
  · rintro ⟨μ, hμ, ⟨x, y, w⟩, hs, h⟩
    simp only [Prod.mk.injEq] at h
    exact ⟨μ, hμ, x, y, w, hs, h.1, h.2.1, h.2.2⟩
  · rintro ⟨μ, hμ, x, y, w, hs, h1, h2, h3⟩
    exact ⟨μ, hμ, (x, y, w), hs, by rw [h1, h2, h3]⟩

lemma simTriple_swap12 {t : ℝ × ℝ × ℝ} {a b c : ℝ} (h : SimTriple t (a, b, c)) :
    SimTriple t (b, a, c) := by
  obtain ⟨μ, hμ, s', hs, ht⟩ := h
  refine ⟨μ, hμ, s', ?_, ht⟩
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  tauto

lemma simTriple_swap23 {t : ℝ × ℝ × ℝ} {a b c : ℝ} (h : SimTriple t (a, b, c)) :
    SimTriple t (a, c, b) := by
  obtain ⟨μ, hμ, s', hs, ht⟩ := h
  refine ⟨μ, hμ, s', ?_, ht⟩
  simp only [perms3, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  tauto

/-- The angle of the shape `(a, b, c)` at the vertex of radius `x`. -/
noncomputable def th (a b c x : ℝ) : ℝ := 2 * arctan (1 / (nu a b c * x))

lemma angle_role {a b c μ x y w : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hμ : 0 < μ)
    (hm : (x, y, w) ∈ perms3 a b c) : angleAt (μ * x) (μ * y) (μ * w) = th a b c x := by
  rw [perms3_mem] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rw [angleAt_smul hμ (by assumption) (by assumption) (by assumption)] <;>
    unfold angleAt th nu <;> congr 4 <;> ring_nf

lemma th_sum {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    th a b c a + th a b c b + th a b c c = π := by
  have h := angle_sum ha hb hc
  have e1 := angle_role ha hb hc one_pos (x := a) (y := b) (w := c) (by simp [perms3])
  have e2 := angle_role ha hb hc one_pos (x := b) (y := c) (w := a) (by simp [perms3])
  have e3 := angle_role ha hb hc one_pos (x := c) (y := a) (w := b) (by simp [perms3])
  simp only [one_mul] at e1 e2 e3
  linarith

lemma th_lt {a b c x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x)
    (hxy : x < y) : th a b c y < th a b c x := by
  unfold th
  have hν := nu_pos ha hb hc
  have : 1 / (nu a b c * y) < 1 / (nu a b c * x) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  linarith [arctan_strictMono this]

lemma th_inj {a b c x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x)
    (hy : 0 < y) (h : th a b c x = th a b c y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · linarith [th_lt ha hb hc hx hxy]
  · exact hxy
  · linarith [th_lt ha hb hc hy hxy]

lemma cross_ratio {μ μ' x x' w y' p q : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ')
    (h1 : p = μ * x) (h2 : p = μ' * x') (h3 : q = μ * w) (h4 : q = μ' * y') :
    w * x' = y' * x := by
  have : μ * μ' * (w * x') = μ * μ' * (y' * x) := by
    have e : μ * w * (μ' * x') = μ' * y' * (μ * x) := by rw [← h3, ← h4, ← h1, ← h2]
    linarith [e]
  exact mul_left_cancel₀ (by positivity) this

lemma fin6_const {α : Type*} {f : Fin 6 → α} (h : ∀ i, f (i + 1) = f i) (i : Fin 6) :
    f i = f 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  simp only [show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl,
    show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl,
    show (4 : Fin 6) + 1 = 5 from rfl] at h0 h1 h2 h3 h4
  fin_cases i
  · rfl
  · exact h0
  · exact h1.trans h0
  · exact h2.trans (h1.trans h0)
  · exact h3.trans (h2.trans (h1.trans h0))
  · exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

/-! ### The data of a radius function with one triangle shape -/

/-- Radii on `ℤ × ℤ`. -/
def Rr (r : ℤ → ℤ → ℝ) (u : ℤ × ℤ) : ℝ := r u.1 u.2

/-- All center triangles similar to `(a, b, c)`, each listed from each of its vertices. -/
def OneShape (r : ℤ → ℤ → ℝ) (a b c : ℝ) : Prop :=
  ∀ u : ℤ × ℤ, ∀ i : Fin 6,
    SimTriple (Rr r u, Rr r (u + ldir i), Rr r (u + ldir (i + 1))) (a, b, c)

lemma LocUniv.sum {r : ℤ → ℤ → ℝ} (h : LocUniv r) (u : ℤ × ℤ) :
    ∑ i : Fin 6, angleAt (Rr r u) (Rr r (u + ldir i)) (Rr r (u + ldir (i + 1))) = 2 * π :=
  h u

section Roles

variable {r : ℤ → ℤ → ℝ} {a b c : ℝ}

/-- The angle sum at a vertex in terms of the roles. -/
lemma sum_roles (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hloc : LocUniv r) (u : ℤ × ℤ)
    (μ : Fin 6 → ℝ) (X Y W : Fin 6 → ℝ) (hμ : ∀ i, 0 < μ i)
    (hm : ∀ i, (X i, Y i, W i) ∈ perms3 a b c)
    (hX : ∀ i, Rr r u = μ i * X i) (hY : ∀ i, Rr r (u + ldir i) = μ i * Y i)
    (hW : ∀ i, Rr r (u + ldir (i + 1)) = μ i * W i) :
    ∑ i : Fin 6, th a b c (X i) = 2 * π := by
  rw [← hloc.sum u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hX i, hY i, hW i, angle_role ha hb hc (hμ i) (hm i)]

end Roles

/-! ### Case 1: no coincidences -/

lemma generic_ratio {a b c x y w x' y' w' : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hne : b ^ 2 ≠ a * c) (hm : (x, y, w) ∈ perms3 a b c) (hm' : (x', y', w') ∈ perms3 a b c)
    (h : w * x' = y' * x) : x = x' := by
  rw [perms3_mem] at hm hm'
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hm' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  first
    | rfl
    | (exfalso; nlinarith)
    | (exfalso; exact hne (by nlinarith))

lemma generic_ratio' {a b c x y w x' y' w' : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hne : b ^ 2 ≠ a * c) (hm : (x, y, w) ∈ perms3 a b c) (hm' : (x', y', w') ∈ perms3 a b c)
    (h : w * x' = y' * y) : y = x' := by
  rw [perms3_mem] at hm hm'
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hm' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  first
    | rfl
    | (exfalso; nlinarith)
    | (exfalso; exact hne (by nlinarith))

lemma perms3_pos {a b c x y w : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hm : (x, y, w) ∈ perms3 a b c) : 0 < x ∧ 0 < y ∧ 0 < w := by
  rw [perms3_mem] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact ⟨by assumption, by assumption, by assumption⟩

lemma perms3_ne {a b c x y w : ℝ} (hab : a < b) (hbc : b < c)
    (hm : (x, y, w) ∈ perms3 a b c) : x ≠ y := by
  rw [perms3_mem] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> intro h <;> linarith

/-- **Case 1 of Theorem A 8.1.** No radius function with closing flowers has all triangles
similar to a triangle `a < b < c` with `b² ≠ ac`. -/
theorem case_generic {r : ℤ → ℤ → ℝ} {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hne : b ^ 2 ≠ a * c) (hloc : LocUniv r) (hs : OneShape r a b c) : False := by
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  have hs' := fun u i => simTriple_iff.1 (hs u i)
  choose μ hμ X Y W hm hX hY hW using hs'
  -- the role of `u` is the same in consecutive triangles
  have hrole : ∀ u i, X u (i + 1) = X u i := by
    intro u i
    have e := cross_ratio (hμ u i) (hμ u (i + 1)) (hX u i) (hX u (i + 1)) (hW u i) (hY u (i + 1))
    exact (generic_ratio ha hab hbc hne (hm u i) (hm u (i + 1)) e).symm
  -- so `6 θ(X u 0) = 2π`
  have hsix : ∀ u, th a b c (X u 0) = π / 3 := by
    intro u
    have hsum := sum_roles ha hb hc hloc u (μ u) (X u) (Y u) (W u) (hμ u) (hm u) (hX u)
      (hY u) (hW u)
    rw [Finset.sum_congr rfl fun i _ => by rw [fin6_const (hrole u) i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    linarith
  -- the second vertex of triangle 0 at `0` has the same role around itself
  set u : ℤ × ℤ := 0
  set v := u + ldir 0
  have hv2 : v + ldir 2 = u + ldir 1 := by simp [v, u, ldir]
  have hW0 : Rr r (u + ldir 1) = μ u 0 * W u 0 := hW u 0
  have hY2 : Rr r (u + ldir 1) = μ v 2 * Y v 2 := by rw [← hv2]; exact hY v 2
  have e := cross_ratio (hμ u 0) (hμ v 2) (hY u 0) (hX v 2) hW0 hY2
  have hYX := generic_ratio' ha hab hbc hne (hm u 0) (hm v 2) e
  have h1 := hsix u
  have h2 := hsix v
  rw [← fin6_const (hrole v) 2, ← hYX] at h2
  have hp := perms3_pos ha hb hc (hm u 0)
  have := th_inj ha hb hc hp.1 hp.2.1 (h1.trans h2.symm)
  exact perms3_ne hab hbc (hm u 0) this

/-! ### Case 2: isosceles -/

lemma iso_ratio {s t x y w x' y' w' : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hm : (x, y, w) ∈ perms3 s s t) (hm' : (x', y', w') ∈ perms3 s s t)
    (h : w * x' = y' * x) : (x' = t ↔ x = t) := by
  rw [perms3_mem] at hm hm'
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hm' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  first
    | exact Iff.rfl
    | (exfalso; apply hst; nlinarith)

/-- **Case 2 of Theorem A 8.1.** No radius function with closing flowers has all triangles
similar to an isosceles, non-equilateral triangle `(s, s, t)`. -/
theorem case_isosceles {r : ℤ → ℤ → ℝ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t)
    (hloc : LocUniv r) (hsh : OneShape r s s t) : False := by
  have hs' := fun u i => simTriple_iff.1 (hsh u i)
  choose μ hμ X Y W hm hX hY hW using hs'
  -- being the apex is the same in consecutive triangles
  have hrole : ∀ u i, (X u (i + 1) = t) = (X u i = t) := by
    intro u i
    have e := cross_ratio (hμ u i) (hμ u (i + 1)) (hX u i) (hX u (i + 1)) (hW u i)
      (hY u (i + 1))
    exact propext (iso_ratio hs ht hst (hm u i) (hm u (i + 1)) e)
  have hconst := fun i => fin6_const (f := fun i => X 0 i = t) (hrole 0) i
  have hsum := sum_roles hs hs ht hloc 0 (μ 0) (X 0) (Y 0) (W 0) (hμ 0) (hm 0) (hX 0)
    (hY 0) (hW 0)
  have h3 := th_sum hs hs ht
  have hmem : ∀ i, X 0 i = s ∨ X 0 i = t := by
    intro i
    have := hm 0 i
    rw [perms3_mem] at this
    rcases this with h | h | h | h | h | h <;> simp only [h.1, true_or, or_true]
  by_cases h0 : X 0 0 = t
  · have hall : ∀ i, X 0 i = t := fun i => by
      have := hconst i; simp only [eq_iff_iff] at this; exact this.2 h0
    rw [Finset.sum_congr rfl fun i _ => by rw [hall i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    exact hst (th_inj hs hs ht hs ht (by linarith))
  · have hall : ∀ i, X 0 i = s := fun i => by
      have := hconst i; simp only [eq_iff_iff] at this
      exact (hmem i).resolve_right fun h => h0 (this.1 h)
    rw [Finset.sum_congr rfl fun i _ => by rw [hall i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    exact hst (th_inj hs hs ht hs ht (by linarith))

/-! ### Case 3: geometric progression -/

lemma gp_pair {a B x y w : ℝ} (ha : 0 < a) (hB : 1 < B)
    (hm : (x, y, w) ∈ perms3 a (a * B) (a * B ^ 2)) :
    ∃ e1 e2 : ℤ, PairOK e1 e2 ∧ y = x * B ^ e1 ∧ w = x * B ^ e2 ∧
      th a (a * B) (a * B ^ 2) x = angOf (th a (a * B) (a * B ^ 2) a)
        (th a (a * B) (a * B ^ 2) (a * B)) (th a (a * B) (a * B ^ 2) (a * B ^ 2)) e1 e2 := by
  have hB0 : B ≠ 0 := by positivity
  rw [perms3_mem] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨1, 2, by simp [PairOK], by simp, by simp, by simp [angOf]⟩
  · exact ⟨2, 1, by simp [PairOK], by simp, by simp, by simp [angOf]⟩
  · refine ⟨-1, 1, by simp [PairOK], ?_, ?_, by norm_num [angOf]⟩
    · rw [zpow_neg_one]; field_simp
    · simp; ring
  · refine ⟨1, -1, by simp [PairOK], ?_, ?_, by norm_num [angOf]⟩
    · simp; ring
    · rw [zpow_neg_one]; field_simp
  · refine ⟨-2, -1, by simp [PairOK], ?_, ?_, by norm_num [angOf]⟩
    · rw [zpow_neg, zpow_two]; field_simp
    · rw [zpow_neg_one]; field_simp
  · refine ⟨-1, -2, by simp [PairOK], ?_, ?_, by norm_num [angOf]⟩
    · rw [zpow_neg_one]; field_simp
    · rw [zpow_neg, zpow_two]; field_simp

/-- **Case 3 of Theorem A 8.1.** If all triangles are similar to `(a, aB, aB²)` with `B > 1`
and the flowers close up, then `r(p,q) = r(0,0) B^{p a + q b}` with `(a, b)` a rotation of
`(2,1)`. -/
theorem case_gp {r : ℤ → ℤ → ℝ} {a B : ℝ} (ha : 0 < a) (hB : 1 < B)
    (hloc : LocUniv r) (hsh : OneShape r a (a * B) (a * B ^ 2)) :
    ∃ k : Fin 6, ∀ p q : ℤ, r p q = r 0 0 * B ^ (p * Ppat (0 - k) + q * Ppat (1 - k)) := by
  have hB0 : 0 < B := by linarith
  have hB1 : B ≠ 1 := hB.ne'
  have haB : 0 < a * B := by positivity
  have haB2 : 0 < a * B ^ 2 := by positivity
  have hs' := fun u i => simTriple_iff.1 (hsh u i)
  choose μ hμ X Y W hm hX hY hW using hs'
  have hp := fun u i => gp_pair ha hB (hm u i)
  choose e1 e2 hpair hYe hWe hang using hp
  -- one step multiplies the radius by a power of `B`
  have hstep : ∀ u (j : Fin 6), Rr r (u + ldir j) = Rr r u * B ^ e1 u j := by
    intro u j
    rw [hY u j, hYe u j, hX u j]; ring
  have hexp : ∀ p q : ℤ, ∃ n : ℤ, Rr r (p, q) = Rr r (0, 0) * B ^ n := by
    have f0 : ∀ p q : ℤ, (p, q) + ldir 0 = (p + 1, q) := fun p q => by simp [ldir]
    have f1 : ∀ p q : ℤ, (p, q) + ldir 1 = (p, q + 1) := fun p q => by simp [ldir]
    have f3 : ∀ p q : ℤ, (p, q) + ldir 3 = (p - 1, q) := fun p q => by
      simp [ldir, sub_eq_add_neg]
    have f4 : ∀ p q : ℤ, (p, q) + ldir 4 = (p, q - 1) := fun p q => by
      simp [ldir, sub_eq_add_neg]
    have hrow : ∀ p : ℤ, ∃ n : ℤ, Rr r (p, 0) = Rr r (0, 0) * B ^ n := by
      intro p
      induction p using Int.induction_on with
      | zero => exact ⟨0, by simp⟩
      | succ m ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + e1 (m, 0) 0, ?_⟩
        rw [← f0, hstep, hn, zpow_add₀ hB0.ne']; ring
      | pred m ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨n + e1 (-(m : ℤ), 0) 3, ?_⟩
        rw [← f3, hstep, hn, zpow_add₀ hB0.ne']; ring
    intro p q
    induction q using Int.induction_on with
    | zero => exact hrow p
    | succ m ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + e1 (p, m) 1, ?_⟩
      rw [← f1, hstep, hn, zpow_add₀ hB0.ne']; ring
    | pred m ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + e1 (p, -(m : ℤ)) 4, ?_⟩
      rw [← f4, hstep, hn, zpow_add₀ hB0.ne']; ring
  choose L hL using hexp
  set ℓ : ℤ × ℤ → ℤ := fun u => L u.1 u.2 with hℓdef
  have hℓ : ∀ u, Rr r u = Rr r (0, 0) * B ^ ℓ u := fun u => hL u.1 u.2
  have hR0 : 0 < Rr r (0, 0) := by
    have := hX (0, 0) 0
    have hp0 := (perms3_pos ha haB haB2 (hm (0, 0) 0)).1
    rw [this]; exact mul_pos (hμ _ _) hp0
  -- the exponent differences
  have hdiff : ∀ u (j : Fin 6), ℓ (u + ldir j) - ℓ u = e1 u j := by
    intro u j
    have h := hstep u j
    rw [hℓ, hℓ u, mul_assoc, ← zpow_add₀ hB0.ne'] at h
    have h' := mul_left_cancel₀ hR0.ne' h
    rw [zpow_right_inj₀ hB0 hB1] at h'
    omega
  have hdiff2 : ∀ u (j : Fin 6), ℓ (u + ldir (j + 1)) - ℓ u = e2 u j := by
    intro u j
    have h : Rr r (u + ldir (j + 1)) = Rr r u * B ^ e2 u j := by
      rw [hW u j, hWe u j, hX u j]; ring
    rw [hℓ, hℓ u, mul_assoc, ← zpow_add₀ hB0.ne'] at h
    have h' := mul_left_cancel₀ hR0.ne' h
    rw [zpow_right_inj₀ hB0 hB1] at h'
    omega
  -- the angle facts
  have hsum := th_sum ha haB haB2
  have hLM := th_lt ha haB haB2 haB (by nlinarith : a * B < a * B ^ 2)
  have hMO := th_lt ha haB haB2 ha (by nlinarith : a < a * B)
  have hM : th a (a * B) (a * B ^ 2) (a * B) ≠ π / 3 := by
    have e := angle_role ha haB haB2 one_pos (x := a * B) (y := a * B ^ 2) (w := a)
      (by simp [perms3])
    simp only [one_mul] at e
    rw [← e, show a = a * 1 by ring, show a * 1 * B = a * B by ring,
      show a * 1 * B ^ 2 = a * B ^ 2 by ring, angleAt_smul ha hB0 (by positivity) one_pos]
    exact (cell_angles hB).2.2.2
  -- the axis pattern at every vertex
  have haxis : ∀ u, ∃ k, HasAxis ℓ u k := by
    intro u
    have hs := sum_roles ha haB haB2 hloc u (μ u) (X u) (Y u) (W u) (hμ u) (hm u) (hX u)
      (hY u) (hW u)
    have hpat := vertex_pattern hsum hLM hMO hM (fun i => ℓ (u + ldir i) - ℓ u)
      (fun i => by
        rw [hdiff u i, hdiff2 u i]
        exact hpair u i)
      (by
        rw [← hs]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdiff u i, hdiff2 u i, hang u i])
    exact hpat
  obtain ⟨k, hk⟩ := exponent_affine haxis
  refine ⟨k, fun p q => ?_⟩
  have h1 := hℓ (p, q)
  have h0 := hℓ (0, 0)
  have hl0 : ℓ (0, 0) = 0 := by
    have hz : B ^ ℓ (0, 0) = B ^ (0 : ℤ) := by
      rw [zpow_zero]
      have h00 : Rr r (0, 0) * B ^ ℓ (0, 0) = Rr r (0, 0) * 1 := by rw [mul_one]; exact h0.symm
      exact mul_left_cancel₀ hR0.ne' h00
    exact (zpow_right_inj₀ hB0 hB1).1 hz
  have : r p q = Rr r (p, q) := rfl
  rw [this, h1, hk p q, hl0, zero_add]
  rfl

/-! ### Theorem A 8.1 for the radius function -/

lemma OneShape.swap12 {r : ℤ → ℤ → ℝ} {a b c : ℝ} (h : OneShape r a b c) :
    OneShape r b a c := fun u i => simTriple_swap12 (h u i)

lemma OneShape.swap23 {r : ℤ → ℤ → ℝ} {a b c : ℝ} (h : OneShape r a b c) :
    OneShape r a c b := fun u i => simTriple_swap23 (h u i)

/-- The conclusion of Theorem A 8.1 for radii. -/
def OneShapeConcl (r : ℤ → ℤ → ℝ) : Prop :=
  (∀ u (i : Fin 6), Rr r (u + ldir i) = Rr r u) ∨
    ∃ B > 1, ∃ k : Fin 6, ∀ p q : ℤ,
      r p q = r 0 0 * B ^ (p * Ppat (0 - k) + q * Ppat (1 - k))

lemma oneshape_sorted {r : ℤ → ℤ → ℝ} {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hloc : LocUniv r) (hsh : OneShape r a b c) : OneShapeConcl r := by
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  rcases eq_or_lt_of_le (hab.trans hbc) with hac | hac
  · -- equilateral
    left
    intro u i
    obtain ⟨μ, hμ, x, y, w, hm, h1, h2, -⟩ := simTriple_iff.1 (hsh u i)
    have hb' : b = a := le_antisymm (hac ▸ hbc) hab
    have hc' : c = a := hac.symm
    rw [perms3_mem] at hm
    rw [h1, h2]
    rcases hm with h | h | h | h | h | h <;> rw [h.1, h.2.1] <;> simp [hb', hc']
  · rcases eq_or_lt_of_le hab with hab' | hab'
    · subst hab'
      exact (case_isosceles ha hc hac.ne hloc hsh).elim
    rcases eq_or_lt_of_le hbc with hbc' | hbc'
    · subst hbc'
      exact (case_isosceles hb ha hab'.ne' hloc hsh.swap12.swap23).elim
    by_cases hg : b ^ 2 = a * c
    · right
      set B := b / a with hBdef
      have hB : 1 < B := by rw [hBdef, one_lt_div ha]; exact hab'
      have hbB : b = a * B := by rw [hBdef]; field_simp
      have hcB : c = a * B ^ 2 := by
        rw [hBdef]
        field_simp
        nlinarith [hg]
      rw [hbB, hcB] at hsh
      exact ⟨B, hB, case_gp ha hB hloc hsh⟩
    · exact (case_generic ha hab' hbc' hg hloc hsh).elim

/-- **Theorem A 8.1 for the radius function.** Let `r > 0` have closing flowers
(`LocUniv`) and all center triangles similar to one triangle with radii `(a, b, c)`. Then
either all triangles are equilateral (adjacent radii are equal), or
`r(p,q) = r(0,0) B^{p·a' + q·b'}` with `B > 1` and `(a', b')` a rotation of `(2, 1)`. -/
theorem oneshape_radii {r : ℤ → ℤ → ℝ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hloc : LocUniv r) (hsh : OneShape r a b c) : OneShapeConcl r := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  · exact oneshape_sorted ha hab hbc hloc hsh
  · exact oneshape_sorted ha hab hbc hloc hsh
  · exact oneshape_sorted ha hac hbc hloc hsh.swap23
  · exact oneshape_sorted hc hac hab hloc hsh.swap23.swap12
  · exact oneshape_sorted hb hab hac hloc hsh.swap12
  · exact oneshape_sorted hb hbc hac hloc hsh.swap12.swap23
  · exact oneshape_sorted hc hbc hab hloc hsh.swap12.swap23.swap12
  · exact oneshape_sorted hc hbc hab hloc hsh.swap12.swap23.swap12

end DoyleFormal
