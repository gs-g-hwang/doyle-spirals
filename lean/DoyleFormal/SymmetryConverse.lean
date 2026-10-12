/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.LatticeAut

/-!
# Theorem A 4.1 (`⇒`) for a general configuration — Phase 4j

Let `z` be a configuration (`IsConfig`, Definition A 2.1) with radius function `A^p B^q`
(`A, B > 0`), and let `τ` be a lattice map that preserves adjacency, fixes `(0,0)` and
`(1,0)`, and satisfies `conj z(u) = z(τ u)` and `r(τ u) = r(u)` (conjugation maps `K(u)`
to `K(τ u)`).

* `IsConfig.orient_pos`: every positively oriented lattice triangle (`ldet = 1`) has a
  positively oriented center triangle, not only the upward and downward ones of the
  definition.
* `conj_isIndirectAut`: such a `τ` is indirect (`IsIndirectAut`), because conjugation
  reverses the orientation of center triangles.
* `symmetry_converse` (**Theorem A 4.1, `⇒`**): then `A = B²`.

Together with `mirror_symmetry` / `config_mirror` (`⇐`) this verifies Theorem A 4.1.
-/

namespace DoyleFormal

open Complex

/-- Rotation by `+60°` in lattice coordinates. -/
def rotp (x : ℤ × ℤ) : ℤ × ℤ := (-x.2, x.1 + x.2)

/-- A lattice triangle has determinant `±1`. -/
lemma ldet_pm {x y : ℤ × ℤ} (hx : IsDir x) (hy : IsDir y) (hxy : IsDir (y - x)) :
    ldet x y = 1 ∨ ldet x y = -1 := by
  unfold IsDir at hx hy hxy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [ldet, Prod.ext_iff]

/-- In a positively oriented lattice triangle the third edge is the first one rotated by
`+60°`. -/
lemma rotp_of_ldet {x y : ℤ × ℤ} (hx : IsDir x) (hy : IsDir y) (hxy : IsDir (y - x))
    (hd : ldet x y = 1) : y = rotp x := by
  unfold IsDir at hx hy hxy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [ldet, rotp]

/-- Conjugation reverses orientation. -/
lemma orient_conj (a b c : ℂ) :
    orient ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) ((starRingEnd ℂ) c) = -orient a b c := by
  simp only [orient_eq, Complex.conj_re, Complex.conj_im]
  ring

/-- Every positively oriented lattice triangle `a, a + x, a + rotp x` of a configuration has
a positively oriented center triangle (each one is an upward or downward triangle of the
definition, up to a cyclic relabeling). -/
lemma IsConfig.orient_pos {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z)
    (a x : ℤ × ℤ) (hx : IsDir x) :
    0 < orient (z a.1 a.2) (z (a + x).1 (a + x).2) (z (a + rotp x).1 (a + rotp x).2) := by
  obtain ⟨p, q⟩ := a
  unfold IsDir at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rotp, Prod.mk_add_mk]
  · simpa using hz.up p q
  · simpa [sub_eq_add_neg] using hz.down p q
  · have h := hz.up (p - 1) q
    rw [← orient_cycle] at h
    convert h using 2 <;> congr 1 <;> ring
  · have h := hz.down p (q - 1)
    rw [← orient_cycle] at h
    convert h using 2 <;> congr 1 <;> ring
  · have h := hz.up p (q - 1)
    rw [← orient_cycle, ← orient_cycle] at h
    convert h using 2 <;> congr 1 <;> ring
  · have h := hz.down (p + 1) (q - 1)
    rw [← orient_cycle, ← orient_cycle] at h
    convert h using 2 <;> congr 1 <;> ring

/-- The image of a lattice triangle under `τ` is negatively oriented when the center
triangles are. -/
lemma ldet_neg_of_orient {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z)
    {a b c : ℤ × ℤ} (hx : IsDir (b - a)) (hy : IsDir (c - a)) (hxy : IsDir (c - b))
    (ho : orient (z a.1 a.2) (z b.1 b.2) (z c.1 c.2) < 0) : ldet (b - a) (c - a) = -1 := by
  have hxy' : IsDir ((c - a) - (b - a)) := by simpa using hxy
  rcases ldet_pm hx hy hxy' with h | h
  · have hc := rotp_of_ldet hx hy hxy' h
    have hp := hz.orient_pos a (b - a) hx
    rw [← hc] at hp
    simp only [add_sub_cancel] at hp
    linarith
  · exact h

/-- A lattice map that preserves adjacency and carries a configuration to its mirror image
(`conj z(u) = z(τ u)`) is indirect. -/
theorem conj_isIndirectAut {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z)
    {τ : ℤ → ℤ → ℤ × ℤ}
    (h10 : ∀ p q, IsDir (τ (p + 1) q - τ p q)) (h01 : ∀ p q, IsDir (τ p (q + 1) - τ p q))
    (hm11 : ∀ p q, IsDir (τ (p - 1) (q + 1) - τ p q))
    (hconj : ∀ p q, (starRingEnd ℂ) (z p q) = z (τ p q).1 (τ p q).2) : IsIndirectAut τ where
  t10 := h10
  t01 := h01
  tm11 := hm11
  up p q := by
    refine ldet_neg_of_orient hz (h10 p q) (h01 p q) ?_ ?_
    · have h := hm11 (p + 1) q
      rwa [add_sub_cancel_right] at h
    · rw [← hconj, ← hconj, ← hconj, orient_conj]
      linarith [hz.up p q]
  down p q := by
    refine ldet_neg_of_orient hz (h01 p q) (hm11 p q) ?_ ?_
    · have h := (h10 (p - 1) (q + 1)).neg
      rw [sub_add_cancel] at h
      simpa using h
    · rw [← hconj, ← hconj, ← hconj, orient_conj]
      linarith [hz.down p q]

/-- **Theorem A 4.1 (`⇒`).** Let `z` be a configuration with radius function `A^p B^q`
(`A, B > 0`). If a lattice map `τ` that preserves adjacency and fixes `(0,0)` and `(1,0)`
satisfies `conj K(u) = K(τ u)` (equal centers and radii), then `A = B²`. -/
theorem symmetry_converse {A B : ℝ} (hB : 0 < B) {z : ℤ → ℤ → ℂ}
    (hz : IsConfig (fun p q => A ^ p * B ^ q) z) {τ : ℤ → ℤ → ℤ × ℤ}
    (h10 : ∀ p q, IsDir (τ (p + 1) q - τ p q)) (h01 : ∀ p q, IsDir (τ p (q + 1) - τ p q))
    (hm11 : ∀ p q, IsDir (τ (p - 1) (q + 1) - τ p q))
    (h0 : τ 0 0 = (0, 0)) (h1 : τ 1 0 = (1, 0))
    (hconj : ∀ p q, (starRingEnd ℂ) (z p q) = z (τ p q).1 (τ p q).2)
    (hr : ∀ p q, A ^ (τ p q).1 * B ^ (τ p q).2 = A ^ p * B ^ q) : A = B ^ 2 :=
  mirror_converse hB (conj_isIndirectAut hz h10 h01 hm11 hconj) h0 h1 hr

end DoyleFormal
