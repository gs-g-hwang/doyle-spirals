/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Arm counts (paper A, Lemma 7.4)

Lattice points are `ℤ × ℤ`. For a primitive direction `d`, the lattice lines in
direction `d` are the fibers of `u ↦ det(d, u)`. Translation by `v` shifts this value
by `det(d, v)`. So modulo `ℤv` the lines fall into `|det(d, v)|` classes.

* `same_line_iff`   : for primitive `d`, `det(d,u) = det(d,u')` iff `u' ∈ u + ℤd`.
* `exists_line`     : every value `c ∈ ℤ` labels a line (Bezout).
* `det_add_smul`    : `det(d, u + k v) = det(d, u) + k det(d, v)`.
* `line_classes`    : two line labels are identified mod `ℤv` iff they agree in
  `ZMod |det(d,v)|`; `card_line_classes`: there are `|det(d,v)|` classes.
* `arm_counts`      : for `v_n = (−n, 2n)` the counts are `(n, 2n, n)` in the directions
  `(0,1)`, `(1,0)`, `(−1,1)`.
-/

namespace DoyleFormal

/-- `det(a, b) = a₁b₂ − a₂b₁`. -/
def det2 (a b : ℤ × ℤ) : ℤ := a.1 * b.2 - a.2 * b.1

lemma det_add_smul (d u v : ℤ × ℤ) (k : ℤ) :
    det2 d (u + k • v) = det2 d u + k * det2 d v := by
  simp only [det2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Lattice lines in a primitive direction `d` are exactly the fibers of `det(d, ·)`. -/
theorem same_line_iff {d : ℤ × ℤ} (hd : Int.gcd d.1 d.2 = 1) (u u' : ℤ × ℤ) :
    det2 d u = det2 d u' ↔ ∃ t : ℤ, u' = u + t • d := by
  constructor
  · intro h
    have hb := Int.gcd_eq_gcd_ab d.1 d.2
    rw [hd, Nat.cast_one] at hb
    unfold det2 at h
    refine ⟨Int.gcdA d.1 d.2 * (u'.1 - u.1) + Int.gcdB d.1 d.2 * (u'.2 - u.2), ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      linear_combination (u'.1 - u.1) * hb + Int.gcdB d.1 d.2 * h
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linear_combination (u'.2 - u.2) * hb - Int.gcdA d.1 d.2 * h
  · rintro ⟨t, rfl⟩
    simp only [det2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- Every integer labels a lattice line in a primitive direction `d`. -/
theorem exists_line {d : ℤ × ℤ} (hd : Int.gcd d.1 d.2 = 1) (c : ℤ) :
    ∃ u : ℤ × ℤ, det2 d u = c := by
  have hb := Int.gcd_eq_gcd_ab d.1 d.2
  rw [hd, Nat.cast_one] at hb
  exact ⟨(-(Int.gcdB d.1 d.2 * c), Int.gcdA d.1 d.2 * c), by
    unfold det2; linear_combination (-c) * hb⟩

/-- Line labels `c, c'` are identified by translations in `ℤv` iff they agree
modulo `|det(d, v)|`. -/
theorem line_classes (d v : ℤ × ℤ) (c c' : ℤ) :
    (∃ k : ℤ, c' = c + k * det2 d v) ↔ (c : ZMod (det2 d v).natAbs) = c' := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_natAbs, abs_dvd]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linear_combination hk⟩

/-- **Lemma A 7.4.** Modulo `ℤv` there are `|det(d, v)|` classes of lines. -/
theorem card_line_classes (d v : ℤ × ℤ) :
    Nat.card (ZMod (det2 d v).natAbs) = (det2 d v).natAbs :=
  Nat.card_zmod _

/-- `v_n = (−n, 2n)`. -/
def vn (n : ℤ) : ℤ × ℤ := (-n, 2 * n)

/-- **Lemma A 7.4, arm counts** `(n, 2n, n)` for the directions `(0,1)`, `(1,0)`, `(−1,1)`. -/
theorem arm_counts (n : ℤ) :
    (det2 (0, 1) (vn n)).natAbs = n.natAbs ∧
    (det2 (1, 0) (vn n)).natAbs = (2 * n).natAbs ∧
    (det2 (-1, 1) (vn n)).natAbs = n.natAbs := by
  refine ⟨?_, ?_, ?_⟩
  · congr 1; simp only [det2, vn]; ring
  · congr 1; simp only [det2, vn]; ring
  · rw [show det2 (-1, 1) (vn n) = -n by simp only [det2, vn]; ring, Int.natAbs_neg]

/-- The three directions are primitive. -/
theorem directions_primitive :
    Int.gcd 0 1 = 1 ∧ Int.gcd 1 0 = 1 ∧ Int.gcd (-1) 1 = 1 := by decide

end DoyleFormal
