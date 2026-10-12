/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Tiling

/-!
# The regular packing satisfies the geometric hypotheses — Phase 5j

* `unit_sol`: the integer solutions of `a² + ab + b² = 1` are the six lattice directions.
* `zreg_dist_sq`: `|zreg(p',q') − zreg(p,q)|² = 4(a² + ab + b²)`, `(a,b) = (p'−p, q'−q)`.
* `regularGeo`: the regular packing is a `GeoHexPacking` (the circles tangent to a circle are
  exactly its six neighbors), so the hypotheses of `coherent_classification_geo` are met by the
  regular packing as well as by `D_{B_n}` (`cylGeo`).
-/

namespace DoyleFormal

lemma unit_sol (a b : ℤ) (h : a ^ 2 + a * b + b ^ 2 = 1) : ∃ i : Fin 6, (a, b) = ldir i := by
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg (2 * a + b)]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg (2 * a + b)]
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg (a + 2 * b)]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg (a + 2 * b)]
  interval_cases a <;> interval_cases b <;> first | decide | (norm_num at h)

lemma zreg_dist_sq (p q p' q' : ℤ) :
    ‖zreg 1 p' q' - zreg 1 p q‖ ^ 2 =
      4 * (((p' - p : ℤ) : ℝ) ^ 2 + ((p' - p : ℤ) : ℝ) * ((q' - q : ℤ) : ℝ) +
        ((q' - q : ℤ) : ℝ) ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [zreg, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, omega6, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  have h3 : √3 ^ 2 = 3 := sqrt3_sq
  push_cast
  linear_combination ((q' : ℝ) - q) ^ 2 * h3

/-- **The regular packing is a geometric hexagonal packing.** -/
noncomputable def regularGeo : GeoHexPacking (ℤ × ℤ) where
  c := regularHex.c
  ρ := regularHex.ρ
  ρ_pos := regularHex.ρ_pos
  nb := regularHex.nb
  tan := regularHex.tan
  rim := regularHex.rim
  ori := regularHex.ori
  wind := regularHex.wind
  deg6 v w h := by
    simp only [regularHex] at h ⊢
    obtain ⟨p, q⟩ := v; obtain ⟨p', q'⟩ := w
    have h2 := zreg_dist_sq p q p' q'
    rw [h] at h2
    have key : (p' - p) ^ 2 + (p' - p) * (q' - q) + (q' - q) ^ 2 = 1 := by
      have : (((p' - p) ^ 2 + (p' - p) * (q' - q) + (q' - q) ^ 2 : ℤ) : ℝ) = 1 := by
        push_cast at h2 ⊢; nlinarith [h2]
      exact_mod_cast this
    obtain ⟨i, hi⟩ := unit_sol _ _ key
    refine ⟨i, ?_⟩
    have h1 := congrArg Prod.fst hi
    have h2' := congrArg Prod.snd hi
    simp only at h1 h2'
    ext
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add]; omega
  conn := regularHex.conn

end DoyleFormal
