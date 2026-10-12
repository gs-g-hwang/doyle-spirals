/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.OneShape
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The angle sum of a flower (Definition A 2.1) — Phase 4n

* `six_angles_sum`: six positively oriented triangles around a point have angle sum `2π` or
  `4π` (the arguments of the six ratios lie in `(0, π)` and their product is `1`).
* `IsConfig.edge`: tangency along all six lattice directions.
* `IsConfig.angle_eq`: in a configuration the angle at `z(v)` of the center triangle
  `v, v + d_i, v + d_{i+1}` is `angleAt (r v) (r (v+d_i)) (r (v+d_{i+1}))`.
* `IsConfig.flower_sum`: hence `∑_i angleAt … ∈ {2π, 4π}` at every vertex.

The tangency and orientation conditions of Definition A 2.1 therefore leave exactly one
alternative to a flower that closes up once: a flower that winds twice (`4π`). Definition
A 2.1 excludes it ("each flower still closes up exactly", "the triangles of each flower have
disjoint interiors"); this is `LocUniv`.
-/

namespace DoyleFormal

open Complex

/-- Local univalence (Definition A 2.1): at every vertex the six angles of the flower sum
to `2π`. -/
def LocUniv (r : ℤ → ℤ → ℝ) : Prop :=
  ∀ u : ℤ × ℤ, ∑ i : Fin 6, angleAt (r u.1 u.2) (r (u + ldir i).1 (u + ldir i).2)
    (r (u + ldir (i + 1)).1 (u + ldir (i + 1)).2) = 2 * Real.pi

lemma arg_mem_Ioo_of_im_pos {w : ℂ} (h : 0 < w.im) : 0 < arg w ∧ arg w < Real.pi := by
  refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 h.le) ?_, arg_lt_pi_iff.2 (Or.inr h.ne')⟩
  intro h0
  have := (arg_eq_zero_iff.1 h0.symm).2
  linarith

lemma im_div_pos_of_orient {z a b : ℂ} (ha : a ≠ z) (ho : 0 < orient z a b) :
    0 < ((b - z) / (a - z)).im := by
  have ha' : a - z ≠ 0 := sub_ne_zero.2 ha
  have hn : 0 < Complex.normSq (a - z) := Complex.normSq_pos.2 ha'
  rw [Complex.div_im]
  unfold orient at ho
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at ho
  rw [show (b - z).im * (a - z).re / Complex.normSq (a - z) -
      (b - z).re * (a - z).im / Complex.normSq (a - z) =
      ((a - z).re * (b - z).im + -(a - z).im * (b - z).re) / Complex.normSq (a - z) by ring]
  exact div_pos (by linarith) hn

/-- **Six positive angles around a point sum to `2π` or `4π`.** -/
theorem six_angles_sum {z : ℂ} {w : Fin 6 → ℂ} (hw : ∀ i, w i ≠ z)
    (ho : ∀ i, 0 < orient z (w i) (w (i + 1))) :
    ∑ i, arg ((w (i + 1) - z) / (w i - z)) = 2 * Real.pi ∨
      ∑ i, arg ((w (i + 1) - z) / (w i - z)) = 4 * Real.pi := by
  set ρ : Fin 6 → ℂ := fun i => (w (i + 1) - z) / (w i - z) with hρ
  have hne : ∀ i, w i - z ≠ 0 := fun i => sub_ne_zero.2 (hw i)
  have hρ0 : ∀ i, ρ i ≠ 0 := fun i => div_ne_zero (hne (i + 1)) (hne i)
  have hbd : ∀ i, 0 < arg (ρ i) ∧ arg (ρ i) < Real.pi := fun i =>
    arg_mem_Ioo_of_im_pos (im_div_pos_of_orient (hw i) (ho i))
  -- the product of the ratios is `1`
  have hprod : ∏ i, ρ i = 1 := by
    simp only [hρ, Fin.prod_univ_six]
    simp only [show (0 : Fin 6) + 1 = 1 by decide, show (1 : Fin 6) + 1 = 2 by decide,
      show (2 : Fin 6) + 1 = 3 by decide, show (3 : Fin 6) + 1 = 4 by decide,
      show (4 : Fin 6) + 1 = 5 by decide, show (5 : Fin 6) + 1 = 0 by decide]
    have h0 := hne 0; have h1 := hne 1; have h2 := hne 2
    have h3 := hne 3; have h4 := hne 4; have h5 := hne 5
    field_simp
  -- so `exp (i ∑ arg) = 1`
  have hexp : exp ((∑ i, arg (ρ i) : ℝ) * I) = 1 := by
    have h1 : ∀ i, exp ((arg (ρ i) : ℂ) * I) = ρ i / (‖ρ i‖ : ℂ) := by
      intro i
      have hn : (‖ρ i‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 (hρ0 i))
      rw [eq_div_iff hn, mul_comm]
      exact norm_mul_exp_arg_mul_I (ρ i)
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    simp only [h1]
    rw [Finset.prod_div_distrib, hprod]
    have hn : ∏ i, (‖ρ i‖ : ℂ) = 1 := by
      rw [← Complex.ofReal_prod, ← norm_prod, hprod, norm_one, Complex.ofReal_one]
    rw [hn, div_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  have hS : (∑ i, arg (ρ i) : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hlo : 0 < ∑ i, arg (ρ i) := Finset.sum_pos (fun i _ => (hbd i).1) Finset.univ_nonempty
  have hhi : ∑ i, arg (ρ i) < 6 * Real.pi := by
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => (hbd i).2)
    simpa using this
  have hpi := Real.pi_pos
  have hn1 : (0 : ℝ) < n := by
    by_contra h
    push Not at h
    nlinarith
  have hn3 : (n : ℝ) < 3 := by
    by_contra h
    push Not at h
    nlinarith
  have : n = 1 ∨ n = 2 := by
    have h1 : 0 < n := by exact_mod_cast hn1
    have h3 : n < 3 := by exact_mod_cast hn3
    omega
  rcases this with rfl | rfl
  · left; rw [hS]; push_cast; ring
  · right; rw [hS]; push_cast; ring

section Config

variable {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ}

/-- Tangency along all six lattice directions. -/
lemma IsConfig.edge (hz : IsConfig r z) (u : ℤ × ℤ) (i : Fin 6) :
    ‖z (u + ldir i).1 (u + ldir i).2 - z u.1 u.2‖ =
      r (u + ldir i).1 (u + ldir i).2 + r u.1 u.2 := by
  obtain ⟨p, q⟩ := u
  fin_cases i <;>
    simp only [ldir, Int.reduceNeg, Fin.reduceFinMk, Matrix.cons_val, Prod.mk_add_mk, add_zero]
  · exact hz.t10 p q
  · exact hz.t01 p q
  · have h := hz.tm11 p q
    simpa [sub_eq_add_neg] using h
  · have h := hz.t10 (p + -1) q
    rw [show p + -1 + 1 = p by ring] at h
    rw [norm_sub_rev, h, add_comm]
  · have h := hz.t01 p (q + -1)
    rw [show q + -1 + 1 = q by ring] at h
    rw [norm_sub_rev, h, add_comm]
  · have h := hz.tm11 (p + 1) (q + -1)
    rw [show p + 1 - 1 = p by ring, show q + -1 + 1 = q by ring] at h
    rw [norm_sub_rev, h, add_comm]

lemma ldir_succ_eq (u : ℤ × ℤ) (i : Fin 6) :
    u + ldir i + ldir (i + 2) = u + ldir (i + 1) := by
  rw [add_assoc, ldir_add_two]

/-- In a configuration the angle at `z(v)` of the center triangle `v, v+d_i, v+d_{i+1}` is the
argument of the ratio of the two edge vectors, and equals `angleAt` of the radii. -/
lemma IsConfig.angle_eq (hz : IsConfig r z) (hr : ∀ p q, 0 < r p q) (u : ℤ × ℤ)
    (i : Fin 6) :
    arg ((z (u + ldir (i + 1)).1 (u + ldir (i + 1)).2 - z u.1 u.2) /
        (z (u + ldir i).1 (u + ldir i).2 - z u.1 u.2)) =
      angleAt (r u.1 u.2) (r (u + ldir i).1 (u + ldir i).2)
        (r (u + ldir (i + 1)).1 (u + ldir (i + 1)).2) := by
  set a := u + ldir i
  set b := u + ldir (i + 1)
  have hab : b = a + ldir (i + 2) := (ldir_succ_eq u i).symm
  have e1 := hz.edge u i
  have e2 := hz.edge u (i + 1)
  have e3 := hz.edge a (i + 2)
  rw [← hab] at e3
  have hx := hr u.1 u.2
  have hy := hr a.1 a.2
  have hw := hr b.1 b.2
  have ha0 : z a.1 a.2 - z u.1 u.2 ≠ 0 := by
    intro h; rw [h, norm_zero] at e1; linarith
  have hb0 : z b.1 b.2 - z u.1 u.2 ≠ 0 := by
    intro h; rw [h, norm_zero] at e2; linarith
  have hang := angleAt_eq_angle (V := ℂ) (P := ℂ) hx hy hw (z u.1 u.2) (z a.1 a.2)
    (z b.1 b.2) (by rw [dist_comm, dist_eq_norm, e1, add_comm])
    (by rw [dist_comm, dist_eq_norm, e3, add_comm])
    (by rw [dist_eq_norm, e2])
  rw [← hang, EuclideanGeometry.angle_comm, EuclideanGeometry.angle,
    vsub_eq_sub, vsub_eq_sub, Complex.angle_eq_abs_arg hb0 ha0]
  have ho := hz.orient_pos u (ldir i) (by fin_cases i <;> simp [ldir, IsDir])
  have hrot : u + rotp (ldir i) = b := by
    simp only [b]; congr 1; fin_cases i <;> decide
  rw [hrot] at ho
  have hpos := (arg_mem_Ioo_of_im_pos (im_div_pos_of_orient (sub_ne_zero.1 ha0) ho)).1
  exact (abs_of_pos hpos).symm

/-- **The flower angle sum of a configuration is `2π` or `4π`.** -/
theorem IsConfig.flower_sum (hz : IsConfig r z) (hr : ∀ p q, 0 < r p q) (u : ℤ × ℤ) :
    ∑ i : Fin 6, angleAt (r u.1 u.2) (r (u + ldir i).1 (u + ldir i).2)
        (r (u + ldir (i + 1)).1 (u + ldir (i + 1)).2) = 2 * Real.pi ∨
      ∑ i : Fin 6, angleAt (r u.1 u.2) (r (u + ldir i).1 (u + ldir i).2)
        (r (u + ldir (i + 1)).1 (u + ldir (i + 1)).2) = 4 * Real.pi := by
  simp only [← hz.angle_eq hr u]
  refine six_angles_sum (w := fun i => z (u + ldir i).1 (u + ldir i).2) (z := z u.1 u.2)
    (fun i h => ?_) (fun i => ?_)
  · have e := hz.edge u i
    rw [h, sub_self, norm_zero] at e
    linarith [hr u.1 u.2, hr (u + ldir i).1 (u + ldir i).2]
  · have ho := hz.orient_pos u (ldir i) (by fin_cases i <;> simp [ldir, IsDir])
    have hrot : u + rotp (ldir i) = u + ldir (i + 1) := by
      congr 1; fin_cases i <;> decide
    rw [hrot] at ho
    exact ho

end Config

end DoyleFormal
