/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Tangency

/-!
# Rigidity (paper A, Lemma 2.2) and Proposition 5.4 — Phase 4b

* `apex_unique` : the apex of a triangle with a given base, given side lengths and positive
  orientation is unique.
* `IsConfig r z` : centers `z(p,q)` with radii `r(p,q)` form a hexagonal circle configuration
  (Definition A 2.1): tangency along the three edge directions and positively oriented
  upward and downward center triangles.
* `rigidity` (Lemma A 2.2, uniqueness part): two configurations with the same radius function
  that agree at `(0,0)` and `(1,0)` agree everywhere.
* `prop_5_4` (Proposition A 5.4): every configuration with radii `B^{2p+q}` (`B > 1`) and
  `z(0,0) = 0`, `z(1,0) = 1 + B²` is the closed form `X + B^{2p} β^q (0 − X)`,
  `β = B e^{iψ}`, with `ψ = psi B = θ_O − θ_{P₀}` (`psi_eq_angle_diff`).
-/

namespace DoyleFormal

open Complex

/-- Twice the signed area of the triangle `a, b, c`. -/
noncomputable def orient (a b c : ℂ) : ℝ := ((starRingEnd ℂ) (b - a) * (c - a)).im

lemma orient_eq (a b c : ℂ) :
    orient a b c = (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re) := by
  unfold orient
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

lemma orient_cycle (a b c : ℂ) : orient b c a = orient a b c := by
  rw [orient_eq, orient_eq]; ring

lemma norm_sub_sq_eq (u v : ℂ) : ‖u - v‖ ^ 2 = (u.re - v.re) ^ 2 + (u.im - v.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- The real-variable core of `apex_unique`: `x` and `y` with `|x| = |y|`, `|x − e| = |y − e|`
and positive cross products with `e` are equal. -/
lemma apex_aux {e1 e2 x1 x2 y1 y2 : ℝ} (s1 : x1 ^ 2 + x2 ^ 2 = y1 ^ 2 + y2 ^ 2)
    (s2 : (x1 - e1) ^ 2 + (x2 - e2) ^ 2 = (y1 - e1) ^ 2 + (y2 - e2) ^ 2)
    (ho : 0 < e1 * x2 - e2 * x1) (ho' : 0 < e1 * y2 - e2 * y1) : x1 = y1 ∧ x2 = y2 := by
  -- equal "real parts" `e·x = e·y`
  have hR : e1 * x1 + e2 * x2 = e1 * y1 + e2 * y2 := by linear_combination (s1 - s2) / 2
  -- equal "imaginary parts" `e × x = e × y`
  have hI2 : (e1 * x2 - e2 * x1) ^ 2 = (e1 * y2 - e2 * y1) ^ 2 := by
    linear_combination (e1 ^ 2 + e2 ^ 2) * s1 - (e1 * x1 + e2 * x2 + e1 * y1 + e2 * y2) * hR
  have hI : e1 * x2 - e2 * x1 = e1 * y2 - e2 * y1 := (sq_eq_sq₀ ho.le ho'.le).1 hI2
  have hE : 0 < e1 ^ 2 + e2 ^ 2 := by
    have hid : (e1 ^ 2 + e2 ^ 2) * (x1 ^ 2 + x2 ^ 2)
        = (e1 * x1 + e2 * x2) ^ 2 + (e1 * x2 - e2 * x1) ^ 2 := by ring
    have hprod : 0 < (e1 ^ 2 + e2 ^ 2) * (x1 ^ 2 + x2 ^ 2) := by
      rw [hid]; linarith [pow_pos ho 2, sq_nonneg (e1 * x1 + e2 * x2)]
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with h | h
    · exact h.1
    · linarith [sq_nonneg x1, sq_nonneg x2, h.2]
  have k1 : (e1 ^ 2 + e2 ^ 2) * (x1 - y1) = 0 := by linear_combination e1 * hR - e2 * hI
  have k2 : (e1 ^ 2 + e2 ^ 2) * (x2 - y2) = 0 := by linear_combination e2 * hR + e1 * hI
  have k1' := (mul_eq_zero.1 k1).resolve_left hE.ne'
  have k2' := (mul_eq_zero.1 k2).resolve_left hE.ne'
  exact ⟨by linarith, by linarith⟩

/-- **The apex is unique.** Given the base `a, b`, the distances from the apex to `a` and to
`b`, and positive orientation, the apex is determined. -/
theorem apex_unique {a b c c' : ℂ} (h1 : ‖c - a‖ = ‖c' - a‖) (h2 : ‖c - b‖ = ‖c' - b‖)
    (ho : 0 < orient a b c) (ho' : 0 < orient a b c') : c = c' := by
  have s1 := congrArg (· ^ 2) h1
  have s2 := congrArg (· ^ 2) h2
  simp only [norm_sub_sq_eq] at s1 s2
  rw [orient_eq] at ho ho'
  obtain ⟨k1, k2⟩ := apex_aux (e1 := b.re - a.re) (e2 := b.im - a.im) s1
    (by linear_combination s2) ho ho'
  apply Complex.ext <;> linarith

/-- In a triangle with the same side lengths and positive orientation in two placements,
agreement at two vertices gives agreement at the third. -/
lemma tri_agree {a b c a' b' c' : ℂ} (hab : ‖b - a‖ = ‖b' - a'‖) (hbc : ‖c - b‖ = ‖c' - b'‖)
    (hca : ‖c - a‖ = ‖c' - a'‖) (ho : 0 < orient a b c) (ho' : 0 < orient a' b' c') :
    (a = a' → b = b' → c = c') ∧ (b = b' → c = c' → a = a') ∧
      (c = c' → a = a' → b = b') := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl rfl
    exact apex_unique hca hbc ho ho'
  · rintro rfl rfl
    rw [← orient_cycle] at ho ho'
    exact apex_unique (by rw [norm_sub_rev, hab, norm_sub_rev])
      (by rw [norm_sub_rev, hca, norm_sub_rev]) ho ho'
  · rintro rfl rfl
    rw [orient_cycle] at ho ho'
    exact apex_unique (by rw [norm_sub_rev, hbc, norm_sub_rev]) hab ho ho'

/-- **Definition A 2.1** on the whole lattice: radii `r`, centers `z`, tangency along the three
edge directions `(1,0)`, `(0,1)`, `(−1,1)`, and positively oriented center triangles. -/
structure IsConfig (r : ℤ → ℤ → ℝ) (z : ℤ → ℤ → ℂ) : Prop where
  t10 : ∀ p q, ‖z (p + 1) q - z p q‖ = r (p + 1) q + r p q
  t01 : ∀ p q, ‖z p (q + 1) - z p q‖ = r p (q + 1) + r p q
  tm11 : ∀ p q, ‖z (p - 1) (q + 1) - z p q‖ = r (p - 1) (q + 1) + r p q
  up : ∀ p q, 0 < orient (z p q) (z (p + 1) q) (z p (q + 1))
  down : ∀ p q, 0 < orient (z p q) (z p (q + 1)) (z (p - 1) (q + 1))

section Agree

variable {r : ℤ → ℤ → ℝ} {z w : ℤ → ℤ → ℂ}

lemma up_agree (hz : IsConfig r z) (hw : IsConfig r w) (p q : ℤ) :
    (z p q = w p q → z (p + 1) q = w (p + 1) q → z p (q + 1) = w p (q + 1)) ∧
    (z (p + 1) q = w (p + 1) q → z p (q + 1) = w p (q + 1) → z p q = w p q) ∧
    (z p (q + 1) = w p (q + 1) → z p q = w p q → z (p + 1) q = w (p + 1) q) := by
  have e3z := hz.tm11 (p + 1) q
  have e3w := hw.tm11 (p + 1) q
  rw [add_sub_cancel_right] at e3z e3w
  exact tri_agree (by rw [hz.t10, hw.t10]) (by rw [e3z, e3w]) (by rw [hz.t01, hw.t01])
    (hz.up p q) (hw.up p q)

lemma down_agree (hz : IsConfig r z) (hw : IsConfig r w) (p q : ℤ) :
    (z p q = w p q → z p (q + 1) = w p (q + 1) → z (p - 1) (q + 1) = w (p - 1) (q + 1)) ∧
    (z p (q + 1) = w p (q + 1) → z (p - 1) (q + 1) = w (p - 1) (q + 1) → z p q = w p q) ∧
    (z (p - 1) (q + 1) = w (p - 1) (q + 1) → z p q = w p q → z p (q + 1) = w p (q + 1)) := by
  have e2z := hz.t10 (p - 1) (q + 1)
  have e2w := hw.t10 (p - 1) (q + 1)
  rw [sub_add_cancel] at e2z e2w
  exact tri_agree (by rw [hz.t01, hw.t01])
    (by rw [norm_sub_rev, e2z, norm_sub_rev (w _ _), e2w]) (by rw [hz.tm11, hw.tm11])
    (hz.down p q) (hw.down p q)

/-- **Lemma A 2.2 (rigidity, uniqueness part).** Two configurations with the same radius
function that agree at the adjacent lattice points `(0,0)` and `(1,0)` agree everywhere. -/
theorem rigidity (hz : IsConfig r z) (hw : IsConfig r w) (h0 : z 0 0 = w 0 0)
    (h1 : z 1 0 = w 1 0) : ∀ p q, z p q = w p q := by
  -- the axis row `q = 0`
  have row0 : ∀ p : ℤ, z p 0 = w p 0 ∧ z (p + 1) 0 = w (p + 1) 0 := by
    intro p
    induction p using Int.induction_on with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ n ih =>
      have c1 := (up_agree hz hw n 0).1 ih.1 ih.2
      have c2 := (down_agree hz hw (n + 1) 0).2.2 (by rw [add_sub_cancel_right]; exact c1) ih.2
      have c3 := (up_agree hz hw (n + 1) 0).2.2 c2 ih.2
      exact ⟨ih.2, c3⟩
    | pred n ih =>
      -- know `(p,0)` and `(p+1,0)` with `p = −n`
      have hA := ih.1
      have hB := ih.2
      have d1 := (down_agree hz hw (-(n : ℤ) + 1) (-1)).2.1 (by simpa using hB)
        (by simpa using hA)
      have u1 := (up_agree hz hw (-(n : ℤ)) (-1)).2.1 d1 (by simpa using hA)
      have d2 := (down_agree hz hw (-(n : ℤ)) (-1)).1 u1 (by simpa using hA)
      refine ⟨by simpa using d2, by simpa using hA⟩
  -- all rows, upward and downward
  intro p q
  induction q using Int.induction_on generalizing p with
  | zero => exact (row0 p).1
  | succ n ih => exact (up_agree hz hw p n).1 (ih p) (ih (p + 1))
  | pred n ih =>
    exact (down_agree hz hw p (-(n : ℤ) - 1)).2.1 (by simpa using ih p)
      (by simpa using ih (p - 1))

end Agree

/-- The closed form with `ψ = psi B` is a configuration with radii `B^{2p+q}`. -/
theorem zc_isConfig {B : ℝ} (hB : 1 < B) : IsConfig (rad B) (zc B (psi B)) := by
  have hcos := cos_psi hB
  have hsin : 0 < Real.sin (psi B) :=
    Real.sin_pos_of_pos_of_lt_pi (psi_mem_Ioo hB).1 (psi_mem_Ioo hB).2
  refine ⟨edge_10 _ hB, edge_01 hB hcos, ?_, ?_, ?_⟩
  · intro p q; simpa [sub_eq_add_neg] using edge_m11 hB hcos p q
  · intro p q; exact orient_up hB hsin p q
  · intro p q; simpa [sub_eq_add_neg, orient] using orient_down hB hsin p q

/-- **Proposition A 5.4.** For `B > 1`, every hexagonal circle configuration with radii
`B^{2p+q}` normalized by `z(0,0) = 0`, `z(1,0) = 1 + B²` has centers
`z(p,q) = X + B^{2p} β^q (0 − X)` with `β = B e^{iψ}`, `ψ = psi B`; and
`ψ = θ_O − θ_{P₀}` by `psi_eq_angle_diff`. -/
theorem prop_5_4 {B : ℝ} (hB : 1 < B) {z : ℤ → ℤ → ℂ} (hz : IsConfig (rad B) z)
    (h0 : z 0 0 = 0) (h1 : z 1 0 = ((1 + B ^ 2 : ℝ) : ℂ)) :
    ∀ p q, z p q = zc B (psi B) p q :=
  rigidity hz (zc_isConfig hB) (by rw [h0, zc_zero_zero]) (by rw [h1, zc_one_zero _ hB])

end DoyleFormal
