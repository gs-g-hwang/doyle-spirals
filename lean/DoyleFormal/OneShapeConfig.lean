/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.OneShapeRadii

/-!
# Theorem A 8.1 for configurations — Phase 4p

* `simCenters_oneShape` (Lemma A 3.3): if every center triangle of a configuration is similar
  to the triangle of centers of a tangent triple with radii `(a, b, c)`, then the radii of
  every center triangle are proportional to `(a, b, c)` in the matching order (`OneShape`).
* `IsConfig.rot`, `IsConfig.rot_iter`: relabeling by the lattice rotation
  `R(p,q) = (−q, p+q)` (a direct lattice automorphism) gives a configuration.
* `IsConfig.affine`: a direct similarity `z ↦ α z + β` gives a configuration.
* `zreg_isConfig`: the regular packing `zreg c (p,q) = 2c (p + q ω)`.
* `oneshape_config` (**Theorem A 8.1**): a configuration with closing flowers whose center
  triangles all have one shape is, up to a direct similarity, the regular packing, or, after
  a lattice rotation `R^j` and a direct similarity, `D_B` for some `B > 1`.
-/

namespace DoyleFormal

open Complex

/-! ### Lemma A 3.3: similar center triangles have proportional radii -/

/-- Every center triangle `u, u+d_i, u+d_{i+1}` is similar to the triangle of centers of a
tangent triple with radii `(a, b, c)` (sides `b+c, c+a, a+b`), with some vertex matching. -/
def SimCenters (z : ℤ → ℤ → ℂ) (a b c : ℝ) : Prop :=
  ∀ u : ℤ × ℤ, ∀ i : Fin 6, ∃ μ > 0, ∃ x y w, (x, y, w) ∈ perms3 a b c ∧
    ‖z (u + ldir i).1 (u + ldir i).2 - z (u + ldir (i + 1)).1 (u + ldir (i + 1)).2‖ =
      μ * (y + w) ∧
    ‖z (u + ldir (i + 1)).1 (u + ldir (i + 1)).2 - z u.1 u.2‖ = μ * (w + x) ∧
    ‖z u.1 u.2 - z (u + ldir i).1 (u + ldir i).2‖ = μ * (x + y)

theorem simCenters_oneShape {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} {a b c : ℝ}
    (hz : IsConfig r z) (hs : SimCenters z a b c) : OneShape r a b c := by
  intro u i
  obtain ⟨μ, hμ, x, y, w, hm, h1, h2, h3⟩ := hs u i
  have e1 := hz.edge u i
  have e2 := hz.edge u (i + 1)
  have e3 := hz.edge (u + ldir i) (i + 2)
  rw [ldir_succ_eq] at e3
  rw [norm_sub_rev] at h1 h3
  rw [e3] at h1
  rw [e2] at h2
  rw [e1] at h3
  have := (sides_prop_iff μ x y w (Rr r u) (Rr r (u + ldir i)) (Rr r (u + ldir (i + 1)))).1
    ⟨by unfold Rr; linarith, by unfold Rr; linarith, by unfold Rr; linarith⟩
  refine simTriple_iff.2 ⟨μ, hμ, x, y, w, hm, this.1, this.2.1, this.2.2⟩

/-! ### Lattice rotation -/

/-- The lattice rotation by `60°`: `R(p,q) = (−q, p+q)`. -/
def latRot (u : ℤ × ℤ) : ℤ × ℤ := (-u.2, u.1 + u.2)

theorem IsConfig.rot {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z) :
    IsConfig (fun p q => r (latRot (p, q)).1 (latRot (p, q)).2)
      (fun p q => z (latRot (p, q)).1 (latRot (p, q)).2) where
  t10 p q := by
    simp only [latRot]
    rw [show p + 1 + q = p + q + 1 by ring]
    exact hz.t01 (-q) (p + q)
  t01 p q := by
    simp only [latRot]
    have h := hz.tm11 (-q) (p + q)
    rw [show -q - 1 = -(q + 1) by ring, show p + q + 1 = p + (q + 1) by ring] at h
    exact h
  tm11 p q := by
    simp only [latRot]
    have h := hz.t10 (-(q + 1)) (p + q)
    rw [show -(q + 1) + 1 = -q by ring] at h
    rw [show p - 1 + (q + 1) = p + q by ring, norm_sub_rev, h, add_comm]
  up p q := by
    simp only [latRot]
    have h := hz.down (-q) (p + q)
    rw [show -q - 1 = -(q + 1) by ring, show p + q + 1 = p + (q + 1) by ring] at h
    rw [show p + 1 + q = p + q + 1 by ring]
    convert h using 3; ring_nf
  down p q := by
    simp only [latRot]
    have h := hz.orient_pos (-q, p + q) (-1, 1) (by unfold IsDir; simp)
    simp only [rotp, Prod.mk_add_mk] at h
    convert h using 2 <;> congr 1 <;> ring

theorem IsConfig.rot_iter {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z) (j : ℕ) :
    IsConfig (fun p q => r (latRot^[j] (p, q)).1 (latRot^[j] (p, q)).2)
      (fun p q => z (latRot^[j] (p, q)).1 (latRot^[j] (p, q)).2) := by
  induction j with
  | zero => simpa using hz
  | succ n ih =>
    have h := ih.rot
    simp only [Function.iterate_succ_apply] at h ⊢
    exact h

/-! ### Similarity -/

lemma orient_affine (α β a b c : ℂ) :
    orient (α * a + β) (α * b + β) (α * c + β) = Complex.normSq α * orient a b c := by
  simp only [orient_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

theorem IsConfig.affine {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z) {α : ℂ}
    (hα : α ≠ 0) (β : ℂ) :
    IsConfig (fun p q => ‖α‖ * r p q) (fun p q => α * z p q + β) where
  t10 p q := by
    rw [show α * z (p + 1) q + β - (α * z p q + β) = α * (z (p + 1) q - z p q) by ring,
      norm_mul, hz.t10]; ring
  t01 p q := by
    rw [show α * z p (q + 1) + β - (α * z p q + β) = α * (z p (q + 1) - z p q) by ring,
      norm_mul, hz.t01]; ring
  tm11 p q := by
    rw [show α * z (p - 1) (q + 1) + β - (α * z p q + β) =
      α * (z (p - 1) (q + 1) - z p q) by ring, norm_mul, hz.tm11]; ring
  up p q := by
    rw [orient_affine]; exact mul_pos (Complex.normSq_pos.2 hα) (hz.up p q)
  down p q := by
    rw [orient_affine]; exact mul_pos (Complex.normSq_pos.2 hα) (hz.down p q)

/-! ### The regular packing -/

/-- `ω = e^{iπ/3}`. -/
noncomputable def omega6 : ℂ := ⟨1 / 2, √3 / 2⟩

/-- The regular packing with radius `c`. -/
noncomputable def zreg (c : ℝ) (p q : ℤ) : ℂ := 2 * c * (p + q * omega6)

lemma sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma norm_eq_of_normSq {w : ℂ} {t : ℝ} (ht : 0 ≤ t) (h : Complex.normSq w = t ^ 2) :
    ‖w‖ = t := by
  exact (pow_left_inj₀ (norm_nonneg _) ht two_ne_zero).1 (by rw [← Complex.normSq_eq_norm_sq, h])

theorem zreg_isConfig {c : ℝ} (hc : 0 < c) : IsConfig (fun _ _ => c) (zreg c) where
  t10 p q := by
    apply norm_eq_of_normSq (by linarith)
    simp only [zreg, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, omega6, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
      Complex.im_ofNat]
    push_cast; ring
  t01 p q := by
    apply norm_eq_of_normSq (by linarith)
    simp only [zreg, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, omega6, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
      Complex.im_ofNat]
    push_cast; ring_nf; rw [sqrt3_sq]; ring
  tm11 p q := by
    apply norm_eq_of_normSq (by linarith)
    simp only [zreg, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, omega6, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
      Complex.im_ofNat]
    push_cast; ring_nf; rw [sqrt3_sq]; ring
  up p q := by
    simp only [orient_eq, zreg, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, omega6, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    have h3 : 0 < √3 := by positivity
    nlinarith [mul_pos (mul_pos hc hc) h3]
  down p q := by
    simp only [orient_eq, zreg, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, omega6, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    have h3 : 0 < √3 := by positivity
    nlinarith [mul_pos (mul_pos hc hc) h3]

/-! ### Identification by rigidity -/

/-- A configuration is the image of another one with the same radii up to the factor
`‖α‖ = κ` under the direct similarity that matches `(0,0)` and `(1,0)`. -/
lemma similar_of_rigidity {r : ℤ → ℤ → ℝ} {z w : ℤ → ℤ → ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hz : IsConfig (fun p q => κ * r p q) z) (hw : IsConfig r w) (hr : ∀ p q, 0 < r p q) :
    ∃ α β : ℂ, α ≠ 0 ∧ ∀ p q, z p q = α * w p q + β := by
  have hw0 : w 1 0 - w 0 0 ≠ 0 := by
    intro h
    have e := hw.t10 0 0
    simp only [zero_add] at e
    rw [h, norm_zero] at e
    linarith [hr 1 0, hr 0 0]
  set α := (z 1 0 - z 0 0) / (w 1 0 - w 0 0) with hαdef
  have hzn : ‖z 1 0 - z 0 0‖ = κ * (r 1 0 + r 0 0) := by
    have e := hz.t10 0 0
    simp only [zero_add] at e
    rw [e]; ring
  have hwn : ‖w 1 0 - w 0 0‖ = r 1 0 + r 0 0 := by
    have e := hw.t10 0 0
    simpa using e
  have hαn : ‖α‖ = κ := by
    have hpos : (0 : ℝ) < r 1 0 + r 0 0 := by linarith [hr 1 0, hr 0 0]
    rw [hαdef, norm_div, hzn, hwn, mul_div_assoc, div_self hpos.ne', mul_one]
  have hα : α ≠ 0 := by
    intro h; rw [h, norm_zero] at hαn; linarith
  refine ⟨α, z 0 0 - α * w 0 0, hα, ?_⟩
  have hs := hw.affine hα (z 0 0 - α * w 0 0)
  rw [hαn] at hs
  have := rigidity hz hs (by ring) (by rw [hαdef]; field_simp; ring)
  exact this

/-- **Theorem A 8.1.** Let `z` be a configuration with radii `r > 0` whose flowers close up
(`LocUniv`, Definition A 2.1) and whose center triangles are all similar to one triangle
(`SimCenters`). Then either `z` is a direct similar image of the regular packing, or there
are `B > 1` and a lattice rotation `R^j` (`j < 6`) such that `z ∘ R^j` is a direct similar
image of `D_B`. -/
theorem oneshape_config {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} {a b c : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hz : IsConfig r z) (hr : ∀ p q, 0 < r p q)
    (hloc : LocUniv r) (hs : SimCenters z a b c) :
    (∃ α β : ℂ, α ≠ 0 ∧ ∀ p q, z p q = α * zreg 1 p q + β) ∨
      ∃ B > 1, ∃ j : ℕ, j < 6 ∧ ∃ α β : ℂ, α ≠ 0 ∧ ∀ p q,
        z (latRot^[j] (p, q)).1 (latRot^[j] (p, q)).2 = α * zc B (psi B) p q + β := by
  rcases oneshape_radii ha hb hc hloc (simCenters_oneShape hz hs) with hreg | ⟨B, hB, k, hk⟩
  · -- the regular case: `r` is constant
    left
    have e0 : ∀ p q : ℤ, (p, q) + ldir 0 = (p + 1, q) := fun p q => by simp [ldir]
    have e1 : ∀ p q : ℤ, (p, q) + ldir 1 = (p, q + 1) := fun p q => by simp [ldir]
    have e3 : ∀ p q : ℤ, (p, q) + ldir 3 = (p - 1, q) := fun p q => by
      simp [ldir, sub_eq_add_neg]
    have e4 : ∀ p q : ℤ, (p, q) + ldir 4 = (p, q - 1) := fun p q => by
      simp [ldir, sub_eq_add_neg]
    have hrow : ∀ p : ℤ, r p 0 = r 0 0 := by
      intro p
      induction p using Int.induction_on with
      | zero => rfl
      | succ n ih =>
        have := hreg (n, 0) 0; rw [e0] at this; exact this.trans ih
      | pred n ih =>
        have := hreg (-(n : ℤ), 0) 3; rw [e3] at this; exact this.trans ih
    have hconst : ∀ p q : ℤ, r p q = r 0 0 := by
      intro p q
      induction q using Int.induction_on with
      | zero => exact hrow p
      | succ n ih =>
        have := hreg (p, n) 1; rw [e1] at this; exact this.trans ih
      | pred n ih =>
        have := hreg (p, -(n : ℤ)) 4; rw [e4] at this; exact this.trans ih
    have hz' : IsConfig (fun p q => r 0 0 * (fun _ _ => (1 : ℝ)) p q) z := by
      have : (fun p q => r 0 0 * (fun _ _ => (1 : ℝ)) p q) = r := by
        funext p q; simp [hconst p q]
      rw [this]; exact hz
    exact similar_of_rigidity (hr 0 0) hz' (zreg_isConfig one_pos) (fun _ _ => one_pos)
  · -- the spiral case: rotate the gradient to `(2, 1)`
    right
    refine ⟨B, hB, k.val, k.isLt, ?_⟩
    have hrot := hz.rot_iter k.val
    have hB0 : 0 < B := by linarith
    have hrad : (fun p q => r (latRot^[k.val] (p, q)).1 (latRot^[k.val] (p, q)).2) =
        fun p q => r 0 0 * rad B p q := by
      funext p q
      rw [hk]
      unfold rad
      congr 2
      fin_cases k <;> simp [Function.iterate_succ, latRot, Ppat] <;> ring
    rw [hrad] at hrot
    exact similar_of_rigidity (hr 0 0) hrot (zc_isConfig hB) (fun p q => by
      unfold rad; positivity)

end DoyleFormal
