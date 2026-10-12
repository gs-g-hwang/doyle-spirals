/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PatchGeom
import DoyleFormal.FirstOverlap

/-!
# Coherent hexagonal packings and the developing map (paper B, Theorem 7.2) — Phase 5

* `HexPacking V`: circles indexed by a type `V` (centers `c`, radii `ρ > 0`), each with a flower
  `nb v : Fin 6 → V` of six distinct petals in counterclockwise order: petals tangent to the
  center and to their neighbors, positively oriented triangles, angle sum `2π` (the flower
  wraps once), compatible links along edges, and a connected contact graph.
* `HexPacking.S`: one step of the developing map on states `(vertex, offset)`.
  `S_back`, `S_tri`, `S_tri'`: the local rules (back and forth; around a triangle).
* `HexPacking.F`: the developing map `ℤ² → V × Fin 6`, built along rows and columns, with
  `dev_step : F(u + d_i) = S(F u, i)` for all six directions. No topology is used: this is
  the combinatorial form of "the universal cover of the contact complex is the triangular
  lattice".
-/

namespace DoyleFormal

open Complex

/-- A hexagonal circle packing with closed flowers (the hypotheses of Theorem B 7.2, except
coherence and the triangle shape). -/
structure HexPacking (V : Type*) where
  c : V → ℂ
  ρ : V → ℝ
  ρ_pos : ∀ v, 0 < ρ v
  nb : V → Fin 6 → V
  tan : ∀ v i, ‖c (nb v i) - c v‖ = ρ (nb v i) + ρ v
  rim : ∀ v i, ‖c (nb v (i + 1)) - c (nb v i)‖ = ρ (nb v (i + 1)) + ρ (nb v i)
  ori : ∀ v i, 0 < orient (c v) (c (nb v i)) (c (nb v (i + 1)))
  wind : ∀ v, ∑ i : Fin 6, angleAt (ρ v) (ρ (nb v i)) (ρ (nb v (i + 1))) = 2 * Real.pi
  inj : ∀ v, Function.Injective (nb v)
  compat : ∀ v i, ∃ j, nb (nb v i) j = v ∧ nb (nb v i) (j + 5) = nb v (i + 1) ∧
    nb (nb v i) (j + 1) = nb v (i + 5)
  conn : ∀ v w, Relation.ReflTransGen (fun x y => ∃ i, y = nb x i) v w

namespace HexPacking

variable {V : Type*} (P : HexPacking V)

/-- The index of `v` in the flower of its petal `nb v m`. -/
noncomputable def J (v : V) (m : Fin 6) : Fin 6 := Classical.choose (P.compat v m)

lemma J_spec (v : V) (m : Fin 6) :
    P.nb (P.nb v m) (P.J v m) = v ∧ P.nb (P.nb v m) (P.J v m + 5) = P.nb v (m + 1) ∧
      P.nb (P.nb v m) (P.J v m + 1) = P.nb v (m + 5) :=
  Classical.choose_spec (P.compat v m)

/-- One step of the developing map in lattice direction `i` from the state `(v, k)`. -/
noncomputable def S (x : V × Fin 6) (i : Fin 6) : V × Fin 6 :=
  (P.nb x.1 (i + x.2), P.J x.1 (i + x.2) - (i + 3))

lemma fin_a (i J : Fin 6) : i + 3 + (J - (i + 3)) = J := by revert i J; decide
lemma fin_b (i m : Fin 6) : m - (i + 3 + 3) = m - i := by revert i m; decide
lemma fin_c (i J : Fin 6) : i + 2 + (J - (i + 3)) = J + 5 := by revert i J; decide
lemma fin_d (i k : Fin 6) : i + 1 + k = i + k + 1 := by revert i k; decide
lemma fin_e (m : Fin 6) : m + 1 + 5 = m := by revert m; decide
lemma fin_f (i J' : Fin 6) : J' + 1 - (i + 2 + 3) = J' - (i + 1 + 3) := by revert i J'; decide
lemma fin_g (i : Fin 6) : i + 5 + 2 = i + 1 := by revert i; decide
lemma fin_h (i : Fin 6) : i + 5 + 1 = i := by revert i; decide
lemma fin_i (i : Fin 6) : i + 1 + 3 = i + 4 := by revert i; decide
lemma fin_j (i k : Fin 6) : i + k - i = k := by revert i k; decide

/-- Back and forth. -/
theorem S_back (x : V × Fin 6) (i : Fin 6) : P.S (P.S x i) (i + 3) = x := by
  obtain ⟨v, k⟩ := x
  have hJ := P.J_spec v (i + k)
  have h1 := (P.J_spec (P.nb v (i + k)) (P.J v (i + k))).1
  rw [hJ.1] at h1
  have hJJ : P.J (P.nb v (i + k)) (P.J v (i + k)) = i + k := P.inj v h1
  simp only [S]
  rw [fin_a, hJ.1, hJJ, fin_b, fin_j]

/-- Around a triangle: `d_i + d_{i+2} = d_{i+1}`. -/
theorem S_tri (x : V × Fin 6) (i : Fin 6) : P.S (P.S x i) (i + 2) = P.S x (i + 1) := by
  obtain ⟨v, k⟩ := x
  set m := i + k with hm
  have hJ := P.J_spec v m
  simp only [S]
  rw [fin_c, hJ.2.1, fin_d, ← hm]
  -- the petal `p = nb v (m+1)` sees `w = nb v m` right after `v`
  set p := P.nb v (m + 1)
  have hJ' := P.J_spec v (m + 1)
  have hw : P.nb p (P.J v (m + 1) + 1) = P.nb v m := by
    rw [hJ'.2.2, fin_e]
  have hw' : P.nb p (P.J (P.nb v m) (P.J v m + 5)) = P.nb v m := by
    have := (P.J_spec (P.nb v m) (P.J v m + 5)).1
    rwa [hJ.2.1] at this
  have heq : P.J (P.nb v m) (P.J v m + 5) = P.J v (m + 1) + 1 := P.inj p (hw'.trans hw.symm)
  rw [heq, fin_f]

/-- Around a triangle the other way: `d_i + d_{i+4} = d_{i+5}`. -/
theorem S_tri' (y : V × Fin 6) (i : Fin 6) : P.S (P.S y i) (i + 4) = P.S y (i + 5) := by
  have h := P.S_tri y (i + 5)
  rw [fin_g, fin_h] at h
  have h2 := congrArg (fun x => P.S x (i + 1 + 3)) h
  rw [P.S_back, fin_i] at h2
  exact h2.symm

lemma S_comm01 (x : V × Fin 6) : P.S (P.S x 0) 1 = P.S (P.S x 1) 0 := by
  have h1 := P.S_tri x 0
  have h2 := P.S_tri' (P.S x 0) 2
  simp only [show (0 : Fin 6) + 2 = 2 from rfl, show (0 : Fin 6) + 1 = 1 from rfl] at h1
  simp only [show (2 : Fin 6) + 4 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl] at h2
  rw [← h1, h2]

lemma S_comm04 (x : V × Fin 6) : P.S (P.S x 0) 4 = P.S (P.S x 4) 0 := by
  have h1 := P.S_tri' x 0
  have h2 := P.S_tri x 4
  simp only [show (0 : Fin 6) + 4 = 4 from rfl, show (0 : Fin 6) + 5 = 5 from rfl] at h1
  simp only [show (4 : Fin 6) + 2 = 0 from rfl, show (4 : Fin 6) + 1 = 5 from rfl] at h2
  rw [h1, h2]

/-! ### The developing map -/

/-- The row `q = 0`. -/
noncomputable def G (x0 : V × Fin 6) (p : ℤ) : V × Fin 6 :=
  if 0 ≤ p then (fun x => P.S x 0)^[p.toNat] x0 else (fun x => P.S x 3)^[(-p).toNat] x0

/-- The developing map. -/
noncomputable def F (x0 : V × Fin 6) (p q : ℤ) : V × Fin 6 :=
  if 0 ≤ q then (fun x => P.S x 1)^[q.toNat] (P.G x0 p)
  else (fun x => P.S x 4)^[(-q).toNat] (P.G x0 p)

lemma iter_step {f g : V × Fin 6 → V × Fin 6} (hfg : ∀ x, f (g x) = x) (x0 : V × Fin 6)
    (n : ℤ) :
    (if 0 ≤ n + 1 then f^[(n + 1).toNat] x0 else g^[(-(n + 1)).toNat] x0) =
      f (if 0 ≤ n then f^[n.toNat] x0 else g^[(-n).toNat] x0) := by
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left (by omega), ite_eq_left hn, show (n + 1).toNat = n.toNat + 1 by omega,
      Function.iterate_succ_apply']
  · by_cases hn1 : n = -1
    · subst hn1
      simp only [show (-1 : ℤ) + 1 = 0 by norm_num, le_refl, ite_true, Int.toNat_zero,
        Function.iterate_zero, id_eq, show ¬ (0 : ℤ) ≤ -1 by norm_num, ite_false]
      rw [show (-(-1 : ℤ)).toNat = 0 + 1 by norm_num, Function.iterate_succ_apply',
        Function.iterate_zero, id_eq, hfg]
    · rw [ite_eq_right (by omega), ite_eq_right hn, show (-n).toNat = (-(n + 1)).toNat + 1 by omega,
        Function.iterate_succ_apply', hfg]

lemma G_succ (x0 : V × Fin 6) (p : ℤ) : P.G x0 (p + 1) = P.S (P.G x0 p) 0 :=
  iter_step (f := fun x => P.S x 0) (g := fun x => P.S x 3) (fun x => by
    simpa using P.S_back x 3) x0 p

lemma F_succ (x0 : V × Fin 6) (p q : ℤ) : P.F x0 p (q + 1) = P.S (P.F x0 p q) 1 :=
  iter_step (f := fun x => P.S x 1) (g := fun x => P.S x 4) (fun x => by
    simpa using P.S_back x 4) (P.G x0 p) q

lemma F_zero (x0 : V × Fin 6) (p : ℤ) : P.F x0 p 0 = P.G x0 p := by simp [F]

lemma back_of_succ {f : ℤ → V × Fin 6} {i : Fin 6} (h : ∀ n, f (n + 1) = P.S (f n) i)
    (n : ℤ) : f (n - 1) = P.S (f n) (i + 3) := by
  have := h (n - 1)
  rw [sub_add_cancel] at this
  rw [this, P.S_back]

lemma F_succ_p (x0 : V × Fin 6) (p q : ℤ) : P.F x0 (p + 1) q = P.S (P.F x0 p q) 0 := by
  induction q using Int.induction_on with
  | zero => rw [F_zero, F_zero, G_succ]
  | succ n ih => rw [F_succ, F_succ, ih, S_comm01]
  | pred n ih =>
    have h1 := P.back_of_succ (f := fun q => P.F x0 (p + 1) q) (i := 1)
      (fun q => P.F_succ x0 (p + 1) q) (-(n : ℤ))
    have h2 := P.back_of_succ (f := fun q => P.F x0 p q) (i := 1)
      (fun q => P.F_succ x0 p q) (-(n : ℤ))
    rw [show (1 : Fin 6) + 3 = 4 from rfl] at h1 h2
    rw [h1, ih, h2, S_comm04]

/-- **The developing map.** `F(u + d_i) = S(F u, i)` in all six directions. -/
theorem dev_step (x0 : V × Fin 6) (u : ℤ × ℤ) (i : Fin 6) :
    P.F x0 (u + ldir i).1 (u + ldir i).2 = P.S (P.F x0 u.1 u.2) i := by
  obtain ⟨p, q⟩ := u
  have hp := P.F_succ_p x0
  have hq := P.F_succ x0
  have hp' : ∀ p q, P.F x0 (p - 1) q = P.S (P.F x0 p q) 3 := fun p q =>
    P.back_of_succ (f := fun p => P.F x0 p q) (i := 0) (fun p => hp p q) p
  have hq' : ∀ p q, P.F x0 p (q - 1) = P.S (P.F x0 p q) 4 := fun p q =>
    P.back_of_succ (f := fun q => P.F x0 p q) (i := 1) (fun q => hq p q) q
  have e0 : (p, q) + ldir 0 = (p + 1, q) := by simp [ldir]
  have e1 : (p, q) + ldir 1 = (p, q + 1) := by simp [ldir]
  have e2 : (p, q) + ldir 2 = (p - 1, q + 1) := by simp [ldir, sub_eq_add_neg]
  have e3 : (p, q) + ldir 3 = (p - 1, q) := by simp [ldir, sub_eq_add_neg]
  have e4 : (p, q) + ldir 4 = (p, q - 1) := by simp [ldir, sub_eq_add_neg]
  have e5 : (p, q) + ldir 5 = (p + 1, q - 1) := by simp [ldir, sub_eq_add_neg]
  fin_cases i
  · change P.F x0 ((p, q) + ldir 0).1 ((p, q) + ldir 0).2 = P.S (P.F x0 p q) 0
    rw [e0]; exact hp p q
  · change P.F x0 ((p, q) + ldir 1).1 ((p, q) + ldir 1).2 = P.S (P.F x0 p q) 1
    rw [e1]; exact hq p q
  · -- `d_2 = d_3 + d_1`
    change P.F x0 ((p, q) + ldir 2).1 ((p, q) + ldir 2).2 = P.S (P.F x0 p q) 2
    rw [e2, hq, hp']
    have := P.S_tri' (P.F x0 p q) 3
    rwa [show (3 : Fin 6) + 4 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl] at this
  · change P.F x0 ((p, q) + ldir 3).1 ((p, q) + ldir 3).2 = P.S (P.F x0 p q) 3
    rw [e3]; exact hp' p q
  · change P.F x0 ((p, q) + ldir 4).1 ((p, q) + ldir 4).2 = P.S (P.F x0 p q) 4
    rw [e4]; exact hq' p q
  · -- `d_5 = d_0 + d_4`
    change P.F x0 ((p, q) + ldir 5).1 ((p, q) + ldir 5).2 = P.S (P.F x0 p q) 5
    rw [e5, hq', hp]
    have := P.S_tri' (P.F x0 p q) 0
    rwa [show (0 : Fin 6) + 4 = 4 from rfl, show (0 : Fin 6) + 5 = 5 from rfl] at this

end HexPacking

/-! ### The developed configuration -/

/-- Radii of a configuration are determined by its centers. -/
lemma radii_unique {r r' : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (h : IsConfig r z) (h' : IsConfig r' z)
    (p q : ℤ) : r p q = r' p q := by
  have a := h.t10 p q; have b := h.t01 p q; have c := h.tm11 (p + 1) q
  have a' := h'.t10 p q; have b' := h'.t01 p q; have c' := h'.tm11 (p + 1) q
  rw [add_sub_cancel_right] at c c'
  linarith

lemma latRot_iter_six (u : ℤ × ℤ) : latRot^[6] u = u := by
  obtain ⟨p, q⟩ := u
  simp [Function.iterate_succ, latRot]

namespace HexPacking

variable {V : Type*} (P : HexPacking V) (x0 : V × Fin 6)

/-- Developed centers and radii. -/
noncomputable def zD (p q : ℤ) : ℂ := P.c (P.F x0 p q).1
noncomputable def rD (p q : ℤ) : ℝ := P.ρ (P.F x0 p q).1

lemma fin_k (k : Fin 6) : 0 + k + 1 = 1 + k := by revert k; decide
lemma fin_l (k : Fin 6) : 1 + k + 1 = 2 + k := by revert k; decide
lemma fin_m (i k : Fin 6) : i + 1 + k = i + k + 1 := by revert i k; decide

lemma F_dir (p q : ℤ) :
    P.F x0 (p + 1) q = P.S (P.F x0 p q) 0 ∧ P.F x0 p (q + 1) = P.S (P.F x0 p q) 1 ∧
      P.F x0 (p - 1) (q + 1) = P.S (P.F x0 p q) 2 := by
  refine ⟨P.F_succ_p x0 p q, P.F_succ x0 p q, ?_⟩
  have := P.dev_step x0 (p, q) 2
  rwa [show (p, q) + ldir 2 = (p - 1, q + 1) by simp [ldir, sub_eq_add_neg]] at this

/-- The developed family is a configuration (Definition A 2.1). -/
theorem isConfig_dev : IsConfig (P.rD x0) (P.zD x0) where
  t10 p q := by
    simp only [zD, rD]; rw [(P.F_dir x0 p q).1]; exact P.tan _ _
  t01 p q := by
    simp only [zD, rD]; rw [(P.F_dir x0 p q).2.1]; exact P.tan _ _
  tm11 p q := by
    simp only [zD, rD]; rw [(P.F_dir x0 p q).2.2]; exact P.tan _ _
  up p q := by
    simp only [zD]; rw [(P.F_dir x0 p q).1, (P.F_dir x0 p q).2.1]
    simp only [S]; rw [← fin_k]; exact P.ori _ _
  down p q := by
    simp only [zD]; rw [(P.F_dir x0 p q).2.1, (P.F_dir x0 p q).2.2]
    simp only [S]; rw [← fin_l]; exact P.ori _ _

lemma dev_nb (u : ℤ × ℤ) (i : Fin 6) :
    (P.F x0 (u + ldir i).1 (u + ldir i).2).1 =
      P.nb (P.F x0 u.1 u.2).1 (i + (P.F x0 u.1 u.2).2) := by
  rw [P.dev_step]; rfl

/-- The developed radii have closing flowers. -/
theorem locUniv_dev : LocUniv (P.rD x0) := by
  intro u
  simp only [rD, P.dev_nb x0, fin_m]
  set v := (P.F x0 u.1 u.2).1
  set k := (P.F x0 u.1 u.2).2
  rw [← P.wind v]
  exact Equiv.sum_comp (Equiv.addRight k)
    (fun j => angleAt (P.ρ v) (P.ρ (P.nb v j)) (P.ρ (P.nb v (j + 1))))

/-- All center triangles of the packing are similar to the triangle of centers of a tangent
triple with radii `(a, b, c)`. -/
def SimShape (a b c : ℝ) : Prop :=
  ∀ v i, ∃ μ > 0, ∃ x y w, (x, y, w) ∈ perms3 a b c ∧
    ‖P.c (P.nb v i) - P.c (P.nb v (i + 1))‖ = μ * (y + w) ∧
    ‖P.c (P.nb v (i + 1)) - P.c v‖ = μ * (w + x) ∧ ‖P.c v - P.c (P.nb v i)‖ = μ * (x + y)

lemma simCenters_dev {a b c : ℝ} (h : P.SimShape a b c) : SimCenters (P.zD x0) a b c := by
  intro u i
  obtain ⟨μ, hμ, x, y, w, hm, h1, h2, h3⟩ := h (P.F x0 u.1 u.2).1 (i + (P.F x0 u.1 u.2).2)
  refine ⟨μ, hμ, x, y, w, hm, ?_, ?_, ?_⟩ <;> simp only [zD, P.dev_nb x0, fin_m]
  · exact h1
  · exact h2
  · exact h3

/-- Every circle of a connected packing is developed. -/
lemma dev_surj (v0 w : V) : ∃ u : ℤ × ℤ, (P.F (v0, 0) u.1 u.2).1 = w := by
  induction P.conn v0 w with
  | refl => exact ⟨(0, 0), by simp [F, G]⟩
  | tail _ hst ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨i, rfl⟩ := hst
    refine ⟨u + ldir (i - (P.F (v0, 0) u.1 u.2).2), ?_⟩
    rw [P.dev_nb, sub_add_cancel, hu]

end HexPacking

/-! ### Theorem B 7.2 -/

/-- **Theorem B 7.2 (classification).** Let `P` be a coherent hexagonal circle packing
(`HexPacking` with pairwise disjoint interiors) all of whose center triangles are similar to
one triangle. Then, up to a direct similarity, the circles of `P` are circles of the regular
packing, or circles of `D_{B_n}` for some `n ≥ 2` (`ψ(B_n) = π/n`). -/
theorem coherent_classification {V : Type*} (P : HexPacking V) (v0 : V)
    (hcoh : ∀ v w, v ≠ w → P.ρ v + P.ρ w ≤ ‖P.c v - P.c w‖) {a b c : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hsim : P.SimShape a b c) :
    (∃ α β : ℂ, α ≠ 0 ∧ ∀ v, ∃ p q : ℤ, P.c v = α * zreg 1 p q + β ∧ P.ρ v = ‖α‖) ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ B > 1, psi B = Real.pi / n ∧ ∃ α β : ℂ, α ≠ 0 ∧ ∀ v, ∃ p q : ℤ,
        P.c v = α * zc B (psi B) p q + β ∧ P.ρ v = ‖α‖ * rad B p q := by
  set x0 : V × Fin 6 := (v0, 0)
  have hz := P.isConfig_dev x0
  have hr : ∀ p q, 0 < P.rD x0 p q := fun p q => P.ρ_pos _
  rcases oneshape_config ha hb hc hz hr (P.locUniv_dev x0) (P.simCenters_dev x0 hsim) with
    ⟨α, β, hα, hreg⟩ | ⟨B, hB, j, hj, α, β, hα, hD⟩
  · -- the regular case
    left
    refine ⟨α, β, hα, fun v => ?_⟩
    obtain ⟨⟨p, q⟩, hu⟩ := P.dev_surj v0 v
    have hfun : P.zD x0 = fun p q => α * zreg 1 p q + β := by funext p q; exact hreg p q
    have hc2 := (zreg_isConfig one_pos).affine hα β
    rw [← hfun] at hc2
    have hrad := radii_unique hz hc2 p q
    refine ⟨p, q, ?_, ?_⟩
    · rw [← hu]; exact hreg p q
    · rw [← hu]; simpa [HexPacking.rD] using hrad
  · -- the spiral case
    right
    have hB0 : 0 < B := by linarith
    have hrot := hz.rot_iter j
    have hfun : (fun p q => P.zD x0 (latRot^[j] (p, q)).1 (latRot^[j] (p, q)).2) =
        fun p q => α * zc B (psi B) p q + β := by funext p q; exact hD p q
    rw [hfun] at hrot
    have hc2 := (zc_isConfig hB).affine hα β
    have hrad : ∀ p q, P.rD x0 (latRot^[j] (p, q)).1 (latRot^[j] (p, q)).2 =
        ‖α‖ * rad B p q := fun p q => radii_unique hrot hc2 p q
    have hα0 : 0 < ‖α‖ := norm_pos_iff.2 hα
    -- no two circles of `D_B` overlap
    have hno : ∀ m, ¬ OverlapWithin B m := by
      rintro m ⟨p, q, p', q', -, -, -, hns, hov⟩
      set v := (P.F x0 (latRot^[j] (p, q)).1 (latRot^[j] (p, q)).2).1
      set v' := (P.F x0 (latRot^[j] (p', q')).1 (latRot^[j] (p', q')).2).1
      have hzc : P.c v = α * zc B (psi B) p q + β := hD p q
      have hzc' : P.c v' = α * zc B (psi B) p' q' + β := hD p' q'
      have hρ : P.ρ v = ‖α‖ * rad B p q := hrad p q
      have hρ' : P.ρ v' = ‖α‖ * rad B p' q' := hrad p' q'
      by_cases hvv : v' = v
      · apply hns
        rw [hvv] at hzc' hρ'
        refine ⟨?_, ?_⟩
        · exact (mul_left_cancel₀ hα0.ne' (hρ'.symm.trans hρ))
        · have := hzc'.symm.trans hzc
          exact mul_left_cancel₀ hα (add_right_cancel this)
      · have h := hcoh v' v hvv
        rw [hzc, hzc', hρ, hρ', show α * zc B (psi B) p' q' + β - (α * zc B (psi B) p q + β) =
          α * (zc B (psi B) p' q' - zc B (psi B) p q) by ring, norm_mul] at h
        have : ‖α‖ * (rad B p' q' + rad B p q) ≤
            ‖α‖ * ‖zc B (psi B) p' q' - zc B (psi B) p q‖ := by linarith
        have := le_of_mul_le_mul_left this hα0
        linarith
    -- hence `B` is resonant
    have hfr : Int.fract (Real.pi / psi B) = 0 := by
      by_contra h
      exact hno _ (overlap_at_mFirst hB (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h)))
    have hψ := psi_mem_Ioo hB
    have ht1 : 1 < Real.pi / psi B := by rw [one_lt_div hψ.1]; exact hψ.2
    have hfl : Real.pi / psi B = ⌊Real.pi / psi B⌋ := by
      have := Int.self_sub_floor (Real.pi / psi B)
      rw [hfr] at this; linarith
    set N := ⌊Real.pi / psi B⌋ with hN
    have hN2 : 2 ≤ N := by
      have : (1 : ℝ) < N := by rw [← hfl]; exact ht1
      exact_mod_cast this
    refine ⟨N.toNat, by omega, B, hB, ?_, α, β, hα, fun v => ?_⟩
    · have hNc : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      rw [hNc, ← hfl]; field_simp
    · obtain ⟨u', hu'⟩ := P.dev_surj v0 v
      set u := latRot^[6 - j] u'
      have hju : latRot^[j] u = u' := by
        rw [← Function.iterate_add_apply, show j + (6 - j) = 6 by omega, latRot_iter_six]
      refine ⟨u.1, u.2, ?_, ?_⟩
      · rw [← hu', ← hju]; exact hD u.1 u.2
      · rw [← hu', ← hju]; exact hrad u.1 u.2

/-! ### Non-vacuity: the regular packing is a coherent `HexPacking` -/

lemma ldir_inj : Function.Injective ldir := by decide

lemma angleAt_one : angleAt 1 1 1 = Real.pi / 3 := by
  have := angle_sum (x := 1) (y := 1) (z := 1) one_pos one_pos one_pos
  linarith

lemma ldir_add_four (j : Fin 6) : ldir j + ldir (j + 4) = ldir (j + 5) := by
  fin_cases j <;> decide

/-- The regular packing as a `HexPacking` on `ℤ²`. -/
noncomputable def regularHex : HexPacking (ℤ × ℤ) where
  c u := zreg 1 u.1 u.2
  ρ _ := 1
  ρ_pos _ := one_pos
  nb u i := u + ldir i
  tan u i := (zreg_isConfig one_pos).edge u i
  rim u i := by
    have h := (zreg_isConfig one_pos).edge (u + ldir i) (i + 2)
    rwa [ldir_succ_eq] at h
  ori u i := by
    have h := (zreg_isConfig one_pos).orient_pos u (ldir i) (by fin_cases i <;> simp [ldir, IsDir])
    rwa [rotp_ldir] at h
  wind u := by simp [angleAt_one]; ring
  inj u := fun i j h => ldir_inj (add_left_cancel h)
  compat u i := ⟨i + 3, by rw [add_assoc, ldir_add_three, add_zero],
    by rw [add_assoc, show i + 3 + 5 = i + 2 by revert i; decide, ldir_add_two],
    by rw [add_assoc, show i + 3 + 1 = i + 4 by revert i; decide, ldir_add_four]⟩
  conn u w := by
    -- move along the first coordinate, then the second
    have hstep : ∀ (x : ℤ × ℤ) (d : ℤ × ℤ), (∃ i, d = ldir i) →
        Relation.ReflTransGen (fun x y => ∃ i, y = x + ldir i) x (x + d) := by
      rintro x d ⟨i, rfl⟩
      exact Relation.ReflTransGen.single ⟨i, rfl⟩
    have hline : ∀ (x : ℤ × ℤ) (d : ℤ × ℤ) (hd : ∃ i, d = ldir i) (hd' : ∃ i, -d = ldir i)
        (n : ℤ), Relation.ReflTransGen (fun x y => ∃ i, y = x + ldir i) x (x + n • d) := by
      intro x d hd hd' n
      induction n using Int.induction_on with
      | zero => simp only [zero_smul, add_zero]; exact Relation.ReflTransGen.refl
      | succ m ih =>
        refine ih.trans ?_
        rw [add_smul, one_smul, ← add_assoc]
        exact hstep _ d hd
      | pred m ih =>
        refine ih.trans ?_
        rw [sub_smul, one_smul, sub_eq_add_neg, ← add_assoc]
        exact hstep _ (-d) hd'
    have h1 := hline u (1, 0) ⟨0, rfl⟩ ⟨3, rfl⟩ (w.1 - u.1)
    have h2 := hline (u + (w.1 - u.1) • ((1 : ℤ), (0 : ℤ))) (0, 1) ⟨1, rfl⟩ ⟨4, rfl⟩ (w.2 - u.2)
    have hw : u + (w.1 - u.1) • ((1 : ℤ), (0 : ℤ)) + (w.2 - u.2) • ((0 : ℤ), (1 : ℤ)) = w := by
      ext <;> simp
    rw [hw] at h2
    exact h1.trans h2

/-- The regular packing is coherent. -/
theorem regularHex_coherent (v w : ℤ × ℤ) (h : v ≠ w) :
    regularHex.ρ v + regularHex.ρ w ≤ ‖regularHex.c v - regularHex.c w‖ := by
  simp only [regularHex]
  obtain ⟨p, q⟩ := v; obtain ⟨p', q'⟩ := w
  set a := p - p'; set b := q - q'
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc; push Not at hc
    exact h (by ext <;> simp <;> omega)
  have hsq : 4 ≤ ‖zreg 1 p q - zreg 1 p' q'‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [zreg, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, omega6, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
      Complex.im_ofNat]
    have h3 : √3 ^ 2 = 3 := sqrt3_sq
    have key : (1 : ℝ) ≤ (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ a ^ 2 + a * b + b ^ 2 := by
        rcases hab with ha | hb
        · nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_pos_of_ne_zero ha]
        · nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_pos_of_ne_zero hb]
      exact_mod_cast this
    simp only [a, b] at key
    push_cast at key
    nlinarith [key]
  nlinarith [norm_nonneg (zreg 1 p q - zreg 1 p' q')]

end DoyleFormal
