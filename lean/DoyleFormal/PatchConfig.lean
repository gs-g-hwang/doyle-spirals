/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PatchOneShape

/-!
# Remark A 8.2 for configurations: rigidity on a patch — Phase 4s

* `IsConfigOn m r z`: Definition A 2.1 on the `m`-ring patch, stated through the flowers of the
  interior vertices (`‖u‖ ≤ m − 1`): tangency along the six spokes and the six rim edges, and
  positively oriented center triangles. Every edge of the patch lies in such a flower
  (`edge_interior`). A configuration on the whole lattice restricts to one
  (`IsConfig.isConfigOn`).
* `flower_all`: agreement at an interior vertex and one neighbor gives agreement on its flower.
* `patch_rigidity` (Lemma A 2.2 on a patch): two patch configurations with the same radii that
  agree at `0` and `d_0` agree on the whole patch.
* `IsConfigOn.affine`, `IsConfigOn.rot_iter`: direct similarities and lattice rotations.
* `oneshape_patch_config` (**Remark A 8.2**): for `m ≥ 2`, a patch configuration whose interior
  flowers close up and whose interior triangles all have one shape is a piece of a similar
  copy of the regular packing, or, after a lattice rotation, of `D_B` for some `B > 1`.
-/

namespace DoyleFormal

open Complex

/-- Centers on `ℤ × ℤ`. -/
def Zz (z : ℤ → ℤ → ℂ) (u : ℤ × ℤ) : ℂ := z u.1 u.2

/-- **Definition A 2.1 on the `m`-ring patch**, through the flowers of the interior vertices. -/
def IsConfigOn (m : ℤ) (r : ℤ → ℤ → ℝ) (z : ℤ → ℤ → ℂ) : Prop :=
  ∀ u, InBall (m - 1) u →
    (∀ i : Fin 6, ‖Zz z (u + ldir i) - Zz z u‖ = Rr r (u + ldir i) + Rr r u) ∧
    (∀ i : Fin 6, ‖Zz z (u + ldir (i + 1)) - Zz z (u + ldir i)‖ =
      Rr r (u + ldir (i + 1)) + Rr r (u + ldir i)) ∧
    (∀ i : Fin 6, 0 < orient (Zz z u) (Zz z (u + ldir i)) (Zz z (u + ldir (i + 1))))

lemma inBall_nbr {m : ℤ} {u : ℤ × ℤ} (hu : InBall (m - 1) u) (i : Fin 6) :
    InBall m (u + ldir i) := by
  obtain ⟨p, q⟩ := u; unfold InBall at *
  fin_cases i <;> simp only [ldir] at * <;> simp at * <;> omega

lemma rotp_ldir (i : Fin 6) : rotp (ldir i) = ldir (i + 1) := by fin_cases i <;> decide

theorem IsConfig.isConfigOn {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z) (m : ℤ) :
    IsConfigOn m r z := by
  intro u _
  refine ⟨fun i => hz.edge u i, fun i => ?_, fun i => ?_⟩
  · have h := hz.edge (u + ldir i) (i + 2)
    rw [ldir_succ_eq] at h
    exact h
  · have h := hz.orient_pos u (ldir i) (by fin_cases i <;> simp [ldir, IsDir])
    rw [rotp_ldir] at h
    exact h

section Patch

variable {m : ℤ} {r : ℤ → ℤ → ℝ} {z w : ℤ → ℤ → ℂ}

lemma flower_step (hz : IsConfigOn m r z) (hw : IsConfigOn m r w) {u : ℤ × ℤ}
    (hu : InBall (m - 1) u) (i : Fin 6) (h0 : Zz z u = Zz w u)
    (h1 : Zz z (u + ldir i) = Zz w (u + ldir i)) :
    Zz z (u + ldir (i + 1)) = Zz w (u + ldir (i + 1)) := by
  obtain ⟨ez, cz, oz⟩ := hz u hu
  obtain ⟨ew, cw, ow⟩ := hw u hu
  exact (tri_agree (by rw [ez, ew]) (by rw [cz, cw]) (by rw [ez, ew]) (oz i) (ow i)).1 h0 h1

lemma flower_all (hz : IsConfigOn m r z) (hw : IsConfigOn m r w) {u : ℤ × ℤ}
    (hu : InBall (m - 1) u) (i : Fin 6) (h0 : Zz z u = Zz w u)
    (h1 : Zz z (u + ldir i) = Zz w (u + ldir i)) (j : Fin 6) :
    Zz z (u + ldir j) = Zz w (u + ldir j) := by
  have s1 := flower_step hz hw hu i h0 h1
  have s2 := flower_step hz hw hu _ h0 s1
  have s3 := flower_step hz hw hu _ h0 s2
  have s4 := flower_step hz hw hu _ h0 s3
  have s5 := flower_step hz hw hu _ h0 s4
  have hj : j = i ∨ j = i + 1 ∨ j = i + 1 + 1 ∨ j = i + 1 + 1 + 1 ∨ j = i + 1 + 1 + 1 + 1 ∨
      j = i + 1 + 1 + 1 + 1 + 1 := by
    clear s1 s2 s3 s4 s5 h1
    fin_cases i <;> fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **Lemma A 2.2 on a patch.** -/
theorem patch_rigidity (hm : 1 ≤ m) (hz : IsConfigOn m r z) (hw : IsConfigOn m r w)
    (h0 : Zz z 0 = Zz w 0) (h1 : Zz z (0 + ldir 0) = Zz w (0 + ldir 0)) :
    ∀ u, InBall m u → Zz z u = Zz w u := by
  have hint : ∀ u, InBall (m - 1) u →
      Zz z u = Zz w u ∧ ∀ j, Zz z (u + ldir j) = Zz w (u + ldir j) := by
    intro u hu
    refine ball_induction' (M := m - 1) (by omega)
      (P := fun u => Zz z u = Zz w u ∧ ∀ j, Zz z (u + ldir j) = Zz w (u + ldir j))
      ⟨h0, flower_all hz hw (by unfold InBall; simp; omega) 0 h0 h1⟩ ?_ hu
    intro u j hu _ ⟨hP0, hPj⟩
    have hu0 : Zz z u = Zz w u := by
      have := hPj (j + 3)
      rwa [add_assoc, ldir_j_j3, add_zero] at this
    exact ⟨hu0, flower_all hz hw hu j hu0 hP0⟩
  intro u hu
  rcases ball_step (n := m - 1) (by omega) (by rw [sub_add_cancel]; exact hu) with h | ⟨j, hj⟩
  · exact (hint u h).1
  · have := (hint _ hj).2 (j + 3)
    rwa [add_assoc, ldir_j_j3, add_zero] at this

lemma IsConfigOn.congr_r {r' : ℤ → ℤ → ℝ} (hz : IsConfigOn m r z)
    (h : ∀ u, InBall m u → Rr r u = Rr r' u) : IsConfigOn m r' z := by
  intro u hu
  obtain ⟨e, c, o⟩ := hz u hu
  have huM : InBall m u := inBall_mono (by omega) hu
  refine ⟨fun i => ?_, fun i => ?_, o⟩
  · rw [e, h _ (inBall_nbr hu i), h _ huM]
  · rw [c, h _ (inBall_nbr hu _), h _ (inBall_nbr hu i)]

theorem IsConfigOn.affine (hz : IsConfigOn m r z) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    IsConfigOn m (fun p q => ‖α‖ * r p q) (fun p q => α * z p q + β) := by
  intro u hu
  obtain ⟨e, c, o⟩ := hz u hu
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · simp only [Zz, Rr] at e ⊢
    rw [show α * z (u + ldir i).1 (u + ldir i).2 + β - (α * z u.1 u.2 + β) =
      α * (z (u + ldir i).1 (u + ldir i).2 - z u.1 u.2) by ring, norm_mul, e i]; ring
  · simp only [Zz, Rr] at c ⊢
    rw [show α * z (u + ldir (i + 1)).1 (u + ldir (i + 1)).2 + β -
        (α * z (u + ldir i).1 (u + ldir i).2 + β) =
      α * (z (u + ldir (i + 1)).1 (u + ldir (i + 1)).2 - z (u + ldir i).1 (u + ldir i).2) by
        ring, norm_mul, c i]; ring
  · simp only [Zz] at o ⊢
    rw [orient_affine]; exact mul_pos (Complex.normSq_pos.2 hα) (o i)

lemma latRot_add_ldir (u : ℤ × ℤ) (i : Fin 6) :
    latRot (u + ldir i) = latRot u + ldir (i + 1) := by
  obtain ⟨p, q⟩ := u
  fin_cases i <;> simp [latRot, ldir] <;> ring_nf <;> simp

lemma inBall_latRot {n : ℤ} {u : ℤ × ℤ} : InBall n (latRot u) ↔ InBall n u := by
  obtain ⟨p, q⟩ := u; unfold InBall latRot; simp only; omega

lemma inBall_latRot_iter {n : ℤ} (j : ℕ) {u : ℤ × ℤ} :
    InBall n (latRot^[j] u) ↔ InBall n u := by
  induction j generalizing u with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, inBall_latRot]

theorem IsConfigOn.rot (hz : IsConfigOn m r z) :
    IsConfigOn m (fun p q => Rr r (latRot (p, q))) (fun p q => Zz z (latRot (p, q))) := by
  intro u hu
  obtain ⟨e, c, o⟩ := hz (latRot u) (inBall_latRot.2 hu)
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · simp only [Zz, Rr, Prod.mk.eta]
    rw [latRot_add_ldir]; exact e (i + 1)
  · simp only [Zz, Rr, Prod.mk.eta]
    rw [latRot_add_ldir, latRot_add_ldir]; exact c (i + 1)
  · simp only [Zz, Prod.mk.eta]
    rw [latRot_add_ldir, latRot_add_ldir]; exact o (i + 1)

theorem IsConfigOn.rot_iter (hz : IsConfigOn m r z) (j : ℕ) :
    IsConfigOn m (fun p q => Rr r (latRot^[j] (p, q))) (fun p q => Zz z (latRot^[j] (p, q))) := by
  induction j with
  | zero => simpa [Zz, Rr] using hz
  | succ n ih =>
    have h := ih.rot
    simp only [Zz, Rr, Prod.mk.eta, Function.iterate_succ_apply] at h ⊢
    exact h

/-- Patch version of `similar_of_rigidity`. -/
lemma similar_on (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hz : IsConfigOn m (fun p q => κ * r p q) z) (hw : IsConfigOn m r w)
    (hr : ∀ u, InBall m u → 0 < Rr r u) :
    ∃ α β : ℂ, α ≠ 0 ∧ ∀ u, InBall m u → Zz z u = α * Zz w u + β := by
  have h00 : InBall (m - 1) 0 := by unfold InBall; simp; omega
  have hwe := (hw 0 h00).1 0
  have hze := (hz 0 h00).1 0
  have hr0 := hr 0 (inBall_mono (by omega) h00)
  have hr1 := hr _ (inBall_nbr h00 0)
  have hw0 : Zz w (0 + ldir 0) - Zz w 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hwe; linarith
  set α := (Zz z (0 + ldir 0) - Zz z 0) / (Zz w (0 + ldir 0) - Zz w 0) with hαdef
  have hαn : ‖α‖ = κ := by
    have hpos : (0 : ℝ) < Rr r (0 + ldir 0) + Rr r 0 := by linarith
    rw [hαdef, norm_div, hze, hwe]
    simp only [Rr] at hpos ⊢
    rw [show κ * r (0 + ldir 0).1 (0 + ldir 0).2 + κ * r (0 : ℤ × ℤ).1 (0 : ℤ × ℤ).2 =
      κ * (r (0 + ldir 0).1 (0 + ldir 0).2 + r (0 : ℤ × ℤ).1 (0 : ℤ × ℤ).2) by ring,
      mul_div_assoc, div_self hpos.ne', mul_one]
  have hα : α ≠ 0 := by intro h; rw [h, norm_zero] at hαn; linarith
  refine ⟨α, Zz z 0 - α * Zz w 0, hα, ?_⟩
  have hs := hw.affine hα (Zz z 0 - α * Zz w 0)
  rw [hαn] at hs
  have key : α * (Zz w (0 + ldir 0) - Zz w 0) = Zz z (0 + ldir 0) - Zz z 0 := by
    rw [hαdef]; exact div_mul_cancel₀ _ hw0
  have := patch_rigidity hm hz hs (by simp [Zz]) (by
    simp only [Zz] at key ⊢
    linear_combination -key)
  intro u hu
  simpa [Zz] using this u hu

end Patch

/-- **Remark A 8.2.** Let `m ≥ 2` and let `z` be a configuration on the `m`-ring patch with
radii `r > 0`, whose flowers at the interior vertices close up and whose triangles around the
interior vertices are all similar to one triangle `(a, b, c)`. Then the patch is a piece of a
similar copy of the regular packing, or, after a lattice rotation `R^j`, of `D_B` with
`B > 1`. -/
theorem oneshape_patch_config {m : ℤ} (hm : 2 ≤ m) {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ}
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hz : IsConfigOn m r z)
    (hr : ∀ u, InBall m u → 0 < Rr r u)
    (hgood : ∀ u, InBall (m - 1) u → GoodAt r a b c u) :
    (∃ α β : ℂ, α ≠ 0 ∧ ∀ u, InBall m u → Zz z u = α * Zz (zreg 1) u + β) ∨
      ∃ B > 1, ∃ j : ℕ, j < 6 ∧ ∃ α β : ℂ, α ≠ 0 ∧ ∀ u, InBall m u →
        Zz z (latRot^[j] u) = α * Zz (zc B (psi B)) u + β := by
  have hm1 : 1 ≤ m := by omega
  have h00 : InBall (m - 1) 0 := by unfold InBall; simp; omega
  have hr0 := hr 0 (inBall_mono (by omega) h00)
  rcases oneshape_patch hm ha hb hc hgood with hreg | ⟨B, hB, k, hk⟩
  · left
    -- the radius is constant on the patch
    have hint : ∀ u, InBall (m - 1) u → Rr r u = Rr r 0 := by
      intro u hu
      refine ball_induction' (M := m - 1) (by omega) (P := fun u => Rr r u = Rr r 0) rfl ?_ hu
      intro u j hu _ hP
      rw [← hP, hreg u hu j]
    have hconst : ∀ u, InBall m u → Rr r u = Rr r 0 * 1 := by
      intro u hu
      rw [mul_one]
      rcases ball_step (n := m - 1) (by omega) (by rw [sub_add_cancel]; exact hu) with h | ⟨j, hj⟩
      · exact hint u h
      · have := hreg _ hj (j + 3)
        rw [add_assoc, ldir_j_j3, add_zero] at this
        rw [this, hint _ hj]
    have hz' := hz.congr_r (r' := fun p q => Rr r 0 * (fun _ _ => (1 : ℝ)) p q)
      (fun u hu => by simp only [Rr] at hconst ⊢; exact hconst u hu)
    exact similar_on hm1 hr0 hz' ((zreg_isConfig one_pos).isConfigOn m)
      (fun _ _ => one_pos)
  · right
    refine ⟨B, hB, k.val, k.isLt, ?_⟩
    have hB0 : 0 < B := by linarith
    have hrot := hz.rot_iter k.val
    have hrad : ∀ u, InBall m u →
        Rr (fun p q => Rr r (latRot^[k.val] (p, q))) u = Rr (fun p q => Rr r 0 * rad B p q) u := by
      intro u hu
      simp only [Rr, Prod.mk.eta]
      change Rr r (latRot^[k.val] u) = Rr r 0 * rad B u.1 u.2
      rw [hk _ ((inBall_latRot_iter k.val).2 hu)]
      unfold rad
      congr 2
      obtain ⟨p, q⟩ := u
      fin_cases k <;> simp [Function.iterate_succ, latRot, Ppat] <;> ring
    have hz' := hrot.congr_r hrad
    obtain ⟨α, β, hα, h⟩ := similar_on hm1 hr0 hz' ((zc_isConfig hB).isConfigOn m)
      (fun u _ => by unfold Rr rad; positivity)
    refine ⟨α, β, hα, fun u hu => ?_⟩
    have := h u hu
    simpa [Zz] using this

end DoyleFormal
