/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PatchConfig

/-!
# Remark A 8.2 with geometric hypotheses — Phase 4t

* `SimCentersOn m z a b c`: every center triangle around an interior vertex of the `m`-ring
  patch is similar to the triangle of centers of a tangent triple with radii `(a, b, c)`.
* `simCentersOn_simTriple` (Lemma A 3.3 on a patch): then the radii of these triangles are
  proportional to `(a, b, c)` in the matching order.
* `oneshape_patch_geom` (**Remark A 8.2**, geometric form): a patch configuration whose
  interior flowers close up and whose interior center triangles are all similar to one
  triangle is a piece of a similar copy of the regular packing, or, after a lattice rotation,
  of `D_B` with `B > 1`.
-/

namespace DoyleFormal

/-- Every center triangle around an interior vertex is similar to the triangle of centers of
a tangent triple with radii `(a, b, c)`. -/
def SimCentersOn (m : ℤ) (z : ℤ → ℤ → ℂ) (a b c : ℝ) : Prop :=
  ∀ u : ℤ × ℤ, InBall (m - 1) u → ∀ i : Fin 6, ∃ μ > 0, ∃ x y w, (x, y, w) ∈ perms3 a b c ∧
    ‖Zz z (u + ldir i) - Zz z (u + ldir (i + 1))‖ = μ * (y + w) ∧
    ‖Zz z (u + ldir (i + 1)) - Zz z u‖ = μ * (w + x) ∧
    ‖Zz z u - Zz z (u + ldir i)‖ = μ * (x + y)

theorem simCentersOn_simTriple {m : ℤ} {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} {a b c : ℝ}
    (hz : IsConfigOn m r z) (hs : SimCentersOn m z a b c) {u : ℤ × ℤ}
    (hu : InBall (m - 1) u) (i : Fin 6) :
    SimTriple (Rr r u, Rr r (u + ldir i), Rr r (u + ldir (i + 1))) (a, b, c) := by
  obtain ⟨μ, hμ, x, y, w, hm, h1, h2, h3⟩ := hs u hu i
  obtain ⟨e, c', -⟩ := hz u hu
  rw [norm_sub_rev, c' i] at h1
  rw [e (i + 1)] at h2
  rw [norm_sub_rev, e i] at h3
  have := (sides_prop_iff μ x y w (Rr r u) (Rr r (u + ldir i)) (Rr r (u + ldir (i + 1)))).1
    ⟨by linarith, by linarith, by linarith⟩
  exact simTriple_iff.2 ⟨μ, hμ, x, y, w, hm, this.1, this.2.1, this.2.2⟩

/-- **Remark A 8.2** with geometric hypotheses: Definition A 2.1 on the patch (`IsConfigOn`
and the flower clause `hsum`) and similar center triangles (`SimCentersOn`). -/
theorem oneshape_patch_geom {m : ℤ} (hm : 2 ≤ m) {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ}
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hz : IsConfigOn m r z)
    (hr : ∀ u, InBall m u → 0 < Rr r u)
    (hsum : ∀ u, InBall (m - 1) u →
      ∑ i : Fin 6, angleAt (Rr r u) (Rr r (u + ldir i)) (Rr r (u + ldir (i + 1))) = 2 * Real.pi)
    (hs : SimCentersOn m z a b c) :
    (∃ α β : ℂ, α ≠ 0 ∧ ∀ u, InBall m u → Zz z u = α * Zz (zreg 1) u + β) ∨
      ∃ B > 1, ∃ j : ℕ, j < 6 ∧ ∃ α β : ℂ, α ≠ 0 ∧ ∀ u, InBall m u →
        Zz z (latRot^[j] u) = α * Zz (zc B (psi B)) u + β :=
  oneshape_patch_config hm ha hb hc hz hr
    (fun u hu => ⟨fun i => simCentersOn_simTriple hz hs hu i, hsum u hu⟩)

end DoyleFormal
