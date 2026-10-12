/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.CoherentSymmetry

/-!
# Theorem A 4.1 (`⇐`) for every `B > 0` — Phase 4l

The proof of the paper: the mirror image `w(p,q) = conj z(p+q, −q)` of a configuration is
again a configuration with the same radius function (the lattice reflection `τ` and
conjugation are both indirect), and it agrees with `z` at `(0,0)` and `(1,0)`, so
`rigidity` (Lemma A 2.2) gives `w = z`. No closed form is used, so `B ≤ 1` is included.

* `IsConfig.mirror`: `w` is a configuration whenever `r ∘ τ = r`.
* `config_mirror_of_rigidity`: `conj z(p,q) = z(p+q, −q)` when `z(0,0) = 0` and `z(1,0)`
  is real.
* `config_mirror_all` (**Theorem A 4.1, `⇐`, every `B > 0`**): the case `r = B^{2p+q}`.
* `symmetry_iff` (**Theorem A 4.1**): both directions for a configuration with radii
  `A^p B^q`, `A, B > 0`.
-/

namespace DoyleFormal

open Complex

/-- Swapping two vertices reverses orientation. -/
lemma orient_swap (a b c : ℂ) : orient a c b = -orient a b c := by
  simp only [orient_eq]
  ring

/-- The mirror image of a configuration under conjugation and the lattice reflection
`(p,q) ↦ (p+q, −q)` is a configuration, if the radius function is invariant. -/
theorem IsConfig.mirror {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z)
    (hr : ∀ p q, r (p + q) (-q) = r p q) :
    IsConfig r (fun p q => (starRingEnd ℂ) (z (p + q) (-q))) where
  t10 p q := by
    rw [← map_sub, Complex.norm_conj, ← hr (p + 1) q, ← hr p q,
      show p + 1 + q = p + q + 1 by ring]
    exact hz.t10 (p + q) (-q)
  t01 p q := by
    rw [← map_sub, Complex.norm_conj, ← hr p (q + 1), ← hr p q]
    have h := hz.tm11 (p + q + 1) (-(q + 1))
    rw [show p + q + 1 - 1 = p + q by ring, show -(q + 1) + 1 = -q by ring] at h
    rw [show p + (q + 1) = p + q + 1 by ring, norm_sub_rev, h, add_comm]
  tm11 p q := by
    rw [← map_sub, Complex.norm_conj, ← hr (p - 1) (q + 1), ← hr p q]
    have h := hz.t01 (p + q) (-(q + 1))
    rw [show -(q + 1) + 1 = -q by ring] at h
    rw [show p - 1 + (q + 1) = p + q by ring, norm_sub_rev, h, add_comm]
  up p q := by
    simp only [orient_conj]
    have h := hz.orient_pos (p + q, -q) (1, -1) (by unfold IsDir; simp)
    simp only [rotp, Prod.mk_add_mk] at h
    rw [orient_swap] at h
    have e1 : p + 1 + q = p + q + 1 := by ring
    have e2 : p + (q + 1) = p + q + 1 := by ring
    have e3 : -(q + 1) = -q + -1 := by ring
    rw [e1, e2, e3]
    rw [show p + q + - -1 = p + q + 1 by ring, show -q + (1 + -1) = -q by ring] at h
    exact h
  down p q := by
    simp only [orient_conj]
    have h := hz.orient_pos (p + q, -q) (0, -1) (by unfold IsDir; simp)
    simp only [rotp, Prod.mk_add_mk] at h
    rw [orient_swap] at h
    have e2 : p + (q + 1) = p + q + 1 := by ring
    have e3 : -(q + 1) = -q + -1 := by ring
    have e5 : p - 1 + (q + 1) = p + q := by ring
    rw [e2, e3, e5]
    rw [show -q + (0 + -1) = -q + -1 by ring, show p + q + - -1 = p + q + 1 by ring,
      add_zero] at h
    exact h

/-- **Mirror symmetry from rigidity.** If `r(p+q, −q) = r(p,q)`, `z(0,0) = 0` and `z(1,0)`
is real, then `conj z(p,q) = z(p+q, −q)` for all `(p,q)`. -/
theorem config_mirror_of_rigidity {r : ℤ → ℤ → ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig r z)
    (hr : ∀ p q, r (p + q) (-q) = r p q) (h0 : z 0 0 = 0) (h1 : (z 1 0).im = 0)
    (p q : ℤ) : (starRingEnd ℂ) (z p q) = z (p + q) (-q) := by
  have hw := rigidity (hz.mirror hr) hz (by simp [h0])
    (by simp only [add_zero, neg_zero]; exact Complex.conj_eq_iff_im.2 h1)
  have h := hw (p + q) (-q)
  simp only [add_neg_cancel_right, neg_neg] at h
  exact h

/-- **Theorem A 4.1 (`⇐`) for every `B > 0`.** A configuration with radii `B^{2p+q}`,
`z(0,0) = 0` and `z(1,0)` real is invariant under conjugation with `τ(p,q) = (p+q, −q)`. -/
theorem config_mirror_all {B : ℝ} {z : ℤ → ℤ → ℂ} (hz : IsConfig (rad B) z)
    (h0 : z 0 0 = 0) (h1 : (z 1 0).im = 0) (p q : ℤ) :
    (starRingEnd ℂ) (z p q) = z (p + q) (-q) :=
  config_mirror_of_rigidity hz (fun p q => by unfold rad; congr 1; ring) h0 h1 p q

/-- **Theorem A 4.1.** Let `z` be a configuration with radii `A^p B^q` (`B > 0`),
`z(0,0) = 0` and `z(1,0)` real. Then there is an adjacency-preserving lattice map `τ`
fixing `(0,0)` and `(1,0)` with `conj K(u) = K(τ u)` (equal centers and radii) if and only
if `A = B²`. -/
theorem symmetry_iff {A B : ℝ} (hB : 0 < B) {z : ℤ → ℤ → ℂ}
    (hz : IsConfig (fun p q => A ^ p * B ^ q) z) (h0 : z 0 0 = 0) (h1 : (z 1 0).im = 0) :
    (∃ τ : ℤ → ℤ → ℤ × ℤ,
      (∀ p q, IsDir (τ (p + 1) q - τ p q)) ∧ (∀ p q, IsDir (τ p (q + 1) - τ p q)) ∧
      (∀ p q, IsDir (τ (p - 1) (q + 1) - τ p q)) ∧ τ 0 0 = (0, 0) ∧ τ 1 0 = (1, 0) ∧
      (∀ p q, (starRingEnd ℂ) (z p q) = z (τ p q).1 (τ p q).2) ∧
      (∀ p q, A ^ (τ p q).1 * B ^ (τ p q).2 = A ^ p * B ^ q)) ↔ A = B ^ 2 := by
  constructor
  · rintro ⟨τ, h10, h01, hm11, ht0, ht1, hc, hr⟩
    exact symmetry_converse hB hz h10 h01 hm11 ht0 ht1 hc hr
  · intro hAB
    have hr : ∀ p q : ℤ, A ^ (p + q) * B ^ (-q) = A ^ p * B ^ q := by
      intro p q
      have hB0 : B ≠ 0 := hB.ne'
      rw [hAB, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hB0, ← zpow_add₀ hB0]
      congr 1; push_cast; ring
    refine ⟨mirrorAut, fun p q => mirrorAut_isIndirectAut.t10 p q,
      fun p q => mirrorAut_isIndirectAut.t01 p q, fun p q => mirrorAut_isIndirectAut.tm11 p q,
      by simp [mirrorAut], by simp [mirrorAut], ?_, fun p q => hr p q⟩
    intro p q
    exact config_mirror_of_rigidity hz (fun p q => hr p q) h0 h1 p q

end DoyleFormal
