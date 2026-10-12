/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.CoherentPacking
import DoyleFormal.CoherentTangent

/-!
# `D_{B_n}` on the cylinder (Proposition B 5.3 and the converse of Theorem B 7.2) — Phase 5h

`Cyl n = ℤ² ⧸ ℤ(−n, 2n)`. For `ψ(B) = π/n`, `n ≥ 2`:

* `cylPacking`: the circles of `D_{B_n}`, indexed by `Cyl n`, form a `HexPacking` with flowers
  `v ↦ v + d_i`.
* `cylPacking_coherent`: distinct circles have disjoint interiors (coherence).
* `cylPacking_contact` (**Proposition B 5.3, contact graph**): two distinct circles are
  tangent iff their labels differ by a lattice direction in `Cyl n`, so the contact graph is
  the cylinder `ℤ²/ℤ(−n,2n)` with its triangulation.
* `cylPacking_shape`: all center triangles are similar to the triangle with radii
  `1, B, B²`.

Together with `coherent_classification` this gives both directions of the classification in
Theorem B 7.2. That the packing fills `ℂ ∖ {X}` is not formalized (cited in B from
Beardon–Dubejko–Stephenson 1994).
-/

namespace DoyleFormal

open Complex

/-- The coincidence lattice `ℤ(−n, 2n)`. -/
def Lam (n : ℕ) : AddSubgroup (ℤ × ℤ) := AddSubgroup.zmultiples (-(n : ℤ), 2 * (n : ℤ))

/-- The cylinder `ℤ² ⧸ ℤ(−n, 2n)`. -/
abbrev Cyl (n : ℕ) := (ℤ × ℤ) ⧸ Lam n

lemma cyl_eq_iff {n : ℕ} (u u' : ℤ × ℤ) :
    (u : Cyl n) = (u' : Cyl n) ↔
      ∃ k : ℤ, u'.1 - u.1 = -(k * n) ∧ u'.2 - u.2 = 2 * (k * n) := by
  rw [QuotientAddGroup.eq, Lam, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · have := congrArg Prod.fst hk; simp at this; linarith
    · have := congrArg Prod.snd hk; simp at this; linarith
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, ?_⟩
    ext <;> simp <;> linarith

section Cyl

variable {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n)
include hB hn hψn

lemma same_class {u u' : ℤ × ℤ} (h : (u : Cyl n) = (u' : Cyl n)) :
    zc B (psi B) u'.1 u'.2 = zc B (psi B) u.1 u.2 ∧ rad B u'.1 u'.2 = rad B u.1 u.2 := by
  obtain ⟨k, h1, h2⟩ := (cyl_eq_iff u u').1 h
  have := (coherent_coincide_iff hB hn hψn u.1 u.2 (u'.1 - u.1) (u'.2 - u.2)).2
    ⟨k, h1, h2⟩
  simp only [add_sub_cancel] at this
  exact ⟨this.2, this.1⟩

end Cyl

/-- A representative of a class. -/
noncomputable def cylRep {n : ℕ} (v : Cyl n) : ℤ × ℤ := Quotient.out v

lemma cylRep_mk {n : ℕ} (v : Cyl n) : ((cylRep v : ℤ × ℤ) : Cyl n) = v :=
  QuotientAddGroup.out_eq' v

lemma rad_ldir {B : ℝ} (hB : 0 < B) (u : ℤ × ℤ) (j : Fin 6) :
    rad B (u + ldir j).1 (u + ldir j).2 = rad B u.1 u.2 * B ^ Ppat j := by
  unfold rad
  rw [show 2 * (u + ldir j).1 + (u + ldir j).2 = (2 * u.1 + u.2) + Ppat j by
    have := ldir_exp u j; linarith, zpow_add₀ hB.ne']

section Packing

variable {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n)

/-- Centers and radii on the cylinder. -/
noncomputable def cylC (B : ℝ) {n : ℕ} (v : Cyl n) : ℂ := zc B (psi B) (cylRep v).1 (cylRep v).2
noncomputable def cylR (B : ℝ) {n : ℕ} (v : Cyl n) : ℝ := rad B (cylRep v).1 (cylRep v).2

include hB hn hψn in
lemma cylC_mk (u : ℤ × ℤ) : cylC B (u : Cyl n) = zc B (psi B) u.1 u.2 :=
  (same_class hB hn hψn (cylRep_mk (u : Cyl n)).symm).1

include hB hn hψn in
lemma cylR_mk (u : ℤ × ℤ) : cylR B (u : Cyl n) = rad B u.1 u.2 :=
  (same_class hB hn hψn (cylRep_mk (u : Cyl n)).symm).2

lemma mk_add_ldir {n : ℕ} (u : ℤ × ℤ) (i : Fin 6) :
    ((u : Cyl n) + ((ldir i : ℤ × ℤ) : Cyl n)) = ((u + ldir i : ℤ × ℤ) : Cyl n) :=
  (QuotientAddGroup.mk_add _ _ _).symm

lemma ldir_snd_bound (i j : Fin 6) : -2 ≤ (ldir j - ldir i).2 ∧ (ldir j - ldir i).2 ≤ 2 := by
  fin_cases i <;> fin_cases j <;> decide

include hn in
lemma ldir_cyl_inj {i j : Fin 6} (h : ((ldir i : ℤ × ℤ) : Cyl n) = ((ldir j : ℤ × ℤ) : Cyl n)) :
    i = j := by
  obtain ⟨k, h1, h2⟩ := (cyl_eq_iff _ _).1 h
  have hb := ldir_snd_bound i j
  rw [Prod.snd_sub] at hb
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hk : k = 0 := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · nlinarith
    · exact hk
    · nlinarith
  subst hk
  simp at h1 h2
  exact ldir_inj (Prod.ext (by linarith) (by linarith))

include hB hn hψn in
/-- **`D_{B_n}` on the cylinder is a hexagonal circle packing.** -/
noncomputable def cylPacking : HexPacking (Cyl n) where
  c := cylC B
  ρ := cylR B
  ρ_pos v := by unfold cylR rad; have : 0 < B := by linarith
                positivity
  nb v i := v + ((ldir i : ℤ × ℤ) : Cyl n)
  tan v i := by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
    rw [mk_add_ldir, cylC_mk hB hn hψn, cylC_mk hB hn hψn, cylR_mk hB hn hψn,
      cylR_mk hB hn hψn]
    exact (zc_isConfig hB).edge u i
  rim v i := by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
    rw [mk_add_ldir, mk_add_ldir, cylC_mk hB hn hψn, cylC_mk hB hn hψn, cylR_mk hB hn hψn,
      cylR_mk hB hn hψn]
    have h := (zc_isConfig hB).edge (u + ldir i) (i + 2)
    rwa [ldir_succ_eq] at h
  ori v i := by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
    rw [mk_add_ldir, mk_add_ldir, cylC_mk hB hn hψn, cylC_mk hB hn hψn, cylC_mk hB hn hψn]
    have h := (zc_isConfig hB).orient_pos u (ldir i) (by fin_cases i <;> simp [ldir, IsDir])
    rwa [rotp_ldir] at h
  wind v := by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
    simp only [mk_add_ldir, cylR_mk hB hn hψn]
    exact rad_locUniv (by linarith) u
  inj v i j h := ldir_cyl_inj hn (add_left_cancel h)
  compat v i := ⟨i + 3, by
      rw [add_assoc, ← QuotientAddGroup.mk_add, ldir_add_three]; simp,
    by rw [add_assoc, ← QuotientAddGroup.mk_add, show i + 3 + 5 = i + 2 by revert i; decide,
      ldir_add_two],
    by rw [add_assoc, ← QuotientAddGroup.mk_add, show i + 3 + 1 = i + 4 by revert i; decide,
      ldir_add_four]⟩
  conn v w := by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
    obtain ⟨u', rfl⟩ := QuotientAddGroup.mk_surjective w
    exact (regularHex.conn u u').lift (fun x : ℤ × ℤ => (x : Cyl n))
      (fun x y ⟨i, hi⟩ => ⟨i, by
        rw [hi]
        change ((x + ldir i : ℤ × ℤ) : Cyl n) = (x : Cyl n) + ((ldir i : ℤ × ℤ) : Cyl n)
        exact QuotientAddGroup.mk_add _ _ _⟩)

include hB hn hψn in
/-- **Coherence.** Distinct circles of `D_{B_n}` on the cylinder have disjoint interiors. -/
theorem cylPacking_coherent (v w : Cyl n) (h : v ≠ w) :
    (cylPacking hB hn hψn).ρ v + (cylPacking hB hn hψn).ρ w ≤
      ‖(cylPacking hB hn hψn).c v - (cylPacking hB hn hψn).c w‖ := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨u', rfl⟩ := QuotientAddGroup.mk_surjective w
  change cylR B (u : Cyl n) + cylR B (u' : Cyl n) ≤ ‖cylC B (u : Cyl n) - cylC B (u' : Cyl n)‖
  rw [cylC_mk hB hn hψn, cylC_mk hB hn hψn, cylR_mk hB hn hψn, cylR_mk hB hn hψn]
  have hw : ¬ ∃ k : ℤ, u'.1 - u.1 = -(k * n) ∧ u'.2 - u.2 = 2 * (k * n) :=
    fun hk => h ((cyl_eq_iff u u').2 hk)
  have := coherent_no_overlap hB hn hψn u.1 u.2 (u'.1 - u.1) (u'.2 - u.2) hw
  simp only [add_sub_cancel] at this
  rw [norm_sub_rev]
  push Not at this
  linarith

lemma isUnitDir_iff (x y : ℤ) : IsUnitDir x y ↔ ∃ i : Fin 6, (x, y) = ldir i := by
  unfold IsUnitDir
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [⟨0, rfl⟩, ⟨3, rfl⟩, ⟨1, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, hi⟩
    have h1 := congrArg Prod.fst hi
    have h2 := congrArg Prod.snd hi
    fin_cases i <;> simp [ldir] at h1 h2 <;> omega

include hB hn hψn in
/-- **Proposition B 5.3, contact graph.** Two distinct circles are tangent iff their labels
differ by a lattice direction in `Cyl n`. -/
theorem cylPacking_contact (v w : Cyl n) (h : v ≠ w) :
    ‖(cylPacking hB hn hψn).c w - (cylPacking hB hn hψn).c v‖ =
        (cylPacking hB hn hψn).ρ w + (cylPacking hB hn hψn).ρ v ↔
      ∃ i : Fin 6, w = v + ((ldir i : ℤ × ℤ) : Cyl n) := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
  obtain ⟨u', rfl⟩ := QuotientAddGroup.mk_surjective w
  change ‖cylC B (u' : Cyl n) - cylC B (u : Cyl n)‖ = cylR B (u' : Cyl n) + cylR B (u : Cyl n) ↔ _
  rw [cylC_mk hB hn hψn, cylC_mk hB hn hψn, cylR_mk hB hn hψn, cylR_mk hB hn hψn]
  have ht := coherent_tangent_iff hB hn hψn u.1 u.2 (u'.1 - u.1) (u'.2 - u.2)
  simp only [add_sub_cancel] at ht
  rw [ht]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ := (isUnitDir_iff _ _).1 hk
    refine ⟨i, ?_⟩
    rw [mk_add_ldir]
    apply (cyl_eq_iff _ _).2
    refine ⟨-k, ?_, ?_⟩
    · have := congrArg Prod.fst hi; simp at this ⊢; linarith
    · have := congrArg Prod.snd hi; simp at this ⊢; linarith
  · rintro ⟨i, hi⟩
    rw [mk_add_ldir] at hi
    obtain ⟨k, h1, h2⟩ := (cyl_eq_iff _ _).1 hi
    refine ⟨-k, (isUnitDir_iff _ _).2 ⟨i, ?_⟩⟩
    simp at h1 h2
    ext <;> simp <;> linarith

include hB hn hψn in
/-- **All center triangles of `D_{B_n}` have the shape `1, B, B²`.** -/
theorem cylPacking_shape : (cylPacking hB hn hψn).SimShape 1 B (B ^ 2) := by
  intro v i
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective v
  have hB0 : 0 < B := by linarith
  have hR0 : 0 < rad B u.1 u.2 := by unfold rad; positivity
  -- the radii of the triangle, up to the factor `μ`
  have key : ∃ μ > 0, ∃ x y w, (x, y, w) ∈ perms3 1 B (B ^ 2) ∧
      rad B u.1 u.2 = μ * x ∧ rad B (u + ldir i).1 (u + ldir i).2 = μ * y ∧
      rad B (u + ldir (i + 1)).1 (u + ldir (i + 1)).2 = μ * w := by
    rw [rad_ldir hB0, rad_ldir hB0]
    generalize rad B u.1 u.2 = R at hR0 ⊢
    have hR := hR0
    fin_cases i <;> simp only [Ppat, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one] <;> norm_num
    · exact ⟨R, hR, 1, B ^ 2, B, by simp [perms3], by ring, by ring, by ring⟩
    · exact ⟨R / B, by positivity, B, B ^ 2, 1, by simp [perms3], by field_simp,
        by field_simp, by field_simp⟩
    · exact ⟨R / B ^ 2, by positivity, B ^ 2, B, 1, by simp [perms3], by field_simp,
        by field_simp, by field_simp⟩
    · exact ⟨R / B ^ 2, by positivity, B ^ 2, 1, B, by simp [perms3], by field_simp,
        by field_simp, by field_simp⟩
    · exact ⟨R / B, by positivity, B, 1, B ^ 2, by simp [perms3], by field_simp,
        by field_simp, by field_simp⟩
    · exact ⟨R, hR, 1, B, B ^ 2, by simp [perms3], by ring, by ring, by ring⟩
  obtain ⟨μ, hμ, x, y, w, hm, hx, hy, hw⟩ := key
  refine ⟨μ, hμ, x, y, w, hm, ?_, ?_, ?_⟩
  · have := (cylPacking hB hn hψn).rim (u : Cyl n) i
    rw [norm_sub_rev, this]
    change cylR B ((u : Cyl n) + ((ldir (i + 1) : ℤ × ℤ) : Cyl n)) +
      cylR B ((u : Cyl n) + ((ldir i : ℤ × ℤ) : Cyl n)) = μ * (y + w)
    rw [mk_add_ldir, mk_add_ldir, cylR_mk hB hn hψn, cylR_mk hB hn hψn, hy, hw]; ring
  · have := (cylPacking hB hn hψn).tan (u : Cyl n) (i + 1)
    rw [this]
    change cylR B ((u : Cyl n) + ((ldir (i + 1) : ℤ × ℤ) : Cyl n)) + cylR B (u : Cyl n) =
      μ * (w + x)
    rw [mk_add_ldir, cylR_mk hB hn hψn, cylR_mk hB hn hψn, hw, hx]; ring
  · have := (cylPacking hB hn hψn).tan (u : Cyl n) i
    rw [norm_sub_rev, this]
    change cylR B ((u : Cyl n) + ((ldir i : ℤ × ℤ) : Cyl n)) + cylR B (u : Cyl n) =
      μ * (x + y)
    rw [mk_add_ldir, cylR_mk hB hn hψn, cylR_mk hB hn hψn, hy, hx]; ring

include hB hn hψn in
/-- **Theorem B 7.2, converse.** For `ψ(B) = π/n`, `n ≥ 2`, the circles of `D_{B_n}` form a
coherent hexagonal circle packing (indexed by the cylinder) all of whose center triangles are
similar to the triangle with radii `1, B, B²`. -/
theorem DBn_coherent_hexPacking :
    ∃ P : HexPacking (Cyl n), (∀ v w, v ≠ w → P.ρ v + P.ρ w ≤ ‖P.c v - P.c w‖) ∧
      P.SimShape 1 B (B ^ 2) ∧
      ∀ u : ℤ × ℤ, P.c u = zc B (psi B) u.1 u.2 ∧ P.ρ u = rad B u.1 u.2 :=
  ⟨cylPacking hB hn hψn, cylPacking_coherent hB hn hψn, cylPacking_shape hB hn hψn,
    fun u => ⟨cylC_mk hB hn hψn u, cylR_mk hB hn hψn u⟩⟩

end Packing

end DoyleFormal
