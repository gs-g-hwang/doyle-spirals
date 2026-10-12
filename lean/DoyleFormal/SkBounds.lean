/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PaperC3

/-!
# The Rodin–Sullivan constants `s_k` and the lower bounds of Proposition C 3.1

* `AdmPatch k r z`: a univalent circle packing with the combinatorics of `k` hexagonal
  generations around `K(0)`: Definition A 2.1 on the `k`-ring patch (`IsConfigOn`), positive
  radii, and pairwise disjoint interiors.
* `sk k : EReal`: the supremum of `|1 − ρ|` over such packings, `ρ` the ratio of the radius of a
  generation-one circle to that of `K(0)` (it may be `⊤`, e.g. for `k = 1`).
* `DB_admissible`: for `B ∈ [B_{k+1}, B*_k)` the `k`-ring patch of `D_B` is admissible, with
  `ρ = B²`.
* `sk_lower` (**Proposition C 3.1**): `s_k ≥ (B*_k)² − 1 > B_{k+1}² − 1` for `k ≥ 1`.
* `sk_liminf` (**Proposition C 3.1**): `liminf k s_k ≥ 2π/√3`, in the form: for every `ε > 0`,
  eventually `k s_k ≥ 2π/√3 − ε`.
-/

namespace DoyleFormal

open Real Filter Topology

/-- A univalent `k`-generation hexagonal packing. -/
def AdmPatch (k : ℕ) (r : ℤ → ℤ → ℝ) (z : ℤ → ℤ → ℂ) : Prop :=
  IsConfigOn k r z ∧ (∀ u, InBall k u → 0 < Rr r u) ∧
    ∀ u v, InBall k u → InBall k v → u ≠ v → Rr r u + Rr r v ≤ ‖Zz z u - Zz z v‖

/-- The values `|1 − ρ|` of admissible packings. -/
def skSet (k : ℕ) : Set ℝ :=
  {x | ∃ (r : ℤ → ℤ → ℝ) (z : ℤ → ℤ → ℂ) (i : Fin 6), AdmPatch k r z ∧
    x = |1 - Rr r (0 + ldir i) / Rr r 0|}

/-- **The Rodin–Sullivan constant `s_k`.** -/
noncomputable def sk (k : ℕ) : EReal := sSup ((fun x : ℝ => (x : EReal)) '' skSet k)

lemma le_sk {k : ℕ} {x : ℝ} (hx : x ∈ skSet k) : (x : EReal) ≤ sk k :=
  le_sSup ⟨x, hx, rfl⟩

lemma inBall_iff_hnorm (k : ℤ) (u : ℤ × ℤ) : InBall k u ↔ hnorm u.1 u.2 ≤ k := by
  rw [hnorm_le_iff]; unfold InBall; omega

/-- If no two circles of the `k`-ring patch of `D_B` coincide or overlap, the patch is
admissible, and its ratio `ρ = r(1,0)/r(0,0)` is `B²`. -/
theorem DB_admissible {k : ℕ} {B : ℝ} (hB : 1 < B)
    (h : ∀ p q p' q' : ℤ, hnorm p q ≤ k → hnorm p' q' ≤ k → (p, q) ≠ (p', q') →
      ¬ (rad B p' q' = rad B p q ∧ zc B (psi B) p' q' = zc B (psi B) p q) ∧
        ¬ ‖zc B (psi B) p' q' - zc B (psi B) p q‖ < rad B p' q' + rad B p q) :
    AdmPatch k (rad B) (zc B (psi B)) ∧ B ^ 2 - 1 ∈ skSet k := by
  have hB0 : 0 < B := by linarith
  have hadm : AdmPatch k (rad B) (zc B (psi B)) := by
    refine ⟨(zc_isConfig hB).isConfigOn k, fun u _ => by unfold Rr rad; positivity,
      fun u v hu hv hne => ?_⟩
    obtain ⟨p, q⟩ := u; obtain ⟨p', q'⟩ := v
    rw [inBall_iff_hnorm] at hu hv
    have := (h p q p' q' hu hv hne).2
    push Not at this
    simp only [Rr, Zz]
    rw [norm_sub_rev]; linarith
  refine ⟨hadm, rad B, zc B (psi B), 0, hadm, ?_⟩
  simp only [Rr, rad, ldir, zero_add]
  norm_num
  rw [abs_of_neg (by nlinarith)]; ring

/-- `B²−1` belongs to `skSet k` for every `B ∈ [B_{k+1}, B*_k)`. -/
lemma mem_skSet {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB1 : Bres (k + 1) ≤ B)
    (hB2 : B < if k = 1 then Bstar1 else Bstar k) : B ^ 2 - 1 ∈ skSet k := by
  have hB : 1 < B := lt_of_lt_of_le (Bres_spec (show 2 ≤ k + 1 by omega)).1 hB1
  refine (DB_admissible hB ?_).2
  intro p q p' q' hu hu' hne
  by_cases h1 : k = 1
  · subst h1
    have hB2' : B < Bstar1 := by simpa using hB2
    exact patch_univalent_lower1 hB1 hB2' p q p' q' (by exact_mod_cast hu)
      (by exact_mod_cast hu') hne
  · have hB2' : B < Bstar k := by simpa [h1] using hB2
    exact patch_univalent_lower (by omega) hB1 hB2' p q p' q' hu hu' hne

/-- `B*_k` for all `k ≥ 1` (`B*_1` uses `B₁ = ∞`). -/
noncomputable def BstarAll (k : ℕ) : ℝ := if k = 1 then Bstar1 else Bstar k

lemma Bres_lt_BstarAll {k : ℕ} (hk : 1 ≤ k) : Bres (k + 1) < BstarAll k := by
  unfold BstarAll
  by_cases h1 : k = 1
  · subst h1; simpa using Bstar1_spec.1
  · simpa [h1] using (Bstar_spec (by omega)).1

/-- **Proposition C 3.1.** `s_k ≥ (B*_k)² − 1 > B_{k+1}² − 1` for every `k ≥ 1`. -/
theorem sk_lower {k : ℕ} (hk : 1 ≤ k) :
    ((BstarAll k ^ 2 - 1 : ℝ) : EReal) ≤ sk k ∧ Bres (k + 1) ^ 2 - 1 < BstarAll k ^ 2 - 1 := by
  have hlt := Bres_lt_BstarAll hk
  have h1 := (Bres_spec (show 2 ≤ k + 1 by omega)).1
  refine ⟨?_, by nlinarith⟩
  -- approach `B*_k` from below
  set a := Bres (k + 1); set b := BstarAll k
  set B : ℕ → ℝ := fun n => b - (b - a) / (n + 2)
  have hBmem : ∀ n, a ≤ B n ∧ B n < b := by
    intro n
    have hn : (0 : ℝ) < n + 2 := by positivity
    have hd : 0 < b - a := by linarith
    constructor
    · have : (b - a) / (n + 2) ≤ b - a := div_le_self hd.le (by linarith)
      simp only [B]; linarith
    · simp only [B]; have : 0 < (b - a) / (n + 2) := div_pos hd hn; linarith
  have hlim : Tendsto (fun n => ((B n ^ 2 - 1 : ℝ) : EReal)) atTop
      (𝓝 ((b ^ 2 - 1 : ℝ) : EReal)) := by
    apply (continuous_coe_real_ereal.tendsto _).comp
    have : Tendsto B atTop (𝓝 (b - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop))
    rw [sub_zero] at this
    exact (this.pow 2).sub_const 1
  refine le_of_tendsto' hlim fun n => le_sk ?_
  exact mem_skSet hk (hBmem n).1 (hBmem n).2

/-- **Proposition C 3.1.** `liminf k s_k ≥ 2π/√3`: for every `ε > 0`, eventually
`k s_k ≥ 2π/√3 − ε`. (Witness: the `k`-ring patch of `D_{B_{k+1}}`.) -/
theorem sk_liminf {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∃ x ∈ skSet k, 2 * π / √3 - ε ≤ k * x := by
  have h := Bres_asymp
  have hev : ∀ᶠ k : ℕ in atTop, 2 * π / √3 - ε < k * (Bres (k + 1) ^ 2 - 1) :=
    h.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  refine ⟨Bres (k + 1) ^ 2 - 1, ?_, hk.le⟩
  have hlt := Bres_lt_BstarAll hk1
  exact mem_skSet hk1 le_rfl (by simpa [BstarAll] using hlt)

end DoyleFormal
