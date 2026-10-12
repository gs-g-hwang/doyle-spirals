/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.NonVacuous

/-!
# Uniqueness of `B` in Theorem A 8.1, and the patch version (Remark A 8.2) — Phase 4r

* `oneshape_B_unique`: the `B > 1` of Theorem A 8.1 is determined by the radius function
  (`B²` is the largest ratio of neighboring radii).
* `InBall m u`: `‖u‖ = max(|p|, |q|, |p+q|) ≤ m` (the `m`-ring patch).
* `generic_at`, `isosceles_at`: Cases 1 and 2 of Theorem A 8.1 only use the vertices `0` and
  `d_0` (Case 1) or `0` (Case 2).
* `oneshape_patch` (**Remark A 8.2, radius part**): let `m ≥ 2`, and suppose the triangles
  around the interior vertices (`‖u‖ ≤ m − 1`) are all similar to one triangle and the
  flowers at the interior vertices close up. Then either the triangles at the interior
  vertices are equilateral, or `r(u) = r(0) B^{p a + q b}` on the whole `m`-ring patch, with
  `B > 1` and `(a, b)` a rotation of `(2, 1)`.

Not formalized: the final step of Remark A 8.2 (rigidity on a patch, which identifies the
patch with a piece of `D_B`).
-/

namespace DoyleFormal

open Real

/-! ### Uniqueness of `B` -/

lemma grad_ldir (k j : Fin 6) :
    (ldir j).1 * Ppat (0 - k) + (ldir j).2 * Ppat (1 - k) = Ppat (j - k) := by
  fin_cases k <;> fin_cases j <;> decide

lemma Ppat_le_two (i : Fin 6) : Ppat i ≤ 2 := by fin_cases i <;> decide

/-- **Uniqueness of `B` in Theorem A 8.1.** -/
theorem oneshape_B_unique {r : ℤ → ℤ → ℝ} {B B' : ℝ} (hB : 1 < B) (hB' : 1 < B') {k k' : Fin 6}
    (h : ∀ p q : ℤ, r p q = r 0 0 * B ^ (p * Ppat (0 - k) + q * Ppat (1 - k)))
    (h' : ∀ p q : ℤ, r p q = r 0 0 * B' ^ (p * Ppat (0 - k') + q * Ppat (1 - k')))
    (h0 : 0 < r 0 0) : B = B' := by
  have hB0 : 0 < B := by linarith
  have hB0' : 0 < B' := by linarith
  -- the ratio to the neighbor in direction `j`
  have hrat : ∀ j : Fin 6, B ^ Ppat (j - k) = B' ^ Ppat (j - k') := by
    intro j
    have e := (h (ldir j).1 (ldir j).2).symm.trans (h' (ldir j).1 (ldir j).2)
    rw [grad_ldir, grad_ldir] at e
    exact mul_left_cancel₀ h0.ne' e
  -- `B^2 ≤ B'^2` and `B'^2 ≤ B^2`
  have hle : ∀ (C C' : ℝ) (kk kk' : Fin 6), 1 < C → 1 < C' →
      (∀ j : Fin 6, C ^ Ppat (j - kk) = C' ^ Ppat (j - kk')) → C ^ 2 ≤ C' ^ 2 := by
    intro C C' kk kk' hC hC' hj
    have := hj kk
    rw [sub_self, show Ppat 0 = 2 from rfl] at this
    rw [← zpow_natCast, ← zpow_natCast]
    push_cast
    rw [this]
    exact zpow_le_zpow_right₀ hC'.le (Ppat_le_two _)
  have h1 := hle B B' k k' hB hB' hrat
  have h2 := hle B' B k' k hB' hB (fun j => (hrat j).symm)
  nlinarith

/-! ### Hexagonal balls -/

/-- `u` lies in the `m`-ring patch: `max(|p|, |q|, |p+q|) ≤ m`. -/
def InBall (m : ℤ) (u : ℤ × ℤ) : Prop :=
  -m ≤ u.1 ∧ u.1 ≤ m ∧ -m ≤ u.2 ∧ u.2 ≤ m ∧ -m ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ m

lemma ldir_fst_snd (j : Fin 6) (u : ℤ × ℤ) :
    (u + ldir j).1 = u.1 + (ldir j).1 ∧ (u + ldir j).2 = u.2 + (ldir j).2 := ⟨rfl, rfl⟩

/-- A point of the `(n+1)`-ball lies in the `n`-ball or has a neighbor there. -/
lemma ball_step {n : ℤ} (hn : 0 ≤ n) {u : ℤ × ℤ} (hu : InBall (n + 1) u) :
    InBall n u ∨ ∃ j : Fin 6, InBall n (u + ldir j) := by
  obtain ⟨p, q⟩ := u
  unfold InBall at *
  simp only [ldir] at *
  by_cases h : -n ≤ p ∧ p ≤ n ∧ -n ≤ q ∧ q ≤ n ∧ -n ≤ p + q ∧ p + q ≤ n
  · exact Or.inl h
  right
  by_cases h0 : -n ≤ p + 1 ∧ p + 1 ≤ n ∧ -n ≤ q ∧ q ≤ n ∧ -n ≤ p + 1 + q ∧ p + 1 + q ≤ n
  · exact ⟨0, by simpa using h0⟩
  by_cases h1 : -n ≤ p ∧ p ≤ n ∧ -n ≤ q + 1 ∧ q + 1 ≤ n ∧ -n ≤ p + (q + 1) ∧ p + (q + 1) ≤ n
  · exact ⟨1, by simpa using h1⟩
  by_cases h2 : -n ≤ p - 1 ∧ p - 1 ≤ n ∧ -n ≤ q + 1 ∧ q + 1 ≤ n ∧ -n ≤ p - 1 + (q + 1) ∧
      p - 1 + (q + 1) ≤ n
  · exact ⟨2, by simpa [sub_eq_add_neg] using h2⟩
  by_cases h3 : -n ≤ p - 1 ∧ p - 1 ≤ n ∧ -n ≤ q ∧ q ≤ n ∧ -n ≤ p - 1 + q ∧ p - 1 + q ≤ n
  · exact ⟨3, by simpa [sub_eq_add_neg] using h3⟩
  by_cases h4 : -n ≤ p ∧ p ≤ n ∧ -n ≤ q - 1 ∧ q - 1 ≤ n ∧ -n ≤ p + (q - 1) ∧ p + (q - 1) ≤ n
  · exact ⟨4, by simpa [sub_eq_add_neg] using h4⟩
  by_cases h5 : -n ≤ p + 1 ∧ p + 1 ≤ n ∧ -n ≤ q - 1 ∧ q - 1 ≤ n ∧ -n ≤ p + 1 + (q - 1) ∧
      p + 1 + (q - 1) ≤ n
  · exact ⟨5, by simpa [sub_eq_add_neg] using h5⟩
  exfalso
  omega

lemma inBall_mono {m n : ℤ} (h : m ≤ n) {u : ℤ × ℤ} (hu : InBall m u) : InBall n u := by
  unfold InBall at *; omega

lemma inBall_zero_iff {u : ℤ × ℤ} : InBall 0 u ↔ u = 0 := by
  obtain ⟨p, q⟩ := u
  unfold InBall
  constructor
  · intro h; ext <;> simp <;> omega
  · intro h
    rw [Prod.ext_iff] at h; simp at h; omega

/-- Ball induction: a property of `0` that passes from a point to its neighbors holds on the
`n`-ball. -/
lemma ball_induction {M : ℤ} {P : ℤ × ℤ → Prop} (h0 : P 0)
    (hstep : ∀ u (j : Fin 6), InBall M u → InBall M (u + ldir j) → P (u + ldir j) → P u)
    (n : ℕ) : ∀ u, InBall (min n M) u → 0 ≤ M → P u := by
  induction n with
  | zero =>
    intro u hu hM
    rw [show min ((0 : ℕ) : ℤ) M = 0 by simp [hM]] at hu
    rw [inBall_zero_iff.1 hu]; exact h0
  | succ n ih =>
    intro u hu hM
    by_cases hnM : (n : ℤ) + 1 ≤ M
    · rw [show min ((n + 1 : ℕ) : ℤ) M = (n : ℤ) + 1 by push_cast; omega] at hu
      have hn' : min (n : ℤ) M = n := by omega
      rcases ball_step (by positivity) hu with h | ⟨j, hj⟩
      · exact ih u (by rw [hn']; exact h) hM
      · exact hstep u j (inBall_mono (by omega) hu) (inBall_mono (by omega) hj)
          (ih _ (by rw [hn']; exact hj) hM)
    · have hmin : min ((n + 1 : ℕ) : ℤ) M = min (n : ℤ) M := by push_cast; omega
      rw [hmin] at hu
      exact ih u hu hM

lemma ball_induction' {M : ℤ} (hM : 0 ≤ M) {P : ℤ × ℤ → Prop} (h0 : P 0)
    (hstep : ∀ u (j : Fin 6), InBall M u → InBall M (u + ldir j) → P (u + ldir j) → P u)
    {u : ℤ × ℤ} (hu : InBall M u) : P u := by
  have := ball_induction h0 hstep M.toNat u (by rw [Int.toNat_of_nonneg hM, min_self]; exact hu)
    hM
  exact this

/-- Every edge of the `m`-ball lies in a triangle around an interior vertex. -/
lemma edge_interior {m : ℤ} (hm : 1 ≤ m) {u : ℤ × ℤ} {j : Fin 6} (hu : InBall m u)
    (hv : InBall m (u + ldir j)) :
    InBall (m - 1) u ∨ InBall (m - 1) (u + ldir j) ∨ InBall (m - 1) (u + ldir (j + 1)) ∨
      InBall (m - 1) (u + ldir (j - 1)) := by
  obtain ⟨p, q⟩ := u
  unfold InBall at *
  fin_cases j <;> simp only [ldir] at * <;> simp at * <;> omega

/-! ### Cases 1 and 2 at single vertices -/

section Local

variable {r : ℤ → ℤ → ℝ} {a b c : ℝ}

/-- The triangles around `u` are similar to `(a, b, c)` and the flower at `u` closes. -/
def GoodAt (r : ℤ → ℤ → ℝ) (a b c : ℝ) (u : ℤ × ℤ) : Prop :=
  (∀ i : Fin 6, SimTriple (Rr r u, Rr r (u + ldir i), Rr r (u + ldir (i + 1))) (a, b, c)) ∧
    ∑ i : Fin 6, angleAt (Rr r u) (Rr r (u + ldir i)) (Rr r (u + ldir (i + 1))) = 2 * π

lemma sum_roles_at (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {u : ℤ × ℤ}
    (hsum : ∑ i : Fin 6, angleAt (Rr r u) (Rr r (u + ldir i)) (Rr r (u + ldir (i + 1)))
      = 2 * π)
    (μ : Fin 6 → ℝ) (X Y W : Fin 6 → ℝ) (hμ : ∀ i, 0 < μ i)
    (hm : ∀ i, (X i, Y i, W i) ∈ perms3 a b c)
    (hX : ∀ i, Rr r u = μ i * X i) (hY : ∀ i, Rr r (u + ldir i) = μ i * Y i)
    (hW : ∀ i, Rr r (u + ldir (i + 1)) = μ i * W i) :
    ∑ i : Fin 6, th a b c (X i) = 2 * π := by
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hX i, hY i, hW i, angle_role ha hb hc (hμ i) (hm i)]

/-- **Case 1, local.** -/
theorem generic_at (ha : 0 < a) (hab : a < b) (hbc : b < c) (hne : b ^ 2 ≠ a * c)
    {u : ℤ × ℤ} (hu : GoodAt r a b c u) (hv : GoodAt r a b c (u + ldir 0)) : False := by
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  set v := u + ldir 0
  have hsu := fun i => simTriple_iff.1 (hu.1 i)
  have hsv := fun i => simTriple_iff.1 (hv.1 i)
  choose μ hμ X Y W hm hX hY hW using hsu
  choose μ' hμ' X' Y' W' hm' hX' hY' hW' using hsv
  have hrole : ∀ i, X (i + 1) = X i := fun i =>
    (generic_ratio ha hab hbc hne (hm i) (hm (i + 1))
      (cross_ratio (hμ i) (hμ (i + 1)) (hX i) (hX (i + 1)) (hW i) (hY (i + 1)))).symm
  have hrole' : ∀ i, X' (i + 1) = X' i := fun i =>
    (generic_ratio ha hab hbc hne (hm' i) (hm' (i + 1))
      (cross_ratio (hμ' i) (hμ' (i + 1)) (hX' i) (hX' (i + 1)) (hW' i) (hY' (i + 1)))).symm
  have hsix : th a b c (X 0) = π / 3 := by
    have hsum := sum_roles_at ha hb hc hu.2 μ X Y W hμ hm hX hY hW
    rw [Finset.sum_congr rfl fun i _ => by rw [fin6_const hrole i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    linarith
  have hsix' : th a b c (X' 0) = π / 3 := by
    have hsum := sum_roles_at ha hb hc hv.2 μ' X' Y' W' hμ' hm' hX' hY' hW'
    rw [Finset.sum_congr rfl fun i _ => by rw [fin6_const hrole' i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    linarith
  have hv2 : v + ldir 2 = u + ldir 1 := by
    simp only [v, add_assoc]; congr 1
  have hW0 : Rr r (u + ldir 1) = μ 0 * W 0 := hW 0
  have hY2 : Rr r (u + ldir 1) = μ' 2 * Y' 2 := by rw [← hv2]; exact hY' 2
  have e := cross_ratio (hμ 0) (hμ' 2) (hY 0) (hX' 2) hW0 hY2
  have hYX := generic_ratio' ha hab hbc hne (hm 0) (hm' 2) e
  rw [← fin6_const hrole' 2, ← hYX] at hsix'
  have hp := perms3_pos ha hb hc (hm 0)
  exact perms3_ne hab hbc (hm 0) (th_inj ha hb hc hp.1 hp.2.1 (hsix.trans hsix'.symm))

/-- **Case 2, local.** -/
theorem isosceles_at {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t) {u : ℤ × ℤ}
    (hu : GoodAt r s s t u) : False := by
  have hsu := fun i => simTriple_iff.1 (hu.1 i)
  choose μ hμ X Y W hm hX hY hW using hsu
  have hrole : ∀ i, (X (i + 1) = t) = (X i = t) := fun i =>
    propext (iso_ratio hs ht hst (hm i) (hm (i + 1))
      (cross_ratio (hμ i) (hμ (i + 1)) (hX i) (hX (i + 1)) (hW i) (hY (i + 1))))
  have hconst := fun i => fin6_const (f := fun i => X i = t) hrole i
  have hsum := sum_roles_at hs hs ht hu.2 μ X Y W hμ hm hX hY hW
  have h3 := th_sum hs hs ht
  have hmem : ∀ i, X i = s ∨ X i = t := by
    intro i
    have := hm i
    rw [perms3_mem] at this
    rcases this with h | h | h | h | h | h <;> simp only [h.1, true_or, or_true]
  by_cases h0 : X 0 = t
  · have hall : ∀ i, X i = t := fun i => by
      have := hconst i; simp only [eq_iff_iff] at this; exact this.2 h0
    rw [Finset.sum_congr rfl fun i _ => by rw [hall i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    exact hst (th_inj hs hs ht hs ht (by linarith))
  · have hall : ∀ i, X i = s := fun i => by
      have := hconst i; simp only [eq_iff_iff] at this
      exact (hmem i).resolve_right fun h => h0 (this.1 h)
    rw [Finset.sum_congr rfl fun i _ => by rw [hall i]] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    exact hst (th_inj hs hs ht hs ht (by linarith))

end Local

/-! ### Case 3 on a patch -/

lemma ldir_j1_j4 (j : Fin 6) : ldir (j + 1) + ldir (j + 1 + 3) = 0 := ldir_add_three _

lemma ldir_j1_j5 (j : Fin 6) : ldir (j + 1) + ldir (j + 1 + 3 + 1) = ldir j := by
  fin_cases j <;> decide

lemma ldir_jm1_j2 (j : Fin 6) : ldir (j - 1) + ldir (j - 1 + 3) = 0 := ldir_add_three _

lemma ldir_jm1_j1 (j : Fin 6) : ldir (j - 1) + ldir (j - 1 + 2) = ldir j := by
  fin_cases j <;> decide

lemma ldir_j_j3 (j : Fin 6) : ldir j + ldir (j + 3) = 0 := ldir_add_three _

section Patch

variable {r : ℤ → ℤ → ℝ}

/-- In a triangle around a vertex where the shape is `(a, aB, aB²)`, the radii are `B`-power
multiples of the radius at the vertex. -/
lemma tri_pow {a B : ℝ} (ha : 0 < a) (hB : 1 < B) {w : ℤ × ℤ} (i : Fin 6)
    (hs : SimTriple (Rr r w, Rr r (w + ldir i), Rr r (w + ldir (i + 1)))
      (a, a * B, a * B ^ 2)) :
    ∃ e1 e2 : ℤ, Rr r (w + ldir i) = Rr r w * B ^ e1 ∧
      Rr r (w + ldir (i + 1)) = Rr r w * B ^ e2 := by
  obtain ⟨μ, hμ, x, y, z, hm, hX, hY, hW⟩ := simTriple_iff.1 hs
  obtain ⟨e1, e2, -, hy, hz, -⟩ := gp_pair ha hB hm
  exact ⟨e1, e2, by rw [hY, hy, hX]; ring, by rw [hW, hz, hX]; ring⟩

lemma ratio_swap {B : ℝ} (hB : 0 < B) {P Q : ℝ} {e : ℤ} (h : P = Q * B ^ e) :
    Q = P * B ^ (-e) := by
  rw [h, mul_assoc, ← zpow_add₀ hB.ne', add_neg_cancel, zpow_zero, mul_one]

lemma ratio_trans {B : ℝ} (hB : 0 < B) {P Q S : ℝ} {e f : ℤ} (h1 : Q = P * B ^ e)
    (h2 : S = P * B ^ f) : S = Q * B ^ (f - e) := by
  rw [h1, h2, mul_assoc, ← zpow_add₀ hB.ne']; congr 2; ring

/-- **Case 3 on a patch.** -/
theorem gp_patch {m : ℤ} (hm : 2 ≤ m) {a B : ℝ} (ha : 0 < a) (hB : 1 < B)
    (hgood : ∀ u, InBall (m - 1) u → GoodAt r a (a * B) (a * B ^ 2) u) :
    ∃ k : Fin 6, ∀ u, InBall m u →
      Rr r u = Rr r 0 * B ^ (u.1 * Ppat (0 - k) + u.2 * Ppat (1 - k)) := by
  have hB0 : 0 < B := by linarith
  have hB1 : B ≠ 1 := hB.ne'
  have haB : 0 < a * B := by positivity
  have haB2 : 0 < a * B ^ 2 := by positivity
  have hm1 : 1 ≤ m := by omega
  -- every edge of the patch has a `B`-power ratio
  have hedge : ∀ u (j : Fin 6), InBall m u → InBall m (u + ldir j) →
      ∃ e : ℤ, Rr r (u + ldir j) = Rr r u * B ^ e := by
    intro u j hu hv
    rcases edge_interior hm1 hu hv with h | h | h | h
    · obtain ⟨e1, -, h1, -⟩ := tri_pow ha hB j ((hgood u h).1 j)
      exact ⟨e1, h1⟩
    · obtain ⟨e1, -, h1, -⟩ := tri_pow ha hB (j + 3) ((hgood _ h).1 (j + 3))
      rw [add_assoc, ldir_j_j3, add_zero] at h1
      exact ⟨-e1, ratio_swap hB0 h1⟩
    · obtain ⟨e1, e2, h1, h2⟩ := tri_pow ha hB (j + 1 + 3) ((hgood _ h).1 (j + 1 + 3))
      rw [add_assoc, ldir_j1_j4, add_zero] at h1
      rw [add_assoc, ldir_j1_j5] at h2
      exact ⟨e2 - e1, ratio_trans hB0 h1 h2⟩
    · obtain ⟨e1, e2, h1, h2⟩ := tri_pow ha hB (j - 1 + 2) ((hgood _ h).1 (j - 1 + 2))
      rw [add_assoc, ldir_jm1_j1] at h1
      rw [show j - 1 + 2 + 1 = j - 1 + 3 by rw [add_assoc]; rfl, add_assoc, ldir_jm1_j2,
        add_zero] at h2
      exact ⟨e1 - e2, ratio_trans hB0 h2 h1⟩
  -- an integer exponent on the patch
  have hexp : ∀ u, InBall m u → ∃ e : ℤ, Rr r u = Rr r 0 * B ^ e := by
    intro u hu
    refine ball_induction' (M := m) (by omega)
      (P := fun u => ∃ e : ℤ, Rr r u = Rr r 0 * B ^ e) ⟨0, by simp⟩ ?_ hu
    intro u j hu hv ⟨e, he⟩
    obtain ⟨f, hf⟩ := hedge u j hu hv
    refine ⟨e - f, ?_⟩
    have := ratio_swap hB0 hf
    rw [this, he, mul_assoc, ← zpow_add₀ hB0.ne', ← sub_eq_add_neg]
  have hexp' : ∀ u, ∃ e : ℤ, InBall m u → Rr r u = Rr r 0 * B ^ e := by
    intro u
    by_cases hu : InBall m u
    · obtain ⟨e, he⟩ := hexp u hu; exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => (hu h).elim⟩
  choose ℓ hℓ using hexp'
  have h00 : InBall (m - 1) 0 := by unfold InBall; simp; omega
  have hR0 : 0 < Rr r 0 := by
    obtain ⟨μ, hμ, x, y, w, hmm, hX, -, -⟩ := simTriple_iff.1 ((hgood 0 h00).1 0)
    rw [hX]; exact mul_pos hμ (perms3_pos ha haB haB2 hmm).1
  have hinj : ∀ e f : ℤ, Rr r 0 * B ^ e = Rr r 0 * B ^ f → e = f := fun e f h =>
    (zpow_right_inj₀ hB0 hB1).1 (mul_left_cancel₀ hR0.ne' h)
  -- the pattern at the interior vertices
  have hpat : ∀ u, InBall (m - 1) u → ∃ k, HasAxis ℓ u k := by
    intro u hu
    have hs := fun i => simTriple_iff.1 ((hgood u hu).1 i)
    choose μ hμ X Y W hmm hX hY hW using hs
    have hp := fun i => gp_pair ha hB (hmm i)
    choose e1 e2 hpair hYe hWe hang using hp
    have huM : InBall m u := inBall_mono (by omega) hu
    have hin : ∀ i, InBall m (u + ldir i) := by
      intro i; obtain ⟨p, q⟩ := u; unfold InBall at *
      fin_cases i <;> simp only [ldir] at * <;> simp at * <;> omega
    have hd1 : ∀ i, ℓ (u + ldir i) - ℓ u = e1 i := by
      intro i
      have h := hℓ (u + ldir i) (hin i)
      rw [hY, hYe, ← mul_assoc, ← hX, hℓ u huM, mul_assoc, ← zpow_add₀ hB0.ne'] at h
      have := hinj _ _ h.symm; omega
    have hd2 : ∀ i, ℓ (u + ldir (i + 1)) - ℓ u = e2 i := by
      intro i
      have h := hℓ (u + ldir (i + 1)) (hin (i + 1))
      rw [hW, hWe, ← mul_assoc, ← hX, hℓ u huM, mul_assoc, ← zpow_add₀ hB0.ne'] at h
      have := hinj _ _ h.symm; omega
    have hsum := sum_roles_at ha haB haB2 (hgood u hu).2 μ X Y W hμ hmm hX hY hW
    have hM : th a (a * B) (a * B ^ 2) (a * B) ≠ π / 3 := by
      have e := angle_role ha haB haB2 one_pos (x := a * B) (y := a * B ^ 2) (w := a)
        (by simp [perms3])
      simp only [one_mul] at e
      rw [← e, show a = a * 1 by ring, show a * 1 * B = a * B by ring,
        show a * 1 * B ^ 2 = a * B ^ 2 by ring, angleAt_smul ha hB0 (by positivity) one_pos]
      exact (cell_angles hB).2.2.2
    exact vertex_pattern (th_sum ha haB haB2)
      (th_lt ha haB haB2 haB (by nlinarith : a * B < a * B ^ 2))
      (th_lt ha haB haB2 ha (by nlinarith : a < a * B)) hM (fun i => ℓ (u + ldir i) - ℓ u)
      (fun i => by rw [hd1 i, hd2 i]; exact hpair i)
      (by
        rw [← hsum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hd1 i, hd2 i, hang i])
  -- the axis is constant on the interior
  obtain ⟨k, hk0⟩ := hpat 0 h00
  have haxis : ∀ u, InBall (m - 1) u → HasAxis ℓ u k := by
    intro u hu
    refine ball_induction' (M := m - 1) (by omega) (P := fun u => HasAxis ℓ u k) hk0 ?_ hu
    intro u j hu hv hP
    obtain ⟨k', hk'⟩ := hpat u hu
    have := axis_const hk' hP
    rwa [this] at hk'
  -- `ℓ` is affine on the interior
  have hl0 : ℓ 0 = 0 := by
    have h := hℓ 0 (inBall_mono (by omega) h00)
    exact (hinj _ 0 (by rw [← h, zpow_zero, mul_one])).symm ▸ rfl
  set g : ℤ × ℤ → ℤ := fun u => u.1 * Ppat (0 - k) + u.2 * Ppat (1 - k) with hg
  have hgadd : ∀ u (j : Fin 6), g (u + ldir j) = g u + Ppat (j - k) := by
    intro u j
    rw [← grad_ldir k j]
    simp only [hg, Prod.fst_add, Prod.snd_add]; ring
  have haff : ∀ u, InBall (m - 1) u → ℓ u = g u := by
    intro u hu
    refine ball_induction' (M := m - 1) (by omega) (P := fun u => ℓ u = g u)
      (by rw [hl0]; simp [hg]) ?_ hu
    intro u j hu _ hP
    have := haxis u hu j
    rw [hP, hgadd] at this
    linarith
  -- and on the boundary ring
  refine ⟨k, fun u hu => ?_⟩
  rw [hℓ u hu]
  congr 1
  rcases ball_step (n := m - 1) (by omega) (by rw [sub_add_cancel]; exact hu) with h | ⟨j, hj⟩
  · rw [haff u h]
  · have hax := haxis _ hj (j + 3)
    rw [add_assoc, ldir_j_j3, add_zero, haff _ hj, hgadd] at hax
    have e3 := hgadd (u + ldir j) (j + 3)
    rw [add_assoc, ldir_j_j3, add_zero] at e3
    have e4 := hgadd u j
    change B ^ ℓ u = B ^ g u
    congr 1
    linarith

/-- `GoodAt` is invariant under reordering the shape. -/
lemma GoodAt.swap12 {a b c : ℝ} {u : ℤ × ℤ} (h : GoodAt r a b c u) : GoodAt r b a c u :=
  ⟨fun i => simTriple_swap12 (h.1 i), h.2⟩

lemma GoodAt.swap23 {a b c : ℝ} {u : ℤ × ℤ} (h : GoodAt r a b c u) : GoodAt r a c b u :=
  ⟨fun i => simTriple_swap23 (h.1 i), h.2⟩

/-- The conclusion of Remark A 8.2 for radii. -/
def PatchConcl (r : ℤ → ℤ → ℝ) (m : ℤ) : Prop :=
  (∀ u, InBall (m - 1) u → ∀ i : Fin 6, Rr r (u + ldir i) = Rr r u) ∨
    ∃ B > 1, ∃ k : Fin 6, ∀ u, InBall m u →
      Rr r u = Rr r 0 * B ^ (u.1 * Ppat (0 - k) + u.2 * Ppat (1 - k))

lemma patch_sorted {m : ℤ} (hm : 2 ≤ m) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hgood : ∀ u, InBall (m - 1) u → GoodAt r a b c u) : PatchConcl r m := by
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  have h00 : InBall (m - 1) 0 := by unfold InBall; simp; omega
  have h10 : InBall (m - 1) (0 + ldir 0) := by unfold InBall; simp [ldir]; omega
  rcases eq_or_lt_of_le (hab.trans hbc) with hac | hac
  · left
    intro u hu i
    obtain ⟨μ, hμ, x, y, w, hmm, h1, h2, -⟩ := simTriple_iff.1 ((hgood u hu).1 i)
    have hb' : b = a := le_antisymm (hac ▸ hbc) hab
    have hc' : c = a := hac.symm
    rw [perms3_mem] at hmm
    rw [h1, h2]
    rcases hmm with h | h | h | h | h | h <;> rw [h.1, h.2.1] <;> simp [hb', hc']
  · rcases eq_or_lt_of_le hab with hab' | hab'
    · subst hab'
      exact (isosceles_at ha hc hac.ne (hgood 0 h00)).elim
    rcases eq_or_lt_of_le hbc with hbc' | hbc'
    · subst hbc'
      exact (isosceles_at hb ha hab'.ne' (hgood 0 h00).swap12.swap23).elim
    by_cases hg : b ^ 2 = a * c
    · right
      set B := b / a with hBdef
      have hB : 1 < B := by rw [hBdef, one_lt_div ha]; exact hab'
      have hbB : b = a * B := by rw [hBdef]; field_simp
      have hcB : c = a * B ^ 2 := by
        rw [hBdef]
        field_simp
        nlinarith [hg]
      rw [hbB, hcB] at hgood
      exact ⟨B, hB, gp_patch hm ha hB hgood⟩
    · exact (generic_at ha hab' hbc' hg (hgood 0 h00) (hgood _ h10)).elim

/-- **Remark A 8.2 (radius part).** Let `m ≥ 2`. If the triangles around every interior
vertex of the `m`-ring patch are similar to one triangle `(a, b, c)` and the flowers at the
interior vertices close up, then either these triangles are equilateral or
`r(u) = r(0) B^{p a' + q b'}` on the whole patch, with `B > 1` and `(a', b')` a rotation of
`(2, 1)`. -/
theorem oneshape_patch {m : ℤ} (hm : 2 ≤ m) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hgood : ∀ u, InBall (m - 1) u → GoodAt r a b c u) : PatchConcl r m := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  · exact patch_sorted hm ha hab hbc hgood
  · exact patch_sorted hm ha hab hbc hgood
  · exact patch_sorted hm ha hac hbc fun u hu => (hgood u hu).swap23
  · exact patch_sorted hm hc hac hab fun u hu => (hgood u hu).swap23.swap12
  · exact patch_sorted hm hb hab hac fun u hu => (hgood u hu).swap12
  · exact patch_sorted hm hb hbc hac fun u hu => (hgood u hu).swap12.swap23
  · exact patch_sorted hm hc hbc hab fun u hu => (hgood u hu).swap12.swap23.swap12
  · exact patch_sorted hm hc hbc hab fun u hu => (hgood u hu).swap12.swap23.swap12

end Patch

end DoyleFormal
