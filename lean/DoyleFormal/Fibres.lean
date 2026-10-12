/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Asymp

/-!
# The fibres of the developing map are cosets of a group of translations — Phase 5d

For a `HexPacking` `P` with developing map `F` (`HexPacking.F`), write `f u = (F u).1`.

* `S_shift`: shifting the offset of a state by `s` turns a step in direction `i + s` into a
  step in direction `i`.
* `dev_rot`: if `f u = f u'`, then `F (u' + w)` is `F (u + R^s w)` with the offset shifted by
  `s`, for all `w`, where `R^s` is the lattice rotation by `60° s` and `s` is the difference of
  the offsets at `u'` and `u`.
* `rot_fixed_or_adjacent`: for `s ≠ 0`, every map `x ↦ R^s x + c` moves some lattice point by
  `0` or by a lattice direction.
* `fibre_translation` (**the fibres are cosets of a group of translations**): `f u = f u'` iff
  `u' − u` is a deck translation, i.e. `f (x + (u' − u)) = f x` for all `x`.
-/

namespace DoyleFormal

/-- The lattice rotation `R^m`, `R(p,q) = (−q, p+q)`. -/
def rotN (m : ℕ) (u : ℤ × ℤ) : ℤ × ℤ := latRot^[m] u

lemma latRot_add (a b : ℤ × ℤ) : latRot (a + b) = latRot a + latRot b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [latRot, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring

lemma rotN_add (m : ℕ) (a b : ℤ × ℤ) : rotN m (a + b) = rotN m a + rotN m b := by
  induction m generalizing a b with
  | zero => rfl
  | succ m ih => simp only [rotN, Function.iterate_succ_apply'] at ih ⊢; rw [ih, latRot_add]

lemma rotN_zero (m : ℕ) : rotN m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rotN, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; simp [latRot]

lemma rotN_sub (m : ℕ) (a b : ℤ × ℤ) : rotN m (a - b) = rotN m a - rotN m b := by
  have h := rotN_add m (a - b) b
  rw [sub_add_cancel] at h
  rw [h]; abel

lemma rotN_ldir (s i : Fin 6) : rotN s.val (ldir i) = ldir (i + s) := by
  revert s i; decide

namespace HexPacking

variable {V : Type*} (P : HexPacking V)

lemma nb_ne' (v : V) (i : Fin 6) : P.nb v i ≠ v := by
  intro h
  have := P.tan v i
  rw [h, sub_self, norm_zero] at this
  linarith [P.ρ_pos v]

lemma fin_shift1 (i k s : Fin 6) : i + (k + s) = i + s + k := by revert i k s; decide
lemma fin_shift2 (J i s : Fin 6) : J - (i + 3) = J - (i + s + 3) + s := by revert J i s; decide

/-- Shifting the offset of a state. -/
lemma S_shift (x : V × Fin 6) (s i : Fin 6) :
    P.S (x.1, x.2 + s) i = ((P.S x (i + s)).1, (P.S x (i + s)).2 + s) := by
  obtain ⟨v, k⟩ := x
  simp only [S, fin_shift1]
  rw [fin_shift2 _ i s]

variable (x0 : V × Fin 6)

/-- The developing map on pairs. -/
noncomputable def Fp (u : ℤ × ℤ) : V × Fin 6 := P.F x0 u.1 u.2

/-- `f u = (F u).1`. -/
noncomputable def f (u : ℤ × ℤ) : V := (P.Fp x0 u).1

lemma Fp_step (u : ℤ × ℤ) (i : Fin 6) : P.Fp x0 (u + ldir i) = P.S (P.Fp x0 u) i :=
  P.dev_step x0 u i

/-- Two functions on `ℤ²` obeying the step rule and agreeing at `0` agree. -/
lemma step_unique {G H : ℤ × ℤ → V × Fin 6}
    (hG : ∀ w (i : Fin 6), G (w + ldir i) = P.S (G w) i)
    (hH : ∀ w (i : Fin 6), H (w + ldir i) = P.S (H w) i) (h0 : G 0 = H 0) :
    ∀ w, G w = H w := by
  have e0 : ∀ p q : ℤ, (p, q) + ldir 0 = (p + 1, q) := fun p q => by simp [ldir]
  have e1 : ∀ p q : ℤ, (p, q) + ldir 1 = (p, q + 1) := fun p q => by simp [ldir]
  have e3 : ∀ p q : ℤ, (p, q) + ldir 3 = (p - 1, q) := fun p q => by
    simp [ldir, sub_eq_add_neg]
  have e4 : ∀ p q : ℤ, (p, q) + ldir 4 = (p, q - 1) := fun p q => by
    simp [ldir, sub_eq_add_neg]
  have hrow : ∀ p : ℤ, G (p, 0) = H (p, 0) := by
    intro p
    induction p using Int.induction_on with
    | zero => exact h0
    | succ n ih => rw [← e0, hG, hH, ih]
    | pred n ih => rw [← e3, hG, hH, ih]
  intro w
  obtain ⟨p, q⟩ := w
  induction q using Int.induction_on with
  | zero => exact hrow p
  | succ n ih => rw [← e1, hG, hH, ih]
  | pred n ih => rw [← e4, hG, hH, ih]

/-- **Developing from two points of one fibre.** -/
theorem dev_rot {u u' : ℤ × ℤ} (h : P.f x0 u = P.f x0 u') (w : ℤ × ℤ) :
    P.Fp x0 (u' + w) =
      ((P.Fp x0 (u + rotN ((P.Fp x0 u').2 - (P.Fp x0 u).2).val w)).1,
       (P.Fp x0 (u + rotN ((P.Fp x0 u').2 - (P.Fp x0 u).2).val w)).2 +
         ((P.Fp x0 u').2 - (P.Fp x0 u).2)) := by
  set s := (P.Fp x0 u').2 - (P.Fp x0 u).2 with hs
  refine P.step_unique (G := fun w => P.Fp x0 (u' + w))
    (H := fun w => ((P.Fp x0 (u + rotN s.val w)).1, (P.Fp x0 (u + rotN s.val w)).2 + s))
    ?_ ?_ ?_ w
  · intro w i
    rw [← add_assoc, Fp_step]
  · intro w i
    rw [rotN_add, rotN_ldir, ← add_assoc, Fp_step, ← S_shift]
  · simp only [add_zero, rotN_zero]
    have hf : (P.Fp x0 u').1 = (P.Fp x0 u).1 := h.symm
    ext
    · exact hf
    · simp only [hs]; abel_nf

/-- **The rotations of the lattice move some point by `0` or by a lattice direction.** -/
lemma rot_fixed_or_adjacent (s : Fin 6) (hs : s ≠ 0) (c : ℤ × ℤ) :
    ∃ x : ℤ × ℤ, rotN s.val x + c = x ∨ ∃ j : Fin 6, rotN s.val x + c = x + ldir j := by
  obtain ⟨c1, c2⟩ := c
  fin_cases s
  all_goals try (exact absurd rfl hs)
  · -- 60°: a fixed point
    refine ⟨(-c2, c1 + c2), Or.inl ?_⟩
    ext <;> simp [rotN, latRot]
  · -- 120°: `R² x + c − x = (c₁ − 2p − q, c₂ + p − q)`
    have h3 : (c1 - c2) % 3 = 0 ∨ (c1 - c2) % 3 = 1 ∨ (c1 - c2) % 3 = 2 := by omega
    rcases h3 with h | h | h
    · refine ⟨((c1 - c2) / 3, (c1 - c2) / 3 + c2), Or.inl ?_⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ]
      all_goals omega
    · refine ⟨((c1 - c2 - 1) / 3, (c1 - c2 - 1) / 3 + c2), Or.inr ⟨0, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
    · refine ⟨((c1 - c2 + 1) / 3, (c1 - c2 + 1) / 3 + c2), Or.inr ⟨3, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
  · -- 180°: `c − 2x`
    have ha : c1 % 2 = 0 ∨ c1 % 2 = 1 := by omega
    have hb : c2 % 2 = 0 ∨ c2 % 2 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · refine ⟨(c1 / 2, c2 / 2), Or.inl ?_⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ]
      all_goals omega
    · refine ⟨(c1 / 2, (c2 - 1) / 2), Or.inr ⟨1, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
    · refine ⟨((c1 - 1) / 2, c2 / 2), Or.inr ⟨0, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
    · refine ⟨((c1 + 1) / 2, (c2 - 1) / 2), Or.inr ⟨2, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
  · -- 240°: `R⁴ x + c − x = (c₁ + q − p, c₂ − p − 2q)`
    have h3 : (c1 - c2) % 3 = 0 ∨ (c1 - c2) % 3 = 1 ∨ (c1 - c2) % 3 = 2 := by omega
    rcases h3 with h | h | h
    · refine ⟨((c2 - c1) / 3 + c1, (c2 - c1) / 3), Or.inl ?_⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ]
      all_goals omega
    · refine ⟨((c2 - c1 + 1) / 3 + c1 - 1, (c2 - c1 + 1) / 3), Or.inr ⟨0, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
    · refine ⟨((c2 - c1 - 1) / 3 + c1 + 1, (c2 - c1 - 1) / 3), Or.inr ⟨3, ?_⟩⟩
      ext <;> simp [rotN, latRot, Function.iterate_succ, ldir]
      all_goals omega
  · -- 300°: a fixed point
    refine ⟨(c1 + c2, -c1), Or.inl ?_⟩
    ext <;> simp [rotN, latRot, Function.iterate_succ]
    all_goals ring

/-- **The fibres of the developing map are cosets of a group of translations.** -/
theorem fibre_translation (u u' : ℤ × ℤ) :
    P.f x0 u = P.f x0 u' ↔ ∀ x, P.f x0 (x + (u' - u)) = P.f x0 x := by
  constructor
  · intro h
    have hrot := P.dev_rot x0 h
    obtain ⟨s, hs⟩ : ∃ s, s = (P.Fp x0 u').2 - (P.Fp x0 u).2 := ⟨_, rfl⟩
    simp only [← hs] at hrot
    -- `τ x = u + R^s (x − u')` satisfies `f (τ x) = f x`
    have hτ : ∀ x, P.f x0 (u + rotN s.val (x - u')) = P.f x0 x := by
      intro x
      have := congrArg Prod.fst (hrot (x - u'))
      rw [show u' + (x - u') = x by abel] at this
      exact this.symm
    have hnb : ∀ y (i : Fin 6), P.f x0 (y + ldir i) = P.nb (P.Fp x0 y).1 (i + (P.Fp x0 y).2) :=
      fun y i => by simp only [f]; rw [Fp_step]; rfl
    -- the offsets agree
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨x, hx | ⟨j, hx⟩⟩ := rot_fixed_or_adjacent s hs0 (u - rotN s.val u')
      · -- a fixed point: the flower at `x` would be rotated by `s`
        have hfix : P.f x0 (x + ldir s) = P.f x0 (x + ldir 0) := by
          rw [← hτ (x + ldir 0)]
          congr 1
          rw [rotN_sub, rotN_add, rotN_ldir, zero_add]
          have hx' : x = rotN s.val x + (u - rotN s.val u') := hx.symm
          conv_lhs => rw [hx']
          abel
        rw [hnb, hnb] at hfix
        have := P.inj _ hfix
        exact hs0 (add_right_cancel this)
      · -- `τ x = x + d_j`: a circle would be its own petal
        have hxj : P.f x0 (x + ldir j) = P.f x0 x := by
          rw [← hτ x]
          congr 1
          rw [rotN_sub, ← hx]; abel
        rw [hnb] at hxj
        exact P.nb_ne' _ _ hxj
    -- hence `f (u' + w) = f (u + w)`
    intro x
    have := congrArg Prod.fst (hrot (x - u))
    rw [hs0] at this
    simp only [Fin.val_zero, rotN, Function.iterate_zero, id_eq] at this
    rw [show u' + (x - u) = x + (u' - u) by abel, show u + (x - u) = x by abel] at this
    exact this
  · intro h
    have := h u
    rw [show u + (u' - u) = u' by abel] at this
    exact this.symm

end HexPacking

end DoyleFormal
