/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.Overlap

/-!
# Coherence of the resonant spirals (paper B, Proposition 5.3) — Phase 4g

For `B = B_n` (`ψ = π/n`, `n ≥ 2`), two circles of `D_B` at lattice points `u` and `u + w`:

* `coherent_coincide_iff`: coincide iff `w ∈ ℤ(−n, 2n)`;
* `coherent_no_overlap`: otherwise their interiors are disjoint (no overlap).

So `D_{B_n}` is, after identifying coinciding circles, a packing with disjoint interiors.
(The tangency statement of Proposition B 5.3 is not formalized.)
-/

namespace DoyleFormal

open Complex

lemma sin_sq_add_int_mul_pi (x : ℝ) (k : ℤ) :
    Real.sin (x + k * Real.pi) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_add, Real.sin_int_mul_pi, mul_zero, add_zero, mul_pow]
  have h := Real.sin_sq_add_cos_sq (k * Real.pi)
  rw [Real.sin_int_mul_pi] at h
  rw [show Real.cos (k * Real.pi) ^ 2 = 1 by nlinarith, mul_one]

/-- For `N ≥ 2` and `N ∤ j`: `sin²(π/N) ≤ sin²(jπ/N)`. -/
lemma sin_sq_le_of_not_dvd {N : ℤ} (hN : 2 ≤ N) (j : ℤ) (hj : ¬ N ∣ j) :
    Real.sin (Real.pi / N) ^ 2 ≤ Real.sin (j * Real.pi / N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : (0 : ℤ) < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hρ0 : 0 ≤ j % N := Int.emod_nonneg j (by omega)
  have hρN : j % N < N := Int.emod_lt_of_pos j (by omega)
  have hρne : j % N ≠ 0 := fun h => hj (Int.dvd_of_emod_eq_zero h)
  have hjk : j = N * (j / N) + j % N := by have := Int.mul_ediv_add_emod j N; linarith
  have hρ1 : (1 : ℝ) ≤ ((j % N : ℤ) : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ j % N)
  have hρN' : ((j % N : ℤ) : ℝ) ≤ N - 1 := by
    have : j % N ≤ N - 1 := by omega
    exact_mod_cast this
  have hx : (j : ℝ) * Real.pi / N
      = ((j % N : ℤ) : ℝ) * Real.pi / N + ((j / N : ℤ) : ℝ) * Real.pi := by
    conv_lhs => rw [hjk]
    push_cast
    field_simp
    ring
  rw [hx, sin_sq_add_int_mul_pi]
  have hpi := Real.pi_pos
  have h1 : Real.pi / N ≤ Real.pi / 2 := div_le_div_of_nonneg_left hpi.le (by norm_num) hN2
  have hle := sin_le_sin_of_mem (ψ := Real.pi / N) (x := ((j % N : ℤ) : ℝ) * Real.pi / N)
    (by positivity) h1
    (by rw [div_le_div_iff_of_pos_right hN0]; nlinarith)
    (by
      rw [show Real.pi - Real.pi / N = (N - 1) * Real.pi / N by field_simp,
        div_le_div_iff_of_pos_right hN0]
      nlinarith)
  have h0 : 0 ≤ Real.sin (Real.pi / N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
  nlinarith

/-- **Proposition B 5.3, coincidence.** For `ψ(B) = π/n`, `K(u+w) = K(u)` iff
`w ∈ ℤ(−n, 2n)`. -/
theorem coherent_coincide_iff {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n)
    (hψn : psi B = Real.pi / n) (p q a b : ℤ) :
    (rad B (p + a) (q + b) = rad B p q ∧ zc B (psi B) (p + a) (q + b) = zc B (psi B) p q) ↔
      ∃ k : ℤ, a = -(k * n) ∧ b = 2 * (k * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [same_circle_iff (psi B) hB p q (p + a) (q + b)]
  constructor
  · rintro ⟨j, hj1, hj2, m, hm⟩
    rw [hψn, mul_div_assoc', div_eq_iff hn0.ne'] at hm
    have hjm : (j : ℝ) = m * n := by nlinarith [Real.pi_pos]
    have hjm' : j = m * n := by exact_mod_cast hjm
    exact ⟨m, by omega, by rw [← hjm']; omega⟩
  · rintro ⟨k, ha, hb⟩
    refine ⟨k * n, by omega, by omega, k, ?_⟩
    rw [hψn]; push_cast; field_simp

/-- The case `s = ±1` of Proposition B 5.3: for odd `b`, `sin(ψ/2) ≤ |sin(bψ/2)|`. -/
lemma odd_case {B : ℝ} (_hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n) (b : ℤ)
    (hodd : b % 2 = 1) : Real.sin (psi B / 2) ≤ |Real.sin (b * psi B / 2)| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb : ¬ (2 * n : ℤ) ∣ b := by
    intro h
    have : (2 : ℤ) ∣ b := dvd_trans (Dvd.intro (n : ℤ) rfl) h
    omega
  have h2 := sin_sq_le_of_not_dvd (N := 2 * (n : ℤ)) (by omega) b hb
  push_cast at h2
  have e1 : psi B / 2 = Real.pi / (2 * n) := by rw [hψn]; field_simp
  have e2 : (b : ℝ) * psi B / 2 = b * Real.pi / (2 * n) := by rw [hψn]; field_simp
  rw [e1, e2]
  have hpos : 0 < Real.sin (Real.pi / (2 * n)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact (lt_mul_iff_one_lt_right Real.pi_pos).2 (by linarith)
  have := sq_le_sq.1 h2
  rwa [abs_of_pos hpos] at this

/-- **Proposition B 5.3, disjointness.** For `ψ(B) = π/n`, `n ≥ 2`, circles at `u` and `u + w`
with `w ∉ ℤ(−n, 2n)` do not overlap. -/
theorem coherent_no_overlap {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n)
    (hψn : psi B = Real.pi / n) (p q a b : ℤ) (hw : ¬ ∃ k : ℤ, a = -(k * n) ∧ b = 2 * (k * n)) :
    ¬ ‖zc B (psi B) (p + a) (q + b) - zc B (psi B) p q‖ < rad B (p + a) (q + b) + rad B p q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hfar : 2 ≤ |2 * a + b|
  · exact no_overlap_far _ hB p q a b hfar
  have hs : 2 * a + b = 0 ∨ 2 * a + b = 1 ∨ 2 * a + b = -1 := by
    rw [le_abs', not_or] at hfar; omega
  rcases hs with hs | hs | hs
  · -- `w = j(−1,2)` with `n ∤ j`
    obtain ⟨j, rfl, rfl⟩ : ∃ j, a = -j ∧ b = 2 * j := ⟨-a, by ring, by omega⟩
    have hj : ¬ (n : ℤ) ∣ j := by
      rintro ⟨k, hk⟩
      exact hw ⟨k, by rw [hk]; ring, by rw [hk]; ring⟩
    rw [overlap_s0 _ hB, not_lt]
    have h1 := E_no_overlap_before hB 1 le_rfl (by
      rw [hψn]; push_cast
      rw [show ((1 : ℝ) + 1) * (Real.pi / n) = 2 * Real.pi / n by ring,
        div_le_iff₀ hn0]
      nlinarith [Real.pi_pos])
    rw [not_lt] at h1
    have h2 := sin_sq_le_of_not_dvd (N := (n : ℤ)) (by exact_mod_cast hn) j hj
    push_cast at h1 h2
    rw [hψn] at h1 ⊢
    rw [one_mul] at h1
    rw [show (j : ℝ) * (Real.pi / n) = j * Real.pi / n by ring]
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  · rw [overlap_s1_sin hB p q a b hs, not_lt]
    exact odd_case hB hn hψn b (by omega)
  · rw [overlap_sm1_sin hB p q a b hs, not_lt]
    exact odd_case hB hn hψn b (by omega)

end DoyleFormal
