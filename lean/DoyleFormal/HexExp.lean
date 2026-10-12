/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.DoyleStructure

/-!
# Paper C, Lemma 3.2: the exponential bound (Phase C2)

`Hex s = {z : |Re(z · conj nₖ)| < s, k = 0, 1, 2}` with the edge normals
`nₖ = e^{i(π/6 + kπ/3)}`; `Hex (√3/2)` is the open regular hexagon `P` with vertices at the
sixth roots of unity, and `Hex √3 = 2P`.

* `exp_inj_iff` (**Lemma C 3.2**): `z ↦ e^{cz}` is injective on `P` iff `2πi/c ∉ 2P`.
* `exp_inj_bound`: injectivity implies `|c| ≤ 2π/√3`, with equality only if `2πi/c` is an edge
  midpoint `±√3 nₖ` of `2P`.
-/

namespace DoyleFormal

open Complex

/-- The edge normals. -/
noncomputable def hexN (k : Fin 3) : ℂ := exp (((Real.pi / 6 + k * (Real.pi / 3) : ℝ) : ℂ) * I)

lemma norm_hexN (k : Fin 3) : ‖hexN k‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- The open hexagon with inradius `s`. -/
def Hex (s : ℝ) : Set ℂ := {z | ∀ k : Fin 3, |(z * (starRingEnd ℂ) (hexN k)).re| < s}

lemma re_smul (t : ℝ) (z w : ℂ) : ((t : ℂ) * z * w).re = t * (z * w).re := by
  simp [Complex.mul_re]; ring

lemma hex_scale {s t : ℝ} (ht : 0 < t) {z : ℂ} : (t : ℂ) * z ∈ Hex (t * s) ↔ z ∈ Hex s := by
  simp only [Hex, Set.mem_ofPred_eq, re_smul, abs_mul, abs_of_pos ht]
  constructor <;> intro h k
  · have := h k; nlinarith [abs_nonneg ((z * (starRingEnd ℂ) (hexN k)).re)]
  · have := h k; nlinarith [abs_nonneg ((z * (starRingEnd ℂ) (hexN k)).re)]

lemma hex_neg {s : ℝ} {z : ℂ} (h : z ∈ Hex s) : -z ∈ Hex s := by
  intro k; rw [neg_mul, Complex.neg_re, abs_neg]; exact h k

lemma hex_sub {s : ℝ} {z w : ℂ} (hz : z ∈ Hex s) (hw : w ∈ Hex s) : z - w ∈ Hex (2 * s) := by
  intro k
  have a := hz k; have b := hw k
  rw [sub_mul, Complex.sub_re]
  calc |(z * _).re - (w * _).re| ≤ |(z * _).re| + |(w * _).re| := abs_sub _ _
    _ < 2 * s := by linarith

lemma hex_div_int {s : ℝ} {z : ℂ} (h : z ∈ Hex s) {m : ℤ} (hm : m ≠ 0) :
    z / (m : ℂ) ∈ Hex s := by
  intro k
  have := h k
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have hre : (z / (m : ℂ) * (starRingEnd ℂ) (hexN k)).re =
      (z * (starRingEnd ℂ) (hexN k)).re / m := by
    rw [div_mul_eq_mul_div, show ((m : ℂ)) = ((m : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
  rw [hre, abs_div]
  have hpos : 0 < |(m : ℝ)| := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith [abs_nonneg ((z * (starRingEnd ℂ) (hexN k)).re)]

/-- **Lemma C 3.2.** `z ↦ e^{cz}` is injective on `P = Hex (√3/2)` iff `2πi/c ∉ 2P = Hex √3`. -/
theorem exp_inj_iff {c : ℂ} (hc : c ≠ 0) :
    Set.InjOn (fun z => exp (c * z)) (Hex (√3 / 2)) ↔ 2 * Real.pi * I / c ∉ Hex √3 := by
  set w := 2 * Real.pi * I / c with hw
  have hw0 : w ≠ 0 := by
    simp only [w]; exact div_ne_zero (by simp [Real.pi_ne_zero]) hc
  constructor
  · intro hinj hmem
    -- `±w/2` are two points of `P` with the same exponential
    have h1 : (1 / 2 : ℝ) * w ∈ Hex (√3 / 2) := by
      have := (hex_scale (s := √3) (t := 1 / 2) (by norm_num)).2 hmem
      rwa [show (1 / 2 : ℝ) * √3 = √3 / 2 by ring] at this
    have h2 : -((1 / 2 : ℝ) * w) ∈ Hex (√3 / 2) := hex_neg h1
    have heq : exp (c * ((1 / 2 : ℝ) * w)) = exp (c * (-((1 / 2 : ℝ) * w))) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨1, ?_⟩
      simp only [w]; push_cast; field_simp; ring
    have := hinj h1 h2 heq
    have : (w : ℂ) = 0 := by push_cast at this; linear_combination this
    exact hw0 this
  · intro hnot z1 hz1 z2 hz2 heq
    by_contra hne
    simp only at heq
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 heq
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at hm
      have : c * (z1 - z2) = 0 := by push_cast at hm; linear_combination hm
      rcases mul_eq_zero.1 this with h | h
      · exact hc h
      · exact hne (sub_eq_zero.1 h)
    have hd : z1 - z2 ∈ Hex √3 := by
      have := hex_sub hz1 hz2; rwa [show 2 * (√3 / 2) = √3 by ring] at this
    have hwz : w = (z1 - z2) / (m : ℂ) := by
      simp only [w]
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
      field_simp
      linear_combination -hm
    exact hnot (hwz ▸ hex_div_int hd hm0)

/-- **Lemma C 3.2, bound.** If `z ↦ e^{cz}` is injective on `P`, then `|c| ≤ 2π/√3`, and
equality forces `2πi/c = ±√3 nₖ` for some `k` (an edge midpoint of `2P`). -/
theorem exp_inj_bound {c : ℂ} (hc : c ≠ 0)
    (hinj : Set.InjOn (fun z => exp (c * z)) (Hex (√3 / 2))) :
    ‖c‖ ≤ 2 * Real.pi / √3 ∧
      (‖c‖ = 2 * Real.pi / √3 → ∃ k : Fin 3, 2 * Real.pi * I / c = (√3 : ℂ) * hexN k ∨
        2 * Real.pi * I / c = -((√3 : ℂ) * hexN k)) := by
  have hnot := (exp_inj_iff hc).1 hinj
  set w := 2 * Real.pi * I / c with hw
  have hnw : ‖w‖ = 2 * Real.pi / ‖c‖ := by
    simp only [w, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  simp only [Hex, Set.mem_ofPred_eq, not_forall, not_lt] at hnot
  obtain ⟨k, hk⟩ := hnot
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  have h3 : 0 < √3 := by positivity
  -- `|Re(w n̄)| ≤ |w|`
  have hle : |(w * (starRingEnd ℂ) (hexN k)).re| ≤ ‖w‖ := by
    calc |(w * (starRingEnd ℂ) (hexN k)).re| ≤ ‖w * (starRingEnd ℂ) (hexN k)‖ :=
          Complex.abs_re_le_norm _
      _ = ‖w‖ := by rw [norm_mul, Complex.norm_conj, norm_hexN, mul_one]
  have hw3 : √3 ≤ ‖w‖ := le_trans hk hle
  refine ⟨?_, fun heq => ⟨k, ?_⟩⟩
  · rw [hnw, le_div_iff₀ hcn] at hw3
    rw [le_div_iff₀ h3]; linarith
  · -- equality: `|w| = √3` and `|Re(w n̄)| = |w|`, so `w n̄ = ±√3`
    have hwn : ‖w‖ = √3 := by
      rw [hnw, heq]; field_simp
    set u := w * (starRingEnd ℂ) (hexN k)
    have hu : ‖u‖ = √3 := by
      simp only [u]; rw [norm_mul, Complex.norm_conj, norm_hexN, mul_one, hwn]
    have hre : |u.re| = √3 := le_antisymm (by rw [← hu]; exact Complex.abs_re_le_norm u) hk
    have him : u.im = 0 := by
      have h1 := Complex.sq_norm u
      rw [hu, Complex.normSq_apply] at h1
      have h2 : u.re ^ 2 = 3 := by rw [← sq_abs, hre, Real.sq_sqrt (by norm_num)]
      have : u.im * u.im = 0 := by rw [Real.sq_sqrt (by norm_num)] at h1; nlinarith
      exact mul_self_eq_zero.1 this
    have hn1 : hexN k * (starRingEnd ℂ) (hexN k) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_hexN]; simp
    have hwu : w = u * hexN k := by
      simp only [u]; rw [mul_assoc, mul_comm ((starRingEnd ℂ) (hexN k)), hn1, mul_one]
    rcases abs_eq (h3.le) |>.1 hre with h | h
    · left
      rw [hwu, show u = (√3 : ℂ) by apply Complex.ext <;> simp [h, him]]
    · right
      rw [hwu, show u = -(√3 : ℂ) by apply Complex.ext <;> simp [h, him]]; ring

end DoyleFormal
