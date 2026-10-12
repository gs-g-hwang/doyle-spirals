/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.PaperA5

/-!
# Descartes' circle theorem for externally tangent circles (paper A, Proposition 7.8 (4))

For positive radii `r₁, …, r₄` there are four mutually externally tangent circles with these
radii if and only if the Descartes defect of the curvatures `κᵢ = 1/rᵢ` vanishes:
`(Σ κᵢ)² − 2 Σ κᵢ² = 0`.

* `descartes_of_tangent` (Descartes' theorem): the Gram determinant of the three vectors
  `c₂ − c₁, c₃ − c₁, c₄ − c₁` in the plane vanishes, and with the distances `rᵢ + rⱼ` it equals
  `4 (r₁r₂r₃r₄)² ℰ`.
* `tangent_of_descartes` (converse): put `c₁ = 0`, `c₂ = r₁ + r₂`, `c₃` above the real axis by
  the law of cosines, and `c₄ = x' − i D/(2y)`; the identity
  `D² − 4y²Y = −16 (r₁r₂r₃r₄)² ℰ / (r₁ + r₂)²` gives the remaining distances.
* `coxeter_geometric`: Proposition A 7.8, (1) ⇔ (4) in its geometric form — there are four
  mutually externally tangent circles with radii `1, B, B², B³` iff `ψ(B) = π/2`.
-/

namespace DoyleFormal

open Complex

/-- The Descartes defect `ℰ(κ₁, κ₂, κ₃, κ₄) = (Σ κᵢ)² − 2 Σ κᵢ²`. -/
def defect4 (k₁ k₂ k₃ k₄ : ℝ) : ℝ :=
  (k₁ + k₂ + k₃ + k₄) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2)

/-- Four mutually externally tangent circles with centers `c i` and radii `r i`. -/
def ExtTangent4 (c : Fin 4 → ℂ) (r : Fin 4 → ℝ) : Prop :=
  ∀ i j, i ≠ j → ‖c i - c j‖ = r i + r j

/-- The polynomial `P` with `ℰ(1/r) = −P/(r₁r₂r₃r₄)²`. -/
def descP (r₁ r₂ r₃ r₄ : ℝ) : ℝ :=
  r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2 - 2 * r₁ ^ 2 * r₂ ^ 2 * r₃ * r₄ + r₁ ^ 2 * r₂ ^ 2 * r₄ ^ 2
    - 2 * r₁ ^ 2 * r₂ * r₃ ^ 2 * r₄ - 2 * r₁ ^ 2 * r₂ * r₃ * r₄ ^ 2 + r₁ ^ 2 * r₃ ^ 2 * r₄ ^ 2
    - 2 * r₁ * r₂ ^ 2 * r₃ ^ 2 * r₄ - 2 * r₁ * r₂ ^ 2 * r₃ * r₄ ^ 2
    - 2 * r₁ * r₂ * r₃ ^ 2 * r₄ ^ 2 + r₂ ^ 2 * r₃ ^ 2 * r₄ ^ 2

lemma defect4_inv {r₁ r₂ r₃ r₄ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0) :
    defect4 r₁⁻¹ r₂⁻¹ r₃⁻¹ r₄⁻¹ = -descP r₁ r₂ r₃ r₄ / (r₁ * r₂ * r₃ * r₄) ^ 2 := by
  unfold defect4 descP
  field_simp
  ring

lemma defect4_inv_eq_zero_iff {r₁ r₂ r₃ r₄ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0)
    (h₄ : r₄ ≠ 0) : defect4 r₁⁻¹ r₂⁻¹ r₃⁻¹ r₄⁻¹ = 0 ↔ descP r₁ r₂ r₃ r₄ = 0 := by
  rw [defect4_inv h₁ h₂ h₃ h₄, div_eq_zero_iff, neg_eq_zero]
  have : (r₁ * r₂ * r₃ * r₄) ^ 2 ≠ 0 := by positivity
  simp [this]

/-- The Gram determinant of three plane vectors, written through the six squared distances
`N i j = |cᵢ − cⱼ|²` of four points (vectors from the first point). -/
noncomputable def gram3 (N12 N13 N14 N23 N24 N34 : ℝ) : ℝ :=
  let g23 := (N12 + N13 - N23) / 2
  let g24 := (N12 + N14 - N24) / 2
  let g34 := (N13 + N14 - N34) / 2
  N12 * (N13 * N14 - g34 ^ 2) - g23 * (g23 * N14 - g34 * g24) + g24 * (g23 * g34 - N13 * g24)

/-- Four points of the plane: the Gram determinant of the three difference vectors is zero. -/
lemma gram3_plane (c₁ c₂ c₃ c₄ : ℂ) :
    gram3 (normSq (c₁ - c₂)) (normSq (c₁ - c₃)) (normSq (c₁ - c₄)) (normSq (c₂ - c₃))
      (normSq (c₂ - c₄)) (normSq (c₃ - c₄)) = 0 := by
  simp only [gram3, normSq_apply, sub_re, sub_im]
  ring

lemma gram3_tangent (r₁ r₂ r₃ r₄ : ℝ) :
    gram3 ((r₁ + r₂) ^ 2) ((r₁ + r₃) ^ 2) ((r₁ + r₄) ^ 2) ((r₂ + r₃) ^ 2) ((r₂ + r₄) ^ 2)
      ((r₃ + r₄) ^ 2) = -4 * descP r₁ r₂ r₃ r₄ := by
  simp only [gram3, descP]
  ring

lemma normSq_of_norm {z : ℂ} {s : ℝ} (h : ‖z‖ = s) : normSq z = s ^ 2 := by
  rw [← h, Complex.sq_norm]

lemma norm_of_normSq {z : ℂ} {s : ℝ} (hs : 0 ≤ s) (h : normSq z = s ^ 2) : ‖z‖ = s := by
  rw [Complex.norm_def, h, Real.sqrt_sq hs]

/-- **Descartes' circle theorem** (externally tangent case): the curvatures of four mutually
externally tangent circles have Descartes defect zero. -/
theorem descartes_of_tangent {c : Fin 4 → ℂ} {r : Fin 4 → ℝ} (hr : ∀ i, 0 < r i)
    (h : ExtTangent4 c r) : defect4 (r 0)⁻¹ (r 1)⁻¹ (r 2)⁻¹ (r 3)⁻¹ = 0 := by
  rw [defect4_inv_eq_zero_iff (hr 0).ne' (hr 1).ne' (hr 2).ne' (hr 3).ne']
  have key := gram3_plane (c 0) (c 1) (c 2) (c 3)
  rw [normSq_of_norm (h 0 1 (by decide)), normSq_of_norm (h 0 2 (by decide)),
    normSq_of_norm (h 0 3 (by decide)), normSq_of_norm (h 1 2 (by decide)),
    normSq_of_norm (h 1 3 (by decide)), normSq_of_norm (h 2 3 (by decide)), gram3_tangent] at key
  linarith

lemma mk_sub_mk (a b c d : ℝ) : (⟨a, b⟩ : ℂ) - ⟨c, d⟩ = ⟨a - c, b - d⟩ :=
  Complex.ext (by simp) (by simp)

/-- Six distances determine `ExtTangent4`. -/
lemma extTangent4_of {c : Fin 4 → ℂ} {r : Fin 4 → ℝ}
    (h01 : ‖c 0 - c 1‖ = r 0 + r 1) (h02 : ‖c 0 - c 2‖ = r 0 + r 2)
    (h03 : ‖c 0 - c 3‖ = r 0 + r 3) (h12 : ‖c 1 - c 2‖ = r 1 + r 2)
    (h13 : ‖c 1 - c 3‖ = r 1 + r 3) (h23 : ‖c 2 - c 3‖ = r 2 + r 3) : ExtTangent4 c r := by
  have s : ∀ {i j : Fin 4}, ‖c i - c j‖ = r i + r j → ‖c j - c i‖ = r j + r i :=
    fun h => by rw [norm_sub_rev, h, add_comm]
  intro i j hij
  match i, j with
  | 0, 0 => exact absurd rfl hij
  | 1, 1 => exact absurd rfl hij
  | 2, 2 => exact absurd rfl hij
  | 3, 3 => exact absurd rfl hij
  | 0, 1 => exact h01
  | 0, 2 => exact h02
  | 0, 3 => exact h03
  | 1, 2 => exact h12
  | 1, 3 => exact h13
  | 2, 3 => exact h23
  | 1, 0 => exact s h01
  | 2, 0 => exact s h02
  | 3, 0 => exact s h03
  | 2, 1 => exact s h12
  | 3, 1 => exact s h13
  | 3, 2 => exact s h23

/-- The construction behind the converse, with explicit radii. -/
theorem tangent_core {r₁ r₂ r₃ r₄ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (h₃ : 0 < r₃) (h₄ : 0 < r₄)
    (hE : descP r₁ r₂ r₃ r₄ = 0) :
    ∃ c₁ c₂ c₃ c₄ : ℂ, ‖c₁ - c₂‖ = r₁ + r₂ ∧ ‖c₁ - c₃‖ = r₁ + r₃ ∧ ‖c₁ - c₄‖ = r₁ + r₄ ∧
      ‖c₂ - c₃‖ = r₂ + r₃ ∧ ‖c₂ - c₄‖ = r₂ + r₄ ∧ ‖c₃ - c₄‖ = r₃ + r₄ := by
  have h12 : r₁ + r₂ ≠ 0 := by positivity
  -- the third center `⟨x, y⟩`
  obtain ⟨x, hx⟩ : ∃ x : ℝ,
      x = ((r₁ + r₂) ^ 2 + (r₁ + r₃) ^ 2 - (r₂ + r₃) ^ 2) / (2 * (r₁ + r₂)) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2 : ℝ, y2 = 4 * r₁ * r₂ * r₃ * (r₁ + r₂ + r₃) / (r₁ + r₂) ^ 2 :=
    ⟨_, rfl⟩
  have hy2pos : 0 < y2 := by rw [hy2]; positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = √y2 := ⟨_, rfl⟩
  have hypos : 0 < y := by rw [hy]; exact Real.sqrt_pos.2 hy2pos
  have hyy : y ^ 2 = y2 := by rw [hy]; exact Real.sq_sqrt hy2pos.le
  -- the fourth center `⟨x', y'⟩`
  obtain ⟨x', hx'⟩ : ∃ x' : ℝ,
      x' = ((r₁ + r₂) ^ 2 + (r₁ + r₄) ^ 2 - (r₂ + r₄) ^ 2) / (2 * (r₁ + r₂)) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (r₁ + r₄) ^ 2 - x' ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (r₃ + r₄) ^ 2 - (x - x') ^ 2 - y2 - Y := ⟨_, rfl⟩
  have hDY : D ^ 2 = 4 * y2 * Y := by
    have : D ^ 2 - 4 * y2 * Y = 16 * descP r₁ r₂ r₃ r₄ / (r₁ + r₂) ^ 2 := by
      rw [hD, hY, hx, hx', hy2]
      unfold descP
      field_simp
      ring
    rw [hE, mul_zero, zero_div] at this
    linarith
  have hx3 : x ^ 2 + y2 = (r₁ + r₃) ^ 2 := by
    rw [hx, hy2]; field_simp; ring
  have hx3' : (x - (r₁ + r₂)) ^ 2 + y2 = (r₂ + r₃) ^ 2 := by
    rw [hx, hy2]; field_simp; ring
  have hx4' : (x' - (r₁ + r₂)) ^ 2 + Y = (r₂ + r₄) ^ 2 := by
    rw [hY, hx']; field_simp; ring
  have hy0 : y ≠ 0 := hypos.ne'
  obtain ⟨y', hy'⟩ : ∃ y' : ℝ, y' = -D / (2 * y) := ⟨_, rfl⟩
  have hyy' : y' ^ 2 = Y := by
    have h4 : 4 * y2 ≠ 0 := by positivity
    rw [hy', div_pow, neg_sq, hDY, mul_pow, hyy]
    field_simp
    ring
  have hyy'' : y * y' = -D / 2 := by rw [hy']; field_simp
  have pos : ∀ a b : ℝ, 0 < a → 0 < b → 0 ≤ a + b := fun a b ha hb => (add_pos ha hb).le
  refine ⟨⟨0, 0⟩, ⟨r₁ + r₂, 0⟩, ⟨x, y⟩, ⟨x', y'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [mk_sub_mk] <;> refine norm_of_normSq (pos _ _ (by assumption) (by assumption)) ?_ <;>
    rw [normSq_mk]
  · ring
  · linear_combination hx3 + hyy
  · linear_combination hyy' + hY
  · linear_combination hx3' + hyy
  · linear_combination hx4' + hyy'
  · linear_combination hyy + hyy' - 2 * hyy'' + hD

/-- **Converse of Descartes' theorem** (externally tangent case): positive radii whose
curvatures have Descartes defect zero are the radii of four mutually externally tangent
circles. -/
theorem tangent_of_descartes {r : Fin 4 → ℝ} (hr : ∀ i, 0 < r i)
    (hE : defect4 (r 0)⁻¹ (r 1)⁻¹ (r 2)⁻¹ (r 3)⁻¹ = 0) : ∃ c : Fin 4 → ℂ, ExtTangent4 c r := by
  rw [defect4_inv_eq_zero_iff (hr 0).ne' (hr 1).ne' (hr 2).ne' (hr 3).ne'] at hE
  obtain ⟨c₁, c₂, c₃, c₄, d12, d13, d14, d23, d24, d34⟩ :=
    tangent_core (hr 0) (hr 1) (hr 2) (hr 3) hE
  exact ⟨![c₁, c₂, c₃, c₄], extTangent4_of d12 d13 d14 d23 d24 d34⟩

/-- **Descartes' theorem and its converse** for positive radii. -/
theorem descartes_iff {r : Fin 4 → ℝ} (hr : ∀ i, 0 < r i) :
    (∃ c : Fin 4 → ℂ, ExtTangent4 c r) ↔ defect4 (r 0)⁻¹ (r 1)⁻¹ (r 2)⁻¹ (r 3)⁻¹ = 0 :=
  ⟨fun ⟨_, h⟩ => descartes_of_tangent hr h, tangent_of_descartes hr⟩

/-- The radii `1, B, B², B³` of Coxeter's quadruple. -/
def coxRadii (B : ℝ) : Fin 4 → ℝ := ![1, B, B ^ 2, B ^ 3]

lemma defect4_coxRadii (B : ℝ) :
    defect4 (coxRadii B 0)⁻¹ (coxRadii B 1)⁻¹ (coxRadii B 2)⁻¹ (coxRadii B 3)⁻¹ =
      descartes B := by
  simp [coxRadii, defect4, descartes]

/-- **Proposition A 7.8, (4) ⇔ ℰ(B) = 0, geometrically**: for `B > 0` there are four mutually
externally tangent circles with radii `1, B, B², B³` iff the Descartes defect `ℰ(B)` vanishes. -/
theorem coxeter_quadruple_iff {B : ℝ} (hB : 0 < B) :
    (∃ c : Fin 4 → ℂ, ExtTangent4 c (coxRadii B)) ↔ descartes B = 0 := by
  have hr : ∀ i, 0 < coxRadii B i := by
    intro i
    fin_cases i
    · show (0 : ℝ) < 1; norm_num
    · show 0 < B; exact hB
    · show 0 < B ^ 2; positivity
    · show 0 < B ^ 3; positivity
  rw [descartes_iff hr, defect4_coxRadii]

/-- **Proposition A 7.8, (1) ⇔ (3) ⇔ (4) in geometric form**: for `B > 1` there are four mutually
externally tangent circles with radii `1, B, B², B³` (Coxeter's quadruple) iff `ψ(B) = π/2`, iff
`B = φ + √φ`. -/
theorem coxeter_geometric {B : ℝ} (hB : 1 < B) :
    ((∃ c : Fin 4 → ℂ, ExtTangent4 c (coxRadii B)) ↔ psi B = Real.pi / 2) ∧
      ((∃ c : Fin 4 → ℂ, ExtTangent4 c (coxRadii B)) ↔ B = φ + √φ) := by
  rw [coxeter_quadruple_iff (by linarith)]
  have := coxeter_tfae hB
  exact ⟨(this.out 1 4).symm, (this.out 3 4).symm⟩

end DoyleFormal
