/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import DoyleFormal.CylinderPacking

/-!
# Hexagonal packings from geometric hypotheses — Phase 5i

`GeoHexPacking V`: circles with a flower of six petals (tangent to the center and to their
neighbors, positively oriented, wrapping once), a connected contact graph, and the condition
that **the circles tangent to `v` are exactly its petals** ("surrounded by exactly six
circles"). The two combinatorial fields of `HexPacking` are derived:

* `petal_inj`: the six petals are distinct (a partial angle sum strictly between `0` and `2π`
  cannot be a multiple of `2π`);
* `petal_compat`: the flowers of adjacent circles are compatible (the petal before `v` around
  `w = nb v i` is `nb v (i+1)`; otherwise two angle comparisons give opposite inequalities
  between radii, since `angleAt x y z` increases with `z`).

`GeoHexPacking.toHexPacking` and `coherent_classification_geo` (**Theorem B 7.2** with geometric
hypotheses only).
-/

namespace DoyleFormal

open Complex

/-- The angle at `a` of a positively oriented triangle of three mutually tangent circles. -/
lemma arg_eq_angleAt {a b d : ℂ} {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hab : ‖b - a‖ = x + y) (had : ‖d - a‖ = x + z) (hbd : ‖d - b‖ = y + z)
    (ho : 0 < orient a b d) : arg ((d - a) / (b - a)) = angleAt x y z := by
  have hb0 : b - a ≠ 0 := by intro h; rw [h, norm_zero] at hab; linarith
  have hd0 : d - a ≠ 0 := by intro h; rw [h, norm_zero] at had; linarith
  have hang := angleAt_eq_angle (V := ℂ) (P := ℂ) hx hy hz a b d
    (by rw [dist_comm, dist_eq_norm, hab]) (by rw [dist_comm, dist_eq_norm, hbd])
    (by rw [dist_eq_norm, had]; ring)
  rw [← hang, EuclideanGeometry.angle_comm, EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
    Complex.angle_eq_abs_arg hd0 hb0]
  have hpos := (arg_mem_Ioo_of_im_pos (im_div_pos_of_orient (sub_ne_zero.1 hb0) ho)).1
  exact (abs_of_pos hpos).symm

/-- `angleAt x y z` increases with `z`. -/
lemma angleAt_lt_of_lt {x y z z' : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hzz : z < z') :
    angleAt x y z < angleAt x y z' := by
  have hz' : 0 < z' := by linarith
  unfold angleAt
  have hν := nu_pos hx hy hz
  have hν' := nu_pos hx hy hz'
  have h1 := nu_sq hx hy hz
  have h2 := nu_sq hx hy hz'
  -- `ν² = 1/(yz) + 1/(xz) + 1/(xy)` decreases in `z`
  have hlt : nu x y z' < nu x y z := by
    have e1 : nu x y z ^ 2 = 1 / (y * z) + 1 / (x * z) + 1 / (x * y) := by
      field_simp; nlinarith [h1]
    have e2 : nu x y z' ^ 2 = 1 / (y * z') + 1 / (x * z') + 1 / (x * y) := by
      field_simp; nlinarith [h2]
    have : nu x y z' ^ 2 < nu x y z ^ 2 := by
      rw [e1, e2]
      have a1 : 1 / (y * z') < 1 / (y * z) :=
        one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
      have a2 : 1 / (x * z') < 1 / (x * z) :=
        one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
      linarith
    nlinarith
  have : 1 / (nu x y z * x) < 1 / (nu x y z' * x) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  linarith [Real.arctan_strictMono this]

/-- A hexagonal circle packing given by geometric conditions only. -/
structure GeoHexPacking (V : Type*) where
  c : V → ℂ
  ρ : V → ℝ
  ρ_pos : ∀ v, 0 < ρ v
  nb : V → Fin 6 → V
  tan : ∀ v i, ‖c (nb v i) - c v‖ = ρ (nb v i) + ρ v
  rim : ∀ v i, ‖c (nb v (i + 1)) - c (nb v i)‖ = ρ (nb v (i + 1)) + ρ (nb v i)
  ori : ∀ v i, 0 < orient (c v) (c (nb v i)) (c (nb v (i + 1)))
  wind : ∀ v, ∑ i : Fin 6, angleAt (ρ v) (ρ (nb v i)) (ρ (nb v (i + 1))) = 2 * Real.pi
  /-- The circles tangent to `v` are its petals. -/
  deg6 : ∀ v w, ‖c w - c v‖ = ρ w + ρ v → ∃ i, w = nb v i
  conn : ∀ v w, Relation.ReflTransGen (fun x y => ∃ i, y = nb x i) v w

namespace GeoHexPacking

variable {V : Type*} (P : GeoHexPacking V)

/-- The ratio of consecutive spokes at `v`. -/
noncomputable def ratio (v : V) (k : Fin 6) : ℂ :=
  (P.c (P.nb v (k + 1)) - P.c v) / (P.c (P.nb v k) - P.c v)

/-- The angle at `v` between consecutive petals. -/
noncomputable def α (v : V) (k : Fin 6) : ℝ := arg (P.ratio v k)

lemma spoke_ne (v : V) (k : Fin 6) : P.c (P.nb v k) - P.c v ≠ 0 := by
  intro h
  have := P.tan v k
  rw [h, norm_zero] at this
  linarith [P.ρ_pos v, P.ρ_pos (P.nb v k)]

lemma nb_ne (v : V) (k : Fin 6) : P.nb v k ≠ v := by
  intro h; have := P.spoke_ne v k; rw [h, sub_self] at this; exact this rfl

lemma ratio_ne (v : V) (k : Fin 6) : P.ratio v k ≠ 0 :=
  div_ne_zero (P.spoke_ne v (k + 1)) (P.spoke_ne v k)

lemma α_eq (v : V) (k : Fin 6) :
    P.α v k = angleAt (P.ρ v) (P.ρ (P.nb v k)) (P.ρ (P.nb v (k + 1))) :=
  arg_eq_angleAt (P.ρ_pos v) (P.ρ_pos _) (P.ρ_pos _) (by rw [P.tan]; ring)
    (by rw [P.tan]; ring) (by rw [P.rim]; ring) (P.ori v k)

lemma α_pos (v : V) (k : Fin 6) : 0 < P.α v k :=
  (arg_mem_Ioo_of_im_pos (im_div_pos_of_orient
    (sub_ne_zero.1 (P.spoke_ne v k)) (P.ori v k))).1

lemma α_sum (v : V) : ∑ k : Fin 6, P.α v k = 2 * Real.pi := by
  simp only [P.α_eq]; exact P.wind v

/-- Successor in `Fin 6`. -/
def succ6 (j : Fin 6) : Fin 6 := j + 1

/-- Partial angle sum: `k` steps counterclockwise from petal `i`. -/
noncomputable def S (v : V) (i : Fin 6) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range k, P.α v (succ6^[m] i)

lemma S_succ (v : V) (i : Fin 6) (k : ℕ) : P.S v i (k + 1) = P.S v i k + P.α v (succ6^[k] i) :=
  Finset.sum_range_succ _ _

lemma succ6_six (i : Fin 6) :
    succ6^[0] i = i + 0 ∧ succ6^[1] i = i + 1 ∧ succ6^[2] i = i + 2 ∧ succ6^[3] i = i + 3 ∧
      succ6^[4] i = i + 4 ∧ succ6^[5] i = i + 5 := by
  revert i; decide

lemma fin_sub_val (i j : Fin 6) : succ6^[(j - i).val] i = j := by revert i j; decide

lemma fin_sub_val_pos (i j : Fin 6) (h : i ≠ j) : 1 ≤ (j - i).val := by revert h; revert i j; decide

lemma fin_sub_val_two (i j : Fin 6) (h0 : j ≠ i) (h1 : j ≠ i + 1) : 2 ≤ (j - i).val := by
  revert h0 h1; revert i j; decide

lemma fin_sub_val_two' (i j : Fin 6) (h0 : j ≠ i) (h1 : i + 1 ≠ j) : 2 ≤ (j - i).val := by
  revert h0 h1; revert i j; decide

lemma fin_j5 (j : Fin 6) : j + 5 + 1 = j := by revert j; decide

lemma fin_pred_aux (x : Fin 6) : x = x + 1 + 5 := by revert x; decide

lemma fin_pred (x j : Fin 6) (h : x + 1 = j) : x = j + 5 := by
  rw [← h]; exact fin_pred_aux x

lemma S_six (v : V) (i : Fin 6) : P.S v i 6 = 2 * Real.pi := by
  rw [← P.α_sum v, ← Equiv.sum_comp (Equiv.addLeft i) (P.α v), Fin.sum_univ_six]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := succ6_six i
  simp only [S, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, h2, h3, h4, h5,
    Equiv.coe_addLeft, add_zero]

lemma S_pos (v : V) (i : Fin 6) {k : ℕ} (hk : 1 ≤ k) : 0 < P.S v i k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [S_succ]
  have : 0 ≤ P.S v i m := Finset.sum_nonneg fun j _ => (P.α_pos v _).le
  linarith [P.α_pos v (succ6^[m] i)]

lemma S_mono (v : V) (i : Fin 6) {k l : ℕ} (hkl : k < l) : P.S v i k < P.S v i l := by
  induction l with
  | zero => omega
  | succ l ih =>
    rw [S_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkl with h | h
    · linarith [ih h, P.α_pos v (succ6^[l] i)]
    · subst h; linarith [P.α_pos v (succ6^[k] i)]

lemma S_lt (v : V) (i : Fin 6) {k : ℕ} (hk : k ≤ 5) : P.S v i k < 2 * Real.pi := by
  rw [← P.S_six v i]; exact P.S_mono v i (by omega)

/-- The total ratio after `k` steps. -/
noncomputable def R (v : V) (i : Fin 6) (k : ℕ) : ℂ :=
  (P.c (P.nb v (succ6^[k] i)) - P.c v) / (P.c (P.nb v i) - P.c v)

lemma R_ne (v : V) (i : Fin 6) (k : ℕ) : P.R v i k ≠ 0 :=
  div_ne_zero (P.spoke_ne v _) (P.spoke_ne v i)

/-- `exp(i S) = R/|R|`. -/
lemma exp_S (v : V) (i : Fin 6) (k : ℕ) :
    exp ((P.S v i k : ℂ) * I) = P.R v i k / (‖P.R v i k‖ : ℂ) := by
  induction k with
  | zero =>
    simp only [S, Finset.range_zero, Finset.sum_empty, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, R, Function.iterate_zero, id_eq]
    rw [div_self (P.spoke_ne v i), norm_one, Complex.ofReal_one, div_one]
  | succ k ih =>
    have hr : P.R v i (k + 1) = P.R v i k * P.ratio v (succ6^[k] i) := by
      simp only [R, ratio, Function.iterate_succ_apply', succ6]
      field_simp [P.spoke_ne v (succ6^[k] i), P.spoke_ne v i]
    have hrat : exp ((arg (P.ratio v (succ6^[k] i)) : ℂ) * I) =
        P.ratio v (succ6^[k] i) / (‖P.ratio v (succ6^[k] i)‖ : ℂ) := by
      have hn : (‖P.ratio v (succ6^[k] i)‖ : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.2 (P.ratio_ne v _)
      rw [eq_div_iff hn, mul_comm]
      exact norm_mul_exp_arg_mul_I _
    rw [S_succ, Complex.ofReal_add, add_mul, Complex.exp_add, ih]
    simp only [α] at hrat ⊢
    rw [hrat, hr, norm_mul, Complex.ofReal_mul]
    field_simp

lemma S_eq_of_exp {S T : ℝ} (hS : 0 < S) (hS2 : S < 2 * Real.pi) (hT : 0 < T)
    (hT2 : T < 2 * Real.pi) (h : exp ((S : ℂ) * I) = exp ((T : ℂ) * I)) : S = T := by
  have h1 : exp (((S - T : ℝ) : ℂ) * I) = 1 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have hre : S - T = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn; simpa using this
  have hpi := Real.pi_pos
  have : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hn' | hn'
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn'
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn'
      nlinarith
  subst this; simp at hre; linarith

lemma exp_ne_one {S : ℝ} (hS : 0 < S) (hS2 : S < 2 * Real.pi) : exp ((S : ℂ) * I) ≠ 1 := by
  intro h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have hre : S = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn; simpa using this
  have hpi := Real.pi_pos
  rcases lt_trichotomy n 0 with hn' | hn' | hn'
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn'
    nlinarith
  · subst hn'; simp at hre; linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn'
    nlinarith

/-- **The petals are distinct.** -/
theorem petal_inj (v : V) : Function.Injective (P.nb v) := by
  intro i j hij
  by_contra hne
  set k := (j - i).val
  have hk : succ6^[k] i = j := fin_sub_val i j
  have hk1 : 1 ≤ k := fin_sub_val_pos i j hne
  have hk5 : k ≤ 5 := by simp only [k]; omega
  have hR : P.R v i k = 1 := by
    simp only [R, hk, hij]; exact div_self (P.spoke_ne v j)
  have := P.exp_S v i k
  rw [hR, norm_one, Complex.ofReal_one, div_one] at this
  exact exp_ne_one (P.S_pos v i hk1) (P.S_lt v i hk5) this

/-- With positive orientation, the partial angle sum is the argument of the total ratio. -/
lemma S_eq_arg (v : V) (i : Fin 6) {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5)
    (ho : 0 < orient (P.c v) (P.c (P.nb v i)) (P.c (P.nb v (succ6^[k] i)))) :
    P.S v i k = arg (P.R v i k) := by
  have hpos : 0 < arg (P.R v i k) ∧ arg (P.R v i k) < Real.pi :=
    arg_mem_Ioo_of_im_pos (im_div_pos_of_orient (sub_ne_zero.1 (P.spoke_ne v i)) ho)
  refine S_eq_of_exp (P.S_pos v i hk1) (P.S_lt v i hk5) hpos.1
    (by linarith [hpos.2, Real.pi_pos]) ?_
  rw [P.exp_S]
  have hn : (‖P.R v i k‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (P.R_ne v i k)
  rw [div_eq_iff hn, mul_comm]
  exact (norm_mul_exp_arg_mul_I _).symm

/-- **Compatibility of adjacent flowers.** If `nb (nb v i) j = v`, then the petal before `v`
around `w = nb v i` is `nb v (i+1)`. -/
theorem petal_compat (v : V) (i j : Fin 6) (hj : P.nb (P.nb v i) j = v) :
    P.nb (P.nb v i) (j + 5) = P.nb v (i + 1) := by
  set w := P.nb v i with hw
  set q := P.nb w (j + 5) with hq
  set p := P.nb v (i + 1) with hp
  have hρv := P.ρ_pos v; have hρw := P.ρ_pos w; have hρq := P.ρ_pos q; have hρp := P.ρ_pos p
  have hj5 : j + 5 + 1 = j := fin_j5 j
  -- tangencies
  have t_vw : ‖P.c w - P.c v‖ = P.ρ w + P.ρ v := P.tan v i
  have t_wq : ‖P.c q - P.c w‖ = P.ρ q + P.ρ w := P.tan w (j + 5)
  have t_qv : ‖P.c v - P.c q‖ = P.ρ v + P.ρ q := by
    have := P.rim w (j + 5); rwa [hj5, hj] at this
  have t_vp : ‖P.c p - P.c v‖ = P.ρ p + P.ρ v := P.tan v (i + 1)
  have t_wp : ‖P.c p - P.c w‖ = P.ρ p + P.ρ w := P.rim v i
  -- orientations
  have o_wqv : 0 < orient (P.c w) (P.c q) (P.c v) := by
    have := P.ori w (j + 5); rwa [hj5, hj] at this
  have o_vwp : 0 < orient (P.c v) (P.c w) (P.c p) := P.ori v i
  by_contra hne
  -- around `v`: `q` is a petal `l` of `v` with `l ∉ {i, i+1}`
  obtain ⟨l, hl⟩ := P.deg6 v q (by rw [norm_sub_rev] at t_qv; linarith)
  have hl0 : l ≠ i := by
    intro h; rw [h] at hl
    have := P.nb_ne w (j + 5); rw [← hq, hl, ← hw] at this; exact this rfl
  have hl1 : l ≠ i + 1 := by intro h; rw [h] at hl; exact hne hl
  have hk := fin_sub_val_two i l hl0 hl1
  have hk5 : (l - i).val ≤ 5 := by omega
  have o_vwq : 0 < orient (P.c v) (P.c w) (P.c q) := by rw [← orient_cycle]; exact o_wqv
  have hSv := P.S_eq_arg v i (by omega) hk5 (by rw [fin_sub_val, ← hl]; exact o_vwq)
  have hRv : P.R v i (l - i).val = (P.c q - P.c v) / (P.c w - P.c v) := by
    simp only [R, fin_sub_val, ← hl, ← hw]
  rw [hRv, arg_eq_angleAt hρv hρw hρq (by rw [t_vw]; ring) (by rw [norm_sub_rev, t_qv])
    (by rw [t_wq]; ring) o_vwq] at hSv
  have hS1 : P.S v i 1 = angleAt (P.ρ v) (P.ρ w) (P.ρ p) := by
    simp only [S, Finset.sum_range_one, Function.iterate_zero, id_eq]; rw [P.α_eq]
  have hcmp1 : angleAt (P.ρ v) (P.ρ w) (P.ρ p) < angleAt (P.ρ v) (P.ρ w) (P.ρ q) := by
    rw [← hS1, ← hSv]; exact P.S_mono v i (by omega)
  -- around `w`: `p` is a petal `l'` of `w` with `l' ∉ {j, j+5}`
  obtain ⟨l', hl'⟩ := P.deg6 w p (by linarith)
  have hl'0 : j ≠ l' := by
    intro h; rw [← h, hj] at hl'
    have := P.nb_ne v (i + 1); rw [← hp, hl'] at this; exact this rfl
  have hl'1 : l' + 1 ≠ j := by
    intro h
    rw [fin_pred l' j h] at hl'; exact hne hl'.symm
  have hk' := fin_sub_val_two' l' j hl'0 hl'1
  have hk'5 : (j - l').val ≤ 5 := by omega
  have o_wpv : 0 < orient (P.c w) (P.c p) (P.c v) := by rw [orient_cycle]; exact o_vwp
  have hSw := P.S_eq_arg w l' (by omega) hk'5 (by rw [fin_sub_val, hj, ← hl']; exact o_wpv)
  have hRw : P.R w l' (j - l').val = (P.c v - P.c w) / (P.c p - P.c w) := by
    simp only [R, fin_sub_val, hj, ← hl']
  rw [hRw, arg_eq_angleAt hρw hρp hρv (by rw [t_wp]; ring) (by rw [norm_sub_rev, t_vw])
    (by rw [norm_sub_rev, t_vp]) o_wpv] at hSw
  -- the last step before `v` around `w` is from `q`
  obtain ⟨m, hm⟩ : ∃ m, (j - l').val = m + 1 := ⟨(j - l').val - 1, by omega⟩
  have hlast : succ6^[m] l' = j + 5 := by
    have h := fin_sub_val l' j
    rw [hm, Function.iterate_succ_apply'] at h
    exact fin_pred _ j h
  have hαlast : P.α w (succ6^[m] l') = angleAt (P.ρ w) (P.ρ q) (P.ρ v) := by
    rw [hlast, P.α_eq, ← hq, hj5, hj]
  have hSw' : P.S w l' (j - l').val = P.S w l' m + P.α w (succ6^[m] l') := by
    rw [hm, S_succ]
  have hpos : 0 < P.S w l' m := P.S_pos w l' (by omega)
  have hcmp2 : angleAt (P.ρ w) (P.ρ v) (P.ρ q) < angleAt (P.ρ w) (P.ρ v) (P.ρ p) := by
    rw [← angleAt_swap (P.ρ w) (P.ρ v) (P.ρ q), ← angleAt_swap (P.ρ w) (P.ρ v) (P.ρ p),
      ← hαlast, ← hSw]
    linarith
  -- opposite inequalities between the radii of `p` and `q`
  rcases lt_trichotomy (P.ρ p) (P.ρ q) with h | h | h
  · linarith [angleAt_lt_of_lt hρw hρv hρp h]
  · rw [h] at hcmp1; exact lt_irrefl _ hcmp1
  · linarith [angleAt_lt_of_lt hρv hρw hρq h]

/-- The combinatorial structure of a geometric hexagonal packing. -/
noncomputable def toHexPacking : HexPacking V where
  c := P.c
  ρ := P.ρ
  ρ_pos := P.ρ_pos
  nb := P.nb
  tan := P.tan
  rim := P.rim
  ori := P.ori
  wind := P.wind
  inj := P.petal_inj
  compat v i := by
    obtain ⟨j, hj⟩ := P.deg6 (P.nb v i) v (by rw [norm_sub_rev, P.tan]; ring)
    refine ⟨j, hj.symm, P.petal_compat v i j hj.symm, ?_⟩
    -- apply the first part at `w = nb v i`, whose petal `j` is `v`
    have h := P.petal_compat (P.nb v i) j i (by rw [← hj])
    rw [← hj] at h
    exact h.symm
  conn := P.conn

end GeoHexPacking

/-- **Theorem B 7.2 with geometric hypotheses.** A coherent hexagonal circle packing in which
every circle is surrounded by exactly six tangent circles, forming a flower that wraps once,
and all of whose center triangles are similar, is (up to a direct similarity) the regular
packing or `D_{B_n}` for some `n ≥ 2`. -/
theorem coherent_classification_geo {V : Type*} (P : GeoHexPacking V) (v0 : V)
    (hcoh : ∀ v w, v ≠ w → P.ρ v + P.ρ w ≤ ‖P.c v - P.c w‖) {a b c : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hsim : P.toHexPacking.SimShape a b c) :
    (∃ α β : ℂ, α ≠ 0 ∧ ∀ v, ∃ p q : ℤ, P.c v = α * zreg 1 p q + β ∧ P.ρ v = ‖α‖) ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ B > 1, psi B = Real.pi / n ∧ ∃ α β : ℂ, α ≠ 0 ∧ ∀ v, ∃ p q : ℤ,
        P.c v = α * zc B (psi B) p q + β ∧ P.ρ v = ‖α‖ * rad B p q :=
  coherent_classification P.toHexPacking v0 hcoh ha hb hc hsim

section Cyl

variable {B : ℝ} (hB : 1 < B) {n : ℕ} (hn : 2 ≤ n) (hψn : psi B = Real.pi / n)

include hB hn hψn in
/-- `D_{B_n}` on the cylinder satisfies the geometric hypotheses: the circles tangent to a
circle are exactly its six petals. -/
noncomputable def cylGeo : GeoHexPacking (Cyl n) where
  c := (cylPacking hB hn hψn).c
  ρ := (cylPacking hB hn hψn).ρ
  ρ_pos := (cylPacking hB hn hψn).ρ_pos
  nb := (cylPacking hB hn hψn).nb
  tan := (cylPacking hB hn hψn).tan
  rim := (cylPacking hB hn hψn).rim
  ori := (cylPacking hB hn hψn).ori
  wind := (cylPacking hB hn hψn).wind
  deg6 v w h := by
    by_cases hvw : v = w
    · subst hvw
      rw [sub_self, norm_zero] at h
      linarith [(cylPacking hB hn hψn).ρ_pos v]
    · exact (cylPacking_contact hB hn hψn v w hvw).1 h
  conn := (cylPacking hB hn hψn).conn

end Cyl

end DoyleFormal
