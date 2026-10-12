/-
Copyright (c) 2026 Hai-Yeh Hwang, Gwang-Syung George Hwang. All rights reserved.
Authors: Hai-Yeh Hwang, Gwang-Syung George Hwang
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Smoke test

The golden ratio satisfies φ² = φ + 1.

Only the needed Mathlib modules are imported: `import Mathlib` took about 39 minutes
on this 8 GB PC.
-/

namespace DoyleFormal

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_sq : φ ^ 2 = φ + 1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold φ
  nlinarith [h]

end DoyleFormal
