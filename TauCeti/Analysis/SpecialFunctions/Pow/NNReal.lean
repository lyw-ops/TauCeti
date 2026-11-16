/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A bound for positive real powers in `ℝ≥0∞`.
-/

public section

open scoped ENNReal NNReal Topology

namespace ENNReal

/-- If `m ≤ K * m ^ p` for a finite `m` and an exponent `p < 1`, then `m ^ (1 - p) ≤ K`: the
factor `m ^ p` cancels. -/
theorem rpow_one_sub_le_of_le_mul_rpow {m K : ℝ≥0∞} {p : ℝ} (hp : p < 1) (hm : m ≠ ∞)
    (h : m ≤ K * m ^ p) : m ^ (1 - p) ≤ K := by
  rcases eq_or_ne m 0 with rfl | h0
  · rw [zero_rpow_of_pos (sub_pos.2 hp)]
    exact zero_le
  rwa [rpow_sub _ _ h0 hm, rpow_one, ENNReal.div_le_iff
    (rpow_pos (pos_iff_ne_zero.2 h0) hm).ne' (rpow_ne_top_of_ne_zero h0 hm)]

end ENNReal

namespace NNReal

end NNReal

namespace TauCeti

end TauCeti
