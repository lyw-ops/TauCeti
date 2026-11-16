/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Relating `eLpNorm` to the lower integral of a power.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

variable {α ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε] [ContinuousENorm ε]

namespace TauCeti

end TauCeti

namespace MeasureTheory

/-- For `p ≠ 0, ∞`, the integral of `‖f‖ₑ ^ p` is the `p`-th power of the `Lᵖ` seminorm of `f`. -/
theorem lintegral_rpow_enorm_eq_eLpNorm_rpow {f : α → ε} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]

/-- If `∫ ‖k‖ ^ q ≤ t ^ q` then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_lintegral_rpow_le {k : α → ε} {q : ℝ≥0∞} {t : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hk : AEStronglyMeasurable k μ) (h : ∫⁻ x, ‖k x‖ₑ ^ q.toReal ∂μ ≤ t ^ q.toReal) :
    eLpNorm k q μ ≤ t := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [← ENNReal.rpow_le_rpow_iff hq', ← lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hk]
  exact h

end MeasureTheory

namespace MeasureTheory.MemLp

end MeasureTheory.MemLp
