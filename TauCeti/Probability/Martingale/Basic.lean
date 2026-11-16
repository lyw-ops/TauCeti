/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.Process.Filtration.Comp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Sampling a submartingale and taking the norm of a martingale.
-/

public section

noncomputable section

open Filter
open scoped ENNReal

namespace MeasureTheory

section Sampling

variable {Ω ι κ E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Preorder ι] [Preorder κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ℱ : Filtration ι m} {X : ι → Ω → E} {τ : κ → ι}

/-- Sampling a submartingale along a monotone map gives a submartingale. -/
theorem Submartingale.comp [LE E] (hX : Submartingale X ℱ μ) (hτ : Monotone τ) :
    Submartingale (fun n ↦ X (τ n)) (ℱ.comp hτ) μ := by
  refine ⟨hX.stronglyAdapted.comp hτ, fun i j hij ↦ ?_, fun i ↦ hX.integrable (τ i)⟩
  simpa only [Filtration.comp_apply] using hX.ae_le_condExp (hτ hij)

end Sampling

section NormAndMultipliers

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {Y : ι → Ω → ℝ}

/-- The norm of a Banach-valued martingale is a submartingale. -/
theorem Martingale.norm (hX : Martingale X ℱ μ) :
    Submartingale (fun t ω => ‖X t ω‖) ℱ μ := by
  refine ⟨fun t => (hX.stronglyAdapted t).norm, fun s t hst => ?_,
    fun t => (hX.integrable t).norm⟩
  filter_upwards [hX.condExp_ae_eq hst, norm_condExp_le (m := ℱ s) (X t)] with ω he hle
  simpa only [he] using hle

end NormAndMultipliers

end MeasureTheory
