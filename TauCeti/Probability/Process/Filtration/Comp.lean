/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted

/-!
# Sampling a filtration along a monotone map.
-/

public section

namespace MeasureTheory.Filtration

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]

/-- Sample a filtration along a monotone time map. -/
def comp (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ) : Filtration κ m where
  seq n := ℱ (τ n)
  mono' _ _ h := ℱ.mono (hτ h)
  le' n := ℱ.le (τ n)

/-- The sampled filtration at an index is the original filtration at its sampling time. -/
@[simp]
theorem comp_apply (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ) (n : κ) :
    ℱ.comp hτ n = ℱ (τ n) := (rfl)

/-- Strong measurability at a sampled index is that at its sampling time. -/
@[simp]
theorem stronglyMeasurable_comp_iff {E : Type*} [TopologicalSpace E] (ℱ : Filtration ι m)
    {τ : κ → ι} (hτ : Monotone τ) (n : κ) {f : Ω → E} :
    StronglyMeasurable[ℱ.comp hτ n] f ↔ StronglyMeasurable[ℱ (τ n)] f := (Iff.rfl)

end MeasureTheory.Filtration

namespace MeasureTheory

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]
  {ℱ : Filtration ι m} {τ : κ → ι}

/-- Sampling a strongly adapted process preserves strong adaptation. -/
theorem StronglyAdapted.comp {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    {X : (i : ι) → Ω → E i} (hX : StronglyAdapted ℱ X) (hτ : Monotone τ) :
    StronglyAdapted (ℱ.comp hτ) (fun n ↦ X (τ n)) := by
  intro n
  simpa only [Filtration.stronglyMeasurable_comp_iff] using hX (τ n)

end MeasureTheory
