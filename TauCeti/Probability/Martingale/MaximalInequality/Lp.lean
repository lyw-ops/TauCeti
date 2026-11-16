/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PartialSups
public import TauCeti.Probability.Martingale.MaximalInequality.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import TauCeti.Basic.ENNReal.Real
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Superlevel
import TauCeti.Order.Filter.PosPart

/-!
# Doob’s discrete-time strong `Lᵖ` maximal inequalities.
-/

public section

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Doob's strong `Lᵖ` maximal inequalities (`1 < p < ∞`) -/

section StrongLp

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's `Lᵖ` maximal inequality on a countable set (positive-part form).** For `1 < p < ∞` in
`ℝ≥0∞`, no sign or `MemLp` assumption on `f` is needed. -/
theorem eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart
    (hf : Submartingale f ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm ((f⁺) T) p μ := by
  have := hS.to_subtype
  have hu : AEStronglyMeasurable (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) μ := by
    have hmeas : AEMeasurable (fun ω ↦ ⨆ s : S, ENNReal.ofReal (f s ω)) μ :=
      AEMeasurable.iSup fun s : S ↦
        (((hf.stronglyAdapted s).measurable.mono (ℱ.le s) le_rfl).aemeasurable).ennreal_ofReal
    simpa only [iSup_subtype] using hmeas.aestronglyMeasurable
  refine TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral hp hp_top hu
    (fun _ _ ↦ measure_ne_top μ _) fun t ht ↦ ?_
  let ε : ℝ≥0 := Real.toNNReal t
  have hε_coe : (ε : ℝ) = t := Real.coe_toNNReal t ht.le
  have hε_enn : (ε : ℝ≥0∞) = ENNReal.ofReal t := by rw [← ENNReal.ofReal_coe_nnreal, hε_coe]
  have hset : {ω | ENNReal.ofReal t < ‖⨆ s ∈ S, ENNReal.ofReal (f s ω)‖ₑ} =
      {ω | ∃ s ∈ S, (ε : ℝ) < f s ω} := by
    ext ω
    simp only [mem_ofPred_eq, enorm_eq_self, ← hε_enn, lt_iSup_iff, exists_prop,
      ENNReal.coe_lt_ofReal]
  rw [hset, ← hε_enn]
  refine (hf.mul_measure_exists_mem_lt_le_setIntegral_posPart_of_countable ε hS hST).trans_eq ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hf.pos.integrable T).integrableOn
    (Eventually.of_forall fun _ ↦ posPart_nonneg _)]
  exact lintegral_congr fun ω ↦ (Real.enorm_eq_ofReal (posPart_nonneg (f T ω))).symm

end StrongLp

section DiscreteTimeLp

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsFiniteMeasure μ]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's discrete-time `Lᵖ` maximal inequality (positive-part form).** No `MemLp` assumption is
needed. -/
theorem eLpNorm_partialSups_posPart_le
    (hf : Submartingale f ℱ μ) (n : ι) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups (f⁺) n) p μ ≤ p / (p - 1) * eLpNorm ((f⁺) n) p μ := by
  have heq (ω : Ω) : ‖partialSups (f⁺) n ω‖ₑ = ⨆ k ∈ Set.Iic n, ENNReal.ofReal (f k ω) := by
    have hnn : 0 ≤ partialSups (f⁺) n ω :=
      (posPart_nonneg (f n ω)).trans (le_partialSups (f⁺) n ω)
    rw [Real.enorm_eq_ofReal hnn, Pi.partialSups_apply, partialSups_apply]
    refine le_antisymm ?_ ?_
    · obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_Iic (fun j ↦ (f⁺) j ω)
      rw [hsup, Pi.posPart_apply, Pi.posPart_apply, ENNReal.ofReal_posPart]
      exact le_iSup₂_of_le k (Finset.mem_Iic.1 hk) le_rfl
    · refine iSup₂_le fun k hk ↦ ?_
      rw [← ENNReal.ofReal_posPart]
      exact ENNReal.ofReal_le_ofReal
        (Finset.le_sup' (f := fun j ↦ (f⁺) j ω) (Finset.mem_Iic.2 hk))
  have hm_sup : AEStronglyMeasurable (partialSups (f⁺) n) μ := by
    rw [partialSups_apply]
    exact (Finset.sup'_induction _ _ (fun _ h₁ _ h₂ ↦ h₁.sup h₂) fun k _ ↦
      (hf.pos.stronglyAdapted k).mono (ℱ.le k)).aestronglyMeasurable
  calc eLpNorm (partialSups (f⁺) n) p μ
      ≤ eLpNorm (fun ω ↦ ⨆ k ∈ Set.Iic n, ENNReal.ofReal (f k ω)) p μ :=
        eLpNorm_mono_enorm hm_sup fun ω ↦ by simpa only [enorm_eq_self] using (heq ω).le
    _ ≤ p / (p - 1) * eLpNorm ((f⁺) n) p μ :=
        hf.eLpNorm_biSup_ofReal_le_mul_eLpNorm_posPart
          (Set.finite_Iic n).countable (fun _ hk ↦ hk) hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality.** Requires nonnegativity only at the terminal
index `n` (`0 ≤ᵐ[μ] f n`) and no `MemLp` hypothesis. -/
theorem eLpNorm_partialSups_le
    (hf : Submartingale f ℱ μ) {n : ι} (hposn : 0 ≤ᵐ[μ] f n)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups f n) p μ ≤ p / (p - 1) * eLpNorm (f n) p μ := by
  rw [eLpNorm_congr_ae hposn.partialSups_posPart_eq.symm,
    eLpNorm_congr_ae hposn.posPart_eq.symm]
  exact hf.eLpNorm_partialSups_posPart_le n hp hp_top

end DiscreteTimeLp

end MeasureTheory.Submartingale

/-! ### Banach-valued martingales -/

namespace MeasureTheory.Martingale

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section DiscreteTime

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsFiniteMeasure μ]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E}

/-- **Doob's discrete-time `Lᵖ` maximal inequality for Banach-valued martingales (`eLpNorm` form).**
No `MemLp` assumption is needed. -/
theorem eLpNorm_partialSups_norm_le
    (hX : Martingale X ℱ μ) (n : ι) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups (fun k ω ↦ ‖X k ω‖) n) p μ ≤ p / (p - 1) * eLpNorm (X n) p μ := by
  rw [← eLpNorm_norm (X n) ((hX.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable]
  exact hX.norm.eLpNorm_partialSups_le (Eventually.of_forall fun _ ↦ norm_nonneg _) hp hp_top

end DiscreteTime

end MeasureTheory.Martingale
