/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import TauCeti.Probability.Martingale.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Event-refined Doob inequalities over finite and countable sets of times.
-/

public section

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Event-refined Doob inequality on a finite set.** The terminal expectation is restricted
to the same crossing event, even when the terminal time does not belong to the sampled set. -/
theorem mul_measure_exists_mem_le_le_setIntegral [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) (ε : ℝ≥0) {F : Finset ι} {T : ι}
    (hF : ∀ t ∈ F, t ≤ T) :
    ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f T ω ∂μ) := by
  classical
  obtain hEmpty | hne := F.eq_empty_or_nonempty
  · simp [hEmpty]
  -- Sample exactly F, not F ∪ {T}: adding T would enlarge the event on the right.
  set n := F.card - 1
  have hcard : F.card = n + 1 := (Nat.sub_add_cancel hne.card_pos).symm
  let e := F.orderEmbOfFin hcard
  let τ : ℕ → ι := fun j ↦ e ⟨min j n, by omega⟩
  have hτ : Monotone τ := fun i j hij ↦ e.monotone (Fin.mk_le_mk.2 (min_le_min_right _ hij))
  have hmem (j : ℕ) : τ j ∈ F := F.orderEmbOfFin_mem hcard _
  have hτn : τ n = F.max' hne := by
    simpa [τ, e] using Finset.orderEmbOfFin_last hcard (Nat.succ_pos n)
  let 𝒢 : Filtration ℕ m0 := ℱ.comp hτ
  have hg : Submartingale (fun j ↦ f (τ j)) 𝒢 μ := hf.comp hτ
  have hset : {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} = {ω | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f (τ k) ω} := by
    ext ω
    simp only [mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨t, ht, hεt⟩
      obtain ⟨i, rfl⟩ : t ∈ range e := by
        rw [Finset.range_orderEmbOfFin]
        exact ht
      exact ⟨i, Finset.mem_range.2 i.2, by simpa [τ, min_eq_left (by omega : (i : ℕ) ≤ n)]⟩
    · rintro ⟨j, _, hεj⟩
      exact ⟨τ j, hmem j, hεj⟩
  have hmeas : MeasurableSet[ℱ (τ n)] {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} := by
    simp only [← exists_prop, ofPred_exists]
    apply F.measurableSet_biUnion
    intro t ht
    exact measurableSet_le measurable_const
      (((hf.stronglyAdapted t).mono (ℱ.mono (by rw [hτn]; exact F.le_max' t ht))).measurable)
  calc ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
      ≤ ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f (τ n) ω ∂μ) := by
        rw [hset]
        exact maximal_ineq hg (fun _ ↦ hnonneg _) n
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hf.setIntegral_le (hF _ (hmem n)) hmeas)

/-- **Event-refined Doob inequality on a countable set.** Sampling need not include the
terminal time; the expectation is restricted to exactly the sampled crossing event. -/
theorem mul_measure_exists_mem_le_le_setIntegral_of_countable [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) (ε : ℝ≥0)
    {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T) :
    ε * μ {ω | ∃ t ∈ S, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ S, (ε : ℝ) ≤ f t ω}, f T ω ∂μ) := by
  classical
  have := hS.to_subtype
  let A : Finset S → Set Ω := fun F ↦ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
  have hdir : Directed (· ⊆ ·) A := fun F G ↦ ⟨F ∪ G,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_left _ ht, h⟩,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_right _ ht, h⟩⟩
  have hUnion : (⋃ F, A F) = {ω | ∃ t ∈ S, (ε : ℝ) ≤ f t ω} := by
    simpa only [A, ← exists_prop, Set.ofPred_exists, iUnion_subtype] using
      (Set.iUnion_eq_iUnion_finset (fun t : S ↦ {ω | (ε : ℝ) ≤ f t ω})).symm
  rw [← hUnion, hdir.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro F
  have hbound := hf.mul_measure_exists_mem_le_le_setIntegral hnonneg ε
    (F := F.map (Function.Embedding.subtype _)) (T := T) (by
      intro t ht
      obtain ⟨⟨t, htS⟩, _, rfl⟩ := Finset.mem_map.1 ht
      exact hST t htS)
  have hset : {ω | ∃ t ∈ F.map (Function.Embedding.subtype _), (ε : ℝ) ≤ f t ω} = A F := by
    ext ω
    simp [A]
  rw [hset] at hbound
  refine hbound.trans (ENNReal.ofReal_le_ofReal (setIntegral_mono_set
    (hf.integrable T).integrableOn (Eventually.of_forall (fun _ ↦ hnonneg T _)) ?_))
  exact Eventually.of_forall (subset_iUnion A F)

/-- The event-refined Doob inequality also holds for strict crossings on a countable set. -/
theorem mul_measure_exists_mem_lt_le_setIntegral_of_countable [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) (ε : ℝ≥0)
    {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T) :
    ε * μ {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ S, (ε : ℝ) < f t ω}, f T ω ∂μ) := by
  obtain ⟨δ, hδanti, hδlt, hδlim⟩ := exists_seq_strictAnti_tendsto ε
  let A : ℕ → Set Ω := fun n ↦ {ω | ∃ t ∈ S, (δ n : ℝ) ≤ f t ω}
  have hmono : Monotone A := by
    intro i j hij ω ⟨t, ht, h⟩
    refine ⟨t, ht, le_trans ?_ h⟩
    exact_mod_cast hδanti.antitone hij
  have hsub (n : ℕ) : A n ⊆ {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} := by
    rintro ω ⟨t, ht, h⟩
    have hn : (ε : ℝ) < δ n := hδlt n
    exact ⟨t, ht, hn.trans_le h⟩
  have hUnion : (⋃ n, A n) = {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} := by
    apply Subset.antisymm (iUnion_subset hsub)
    rintro ω ⟨t, ht, h⟩
    obtain ⟨n, hn⟩ := ((NNReal.tendsto_coe.2 hδlim).eventually (Iio_mem_nhds h)).exists
    exact mem_iUnion.2 ⟨n, t, ht, hn.le⟩
  rw [← hUnion, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  calc ε * μ (A n) ≤ δ n * μ (A n) := by gcongr; exact (hδlt n).le
    _ ≤ ENNReal.ofReal (∫ ω in A n, f T ω ∂μ) :=
      hf.mul_measure_exists_mem_le_le_setIntegral_of_countable hnonneg (δ n) hS hST
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_mono_set
      (hf.integrable T).integrableOn (Eventually.of_forall (fun _ ↦ hnonneg T _))
      (Eventually.of_forall (by rw [hUnion]; exact hsub n)))

/-- **Event-refined positive-part Doob inequality for strict crossings on a countable set.** -/
theorem mul_measure_exists_mem_lt_le_setIntegral_posPart_of_countable [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {S : Set ι} (hS : S.Countable) {T : ι}
    (hST : ∀ t ∈ S, t ≤ T) :
    ε * μ {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ S, (ε : ℝ) < f t ω}, (f⁺) T ω ∂μ) := by
  have hset : {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} = {ω | ∃ t ∈ S, (ε : ℝ) < (f⁺) t ω} := by
    ext ω
    simp only [mem_ofPred_eq, Pi.posPart_apply, posPart_def, lt_max_iff]
    exact exists_congr fun t ↦ and_congr_right fun _ ↦
      ⟨Or.inl, fun h ↦ h.resolve_right (not_lt_of_ge ε.coe_nonneg)⟩
  rw [hset]
  exact hf.pos.mul_measure_exists_mem_lt_le_setIntegral_of_countable
    (fun _ _ ↦ posPart_nonneg _) ε hS hST

end MeasureTheory.Submartingale
