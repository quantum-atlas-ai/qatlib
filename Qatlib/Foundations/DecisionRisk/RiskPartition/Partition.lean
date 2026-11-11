/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DecisionRisk.RiskPartition.RiskGrid

/-!
# Partition

Risk Partition constructions for Decision Risk.
Defines `partitionFunction`.
Proves `partitionFunction_at`, `integrable_partitionFunction`, `integral_partitionFunction`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- Definition of partition Function in the Risk Partition construction. -/
def partitionFunction {Y α : Type*} [Fintype α] (B : α → Set Y) (v : α → ℝ) : Y → ℝ :=
  fun y => ∑ a, (B a).indicator (fun _ => v a) y

/-- The stated finite risk construction satisfies `partitionFunction_at` with all displayed hypotheses retained. -/
lemma partitionFunction_at {Y α : Type*} [Fintype α]
    (B : α → Set Y) (hd : Pairwise (fun a b => Disjoint (B a) (B b)))
    (v : α → ℝ) {a : α} {y : Y} (hy : y ∈ B a) : partitionFunction B v y=v a := by
  classical
  unfold partitionFunction
  rw [Finset.sum_eq_single a]
  · exact Set.indicator_of_mem hy _
  · intro b _ hba
    exact Set.indicator_of_notMem (fun hyb => Set.disjoint_left.mp (hd hba.symm) hy hyb) _
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- The stated finite risk construction satisfies `integrable_partitionFunction` with all displayed hypotheses retained. -/
lemma integrable_partitionFunction {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (B : α → Set Y)
    (hB : ∀ a, MeasurableSet (B a)) (v : α → ℝ) : Integrable (partitionFunction B v) μ := by
  apply integrable_finsetSum
  intro a _
  exact (integrable_const (v a)).indicator (hB a)

/-- The stated finite risk construction satisfies `integral_partitionFunction` with all displayed hypotheses retained. -/
lemma integral_partitionFunction {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (B : α → Set Y)
    (hB : ∀ a, MeasurableSet (B a)) (v : α → ℝ) :
    (∫ y, partitionFunction B v y ∂μ)=∑ a, μ.real (B a)*v a := by
  unfold partitionFunction
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (hB _), smul_eq_mul]
  · intro a _
    exact (integrable_const (v a)).indicator (hB a)

/-- Every bounded measurable continuation risk is genuinely integrable. -/
lemma integrable_unitRisk {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] (c : Y → ℝ) (hm : Measurable c) (hc : ∀ y, 0 ≤ c y ∧ c y ≤ 1) :
    Integrable c μ := by
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hc y).1]
    exact (hc y).2

/-- Finite representative substitution controls actual integrated risk. The
same representative is used throughout a cell; empty cells need no witness. -/
theorem partition_risk_bound {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (B : α → Set Y)
    (hB : ∀ a, MeasurableSet (B a)) (hd : Pairwise (fun a b => Disjoint (B a) (B b)))
    (hu : ⋃ a, B a=Set.univ) (r : α → Y)
    (hr : ∀ a, (B a).Nonempty → r a ∈ B a)
    (c : Y → ℝ) (hm : Measurable c) (hc : ∀ y, 0 ≤ c y ∧ c y ≤ 1) {δ : ℝ}
    (hdiam : ∀ a, ∀ y ∈ B a, ∀ z ∈ B a, |c y-c z| ≤ δ) :
    |(∑ a, μ.real (B a)*c (r a))-(∫ y, c y ∂μ)| ≤ δ*μ.real Set.univ := by
  have hpoint : ∀ y, ‖partitionFunction B (fun a => c (r a)) y-c y‖ ≤ δ := by
    intro y
    have hy : y ∈ ⋃ a, B a := hu.symm ▸ Set.mem_univ y
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hy
    rw [partitionFunction_at B hd _ ha, Real.norm_eq_abs]
    exact hdiam a (r a) (hr a ⟨y, ha⟩) y ha
  have hn := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hpoint)
  rw [integral_sub (integrable_partitionFunction μ B hB _) (integrable_unitRisk μ c hm hc),
    integral_partitionFunction μ B hB, Real.norm_eq_abs] at hn
  exact hn

end Qatlib.Foundations.DecisionRisk.RiskPartition
