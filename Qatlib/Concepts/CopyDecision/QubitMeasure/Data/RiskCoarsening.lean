/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.GeneralPOVM
import Qatlib.Foundations.DecisionRisk.RiskPartition.Partition

/-!
# Risk Coarsening

Qubit Measure constructions for Copy Decision.
Proves `GeneralQubitPOVM.coarsenRisk_bound`, `GeneralQubitPOVM.exists_finite_risk_coarsening`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- Actual finite POVM branch risk versus the original measurable-outcome
integral, with one common representative for all labels and arbitrary priors. -/
theorem GeneralQubitPOVM.coarsenRisk_bound {Y : Type*} [MeasurableSpace Y]
    (M : GeneralQubitPOVM Y) {m : ℕ} (B : Fin m → Set Y)
    (hB : ∀ a, MeasurableSet (B a)) (hd : Pairwise (fun a b => Disjoint (B a) (B b)))
    (hu : ⋃ a, B a=Set.univ) (r : Fin m → Y)
    (hr : ∀ a, (B a).Nonempty → r a ∈ B a)
    (c : Y → Fin 3 → ℝ) (hm : ∀ i, Measurable (fun y => c y i))
    (hc : ∀ y i, 0 ≤ c y i ∧ c y i ≤ 1) {δ : ℝ}
    (hdiam : ∀ a, ∀ y ∈ B a, ∀ z ∈ B a, ∀ i, |c y i-c z i| ≤ δ)
    (q : Fin 3 → ℝ) (hq : ∀ i, 0 ≤ q i) :
    |(∑ a, ∑ i, (q i*qubitBorn ((M.coarsen B hB hd hu).mats a) (trineState i))*c (r a) i)-
      (∑ i, q i*(∫ y, c y i ∂M.bornMeasure (trineState i)))| ≤ δ*(∑ i, q i) := by
  let d : Fin 3 → ℝ := fun i =>
    (∑ a, (M.bornMeasure (trineState i)).real (B a)*c (r a) i)-
      (∫ y, c y i ∂M.bornMeasure (trineState i))
  have hi : ∀ i, |d i| ≤ δ := by
    intro i
    have h := partition_risk_bound (M.bornMeasure (trineState i)) B hB hd hu r hr
      (fun y => c y i) (hm i) (fun y => hc y i)
      (fun a y hy z hz => hdiam a y hy z hz i)
    simpa only [probReal_univ, mul_one] using h
  have heq :
      (∑ a, ∑ i, (q i*qubitBorn ((M.coarsen B hB hd hu).mats a) (trineState i))*c (r a) i)-
        (∑ i, q i*(∫ y, c y i ∂M.bornMeasure (trineState i)))=∑ i, q i*d i := by
    rw [Finset.sum_comm]
    simp only [d, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib,
      M.coarsen_born B hB hd hu, mul_assoc]
  rw [heq]
  calc
    _ ≤ ∑ i, |q i*d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, q i*δ := Finset.sum_le_sum fun i _ => by
      rw [abs_mul, abs_of_nonneg (hq i)]
      exact mul_le_mul_of_nonneg_left (hi i) (hq i)
    _ = δ*(∑ i, q i) := by rw [← Finset.sum_mul]; ring

/-- Constructive finite-grid existence (not an efficient algorithm claim).
The representatives are actual outcomes, common to all hidden labels. The
partition depends only on the original conditional error vector, not the prior. -/
theorem GeneralQubitPOVM.exists_finite_risk_coarsening {Y : Type*} [MeasurableSpace Y]
    (M : GeneralQubitPOVM Y) (c : Y → Fin 3 → ℝ)
    (hm : ∀ i, Measurable (fun y => c y i)) (hc : ∀ y i, 0 ≤ c y i ∧ c y i ≤ 1)
    (K : ℕ) (hK : 0 < K) :
    ∃ (m : ℕ) (Λ : POVM (Fin m) (Fin 2)) (r : Fin m → Y),
      ∀ (q : Fin 3 → ℝ), (∀ i, 0 ≤ q i) →
      |(∑ a, ∑ i, (q i*qubitBorn (Λ.mats a) (trineState i))*c (r a) i)-
        (∑ i, q i*(∫ y, c y i ∂M.bornMeasure (trineState i)))| ≤ (1/(K:ℝ))*(∑ i, q i) := by
  classical
  let α := Fin 3 → Fin (K+1)
  let m := Fintype.card α
  let e : α ≃ Fin m := Fintype.equivFin α
  let B : Fin m → Set Y := fun a => riskCell K c (e.symm a)
  have hB : ∀ a, MeasurableSet (B a) := fun a => riskCell_measurable K c hm (e.symm a)
  have hd : Pairwise (fun a b => Disjoint (B a) (B b)) := by
    intro a b hab
    exact riskCell_disjoint K c (fun h => hab (e.symm.injective h))
  have hu : ⋃ a, B a=Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro y _
    have hcover := riskCell_cover K c (fun y i => (hc y i).2)
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcover.symm ▸ Set.mem_univ y)
    exact Set.mem_iUnion.2 ⟨e b, by simpa only [B, e.symm_apply_apply] using hb⟩
  let y0 : Y := Classical.choice M.outcome_nonempty
  let r : Fin m → Y := fun a => if h : (B a).Nonempty then h.choose else y0
  have hr : ∀ a, (B a).Nonempty → r a ∈ B a := by
    intro a ha
    dsimp only [r]
    rw [dif_pos ha]
    exact ha.choose_spec
  refine ⟨m, M.coarsen B hB hd hu, r, ?_⟩
  intro q hq
  apply M.coarsenRisk_bound B hB hd hu r hr c hm hc _ q hq
  intro a y hy z hz i
  exact riskCell_diameter hK c (fun y i => (hc y i).1) hy hz i

end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
