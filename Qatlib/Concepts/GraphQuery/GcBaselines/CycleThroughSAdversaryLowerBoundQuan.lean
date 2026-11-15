/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.GcBaselines.CycleThroughSAdversaryLowerBoundStat
public import Qatlib.Concepts.GraphQuery.GcBaselines.CycleGadgetEquivalenceQuan
public import Qatlib.Concepts.GraphQuery.GcBaselines.AdversaryStar
public import Qatlib.Concepts.GraphQuery.GcBaselines.Section6Gadget

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GraphQuery.EdgeQuery
open Qatlib.Concepts.AdversaryBounds.AdvWitness
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.GraphQuery.GcBaselines.QuantumAlgorithmsForPathAndCycleContainmentProblems2026
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.GraphQuery.GcBaselines

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def collisionLeafEquiv {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Fin (edges.card * n) ≃ (↥edges × Fin n) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

def edgePositionLabel {n : ℕ} (e : Fin n × Fin n) (p b a : Fin n) : Bool :=
  decide (a = p ∧ (b = e.1 ∨ b = e.2))

noncomputable def cycleStarLabels {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Option (Fin (edges.card * n)) → Fin n → Fin n → Bool
  | none => fun _ _ => false
  | some k => edgePositionLabel (collisionLeafEquiv edges k).1.1 (collisionLeafEquiv edges k).2

noncomputable def cycleStarGraph {n : ℕ} (adj : Fin n → Fin n → Bool)
    (edges : Finset (Fin n × Fin n)) (k : Option (Fin (edges.card * n))) : GadgetSimpleAdj n :=
  ⟨gadgetAdjAt adj (cycleStarLabels edges k), gadgetAdjAt_simple adj _⟩

/-- Shows that the cycle star graph has a five-cycle through the station exactly when its index
is present. -/
private theorem cycleStarGraph_value {n : ℕ} (adj : Fin n → Fin n → Bool)
    (edges : Finset (Fin n × Fin n)) (hAdj : ∀ e ∈ edges, adj e.1 e.2 = true)
    (k : Option (Fin (edges.card * n))) :
    cycle5ThroughStation (cycleStarGraph adj edges k).1 = k.isSome := by
  rw [show (cycleStarGraph adj edges k).1 = gadgetAdjAt adj (cycleStarLabels edges k) from rfl,
    cycleGadgetEquivalence n adj (cycleStarLabels edges k)]
  cases k with
  | none => simp [gcOr, cycleStarLabels]
  | some k =>
    let ep := collisionLeafEquiv edges k
    apply decide_eq_true
    refine ⟨ep.1.1.1, ep.1.1.2, hAdj _ ep.1.2, ?_, ?_⟩
    · exact ⟨ep.2, by simp [cycleStarLabels, edgePositionLabel, ep]⟩
    · exact ⟨ep.2, by simp [cycleStarLabels, edgePositionLabel, ep]⟩

/-- Bounds the number of star leaves activating a fixed label bit by the corresponding graph
collision degree. -/
private theorem leafBit_card_le {n : ℕ} (edges : Finset (Fin n × Fin n)) (b a : Fin n) :
    (Finset.univ.filter (fun k : Fin (edges.card * n) =>
      cycleStarLabels edges (some k) b a = true)).card ≤ gcDegree edges b := by
  let S :=
      Finset.univ.filter (fun k : Fin (edges.card * n) => cycleStarLabels edges (some k) b a = true)
  let f := fun k : Fin (edges.card * n) => (collisionLeafEquiv edges k).1.1
  have hp (k : Fin (edges.card * n)) (hk : k ∈ S) :
      a = (collisionLeafEquiv edges k).2 ∧ (b = (f k).1 ∨ b = (f k).2) := by
    have h := (Finset.mem_filter.mp hk).2
    simpa [cycleStarLabels, edgePositionLabel, f] using! h
  have hi : Set.InjOn f S := by
    intro k hk l hl hkl
    apply (collisionLeafEquiv edges).injective
    apply Prod.ext
    · exact Subtype.ext hkl
    · exact (hp k hk).1.symm.trans (hp l hl).1
  have hsub : S.image f ⊆ edges.filter (fun e => e.1 = b ∨ e.2 = b) := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    refine ⟨(collisionLeafEquiv edges k).1.2, ?_⟩
    exact (hp k hk).2.imp Eq.symm Eq.symm
  change S.card ≤ _
  rw [← Finset.card_image_of_injOn hi]
  exact Finset.card_le_card hsub

/-- Bounds the square root of the number of activating leaves by the square root of the maximum
degree. -/
private theorem leafBit_norm_bound {n : ℕ} (edges : Finset (Fin n × Fin n)) (b a : Fin n) :
    Real.sqrt ((Finset.univ.filter (fun k : Fin (edges.card * n) =>
      cycleStarLabels edges (some k) b a = true)).card : ℝ) ≤ Real.sqrt (gcMaxDegree edges : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast (leafBit_card_le edges b a).trans (Finset.le_sup (Finset.mem_univ b))

/-- Bounds the cycle star adversary filter bound by the square root of the maximum degree. -/
private theorem cycleStar_filter (n : ℕ) (adj : Fin n → Fin n → Bool)
    (edges : Finset (Fin n × Fin n)) :
    advFilterBound (fun k => gadgetOracleInput (cycleStarGraph adj edges k))
      (advStarGamma (edges.card * n)) ≤ Real.sqrt (gcMaxDegree edges : ℝ) := by
  apply starFilterBound_le _ _ (Real.sqrt_nonneg _)
  intro i
  have h := starFilter_norm_le (fun k => gadgetOracleInput (cycleStarGraph adj edges k)) i
  apply h.trans
  let p := (gadgetAddrEquiv n i).1
  let q := (gadgetAddrEquiv n i).2
  change Real.sqrt ((Finset.univ.filter (fun k : Fin (edges.card * n) =>
      gadgetAdjAt adj (cycleStarLabels edges (some k)) p q ≠
        gadgetAdjAt adj (cycleStarLabels edges none) p q)).card : ℝ) ≤ _
  cases p with
  | station =>
    cases q with
    | station => simp [gadgetAdjAt]
    | layer l a => fin_cases l <;> simp [gadgetAdjAt]
  | layer l a =>
    cases q with
    | station => fin_cases l <;> simp [gadgetAdjAt]
    | layer k b =>
      fin_cases l <;> fin_cases k <;> simp only [gadgetAdjAt, cycleStarLabels]
      all_goals first
        | (solve | simp)
        | simpa using! leafBit_norm_bound edges b a
        | simpa using! leafBit_norm_bound edges a b

/-- Establishes the adversary lower bound for cycles through the designated set in
`CycleThroughSAdversaryLowerBound`. -/
theorem cycleThroughSAdversaryLowerBound : CycleThroughSAdversaryLowerBound := by
  intro n adj edges _ _ hAdj W _ _ C ψ E hC hψ hsuccess
  by_cases hm : edges.card * n = 0
  · have he : (n : ℝ) * (edges.card : ℝ) = 0 := by exact_mod_cast (by simpa [mul_comm] using! hm)
    rw [he, Real.sqrt_zero, mul_zero]
    positivity
  have hmpos : 0 < edges.card * n := Nat.pos_of_ne_zero hm
  have hw := negative_adversary_star_actual_search_witness (edges.card * n) hmpos
  have hs : ∀ k : Option (Fin (edges.card * n)), 1 - (1 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) (gadgetOracleInput (cycleStarGraph adj edges k))) C ψ)
        (if k.isSome then E else Eᶜ) := by
    intro k
    have h := hsuccess (cycleStarGraph adj edges k)
    rw [cycleStarGraph_value adj edges hAdj] at h
    convert! h using 1
    norm_num
  have h := negative_adversary_actual_bounded_error_circuit_lower_bound
    (Option (Fin (edges.card * n))) W (gadgetAddrCount n)
    (fun k => gadgetOracleInput (cycleStarGraph adj edges k)) (advStarGamma (edges.card * n))
    Option.isSome C ψ E (1 / 3) hw.1 hw.2.2.2.1 hC hψ (by norm_num) (by norm_num) hs
  rw [hw.2.1] at h
  have hb := mul_le_mul_of_nonneg_left (cycleStar_filter n adj edges)
    (by positivity : 0 ≤ 2 * (QueryCount C : ℝ))
  have hf := h.trans hb
  convert! hf using 1
  norm_num [Nat.cast_mul, mul_comm]

end Qatlib.Concepts.GraphQuery.GcBaselines
