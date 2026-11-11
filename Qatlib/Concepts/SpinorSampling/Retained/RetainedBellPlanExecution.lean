/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPlanBounds

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Plan Execution

Retained Bell Plan Execution constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [DecidableEq S] {n m K : ℕ}

/-- Construction for captured Address Records in the retained bell plan execution model. -/
def capturedAddressRecords (τ : S → S) (ω : Fin K → CohortObservation n m τ) : List S :=
  (List.ofFn fun j => (List.ofFn (ω j).1)++(List.ofFn (ω j).2.1)).flatten

/-- Complete original `captured_address_records_length` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem captured_address_records_length (τ : S → S) (ω : Fin K → CohortObservation n m τ) :
    (capturedAddressRecords τ ω).length=K*(n+m) := by
  simp [capturedAddressRecords,List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const]

-- The used wires are the actual first-address-selected physical wires of
-- each block's native Bell program. Discards are the complement, not a
/-- caller-provided success/resource certificate. -/
def usedCaptureWires (τ : S → S) (ω : CohortObservation n m τ) : Finset (Fin (n+m)) :=
  Finset.univ.image (matchedPhysicalFin ω.1 ω.2.1 τ)

/-- Complete original `used_capture_wires_card` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem used_capture_wires_card (τ : Equiv.Perm S) (ω : CohortObservation n m τ) :
    (usedCaptureWires τ ω).card=2*(matchedSites ω.1 ω.2.1 τ).card := by
  rw [usedCaptureWires,Finset.card_image_of_injective _
    (matched_physical_fin_injective ω.1 ω.2.1 τ τ.injective)]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_coe,Fintype.card_bool]
  ring

/-- Construction for observed Discard Count in the retained bell plan execution model. -/
def observedDiscardCount (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℕ :=
  ∑ j : Fin K,((Finset.univ : Finset (Fin (n+m)))\usedCaptureWires τ (ω j)).card

/-- Complete original `observed_discard_account` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem observed_discard_account (τ : Equiv.Perm S) (ω : Fin K → CohortObservation n m τ) :
    observedDiscardCount τ ω+2*pooledMatches τ ω=(capturedAddressRecords τ ω).length := by
  have hblock (j : Fin K) :
      ((Finset.univ : Finset (Fin (n+m)))\usedCaptureWires τ (ω j)).card+
        2*(matchedSites (ω j).1 (ω j).2.1 τ).card=n+m := by
    have hc := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (usedCaptureWires τ (ω j)))
    simpa only [used_capture_wires_card,Finset.card_univ,Fintype.card_fin] using hc
  rw [captured_address_records_length]
  unfold observedDiscardCount pooledMatches observedRvec
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  simp_rw [hblock]
  simp

/-- Construction for observed Native Bell Gates in the retained bell plan execution model. -/
def observedNativeBellGates (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℕ :=
  ∑ j : Fin K,GateCount (pairProgram (matchedPhysicalFin (ω j).1 (ω j).2.1 τ)
    (matchedEnumeration (ω j).1 (ω j).2.1 τ))

/-- Construction for observed Native Bell Queries in the retained bell plan execution model. -/
def observedNativeBellQueries (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℕ :=
  ∑ j : Fin K,QueryCount (pairProgram (matchedPhysicalFin (ω j).1 (ω j).2.1 τ)
    (matchedEnumeration (ω j).1 (ω j).2.1 τ))

/-- Complete original `observed_native_bell_account` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem observed_native_bell_account (τ : S → S) (ω : Fin K → CohortObservation n m τ) :
    observedNativeBellGates τ ω=2*pooledMatches τ ω ∧ observedNativeBellQueries τ ω=0 := by
  constructor
  · unfold observedNativeBellGates pooledMatches observedRvec
    simp_rw [(observation_bell_counts τ _).2]
    rw [Finset.mul_sum]
  · unfold observedNativeBellQueries
    simp_rw [(observation_bell_counts τ _).1]
    simp

/-- Data and invariants for Planned Bell Receipt Q in the retained bell plan execution model. -/
structure PlannedBellReceiptQ where
  value : ℚ
  copies : ℕ
  discards : ℕ
  bellTests : ℕ
  nativeBellGates : ℕ
  nativeBellQueries : ℕ

/-- Construction for execute Planned Bell Q in the retained bell plan execution model. -/
def executePlannedBellQ (q : BellPlanQ) (τ : Equiv.Perm S)
    (ω : Fin q.blocks → CohortObservation q.records q.records τ) : PlannedBellReceiptQ where
  value := plannedBellMeanQ q τ ω
  copies := (capturedAddressRecords τ ω).length
  discards := observedDiscardCount τ ω
  bellTests := pooledMatches τ ω
  nativeBellGates := observedNativeBellGates τ ω
  nativeBellQueries := observedNativeBellQueries τ ω

/-- Complete original `executed_bell_wire_account` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem executed_bell_wire_account (q : BellPlanQ) (τ : Equiv.Perm S)
    (ω : Fin q.blocks → CohortObservation q.records q.records τ) :
    (executePlannedBellQ q τ ω).copies=
      (executePlannedBellQ q τ ω).discards+2*(executePlannedBellQ q τ ω).bellTests ∧
    (executePlannedBellQ q τ ω).nativeBellGates=2*(executePlannedBellQ q τ ω).bellTests ∧
    (executePlannedBellQ q τ ω).nativeBellQueries=0 := by
  exact ⟨(observed_discard_account τ ω).symm,observed_native_bell_account τ ω⟩

/-- Complete original `executed_bell_plan_copies` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem executed_bell_plan_copies (side M : ℕ) (p ε δ : ℚ) (τ : Equiv.Perm S)
    (ω : Fin (bellPlanQ side M p ε δ).blocks →
      CohortObservation (bellPlanQ side M p ε δ).records
        (bellPlanQ side M p ε δ).records τ) :
    (executePlannedBellQ (bellPlanQ side M p ε δ) τ ω).copies=
      (bellPlanQ side M p ε δ).copies := by
  change (capturedAddressRecords τ ω).length=_
  rw [captured_address_records_length]
  by_cases hside : side≤2
  · simp [bellPlanQ,hside]
  · by_cases hmid : p≤2*ε
    · simp [bellPlanQ,hside,hmid]
    · by_cases hn : bellRecordsQ M p ε δ≤M
      · simp only [bellPlanQ,ite_eq_right hside,ite_eq_right hmid,ite_eq_left hn]
        ring
      · simp only [bellPlanQ,ite_eq_right hside,ite_eq_right hmid,ite_eq_right hn]
        ring

/-- Complete original `executed_bell_plan_copies_upper` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem executed_bell_plan_copies_upper (side M : ℕ) (hM : 0<M) (p ε δ : ℚ)
    (hp : 0≤p) (hε : 0<ε) (τ : Equiv.Perm S)
    (ω : Fin (bellPlanQ side M p ε δ).blocks →
      CohortObservation (bellPlanQ side M p ε δ).records
        (bellPlanQ side M p ε δ).records τ) :
    ((executePlannedBellQ (bellPlanQ side M p ε δ) τ ω).copies : ℝ)≤
      4*(bellStrengthQ p ε δ : ℝ)+
        2*Real.sqrt ((M : ℝ)*(bellStrengthQ p ε δ : ℝ))+2 := by
  rw [executed_bell_plan_copies]
  exact bell_plan_copies_upper side M hM p ε δ hp hε

-- The same receipt carries the output and observed native Bell-word counts.
-- Address measurement, routing, memory, loading and classical processing are
-- additional costs; nativeBellGates does not purport to include them.
/-- Complete original `executed_periodic_bell_confidence` guarantee for `RetainedBellPlanExecution`; all source hypotheses and output obligations are retained. -/
theorem executed_periodic_bell_confidence (d N : ℕ) [NeZero N] (j : Fin d)
    (a b c k : (Fin d → Fin N) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (p ε δ : ℚ) (hp : 0≤p) (hp1 : p≤1/2) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1)
    (hmean : bellMean a b c k (periodicDoubleShift d N j)≤(p : ℝ)) :
    let q := bellPlanQ N (N^d) p ε δ
    (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz
      (periodicDoubleShift d N j) q.blocks).expect
      (fun ω => if (ε : ℝ)< |((executePlannedBellQ q (periodicDoubleShift d N j) ω).value : ℝ)-
        bellMean a b c k (periodicDoubleShift d N j)| then 1 else 0)≤(δ : ℝ) := by
  exact periodic_bell_plan_confidence d N j a b c k hz p ε δ hp hp1 hε hδ hδ1 hmean

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.captured_address_records_length
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.used_capture_wires_card
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observed_discard_account
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observed_native_bell_account
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_bell_wire_account
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_bell_plan_copies
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_bell_plan_copies_upper
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.executed_periodic_bell_confidence
