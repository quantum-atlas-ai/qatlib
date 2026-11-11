/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.ForwardProgram
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# A one-stage growing-stop example

This module gives a concrete growing-stop pipeline whose only stage swaps the running and good
flags. The example has unit success probability and satisfies the endpoint hypotheses, yielding
an explicit instance of the finite program-family guarantee associated with [Ambainis2012].

## Main statements

* `fresh_stop_has_success`: unit success and reached-stop mass.
* `fresh_stop_endpoint_premises`: the endpoint hypotheses for the example.
* `fresh_stop_endpoint_witness`: a finite family of legal bounded-time programs.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical

/-- The stop history on a unit payload, empty initially and full after the first stage. -/
def freshStopHistory : ℕ → Finset Unit
  | 0=>∅
  | _+1=>Finset.univ

/-- The permutation swapping the good and running flags while preserving the unit payload. -/
def freshStopPerm : VtSpace Unit≃VtSpace Unit :=
    Equiv.prodCongr (Equiv.swap vtGoodFlag vtRunningFlag) (Equiv.refl Unit)
/-- The permutation matrix of `freshStopPerm`. -/
def freshStopGate : Matrix (VtSpace Unit) (VtSpace Unit) ℂ := permMatrix freshStopPerm

/-- The good-running flag swap is an involution. -/
theorem freshStopPerm_involutive : Function.Involutive freshStopPerm := by
  intro ⟨f,c⟩
  change (Equiv.swap vtGoodFlag vtRunningFlag (Equiv.swap vtGoodFlag vtRunningFlag f),c)=(f,c)
  simp

/-- The fresh-stop permutation gate is unitary. -/
theorem freshStopGate_unitary : freshStopGate∈Matrix.unitaryGroup (VtSpace Unit) ℂ :=
    permMatrix_unitary freshStopPerm_involutive

/-- The single-gate pipeline is legal for the specified growing stop history. -/
theorem fresh_stop_pipeline_legal : GrowingVtLegal [freshStopGate] freshStopHistory := by
  refine ⟨rfl,?_,by simp [freshStopHistory],?_⟩
  · intro k
    cases k <;> simp [freshStopHistory]
  · intro k hk
    have hk0 : k=0 := by simp only [List.length_singleton] at hk;omega
    subst k
    refine ⟨freshStopGate_unitary,?_⟩
    intro p hp
    simp [reachedStoppedSet,freshStopHistory] at hp

/-- The single stage maps the running basis state to the good basis state. -/
theorem fresh_stop_state : vtState [freshStopGate] 1 (Ket (vtRunningFlag,()))=Ket (vtGoodFlag,()) := by
  have hs : ApplyGate freshStopGate (Ket (vtRunningFlag,()))=Ket (vtGoodFlag,()) := by
    change ApplyGate (permMatrix freshStopPerm) (Ket (vtRunningFlag,()))=Ket (vtGoodFlag,())
    rw [applyGate_permMatrix_ket freshStopPerm_involutive]
    simp [freshStopPerm,vtRunningFlag,vtGoodFlag]
  simpa [vtState,vtRunMatrix,ApplyGate] using hs

/-- The example has success probability one and reached-stop mass one at its first stage. -/
theorem fresh_stop_has_success :
    psucc [freshStopGate] (vtRunningFlag,())=1 ∧
      reachedPstop [freshStopGate] freshStopHistory (Ket (vtRunningFlag,())) 0=1 := by
  have hstate := fresh_stop_state
  change MeasureProb (vtState [freshStopGate] 1 (Ket (vtRunningFlag,()))) (goodSet Unit)=1 ∧ _
  rw [hstate]
  constructor
  · simp [MeasureProb,bornProb_ket,goodSet,vtGoodFlag]
  · unfold reachedPstop reachedStoppedMass
    rw [hstate]
    simp [vtState,vtRunMatrix,reachedStoppedSet,freshStopHistory,MeasureProb,bornProb_ket,vtGoodFlag,vtRunningFlag]

/-- The example satisfies the growing-stop support condition from its running initial basis
state. -/
theorem fresh_stop_supported : GrowingVtSupported [freshStopGate] freshStopHistory (vtRunningFlag,()) := by
  intro k hk p hn
  have hk1 : k ≤ 1 := by simpa using hk
  cases k with
  | zero=>
    have he : p=(vtRunningFlag,()) := by
      by_contra hp
      simp [vtState,vtRunMatrix,Ket,hp] at hn
    subst p
    simp [freshStopHistory]
  | succ k=>
    have hk0 : k=0 := by omega
    subst k
    have hs : vtState [freshStopGate] 1 (Ket (vtRunningFlag,()))=Ket (vtGoodFlag,()) := by
      exact fresh_stop_state
    have he : p=(vtGoodFlag,()) := by
      rw [hs] at hn
      by_contra hp
      simp [Ket,hp] at hn
    subst p
    simp [freshStopHistory,vtGoodFlag,vtRunningFlag]

/-- The example satisfies growing-stop legality and support, has no final running mass, and
meets the stated success-probability lower bound. -/
theorem fresh_stop_endpoint_premises :
    GrowingVtLegal [freshStopGate] freshStopHistory ∧
    GrowingVtSupported [freshStopGate] freshStopHistory (vtRunningFlag,()) ∧
    MeasureProb (vtState [freshStopGate] 1 (Ket (vtRunningFlag,()))) (runningSet Unit)=0 ∧
    1/(10^12*([freshStopGate].length : ℝ)^3) ≤ psucc [freshStopGate] (vtRunningFlag,()) := by
  refine ⟨fresh_stop_pipeline_legal,fresh_stop_supported,?_,?_⟩
  · have hs : vtState [freshStopGate] 1 (Ket (vtRunningFlag,()))=Ket (vtGoodFlag,()) := by
      exact fresh_stop_state
    rw [hs]
    simp [MeasureProb,bornProb_ket,runningSet,vtRunningFlag,vtGoodFlag]
  · rw [fresh_stop_has_success.1]
    norm_num

/-- The one-stage example possesses a finite probability law on legal programs satisfying the
stated uniform time bound, with good-record mass at least `9 / 10`, success at least `2 /
5`, running mass at most `3 / 5`, and the prescribed good-output direction. -/
theorem fresh_stop_endpoint_witness :
    ∃ (Ω : Type) (_ : Fintype Ω) (law : Ω → ℝ) (good : Finset Ω)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W) (w₀ : W)
      (prog : Ω → List (StructuralVtStep W Unit)),
      (∑ ω, law ω = 1) ∧ (∀ ω, 0 ≤ law ω) ∧
      (∀ ω, StructuralWordLegal [freshStopGate] (prog ω)) ∧
      (∀ ω, (structuralWordTime (prog ω) : ℝ) ≤
        4000000 * ([freshStopGate].length : ℝ) * Real.sqrt ([freshStopGate].length : ℝ) *
          (vtTmax [freshStopGate] +
            reachedTav [freshStopGate] freshStopHistory (vtRunningFlag, ()) /
              Real.sqrt (MeasureProb (vtState [freshStopGate] [freshStopGate].length
                (Ket (vtRunningFlag, ()))) (goodSet Unit)))) ∧
      (1 - 1 / 10 ≤ ∑ ω ∈ good, law ω) ∧
      (∀ ω ∈ good,
        let out := Run 1 (compileStructuralWord [freshStopGate] freshStopHistory
            (vtRunningFlag, ()) (prog ω)) (Ket (w₀, (false, (vtRunningFlag, ()))))
        2 / 5 ≤ MeasureProb out (Finset.univ.filter (fun p : VtReg W Unit => p.2.2.1 = vtGoodFlag)) ∧
        MeasureProb out (Finset.univ.filter (fun p : VtReg W Unit => p.2.2.1 = vtRunningFlag)) ≤ 3 / 5 ∧
        ∃ c : ℂ, Collapse out (Finset.univ.filter (fun p : VtReg W Unit => p.2.2.1 = vtGoodFlag)) =
          c • embedState w₀ (Collapse (vtState [freshStopGate] [freshStopGate].length
            (Ket (vtRunningFlag, ()))) (goodSet Unit))) := by
  classical
  refine ⟨Unit, inferInstance, fun _ => 1, Finset.univ, Unit, inferInstance, inferInstance, (),
    fun _ => vtForwardWord 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro ω; norm_num
  · intro ω; exact vt_forward_word_legal [freshStopGate] 1 (by simp)
  · intro ω
    have hlen : [freshStopGate].length = 1 := by simp
    have hcost : structuralWordTime (vtForwardWord (W := Unit) (C := Unit) 1) = 1 := by
      simpa using vt_forward_word_cost 1
    have hpsucc : MeasureProb (vtState [freshStopGate] 1 (Ket (vtRunningFlag, ())))
        (goodSet Unit) = 1 := fresh_stop_has_success.1
    have htav : reachedTav [freshStopGate] freshStopHistory (vtRunningFlag, ()) = 2 := by
      unfold reachedTav
      rw [hlen, Finset.sum_range_one, fresh_stop_has_success.2]
      norm_num [stopTime]
    have htmax : vtTmax [freshStopGate] = 2 := by unfold vtTmax; rw [hlen]; norm_num
    rw [hcost]
    simp only [hlen, htav, hpsucc, htmax, Real.sqrt_one]
    norm_num
  · simp
  · intro ω _
    have h1 : 1 ≤ [freshStopGate].length := by simp
    have htr := vt_forward_word_state [freshStopGate] freshStopHistory
      (vtRunningFlag, ()) () (Ket (vtRunningFlag, ())) 1 h1
    rw [show Ket ((), false, vtRunningFlag, ()) =
        TensorState (Ket ()) (TensorState (Ket false) (Ket (vtRunningFlag, ()))) from by
      rw [← tensorState_ket_ket, ← tensorState_ket_ket]]
    rw [htr, fresh_stop_state, tensorState_ket_ket, tensorState_ket_ket]
    simp only []
    constructor
    · simp only [MeasureProb, bornProb_ket]
      rw [Finset.sum_eq_single ((), false, vtGoodFlag, ()) ?_ ?_]
      · norm_num
      · intro b _ hb; simp [hb]
      · simp
    constructor
    · have hz : MeasureProb (Ket ((), false, vtGoodFlag, ()))
          (Finset.univ.filter (fun p : VtReg Unit Unit => p.2.2.1 = vtRunningFlag)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hne : b ≠ ((), false, vtGoodFlag, ()) := by
          intro he
          have hh := (Finset.mem_filter.mp hb).2
          rw [he] at hh
          exact (by decide : vtGoodFlag ≠ vtRunningFlag) hh
        simp [bornProb_ket, hne]
      rw [hz]; norm_num
    · refine ⟨1, ?_⟩
      rw [show ([freshStopGate].length : ℕ) = 1 from rfl, fresh_stop_state]
      funext p
      fin_cases p <;> simp [collapse_apply, embedState, Ket, goodSet]
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
