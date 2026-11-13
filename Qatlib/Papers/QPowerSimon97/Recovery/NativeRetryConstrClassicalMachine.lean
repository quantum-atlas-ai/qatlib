/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodSimo

/-!
# Classical serialization and verification for Simon recovery

Verifies bit serialization, Boolean comparison, and decoder agreement for the classical stage of
Simon recovery. The explicit bit-operation ledger and expected retry bound account for classical
work and compare it with the decoding padding allowance used in the construction of [Simon1997].

## Main statements

* `simonClassicalStage_output`: The serialized decoder followed by Boolean comparison of the
  candidate and zero oracle values agrees with `simonVerifyCandidate` on the decoded record.
* `clause4_bit_time_bound`: Under the Boolean Simon promise, the unbounded retry time times the
  classical bit ledger is at most twice the explicit per-block bit-work bound.

## References

* [Simon, 1997][Simon1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QPowerSimon97.Recovery
variable {n : ℕ}
noncomputable section

/-- The Boolean register comparison returns `true` exactly when its two input registers are
equal. -/
theorem simonCompare_iff {m : ℕ} (a b : Reg m) :
    simonCompare a b = true ↔ a = b := by
  constructor
  · intro h
    funext j
    have hj := List.all_eq_true.mp h j (List.mem_finRange j)
    exact of_decide_eq_true hj
  · intro h
    subst h
    simp only [simonCompare]
    apply List.all_eq_true.mpr
    intro x hx
    simp
end
noncomputable section

/-- Comparing the register encodings of two Boolean vectors returns `true` exactly when the
vectors are equal. -/
theorem simonCompare_output {m : ℕ} (a b : BooleanVec m) :
    simonCompare ((regBooleanEquiv m).symm a) ((regBooleanEquiv m).symm b) = true ↔ a = b := by
  constructor
  · intro h
    have h' : ((regBooleanEquiv m).symm a) = ((regBooleanEquiv m).symm b) :=
      (simonCompare_iff _ _).1 h
    exact (regBooleanEquiv m).symm.injective h'
  · intro h
    have h' : ((regBooleanEquiv m).symm a) = ((regBooleanEquiv m).symm b) :=
      congrArg (regBooleanEquiv m).symm h
    exact (simonCompare_iff _ _).2 h'
end
noncomputable section

/-- Serializing a measured character sample returns the corresponding bit of `simonRecordBits`. -/
theorem simonSerializeBit_actual {n : ℕ} (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ)
    (i : Fin (n+1)) (j : Fin n) :
    simonSerializeBit xs i j = simonRecordBits xs i j := by
  calc
    simonRecordBits xs i j = boolZModEquiv.symm (boolZModEquiv (simonRecordBits xs i j)) :=
      (Equiv.symm_apply_apply _ _).symm
    _ = boolZModEquiv.symm (regBooleanEquiv n (simonRecordBits xs i) j) := by
      rw [regBooleanEquiv_apply]
    _ = boolZModEquiv.symm (booleanDecodedSamples xs i j) := by
      congr 1
      exact congrFun (congrFun (regBooleanEquiv_simonRecordBits xs) i) j
end
noncomputable section

/-- Decoding the serialized bits gives the same result as decoding `simonRecordBits`. -/
theorem simonDecodeMachine_agrees {n : ℕ} (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) :
    decodeSimonSecret (fun i => fun j => simonSerializeBit xs i j) =
      decodeSimonSecret (simonRecordBits xs) := by
  have h : (fun i => fun j => simonSerializeBit xs i j) = simonRecordBits xs := by
    funext i
    funext j
    exact (simonSerializeBit_actual xs i j).symm
  exact congrArg decodeSimonSecret h
end
noncomputable section

/-- The Boolean echelon run on the sampled Simon rows uses at most `simonBitOpsBound n` recorded
bit operations. -/
theorem simonBitOpsBound_actual {n : ℕ} (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) :
    (booleanEchelonRun (List.ofFn (simonRecordBits xs))).bitOps ≤ simonBitOpsBound n := by
  have h := (boolean_gaussian_actual_operation_bound (simonRecordBits xs)).2.2
  exact h
end
noncomputable section

/-- The classical bit ledger is at most `2 * Tf + (n + 1) * n + m + simonBitOpsBound n`. -/
theorem simonClassicalBitLedger_le {n : ℕ} (m : ℕ) (Tf : ℕ)
    (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) :
    simonClassicalBitLedger m Tf xs ≤ 2*Tf + (n+1)*n + m + simonBitOpsBound n := by
  unfold simonClassicalBitLedger
  have h3 : (booleanEchelonRun (List.ofFn (simonRecordBits xs))).bitOps ≤ simonBitOpsBound n :=
    simonBitOpsBound_actual xs
  have hser : simonSerializeSteps (simonRecordBits xs) = (n+1)*n := rfl
  have hcmp : simonCompareSteps m = m := rfl
  rw [hser, hcmp]
  exact Nat.add_le_add_left h3 _
end
noncomputable section

/-- The serialized decoder followed by Boolean comparison of the candidate and zero oracle
values agrees with `simonVerifyCandidate` on the decoded record. -/
theorem simonClassicalStage_output {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) :
    (match decodeSimonSecret (fun i => fun j => simonSerializeBit xs i j) with
      | none => none
      | some t => if simonCompare ((regBooleanEquiv m).symm (f (regBooleanEquiv n t)))
                                ((regBooleanEquiv m).symm (f (0 : BooleanVec n)))
                  then some t else none)
      = simonVerifyCandidate f (decodeSimonSecret (simonRecordBits xs)) := by
  rw [simonDecodeMachine_agrees xs]
  cases h : decodeSimonSecret (simonRecordBits xs) with
  | none => simp [simonVerifyCandidate]
  | some t =>
      show (if simonCompare ((regBooleanEquiv m).symm (f (regBooleanEquiv n t)))
                          ((regBooleanEquiv m).symm (f (0 : BooleanVec n)))
            then some t else none) = simonVerifyCandidate f (some t)
      have hRHS : simonVerifyCandidate f (some t) =
          if f (regBooleanEquiv n t) = f (0 : BooleanVec n) then some t else none := by
        simp [simonVerifyCandidate]
      by_cases he : f (regBooleanEquiv n t) = f (0 : BooleanVec n)
      · have hb : simonCompare ((regBooleanEquiv m).symm (f (regBooleanEquiv n t)))
                            ((regBooleanEquiv m).symm (f (0 : BooleanVec n))) = true :=
          (simonCompare_output _ _).2 he
        rw [if_pos hb, hRHS, if_pos he]
      · have hb : simonCompare ((regBooleanEquiv m).symm (f (regBooleanEquiv n t)))
                            ((regBooleanEquiv m).symm (f (0 : BooleanVec n))) ≠ true :=
          fun h' => he ((simonCompare_output _ _).1 h')
        rw [if_neg hb, hRHS, if_neg he]
end
noncomputable section

/-- Under the Boolean Simon promise, the unbounded retry time times the classical bit ledger is
at most twice the explicit per-block bit-work bound. -/
theorem clause4_bit_time_bound {n m : ℕ} (f : BooleanVec n → BooleanVec m) (s : Reg n)
    (hp : BooleanSimonPromise f (regBooleanEquiv n s)) (Tf : ℕ)
    (xs : Fin (n+1) → AddChar (BooleanVec n) ℂ) :
    (generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) : ℝ≥0∞) *
      (simonClassicalBitLedger m Tf xs : ℕ) ≤
    (2 : ℝ≥0∞) * (2*Tf + (n+1)*n + m + simonBitOpsBound n) := by
  have ht := (simon_verified_unbounded_expected_queries_and_cutoff n (BooleanVec m) f s hp).2.1
  refine mul_le_mul' ht ?_
  exact_mod_cast simonClassicalBitLedger_le m Tf xs
end
noncomputable section

/-- The recorded bit-operation bound is at most the decoding gate-padding allowance. -/
theorem simonBitOpsBound_le_decodePad (n : ℕ) :
    simonBitOpsBound n ≤ simonDecodePadGates n := by
  have hinner : (n+1)*n^2+(n+1)*n+(n+1) ≤ (n+1)*n^2+n^3+(n+1)*n+n^2+n+1 := by
    nlinarith
  have h1 : 1 ≤ 64*(n+1) := by omega
  calc
    simonBitOpsBound n = 10*((n+1)*n^2+(n+1)*n+(n+1)) := rfl
    _ ≤ 10*((n+1)*n^2+n^3+(n+1)*n+n^2+n+1) := Nat.mul_le_mul_left _ hinner
    _ = simonBlockOpsBound n := rfl
    _ ≤ 64*(n+1)*simonBlockOpsBound n := by
      calc
        simonBlockOpsBound n = 1 * simonBlockOpsBound n := by simp
        _ ≤ 64*(n+1) * simonBlockOpsBound n := Nat.mul_le_mul_right _ h1
    _ = simonDecodePadGates n := rfl
end
noncomputable section

/-- For positive `n`, the recorded bit-operation bound is strictly less than the decoding
gate-padding allowance. -/
theorem simonBitOpsBound_lt_decodePad {n : ℕ} (hn : 0 < n) :
    simonBitOpsBound n < simonDecodePadGates n := by
  have h1 : simonBitOpsBound n ≤ simonBlockOpsBound n := by
    have hinner : (n+1)*n^2+(n+1)*n+(n+1) ≤ (n+1)*n^2+n^3+(n+1)*n+n^2+n+1 := by
      nlinarith
    calc
      simonBitOpsBound n = 10*((n+1)*n^2+(n+1)*n+(n+1)) := rfl
      _ ≤ 10*((n+1)*n^2+n^3+(n+1)*n+n^2+n+1) := Nat.mul_le_mul_left _ hinner
      _ = simonBlockOpsBound n := rfl
  have hpos : 0 < simonBlockOpsBound n := by
    unfold simonBlockOpsBound
    positivity
  have hlt : 1 < 64*(n+1) := by omega
  have h2 : simonBlockOpsBound n < 64*(n+1)*simonBlockOpsBound n := by
    calc
      simonBlockOpsBound n = 1 * simonBlockOpsBound n := by simp
      _ < 64*(n+1) * simonBlockOpsBound n := Nat.mul_lt_mul_of_pos_right hlt hpos
  exact h1.trans_lt h2
end
end Qatlib.Papers.QPowerSimon97.Recovery
