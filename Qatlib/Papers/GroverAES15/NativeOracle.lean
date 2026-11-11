/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CipherCircuits.CipherOracle
import Qatlib.Concepts.SearchStopping.KnownCount.PreparedSearch

/-!
# Lifting phase-query circuits to a cipher workspace

This module lifts a phase-query circuit to a larger register carrying the cipher workspace and
flag. The lifted execution agrees with the embedded phase-oracle execution, preserving
normalization and event probabilities in the oracle model used for the Grover key-search setting
of [GrasslEtAl2015].

## Main statements

* `run_workCircuit`: exact correspondence between lifted and phase-oracle execution.
* `workCircuit_queries`: preservation of query count.
* `measure_work_run`: equality of success-event probabilities.

## References

* [Grassl et al., 2015][GrasslEtAl2015]
-/

set_option warningAsError false

namespace Qatlib.Papers.GroverAES15.NativeOracle
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CipherCircuits.CipherOracle
open scoped Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Lift a circuit to the key, bank, and flag register by tensoring each gate with the auxiliary
identity and retaining each query step. -/
def workCircuit : Circuit I → Circuit (Whole I J)
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate U (1 : Matrix (Bank J × Bool) (Bank J × Bool) ℂ)) :: workCircuit C
  | Step.query :: C => Step.query :: workCircuit C
omit [Fintype I] [DecidableEq I] [DecidableEq J] in

/-- Lifting a circuit to the workspace register preserves its query count. -/
theorem workCircuit_queries (C : Circuit I) : QueryCount (workCircuit (J:=J) C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workCircuit, ih]
omit [Fintype I] [DecidableEq I] [DecidableEq J] in

/-- Lifting a circuit to the workspace register preserves its gate-step count. -/
theorem workCircuit_macros (C : Circuit I) : GateCount (workCircuit (J:=J) C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workCircuit, ih]

/-- The workspace lift of a unitary circuit is unitary. -/
theorem workCircuit_unitary (C : Circuit I) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (workCircuit (J:=J) C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU,hC⟩ := (isUnitaryCircuit_gate U C).mp hC
      exact (isUnitaryCircuit_gate _ _).mpr
        ⟨tensorGate_unitary hU (Submonoid.one_mem _), ih hC⟩
    | query => exact (isUnitaryCircuit_query _).mpr (ih ((isUnitaryCircuit_query C).mp hC))

/-- Running the lifted circuit with the workspace oracle on an embedded state equals embedding
the phase-oracle execution [GrasslEtAl2015]. -/
theorem run_workCircuit (values : I → Bank J) (target : Bank J) (C : Circuit I) (ψ : I → ℂ) :
    Run (oracleMatrix values target) (workCircuit C) (embed ψ) =
      embed (Run (phaseMatrix values target) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [workCircuit, Run]
      rw [show embed ψ = TensorState ψ (auxiliary (J:=J)) from rfl,
        applyGate_tensorGate, applyGate_one]
      exact ih (ApplyGate U ψ)
    | query =>
      simp only [workCircuit, Run]
      rw [show ApplyGate (oracleMatrix values target) (embed ψ) =
          embed (ApplyGate (phaseMatrix values target) ψ) from oracleMatrix_embed values target ψ]
      exact ih _

/-- The auxiliary workspace state is normalized. -/
theorem normalized_auxiliary : Normalized (auxiliary (J:=J)) := auxiliary_normalized

/-- Embedding a normalized state with the auxiliary workspace preserves normalization. -/
theorem normalized_embed {ψ : I → ℂ} (hψ : Normalized ψ) : Normalized (embed (J:=J) ψ) :=
  normalized_tensorState hψ normalized_auxiliary

/-- Running a lifted unitary circuit with the workspace oracle on an embedded normalized state
gives a normalized state [GrasslEtAl2015]. -/
theorem normalized_work_run (values : I → Bank J) (target : Bank J) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (ψ : I → ℂ) (hψ : Normalized ψ) :
    Normalized (Run (oracleMatrix values target) (workCircuit C) (embed ψ)) :=
  normalized_run (oracleMatrix values target) (oracleMatrix_unitary values target)
    (workCircuit C) (workCircuit_unitary C hC) (normalized_embed hψ)

/-- The auxiliary event in which the bank is zero and the flag is unrestricted. -/
def cleanEvent : Finset (Bank J × Bool) := ({zeroBank} : Finset (Bank J)).product Finset.univ
omit [DecidableEq J] in

/-- The auxiliary state assigns probability one to the clean-workspace event. -/
theorem auxiliary_clean_mass : MeasureProb (auxiliary (J:=J)) cleanEvent = 1 := by
  norm_num [MeasureProb, cleanEvent, BornProb, auxiliary, minus_norm_sq]

/-- The joint event consisting of a key event `A` and the clean auxiliary event. -/
def fullEvent (A : Finset I) : Finset (Whole I J) := A.product cleanEvent

/-- The embedded state assigns to the joint clean-workspace event the same probability that the
original state assigns to `A`. -/
theorem measure_embed (ψ : I → ℂ) (A : Finset I) :
    MeasureProb (embed (J:=J) ψ) (fullEvent A) = MeasureProb ψ A := by
  calc
    _ = MeasureProb ψ A * MeasureProb (auxiliary (J:=J)) (cleanEvent (J:=J)) :=
      measureProb_tensorState_prod ψ (auxiliary (J:=J)) A (cleanEvent (J:=J))
    _ = _ := by rw [auxiliary_clean_mass, mul_one]

/-- The lifted workspace execution and the phase-oracle execution assign equal probabilities to
the corresponding joint and key events [GrasslEtAl2015]. -/
theorem measure_work_run (values : I → Bank J) (target : Bank J) (C : Circuit I)
    (ψ : I → ℂ) (A : Finset I) :
    MeasureProb (Run (oracleMatrix values target) (workCircuit C) (embed ψ)) (fullEvent A) =
      MeasureProb (Run (phaseMatrix values target) C ψ) A := by
  rw [run_workCircuit, measure_embed]

end
end Qatlib.Papers.GroverAES15.NativeOracle
