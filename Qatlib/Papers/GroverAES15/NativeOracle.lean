/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CipherCircuits.CipherOracle
import Qatlib.Concepts.SearchStopping.KnownCount.PreparedSearch
set_option warningAsError false

namespace Qatlib.Papers.GroverAES15.NativeOracle
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CipherCircuits.CipherOracle
open scoped Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def workCircuit : Circuit I → Circuit (Whole I J)
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate U (1 : Matrix (Bank J × Bool) (Bank J × Bool) ℂ)) :: workCircuit C
  | Step.query :: C => Step.query :: workCircuit C
omit [Fintype I] [DecidableEq I] [DecidableEq J] in

theorem workCircuit_queries (C : Circuit I) : QueryCount (workCircuit (J:=J) C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workCircuit, ih]
omit [Fintype I] [DecidableEq I] [DecidableEq J] in

theorem workCircuit_macros (C : Circuit I) : GateCount (workCircuit (J:=J) C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [workCircuit, ih]

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

theorem normalized_auxiliary : Normalized (auxiliary (J:=J)) := auxiliary_normalized

theorem normalized_embed {ψ : I → ℂ} (hψ : Normalized ψ) : Normalized (embed (J:=J) ψ) :=
  normalized_tensorState hψ normalized_auxiliary

theorem normalized_work_run (values : I → Bank J) (target : Bank J) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (ψ : I → ℂ) (hψ : Normalized ψ) :
    Normalized (Run (oracleMatrix values target) (workCircuit C) (embed ψ)) :=
  normalized_run (oracleMatrix values target) (oracleMatrix_unitary values target)
    (workCircuit C) (workCircuit_unitary C hC) (normalized_embed hψ)

def cleanEvent : Finset (Bank J × Bool) := ({zeroBank} : Finset (Bank J)).product Finset.univ
omit [DecidableEq J] in

theorem auxiliary_clean_mass : MeasureProb (auxiliary (J:=J)) cleanEvent = 1 := by
  norm_num [MeasureProb, cleanEvent, BornProb, auxiliary, minus_norm_sq]

def fullEvent (A : Finset I) : Finset (Whole I J) := A.product cleanEvent

theorem measure_embed (ψ : I → ℂ) (A : Finset I) :
    MeasureProb (embed (J:=J) ψ) (fullEvent A) = MeasureProb ψ A := by
  calc
    _ = MeasureProb ψ A * MeasureProb (auxiliary (J:=J)) (cleanEvent (J:=J)) :=
      measureProb_tensorState_prod ψ (auxiliary (J:=J)) A (cleanEvent (J:=J))
    _ = _ := by rw [auxiliary_clean_mass, mul_one]

theorem measure_work_run (values : I → Bank J) (target : Bank J) (C : Circuit I)
    (ψ : I → ℂ) (A : Finset I) :
    MeasureProb (Run (oracleMatrix values target) (workCircuit C) (embed ψ)) (fullEvent A) =
      MeasureProb (Run (phaseMatrix values target) C ψ) A := by
  rw [run_workCircuit, measure_embed]

end
end Qatlib.Papers.GroverAES15.NativeOracle
