/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
import Qatlib.Concepts.RiskEstimation.PopulationGap.SimTaylorDefs
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Qatlib.Concepts.RiskEstimation.PopulationGap
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def ratGridTime (τ : ℚ) (M : ℕ) (j : Fin M) : ℚ := τ * j / M

def gridTime (τ : ℝ) (M : ℕ) (j : Fin M) : ℝ := τ * (j : ℝ) / (M : ℝ)

theorem ratGridTime_cast (τ : ℚ) (M : ℕ) (j : Fin M) (hM : 0 < M) :
    (ratGridTime τ M j : ℝ) = gridTime (τ : ℝ) M j := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  simp only [ratGridTime, gridTime]
  push_cast
  field_simp

theorem gridTime_strictMono (τ : ℝ) (M : ℕ) (hM : 0 < M) (hτ : 0 < τ) {j k : Fin M}
    (hj : j < k) : gridTime τ M j < gridTime τ M k := by
  have hj' : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
  have hfrac : (0 : ℝ) < τ / (M : ℝ) := div_pos hτ (by exact_mod_cast hM)
  simp only [gridTime]
  calc
    τ * (j : ℝ) / (M : ℝ) = (τ / (M : ℝ)) * (j : ℝ) := by ring
    _ < (τ / (M : ℝ)) * (k : ℝ) := mul_lt_mul_of_pos_left hj' hfrac
    _ = τ * (k : ℝ) / (M : ℝ) := by ring

def timeCount {l M : ℕ} (t : Fin l → Fin M) (j : Fin M) : ℕ :=
  ((Finset.univ : Finset (Fin l)).filter (fun a => t a = j)).card

theorem timeCount_sum {l M : ℕ} (t : Fin l → Fin M) :
    (∑ j : Fin M, timeCount t j) = l := by
  classical
  have h := Finset.sum_fiberwise (Finset.univ : Finset (Fin l)) (t) (fun _ => (1 : ℕ))
  simpa [timeCount] using! h

def timeNonDecreasing {l M : ℕ} (t : Fin l → Fin M) : Prop :=
  ∀ a b : Fin l, a < b → t a ≤ t b

noncomputable def timeMultiplicity (l M : ℕ) (c : Fin M → ℕ) : ℕ := by
  classical
  exact Fintype.card {u : Fin l → Fin M // ∀ j : Fin M, timeCount u j = c j}

theorem timeMultiplicity_pos (l M : ℕ) (c : Fin M → ℕ) (u : Fin l → Fin M)
    (hc : ∀ j : Fin M, timeCount u j = c j) : 0 < timeMultiplicity l M c := by
  classical
  letI : Nonempty {u : Fin l → Fin M // ∀ j : Fin M, timeCount u j = c j} :=
    ⟨u, fun j => hc j⟩
  exact Nat.pos_of_ne_zero (Fintype.card_ne_zero)

def canonTimes {M : ℕ} (c : Fin M → ℕ) : List (Fin M) :=
  (List.ofFn (fun j : Fin M => List.replicate (c j) j)).flatten

noncomputable def timeHamiltonian (h : ℝ → J → ℝ) (U : J → Matrix I I ℂ)
    (t : ℝ) : Matrix I I ℂ :=
  ∑ m : J, (h t m : ℂ) • U m

noncomputable def timeScale (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) : (Fin M × J) → ℝ :=
  fun p => h (gridTime τ M p.1) p.2 / (M : ℝ)

abbrev TimeWordLabel (J : Type) (K M : ℕ) := TaylorWordLabel (Fin M × J) K

def wordTimeCount {J : Type} {M : ℕ} {l : ℕ}
    (letters : Fin l → (Fin M × J)) : Fin M → ℕ :=
  fun j => ((Finset.univ : Finset (Fin l)).filter (fun a => (letters a).1 = j)).card

def timeCanonical {J : Type} {M : ℕ} {l : ℕ}
    (letters : Fin l → (Fin M × J)) : Prop :=
  List.ofFn (fun a => (letters a).1) = canonTimes (wordTimeCount letters)

noncomputable def timeCoeff (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) :
    TimeWordLabel J K M → ℂ := by
  classical
  intro x
  match x with
  | Sum.inl w =>
      exact if timeCanonical w.2 then
        (taylorWordCoefficient (timeScale h τ M) τ w) *
          ((timeMultiplicity w.1.val M (wordTimeCount w.2) : ℝ))
        else 0
  | Sum.inr b =>
      exact if b then (2 - taylorS0 (timeScale h τ M) τ K) / 2
        else -(2 - taylorS0 (timeScale h τ M) τ K) / 2

noncomputable def timeAmplitude (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) :
    TimeWordLabel J K M → ℝ :=
  fun x => Real.sqrt (‖timeCoeff h τ M K x‖ / 2)

noncomputable def timePhaseGate (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) :
    Matrix (TimeWordLabel J K M) (TimeWordLabel J K M) ℂ :=
  Matrix.diagonal (fun x => coefficientPhase (timeCoeff h τ M K x))

noncomputable def timePrepare (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) :
    Matrix (TimeWordLabel J K M) (TimeWordLabel J K M) ℂ :=
  nonnegativePrepare (fun x => Real.sqrt (‖timeCoeff h τ M K x‖ / 2))
    (taylorEmptyLabel (Fin M × J) K)

noncomputable def timeQuery (U : J → Matrix I I ℂ) (M : ℕ) (K : ℕ) :
    Matrix (TimeWordLabel J K M × (Bool × ((Fin M × J) × I)))
      (TimeWordLabel J K M × (Bool × ((Fin M × J) × I))) ℂ :=
  taylorQuery (fun p : Fin M × J => U p.2) K

noncomputable def timeLCUWord (h : ℝ → J → ℝ) (U : J → Matrix I I ℂ)
    (M : ℕ) (j0 : Fin M × J) (τ : ℝ) (K : ℕ) :
    List (AdjointStep (TimeWordLabel J K M × (Bool × ((Fin M × J) × I)))) :=
  [.gate (TensorGate (timePrepare h τ M K)ᴴ
      (1 : Matrix (Bool × ((Fin M × J) × I)) (Bool × ((Fin M × J) × I)) ℂ)),
    .gate (TensorGate (timePhaseGate h τ M K)
      (1 : Matrix (Bool × ((Fin M × J) × I)) (Bool × ((Fin M × J) × I)) ℂ))] ++
    taylorBlockList j0 K K le_rfl ++
    [.gate (TensorGate (timePrepare h τ M K)
      (1 : Matrix (Bool × ((Fin M × J) × I)) (Bool × ((Fin M × J) × I)) ℂ))]

noncomputable def timeFrame (M : ℕ) (j0 : Fin M × J) (K : ℕ) :
    Matrix (TimeWordLabel J K M × (Bool × ((Fin M × J) × I))) I ℂ :=
  taylorFrame j0 K

end Qatlib.Concepts.CoherentSim.ResetDiscard
