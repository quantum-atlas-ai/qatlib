/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallLawsAqua
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetProbability
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.RealMass
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount
open scoped ENNReal BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def partialState (A : Finset I) (j r : ℕ) : QState (I × Bool) :=
  Run (BitOracleOn fun x => decide (x ∈ A))
    (queryPrefix (LiftCircuit (SearchCircuit I j)) r) (WithMinus (Uniform I))

noncomputable def partialObsMass (A : Finset I) (j r : ℕ) (i : I) : ℝ :=
  MeasureProb (partialState A j r) ({i} ×ˢ (Finset.univ : Finset Bool))

theorem partialObsMass_nonneg (A : Finset I) (j r : ℕ) (i : I) :
    0 ≤ partialObsMass A j r i := by
  unfold partialObsMass MeasureProb
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)

theorem partialState_normalized (hN : 0 < Fintype.card I) (A : Finset I) (j r : ℕ) :
    Normalized (partialState A j r) := by
  have hO : (BitOracleOn fun x : I => decide (x ∈ A)) ∈
      Matrix.unitaryGroup (I × Bool) ℂ := bitOracleOn_unitary _
  have hunit : IsUnitaryCircuit (LiftCircuit (SearchCircuit I j)) :=
    (Qatlib.Concepts.SearchStopping.KnownCount.isUnitaryCircuit_groverCircuit hN j).lift
  have hψ : Normalized ((WithMinus (Uniform I) : QState (I × Bool))) :=
    normalized_tensorState (normalized_uniform hN) normalized_minus
  exact normalized_run (BitOracleOn fun x : I => decide (x ∈ A)) hO
    (queryPrefix (LiftCircuit (SearchCircuit I j)) r)
    (queryPrefix_unitary (LiftCircuit (SearchCircuit I j)) r hunit) hψ

theorem partialObsMass_sum_one (hN : 0 < Fintype.card I) (A : Finset I) (j r : ℕ) :
    HasSum (partialObsMass A j r) 1 := by
  have hnorm : Normalized (partialState A j r) := partialState_normalized hN A j r
  have hone : HasSum (partialObsMass A j r) (∑ i : I, partialObsMass A j r i) :=
    hasSum_fintype _
  have heq : (∑ i : I, partialObsMass A j r i) = 1 := by
    have hsplit : ∀ i : I, partialObsMass A j r i =
        ∑ b : Bool, BornProb (partialState A j r) (i, b) := by
      intro i
      unfold partialObsMass MeasureProb
      rw [Finset.sum_product]
      simp
    calc (∑ i : I, partialObsMass A j r i)
        = ∑ i : I, ∑ b : Bool, BornProb (partialState A j r) (i, b) :=
          Finset.sum_congr rfl fun i _ => hsplit i
      _ = ∑ x : I × Bool, BornProb (partialState A j r) x :=
          (Fintype.sum_prod_type _).symm
      _ = MeasureProb (partialState A j r) Finset.univ := rfl
      _ = 1 := measureProb_univ hnorm
  rwa [heq] at hone

noncomputable def partialObsPMF (hN : 0 < Fintype.card I) (A : Finset I) (j r : ℕ) :
    PMF I :=
  pmfOfRealMass (partialObsMass A j r) (partialObsMass_nonneg A j r)
    (partialObsMass_sum_one hN A j r)

@[simp] theorem partialObsPMF_toReal (hN : 0 < Fintype.card I) (A : Finset I) (j r : ℕ)
    (i : I) : (partialObsPMF hN A j r i).toReal = partialObsMass A j r i :=
  pmfOfRealMass_toReal _ _ _ _

noncomputable def interruptedBudgetEval (A : Finset I) (sizes : ℕ → ℕ)
    (stage budget : ℕ) (onObserved : I → ℕ → ℝ) : ℝ :=
  ∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x *
    (if _hc : x.1.val + 1 ≤ budget then
      match x.2 with
      | some i => onObserved i (budget - (x.1.val + 1))
      | none => interruptedBudgetEval A sizes (stage + 1) (budget - (x.1.val + 1)) onObserved
    else
      (∑ i : I, partialObsMass A x.1.val budget i * onObserved i 0))
termination_by budget

noncomputable def interruptedBudgetPMF (hN : 0 < Fintype.card I) (A : Finset I)
    (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) :
    PMF (I × ℕ) :=
  (iterationPMF (sizes stage) (hsizes stage)).bind fun jj =>
    if _hc : jj.val + 1 ≤ budget then
      (checkedOutcomePMF hN A jj.val).bind fun o =>
        match o with
        | some i => PMF.pure (i, budget - (jj.val + 1))
        | none => interruptedBudgetPMF hN A sizes hsizes (stage + 1) (budget - (jj.val + 1))
    else
      (partialObsPMF hN A jj.val budget).bind fun i => PMF.pure (i, 0)
termination_by budget
decreasing_by
  all_goals simp_wf
  omega

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
