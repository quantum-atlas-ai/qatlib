/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallLawsAqua
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetProbability
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.RealMass

/-!
# Budgeted search with partial observation

This module defines the query-prefix state `partialState` and its index-observation law
`partialObsPMF`. It then constructs a recursive interrupted search call that observes the
available prefix whenever the next complete attempt exceeds the budget.

The model refines the randomized search attempts of [BoyerEtAl1998] by retaining an observation
at interruption.

## Main statements

* `partialObsPMF`: The probability mass function of the index observed after partial search
  execution.
* `interruptedBudgetPMF`: The interrupted search law on observed indices and remaining budgets,
  assigning remaining budget zero when an attempt is interrupted.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

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

/-- The state obtained by running the query prefix of the lifted `j`-iteration search circuit
with query budget `r`. -/
noncomputable def partialState (A : Finset I) (j r : ℕ) : QState (I × Bool) :=
  Run (BitOracleOn fun x => decide (x ∈ A))
    (queryPrefix (LiftCircuit (SearchCircuit I j)) r) (WithMinus (Uniform I))

/-- The probability of observing index `i` in `partialState`, summing over the Boolean ancilla. -/
noncomputable def partialObsMass (A : Finset I) (j r : ℕ) (i : I) : ℝ :=
  MeasureProb (partialState A j r) ({i} ×ˢ (Finset.univ : Finset Bool))

/-- Each partial index-observation mass is nonnegative. -/
theorem partialObsMass_nonneg (A : Finset I) (j r : ℕ) (i : I) :
    0 ≤ partialObsMass A j r i := by
  unfold partialObsMass MeasureProb
  exact Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)

/-- The partially executed search state is normalized on a nonempty index type. -/
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

/-- The partial index-observation masses sum to one on a nonempty index type. -/
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

/-- The probability mass function of the index observed after partial search execution. -/
noncomputable def partialObsPMF (hN : 0 < Fintype.card I) (A : Finset I) (j r : ℕ) :
    PMF I :=
  pmfOfRealMass (partialObsMass A j r) (partialObsMass_nonneg A j r)
    (partialObsMass_sum_one hN A j r)

/-- The real mass of `partialObsPMF` equals `partialObsMass`. -/
@[simp] theorem partialObsPMF_toReal (hN : 0 < Fintype.card I) (A : Finset I) (j r : ℕ)
    (i : I) : (partialObsPMF hN A j r i).toReal = partialObsMass A j r i :=
  pmfOfRealMass_toReal _ _ _ _

/-- The recursive payoff evaluator that retries completed failures and observes a partial search
state when an attempt does not fit the budget. -/
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

/-- The interrupted search law on observed indices and remaining budgets, assigning remaining
budget zero when an attempt is interrupted. -/
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
