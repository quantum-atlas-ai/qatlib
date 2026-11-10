/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchQueryCost
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.RealMass
import Mathlib.Probability.Distributions.Uniform
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib
open scoped ENNReal BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def checkedOutcomePMF (hN : 0 < Fintype.card I) (A : Finset I) (j : ℕ) :
    PMF (Option I) :=
  pmfOfRealMass (fun o => match o with
    | none => CheckedRejectMass A j
    | some i => CheckedOutputMass A j i)
    (fun o => by
      cases o with
      | none => exact (search_checked_attempt hN A j).2.2.2.2.2
      | some i => exact (search_checked_attempt hN A j).2.2.2.2.1 i)
    (by
      convert hasSum_fintype (fun o : Option I => match o with
        | none => CheckedRejectMass A j
        | some i => CheckedOutputMass A j i) using 1
      rw [Fintype.sum_option]
      linarith [(search_checked_attempt hN A j).2.2.2.1])

@[simp] theorem checkedOutcomePMF_toReal (hN : 0 < Fintype.card I) (A : Finset I)
    (j : ℕ) (o : Option I) :
    (checkedOutcomePMF hN A j o).toReal = (match o with
      | none => CheckedRejectMass A j
      | some i => CheckedOutputMass A j i) := by
  exact pmfOfRealMass_toReal _ _ _ o

noncomputable def iterationPMF (m : ℕ) (hm : 0 < m) : PMF (Fin m) := by
  letI : NeZero m := ⟨hm.ne'⟩
  exact PMF.uniformOfFintype' (Fin m)

@[simp] theorem iterationPMF_toReal (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (iterationPMF m hm j).toReal = 1 / (m : ℝ) := by
  simp [iterationPMF, PMF.uniformOfFintype'_apply, one_div]

theorem search_attempt_factor (hN : 0 < Fintype.card I) (A : Finset I)
    (m : ℕ) (hm : 0 < m) (j : Fin m) (o : Option I) :
    (iterationPMF m hm j).toReal * (checkedOutcomePMF hN A j.val o).toReal =
      AttemptMass A m (j, o) := by
  rw [iterationPMF_toReal, checkedOutcomePMF_toReal]
  cases o <;> simp [AttemptMass, div_eq_mul_inv, mul_comm]

noncomputable def attemptPMF (hN : 0 < Fintype.card I) (A : Finset I)
    (m : ℕ) (hm : 0 < m) : PMF (Fin m × Option I) :=
  pmfOfRealMass (AttemptMass A m) (search_joint_attempt_law hN A m hm).1
    (by simpa only [(search_joint_attempt_law hN A m hm).2.1] using
      hasSum_fintype (AttemptMass A m))

@[simp] theorem attemptPMF_apply (hN : 0 < Fintype.card I) (A : Finset I)
    (m : ℕ) (hm : 0 < m) (x : Fin m × Option I) :
    attemptPMF hN A m hm x = ENNReal.ofReal (AttemptMass A m x) := rfl

noncomputable def attemptCostedLaw (hN : 0 < Fintype.card I) (A : Finset I)
    (m : ℕ) (hm : 0 < m) : CostedLaw (Option I) :=
  (attemptPMF hN A m hm).map (fun x => (x.2, x.1.val + 1))

theorem attemptCostedLaw_query_count (hN : 0 < Fintype.card I) (A : Finset I)
    (m : ℕ) (hm : 0 < m) :
    attemptCostedLaw hN A m hm = (attemptPMF hN A m hm).map (fun x =>
      (x.2, QueryCount (LiftCircuit (SearchCircuit I x.1.val)) +
        QueryCount ([Step.query] : Circuit (I × Bool)))) := by
  unfold attemptCostedLaw
  congr 1
  funext x
  rw [(search_checked_attempt hN A x.1.val).1]

noncomputable def terminalPMF (A : Finset I) (hA : 0 < A.card) :
    PMF (TerminalTrace I (ExponentialSizes (Fintype.card I))) :=
  pmfOfRealMass (TerminalMass A (ExponentialSizes (Fintype.card I)))
    (fun x => ((search_terminal_law_nonempty A hA).2 x).1)
    (search_terminal_law_nonempty A hA).1

@[simp] theorem terminalPMF_apply (A : Finset I) (hA : 0 < A.card)
    (x : TerminalTrace I (ExponentialSizes (Fintype.card I))) :
    terminalPMF A hA x = ENNReal.ofReal
      (TerminalMass A (ExponentialSizes (Fintype.card I)) x) := rfl

noncomputable def terminalCostedLaw (A : Finset I) (hA : 0 < A.card) : CostedLaw I :=
  Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.ofRealMass (TerminalMass A (ExponentialSizes (Fintype.card I)))
    (fun x => ((search_terminal_law_nonempty A hA).2 x).1)
    (search_terminal_law_nonempty A hA).1 TerminalOutput
    (TerminalBooleanQueries (ExponentialSizes (Fintype.card I)))

theorem terminalCostedLaw_event (A : Finset I) (hA : 0 < A.card) (E : I × ℕ → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (terminalCostedLaw A hA) E = ENNReal.ofReal
      (∑' x : TerminalTrace I (ExponentialSizes (Fintype.card I)),
        if E (TerminalOutput x, TerminalBooleanQueries (ExponentialSizes (Fintype.card I)) x)
        then TerminalMass A (ExponentialSizes (Fintype.card I)) x else 0) :=
  Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.ofRealMass_event _ _ _ _ _ E

theorem terminalCostedLaw_expectedCost (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        (TerminalBooleanQueries (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (terminalCostedLaw A hA) = ENNReal.ofReal q ∧
      0 ≤ q ∧ q ≤ (29/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  obtain ⟨q, hq, hq0, hqb⟩ := search_terminal_boolean_cost A hA
  exact ⟨q, hq,
      Qatlib.Concepts.AmplitudeSearch.InterruptMin.CostedLaw.ofRealMass_expectedCost _ _ _ _ _ q hq, hq0, hqb⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
