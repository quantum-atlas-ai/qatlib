/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.KrausRefinement
import Qatlib.Concepts.Execution.CircuitCompile.VariableKrausDefs

/-!
# Circuits with finite quantum instruments

`InstrumentCircuit` describes finite adaptive circuits with known gates, oracle queries, and
finite quantum instruments. Its mixed branch semantics records terminal operators, acceptance
flags, outcomes, and resource counts, using the instrument formalism of [Watrous2018].

`compileInstrumentCircuit` replaces instrument outcomes by individual Kraus outcomes, and
`restoreInstrumentRecord` recovers the original outcome record. `instrumentCircuitFold`
expresses linear terminal statistics recursively.

## Main statements

* `compileInstrumentCircuit_wellFormed`: Kraus refinement preserves circuit well-formedness.
* `instrumentCircuit_statistic_fold`: the recursive fold equals the sum of terminal trace
  statistics.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.Execution.CircuitCompile

open Matrix

/-- A finite adaptive circuit with Boolean halting outcomes, gate or query steps, and nodes
carrying finite quantum instruments. -/
inductive InstrumentCircuit (d : ℕ) where
  | halt (accepted : Bool)
  | step (action : Step (Fin d)) (next : InstrumentCircuit d)
  | instrument (s : ℕ) (I : Instrument (Fin s) d d)
      (next : Fin s → InstrumentCircuit d)

/-- Requires every known gate to be unitary and every continuation of an instrument node to be
well-formed. -/
def instrumentCircuitWellFormed {d : ℕ} : InstrumentCircuit d → Prop
  | .halt _ => True
  | .step (.gate G) P => G ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ instrumentCircuitWellFormed P
  | .step .query P => instrumentCircuitWellFormed P
  | .instrument _ _ next => ∀ o, instrumentCircuitWellFormed (next o)

/-- Enumerates terminal mixed branch traces, including unnormalized operators, outcomes, and
resource counts. Each instrument node contributes two gates and one measurement to each
descendant trace. -/
noncomputable def instrumentCircuitMixedTraces {d : ℕ} (O : Operator d) :
    InstrumentCircuit d → Operator d → List (MixedBranchTrace d)
  | .halt b, rho => [⟨rho, b, 0, 0, 0, []⟩]
  | .step (.gate G) P, rho =>
      (instrumentCircuitMixedTraces O P (conjBranch G rho)).map fun t =>
        {t with gates := t.gates + 1}
  | .step .query P, rho =>
      (instrumentCircuitMixedTraces O P (conjBranch O rho)).map fun t =>
        {t with queries := t.queries + 1}
  | .instrument s I next, rho =>
      (List.ofFn fun o : Fin s =>
        (instrumentCircuitMixedTraces O (next o) (I.branch o rho)).map fun t =>
          {t with gates := t.gates + 2, measurements := t.measurements + 1, outcomes := (s, o.val) :: t.outcomes}).flatten

/-- The sum of mixed branch masses whose acceptance flags and outcome records satisfy `event`. -/
noncomputable def instrumentCircuitEventMass {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d)
    (event : Bool → List (ℕ × ℕ) → Bool) : ℝ :=
  ((instrumentCircuitMixedTraces O P rho).map fun t =>
    if event t.accepted t.outcomes then mixedMass t else 0).sum

/-- The sum of terminal query counts weighted by their mixed branch masses. -/
noncomputable def instrumentCircuitExpectedQueries {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) : ℝ :=
  ((instrumentCircuitMixedTraces O P rho).map fun t => mixedMass t * t.queries).sum

/-- Identifies a flat Kraus outcome index with an original instrument outcome and a pair of
matrix indices. -/
def instrumentFineEquiv (d s : ℕ) :
    Fin (s * (d * d)) ≃ Fin s × (Fin d × Fin d) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin s)) finProdFinEquiv.symm)

/-- Replaces each instrument node by its chosen Kraus refinement, retaining the continuation
selected by the original outcome. -/
noncomputable def compileInstrumentCircuit {d : ℕ} :
    InstrumentCircuit d → VariableKrausCircuit d
  | .halt b => .halt b
  | .step action P => .step action (compileInstrumentCircuit P)
  | .instrument s I next =>
      .instrument (s * (d * d))
        (fun a => (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (instrumentFineEquiv d s a))
        (fun a => compileInstrumentCircuit (next (instrumentFineEquiv d s a).1))

/-- Recovers the original instrument outcome record from the fine Kraus indices along a compiled
execution. -/
def restoreInstrumentRecord {d : ℕ} :
    InstrumentCircuit d → List (ℕ × ℕ) → List (ℕ × ℕ)
  | .halt _, record => record
  | .step _ next, record => restoreInstrumentRecord next record
  | .instrument _ _ _, [] => []
  | .instrument s _ next, (_, a) :: rest =>
      if h : a < s * (d * d) then
        let o := (instrumentFineEquiv d s ⟨a, h⟩).1
        (s, o.val) :: restoreInstrumentRecord (next o) rest
      else []

/-- Compiling a well-formed instrument circuit produces a well-formed variable-outcome Kraus
circuit. -/
theorem compileInstrumentCircuit_wellFormed {d : ℕ} (P : InstrumentCircuit d)
    (hP : instrumentCircuitWellFormed P) :
    variableKrausWellFormed (compileInstrumentCircuit P) := by
  induction P with
  | halt b => trivial
  | step action P ih =>
      cases action with
      | gate G => exact ⟨hP.1, ih hP.2⟩
      | query => exact ih hP
  | instrument s I next ih =>
      constructor
      · exact ((instrumentFineEquiv d s).sum_comp
          (fun a => ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a).conjTranspose * (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a)).trans
            (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I)
      · intro a
        exact ih (instrumentFineEquiv d s a).1 (hP _)

/-- A complex linear functional of the terminal operator, indexed by acceptance, query, gate and
measurement counts, and the outcome record. -/
abbrev InstrumentPayoff (d : ℕ) :=
  Bool → ℕ → ℕ → ℕ → List (ℕ × ℕ) → (Operator d →ₗ[ℂ] ℂ)

/-- Recursively evaluates a terminal linear payoff by composing with branch maps and summing
over instrument outcomes. -/
noncomputable def instrumentCircuitFold {d : ℕ} (O : Operator d) :
    InstrumentCircuit d → InstrumentPayoff d → (Operator d →ₗ[ℂ] ℂ)
  | .halt b, F => F b 0 0 0 []
  | .step (.gate G) P, F =>
      (instrumentCircuitFold O P (fun b q g m rec => F b q (g+1) m rec)).comp
        (conjBranch G)
  | .step .query P, F =>
      (instrumentCircuitFold O P (fun b q g m rec => F b (q+1) g m rec)).comp
        (conjBranch O)
  | .instrument s I next, F =>
      ∑ o : Fin s,
        (instrumentCircuitFold O (next o)
          (fun b q g m rec => F b q (g+2) (m+1) ((s,o.val)::rec))).comp (I.branch o)

/-- The sum of a linear payoff over terminal mixed branch traces equals its recursively
evaluated circuit fold. -/
theorem instrumentCircuit_statistic_fold {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (F : InstrumentPayoff d) :
    ((instrumentCircuitMixedTraces O P rho).map fun t =>
      F t.accepted t.queries t.gates t.measurements t.outcomes t.state).sum =
      instrumentCircuitFold O P F rho := by
  induction P generalizing rho F with
  | halt b => simp [instrumentCircuitMixedTraces, instrumentCircuitFold]
  | step action P ih =>
      cases action with
      | gate G =>
          simpa only [instrumentCircuitMixedTraces, instrumentCircuitFold,
            List.map_map, Function.comp_def, LinearMap.comp_apply] using
              ih (conjBranch G rho) (fun b q g m rec => F b q (g+1) m rec)
      | query =>
          simpa only [instrumentCircuitMixedTraces, instrumentCircuitFold,
            List.map_map, Function.comp_def, LinearMap.comp_apply] using
              ih (conjBranch O rho) (fun b q g m rec => F b (q+1) g m rec)
  | instrument s I next ih =>
      simp only [instrumentCircuitMixedTraces, instrumentCircuitFold,
        List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
        List.map_map, Function.comp_def, LinearMap.sum_apply, LinearMap.comp_apply]
      apply Finset.sum_congr rfl
      intro o _
      exact ih o (I.branch o rho)
        (fun b q g m rec => F b q (g+2) (m+1) ((s,o.val)::rec))

end Qatlib.Concepts.Execution.CircuitCompile
