/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuit

/-!
# Statistics preserved by instrument circuit compilation

This module proves that the Kraus refinement compilation of `InstrumentCircuit` preserves linear
terminal statistics after restoring the original outcome records. The branchwise sums reflect
the operator-sum description of quantum instruments in [Watrous2018].

The general transport identity specializes to event masses and unconditional expected query
counts.

## Main statements

* `instrumentCircuit_compile_statistic`: compilation preserves every linear terminal payoff
  after record restoration.
* `instrumentCircuit_compile_event`: compilation preserves event masses.
* `instrumentCircuit_compile_expected`: compilation preserves the expected number of queries.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.Execution.CircuitCompile

open Matrix

/-- Kraus compilation preserves every linear terminal payoff after restoring the original
instrument outcome records. -/
theorem instrumentCircuit_compile_statistic {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) (F : InstrumentPayoff d) :
    ((variableKrausMixedTraces O (compileInstrumentCircuit P) rho).map fun t =>
      F t.accepted t.queries t.gates t.measurements
        (restoreInstrumentRecord P t.outcomes) t.state).sum =
    ((instrumentCircuitMixedTraces O P rho).map fun t =>
      F t.accepted t.queries t.gates t.measurements t.outcomes t.state).sum := by
  classical
  rw [instrumentCircuit_statistic_fold]
  induction P generalizing rho F with
  | halt b =>
      simp [compileInstrumentCircuit, variableKrausMixedTraces, restoreInstrumentRecord,
        instrumentCircuitFold]
  | step action P ih =>
      cases action with
      | gate G =>
          simpa only [compileInstrumentCircuit, variableKrausMixedTraces,
            restoreInstrumentRecord, List.map_map, Function.comp_def,
            instrumentCircuitFold, LinearMap.comp_apply] using
              ih (conjBranch G rho) (fun b q g m rec => F b q (g+1) m rec)
      | query =>
          simpa only [compileInstrumentCircuit, variableKrausMixedTraces,
            restoreInstrumentRecord, List.map_map, Function.comp_def,
            instrumentCircuitFold, LinearMap.comp_apply] using
              ih (conjBranch O rho) (fun b q g m rec => F b (q+1) g m rec)
  | instrument s I next ih =>
      simp only [compileInstrumentCircuit, variableKrausMixedTraces,
        List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
        List.map_map, Function.comp_def, restoreInstrumentRecord, Fin.isLt, dif_pos,
        instrumentCircuitFold, LinearMap.sum_apply, LinearMap.comp_apply]
      let T : Fin s → (Operator d →ₗ[ℂ] ℂ) := fun o =>
        instrumentCircuitFold O (next o)
          (fun b q g m rec => F b q (g+2) (m+1) ((s,o.val)::rec))
      calc
        _ = ∑ a : Fin (s * (d*d)),
            T (instrumentFineEquiv d s a).1
              (conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (instrumentFineEquiv d s a)) rho) := by
          apply Finset.sum_congr rfl
          intro a _
          exact ih (instrumentFineEquiv d s a).1
            (conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (instrumentFineEquiv d s a)) rho)
            (fun b q g m rec => F b q (g+2) (m+1)
              ((s,(instrumentFineEquiv d s a).1.val)::rec))
        _ = ∑ o : Fin s, T o (I.branch o rho) := by
          rw [(instrumentFineEquiv d s).sum_comp
            (fun a => T a.1 (conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a) rho)), Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro o _
          change (∑ k : Fin d × Fin d,
            T o (conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k)) rho)) = T o (I.branch o rho)
          rw [← map_sum]
          congr 1
          exact ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_apply_eq_kraus I) o rho).symm

/-- The real part of a finite list sum of complex numbers is the sum of their real parts. -/
private theorem re_list_sum (xs : List ℂ) :
    xs.sum.re = (xs.map Complex.re).sum :=
  map_list_sum Complex.reAddGroupHom xs

/-- Kraus compilation preserves event masses when the event is evaluated on restored instrument
outcome records. -/
theorem instrumentCircuit_compile_event {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d)
    (E : Bool → List (ℕ × ℕ) → Bool) :
    variableKrausEventMass O (compileInstrumentCircuit P) rho
      (fun b rec => E b (restoreInstrumentRecord P rec)) =
    instrumentCircuitEventMass O P rho E := by
  let F : InstrumentPayoff d := fun b _ _ _ rec =>
    if E b rec then Matrix.traceLinearMap (Fin d) ℂ ℂ else 0
  have hF (b : Bool) (q g m : ℕ) (rec : List (ℕ × ℕ)) (A : Operator d) :
      (F b q g m rec A).re = if E b rec then (Matrix.trace A).re else 0 := by
    dsimp [F]
    split_ifs <;> rfl
  have h := congrArg Complex.re (instrumentCircuit_compile_statistic O P rho F)
  simp only [re_list_sum, List.map_map, Function.comp_def, hF] at h
  simpa only [variableKrausEventMass, instrumentCircuitEventMass, mixedMass] using h

/-- Kraus compilation preserves the mixed-mass-weighted expected query count. -/
theorem instrumentCircuit_compile_expected {d : ℕ} (O : Operator d)
    (P : InstrumentCircuit d) (rho : Operator d) :
    variableKrausExpectedQueries O (compileInstrumentCircuit P) rho =
      instrumentCircuitExpectedQueries O P rho := by
  let F : InstrumentPayoff d := fun _ q _ _ _ =>
    (q : ℂ) • Matrix.traceLinearMap (Fin d) ℂ ℂ
  have h := congrArg Complex.re (instrumentCircuit_compile_statistic O P rho F)
  simpa [re_list_sum, List.map_map, Function.comp_def, F, Complex.mul_re, mul_comm,
    variableKrausExpectedQueries, instrumentCircuitExpectedQueries, mixedMass] using h

end Qatlib.Concepts.Execution.CircuitCompile
