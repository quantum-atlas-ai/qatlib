/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.Execution.KnownKraus.KnownKrausMeasurement

/-!
# Completing adaptive trace-nonincreasing circuits

`completeFamily` adds the square root of a positive Kraus deficit as a failure operator,
yielding `completedInstrument`. `TniCircuit` describes adaptive circuits with such Kraus
families, and `toInstrument` replaces each family by a complete instrument whose added failure
outcome halts with rejection.

The transport preserves mixed branch traces after outcome relabeling, event masses, and expected
query counts. The Kraus description of quantum operations is standard background [Watrous2018],
with measurement based algorithmic context in [Kitaev1995].

## Main statements

- `completeFamily_complete` proves the completeness identity for the extended Kraus family.
- `toInstrument_traces` identifies compiled traces after applying `restoreTniRecord`.
- `toInstrument_wellFormed` preserves the circuit well-formedness condition.
- `toInstrument_event` and `toInstrument_expected` preserve event mass and expected query count.
- `frontier1` packages well-formedness and the trace transport identity.

## References

- [Watrous, 2018][Watrous2018], *The Theory of Quantum Information*.
- [Kitaev, 1995][Kitaev1995], *Quantum measurements and the Abelian Stabilizer Problem*.
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.Execution.CircuitCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

variable {d s : ℕ}

/-- Defines the Kraus deficit as the identity minus the sum of `K a` adjoint times `K a` over
the family. -/
def deficit (K : Fin s → Operator d) : Operator d :=
  1 - ∑ a, (K a)ᴴ * K a

/-- Extends a Kraus family with a new outcome zero carrying the square root of its deficit, and
places the original operators at successor indices. -/
def completeFamily (K : Fin s → Operator d) : Fin (s+1) → Operator d :=
  Fin.cases (CFC.sqrt (deficit K)) K

/-- The added outcome zero of `completeFamily` is the square root of the Kraus deficit. -/
@[simp] theorem completeFamily_zero (K : Fin s → Operator d) :
    completeFamily K 0 = CFC.sqrt (deficit K) := rfl

/-- Each successor outcome of `completeFamily` is the corresponding operator from the original
Kraus family. -/
@[simp] theorem completeFamily_succ (K : Fin s → Operator d) (a : Fin s) :
    completeFamily K a.succ = K a := rfl

/-- If the Kraus deficit is positive semidefinite, the extended family satisfies the
completeness identity with sum of adjoint products equal to the identity. -/
theorem completeFamily_complete (K : Fin s → Operator d) (hK : (deficit K).PosSemidef) :
    ∑ a, (completeFamily K a)ᴴ * completeFamily K a = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [completeFamily_zero, completeFamily_succ]
  have hs : (CFC.sqrt (deficit K))ᴴ = CFC.sqrt (deficit K) := by
    exact (CFC.sqrt_nonneg (deficit K)).isSelfAdjoint
  rw [hs, CFC.sqrt_mul_sqrt_self (deficit K) (Matrix.nonneg_iff_posSemidef.mpr hK)]
  simp [deficit]

/-- Constructs a complete instrument from a Kraus family with positive semidefinite deficit by
adjoining the deficit square root as a failure operator. -/
def completedInstrument (K : Fin s → Operator d) (hK : (deficit K).PosSemidef) :
    Instrument (Fin (s+1)) d d :=
  Instrument.ofKraus (completeFamily K) (completeFamily_complete K hK)

/-- A successor branch of the completed instrument acts by conjugation with the corresponding
original Kraus operator. -/
@[simp] theorem completedInstrument_success (K : Fin s → Operator d)
    (hK : (deficit K).PosSemidef) (a : Fin s) (rho : Operator d) :
    (completedInstrument K hK).branch a.succ rho = K a * rho * (K a)ᴴ := rfl

/-- The failure branch of the completed instrument acts by conjugation with the square root of
the Kraus deficit. -/
@[simp] theorem completedInstrument_failure (K : Fin s → Operator d)
    (hK : (deficit K).PosSemidef) (rho : Operator d) :
    (completedInstrument K hK).branch 0 rho =
      CFC.sqrt (deficit K) * rho * (CFC.sqrt (deficit K))ᴴ := rfl

/-- Summing the traces of all branches of the completed instrument gives the input trace. -/
theorem completed_trace (K : Fin s → Operator d) (hK : (deficit K).PosSemidef)
    (rho : Operator d) :
    ∑ a, Matrix.trace ((completedInstrument K hK).branch a rho) = Matrix.trace rho := by
  rw [← Matrix.trace_sum]
  exact (completedInstrument K hK).total rho

/-- Describes finite adaptive circuits built from Boolean halts, gate or query steps, and
Kraus-family branches with positive semidefinite deficit and outcome-dependent
continuations. -/
inductive TniCircuit (d : ℕ) where
  | halt (accepted : Bool)
  | step (action : Step (Fin d)) (next : TniCircuit d)
  | instrument (s : ℕ) (K : Fin s → Operator d) (hK : (deficit K).PosSemidef)
      (next : Fin s → TniCircuit d)

/-- Requires every gate in a `TniCircuit` to be unitary and every continuation to be well
formed; query steps impose only the continuation condition. -/
def tniWellFormed : TniCircuit d → Prop
  | .halt _ => True
  | .step (.gate G) P => G ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ tniWellFormed P
  | .step .query P => tniWellFormed P
  | .instrument _ _ _ next => ∀ a, tniWellFormed (next a)

/-- Compiles a `TniCircuit` into an instrument circuit by completing each Kraus family and
sending its added failure outcome to a rejecting halt. -/
def toInstrument : TniCircuit d → InstrumentCircuit d
  | .halt b => .halt b
  | .step action P => .step action (toInstrument P)
  | .instrument s K hK next =>
      .instrument (s+1) (completedInstrument K hK)
        (Fin.cases (.halt false) (fun a => toInstrument (next a)))

/-- Enumerates mixed-state branch traces of a trace-nonincreasing circuit, including rejecting
deficit branches, operation counts, and outcome records. Original outcomes retain their
original arity and index in the records. -/
def tniMixedTraces (O : Operator d) : TniCircuit d → Operator d → List (MixedBranchTrace d)
  | .halt b, rho => [⟨rho, b, 0, 0, 0, []⟩]
  | .step (.gate G) P, rho =>
      (tniMixedTraces O P (conjBranch G rho)).map fun t => {t with gates := t.gates+1}
  | .step .query P, rho =>
      (tniMixedTraces O P (conjBranch O rho)).map fun t => {t with queries := t.queries+1}
  | .instrument s K _ next, rho =>
      (List.ofFn fun a : Fin (s+1) =>
        (Fin.cases (motive := fun _ => List (MixedBranchTrace d))
          [⟨CFC.sqrt (deficit K) * rho * (CFC.sqrt (deficit K))ᴴ, false, 0, 0, 0, []⟩]
          (fun i => tniMixedTraces O (next i) (K i * rho * (K i)ᴴ)) a).map fun t =>
            {t with gates := t.gates+2, measurements := t.measurements+1, outcomes := (Fin.cases (s+1,0) (fun i => (s,i.val)) a) :: t.outcomes}).flatten

/-- Translates compiled instrument outcome records back to the original Kraus arities and
indices, retaining the distinguished failure record and following the corresponding circuit
continuations. -/
def restoreTniRecord : TniCircuit d → List (ℕ × ℕ) → List (ℕ × ℕ)
  | .halt _, rec => rec
  | .step _ next, rec => restoreTniRecord next rec
  | .instrument _ _ _ _, [] => []
  | .instrument s _ _ next, (_, a) :: rest =>
      if _h0 : a = 0 then (s+1,0) :: rest
      else if ha : a-1 < s then (s,a-1) :: restoreTniRecord (next ⟨a-1,ha⟩) rest
      else []

/-- Applying `restoreTniRecord` to the outcome records of the compiled instrument traces yields
exactly `tniMixedTraces` for the original circuit. -/
theorem toInstrument_traces (O : Operator d) (P : TniCircuit d) (rho : Operator d) :
    (instrumentCircuitMixedTraces O (toInstrument P) rho).map
      (fun t => {t with outcomes := restoreTniRecord P t.outcomes}) = tniMixedTraces O P rho := by
  induction P generalizing rho with
  | halt b => rfl
  | step action P ih =>
      cases action with
      | gate G =>
          simpa only [toInstrument, instrumentCircuitMixedTraces, tniMixedTraces, restoreTniRecord,
            List.map_map, Function.comp_def] using
              congrArg (List.map (fun t : MixedBranchTrace d => {t with gates := t.gates+1}))
                (ih (conjBranch G rho))
      | query =>
          simpa only [toInstrument, instrumentCircuitMixedTraces, tniMixedTraces, restoreTniRecord,
            List.map_map, Function.comp_def] using
              congrArg (List.map (fun t : MixedBranchTrace d => {t with queries := t.queries+1}))
                (ih (conjBranch O rho))
  | instrument s K hK next ih =>
      simp only [toInstrument, instrumentCircuitMixedTraces, tniMixedTraces,
        List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext a
      refine Fin.cases ?_ (fun i => ?_) a
      · simp [restoreTniRecord, instrumentCircuitMixedTraces]
      · simpa only [Fin.cases_succ, completedInstrument_success, restoreTniRecord,
          Fin.val_succ, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          not_false_eq_true, dif_neg, Fin.isLt, dif_pos, List.map_map, Function.comp_def] using
            congrArg (List.map (fun t : MixedBranchTrace d =>
              {t with gates := t.gates+2, measurements := t.measurements+1, outcomes := (s,i.val)::t.outcomes}))
              (ih i (K i * rho * (K i)ᴴ))

/-- Compilation by `toInstrument` preserves well-formedness of trace-nonincreasing circuits. -/
theorem toInstrument_wellFormed (P : TniCircuit d) (hP : tniWellFormed P) :
    instrumentCircuitWellFormed (toInstrument P) := by
  induction P with
  | halt b => trivial
  | step action P ih =>
      cases action with
      | gate G => exact ⟨hP.1, ih hP.2⟩
      | query => exact ih hP
  | instrument s K hK next ih =>
      intro a
      refine Fin.cases ?_ (fun i => ?_) a
      · trivial
      · exact ih i (hP i)

/-- Sums the masses of mixed branch traces whose acceptance flag and outcome record satisfy the
given Boolean event. -/
def tniEventMass (O : Operator d) (P : TniCircuit d) (rho : Operator d)
    (E : Bool → List (ℕ × ℕ) → Bool) : ℝ :=
  ((tniMixedTraces O P rho).map fun t => if E t.accepted t.outcomes then mixedMass t else 0).sum

/-- Sums each mixed branch mass multiplied by its query count to define the circuit's expected
query count. -/
def tniExpectedQueries (O : Operator d) (P : TniCircuit d) (rho : Operator d) : ℝ :=
  ((tniMixedTraces O P rho).map fun t => mixedMass t * t.queries).sum

/-- The compiled instrument circuit has the same event mass as the original circuit when the
event is evaluated after restoring the original outcome records. -/
theorem toInstrument_event (O : Operator d) (P : TniCircuit d) (rho : Operator d)
    (E : Bool → List (ℕ × ℕ) → Bool) :
    instrumentCircuitEventMass O (toInstrument P) rho
      (fun b rec => E b (restoreTniRecord P rec)) = tniEventMass O P rho E := by
  have h := congrArg (fun ts : List (MixedBranchTrace d) =>
    (ts.map fun t => if E t.accepted t.outcomes then mixedMass t else 0).sum)
    (toInstrument_traces O P rho)
  simpa only [instrumentCircuitEventMass, tniEventMass, List.map_map, Function.comp_def,
      mixedMass] using h

/-- Compilation to a complete instrument circuit preserves the expected query count. -/
theorem toInstrument_expected (O : Operator d) (P : TniCircuit d) (rho : Operator d) :
    instrumentCircuitExpectedQueries O (toInstrument P) rho = tniExpectedQueries O P rho := by
  have h := congrArg (fun ts : List (MixedBranchTrace d) =>
    (ts.map fun t => mixedMass t * t.queries).sum) (toInstrument_traces O P rho)
  simpa only [instrumentCircuitExpectedQueries, tniExpectedQueries, List.map_map,
      Function.comp_def, mixedMass] using h

/-- Recursively counts the maximum query budget along circuit branches, assigning zero to halts
and failure branches and adding one at each query step. -/
def tniBudget : TniCircuit d → ℕ
  | .halt _ => 0
  | .step (.gate _) P => tniBudget P
  | .step .query P => tniBudget P + 1
  | .instrument s _ _ next =>
      Finset.univ.sup (Fin.cases 0 (fun a : Fin s => tniBudget (next a)))

/-- Packages preservation of circuit well-formedness with the exact mixed-trace identity after
restoring compiled outcome records. -/
theorem frontier1 (P : TniCircuit d) (hP : tniWellFormed P) :
    instrumentCircuitWellFormed (toInstrument P) ∧
      ∀ (O : Operator d) (rho : Operator d),
        (instrumentCircuitMixedTraces O (toInstrument P) rho).map
          (fun t => {t with outcomes := restoreTniRecord P t.outcomes}) = tniMixedTraces O P rho :=
  ⟨toInstrument_wellFormed P hP, fun O rho => toInstrument_traces O P rho⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
