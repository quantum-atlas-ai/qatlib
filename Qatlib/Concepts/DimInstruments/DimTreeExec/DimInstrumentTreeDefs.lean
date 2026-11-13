/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# Adaptive instrument programs with changing dimensions

`Program` describes finite adaptive compositions of quantum instruments, allowing different
intermediate dimensions. `leaves` enumerates composite branch maps with their records, while
`forget` sums those maps. The construction uses the finite-dimensional channel and instrument
framework of [Watrous2018].

`eventMap`, `eventMass`, and `conditional` describe conditioning on Boolean predicates of actual
records. `weightedConditionals` sums the normalized positive-mass leaf outputs with their
original masses.

## Main statements

* `Program`: finite instrument trees with terminal channels.
* `thenChannel`: channel postcomposition at every terminal branch.
* `conditional`: normalization available precisely for positive event mass.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.DimInstruments.DimTreeExec
open Matrix
open scoped BigOperators ComplexOrder

/-- Finite adaptive instrument programs with specified input and output dimensions and possibly
different intermediate dimensions. -/
inductive Program : ℕ → ℕ → Type where
  | halt {D E : ℕ} (channel : QuantumChannel D E) : Program D E
  | measure {D M E s : ℕ} (instrument : Instrument (Fin s) D M)
      (next : Fin s → Program M E) : Program D E

/-- An execution leaf with its composite linear map, outcome record, and number of measurements. -/
structure Leaf (D E : ℕ) where
  map : Operator D →ₗ[ℂ] Operator E
  record : List (ℕ × ℕ)
  measurements : ℕ

/-- Enumerates execution leaves by composing instrument branches along each path and recording
outcome arities and indices. -/
def leaves {D E : ℕ} : Program D E → List (Leaf D E)
  | .halt T => [⟨T.map, [], 0⟩]
  | .measure (s := s) I next =>
      (List.ofFn fun o : Fin s => (leaves (next o)).map fun t =>
        ⟨t.map.comp (I.branch o), (s,o.val) :: t.record, t.measurements+1⟩).flatten

/-- The sum of all leaf maps, forgetting the measurement record. -/
def forget {D E : ℕ} (P : Program D E) : Operator D →ₗ[ℂ] Operator E :=
  ((leaves P).map Leaf.map).sum

/-- Appends a quantum channel to every terminal branch of an instrument program. -/
def thenChannel {D E F : ℕ} : Program D E → (QuantumChannel E F) → Program D F
  | .halt T, S => .halt (S.comp T)
  | .measure I next, S => .measure I (fun o => thenChannel (next o) S)

/-- The sum of leaf maps whose records satisfy the specified Boolean event. -/
def eventMap {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool) :
    Operator D →ₗ[ℂ] Operator E :=
  (((leaves P).filter (fun t => event t.record)).map Leaf.map).sum

/-- The real part of the trace of the event output on the given input operator. -/
def eventMass {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    (rho : Operator D) : ℝ := (trace (eventMap P event rho)).re

/-- The event output normalized by its mass when that mass is positive, and `none` otherwise. -/
def conditional {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    (rho : Operator D) : Option (Operator E) :=
  if 0 < eventMass P event rho then
    some (((eventMass P event rho : ℝ) : ℂ)⁻¹ • eventMap P event rho)
  else none

/-- The sum of event-selected positive-mass leaf outputs, each normalized and then weighted by
its original mass. -/
def weightedConditionals {D E : ℕ} (P : Program D E)
    (event : List (ℕ × ℕ) → Bool) (rho : Operator D) : Operator E :=
  (((leaves P).filter (fun t => event t.record)).map fun t =>
    let p := (trace (t.map rho)).re
    if 0 < p then ((p : ℝ) : ℂ) • (((p : ℝ) : ℂ)⁻¹ • t.map rho) else 0).sum

end Qatlib.Concepts.DimInstruments.DimTreeExec
