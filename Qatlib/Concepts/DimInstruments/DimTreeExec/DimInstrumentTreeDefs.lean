/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.DimInstruments.DimTreeExec
open Matrix
open scoped BigOperators ComplexOrder

inductive Program : ℕ → ℕ → Type where
  | halt {D E : ℕ} (channel : QuantumChannel D E) : Program D E
  | measure {D M E s : ℕ} (instrument : Instrument (Fin s) D M)
      (next : Fin s → Program M E) : Program D E

structure Leaf (D E : ℕ) where
  map : Operator D →ₗ[ℂ] Operator E
  record : List (ℕ × ℕ)
  measurements : ℕ

def leaves {D E : ℕ} : Program D E → List (Leaf D E)
  | .halt T => [⟨T.map, [], 0⟩]
  | .measure (s := s) I next =>
      (List.ofFn fun o : Fin s => (leaves (next o)).map fun t =>
        ⟨t.map.comp (I.branch o), (s,o.val) :: t.record, t.measurements+1⟩).flatten

def forget {D E : ℕ} (P : Program D E) : Operator D →ₗ[ℂ] Operator E :=
  ((leaves P).map Leaf.map).sum

def thenChannel {D E F : ℕ} : Program D E → (QuantumChannel E F) → Program D F
  | .halt T, S => .halt (S.comp T)
  | .measure I next, S => .measure I (fun o => thenChannel (next o) S)

def eventMap {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool) :
    Operator D →ₗ[ℂ] Operator E :=
  (((leaves P).filter (fun t => event t.record)).map Leaf.map).sum

def eventMass {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    (rho : Operator D) : ℝ := (trace (eventMap P event rho)).re

def conditional {D E : ℕ} (P : Program D E) (event : List (ℕ × ℕ) → Bool)
    (rho : Operator D) : Option (Operator E) :=
  if 0 < eventMass P event rho then
    some (((eventMass P event rho : ℝ) : ℂ)⁻¹ • eventMap P event rho)
  else none

def weightedConditionals {D E : ℕ} (P : Program D E)
    (event : List (ℕ × ℕ) → Bool) (rho : Operator D) : Operator E :=
  (((leaves P).filter (fun t => event t.record)).map fun t =>
    let p := (trace (t.map rho)).re
    if 0 < p then ((p : ℝ) : ℂ) • (((p : ℝ) : ℂ)⁻¹ • t.map rho) else 0).sum

end Qatlib.Concepts.DimInstruments.DimTreeExec
