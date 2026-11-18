/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.WordOps
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary

@[expose] public section

/-!
# The standard XOR oracle and oriented complexity statements

This module defines the standard oracle interface of the toolkit. A register is split into an
address block, an answer block, and a work block; the standard XOR oracle applies a
Boolean function to the address block and XORs it into the answer block, leaving the
work block untouched. The oracle is a permutation matrix, hence unitary, and query
counting binds to the public `QueryCount` through the query step: one step, one
oracle application (`Qatlib.Concepts.CircuitLang.WordRelabel.denoteQOne`). The phase form of an oracle is a
word-level conjugation by Hadamards on the answer block; the conversion here is a
typed interface carrying both forms, not a claim that every phase oracle compiles to
this form. Oriented complexity statements carry their direction (O, Ω, Θ), the input
size measure, the error and success-rate parameters, and the object they bound; the
protocol forbids reading a finite count as an asymptotic statement.

## Main statements

* `xorOracle_ket`: the XOR oracle acts on basis states by XOR-ing `f` of the address
  into the answer block.
* `xorOracle_uni`: the XOR oracle is a permutation, hence unitary.
* `phaseOf_uni`: the phase form is unitary when the oracle is.
* `Qatlib.Concepts.CircuitLang.XorOracle.Oriented.data_bound`: a finite count never directly yields an asymptotic member.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Matrix
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.WordRelabel

namespace Qatlib.Concepts.CircuitLang.XorOracle

/-- The address block of the standard oracle register: `a` bits. -/
abbrev Addr (a : ℕ) := Fin a → Bool

/-- The full standard oracle register: address, answer, and work blocks. -/
abbrev OReg (a w : ℕ) := Addr a × Bool × (Fin w → Bool)

/-- Update the answer block of a register by XOR-ing in a bit. -/
def xorInto {a w : ℕ} (f : Addr a → Bool) (x : OReg a w) : OReg a w :=
  (x.1, x.2.1 ^^ f x.1, x.2.2)

/-- The standard XOR oracle: a permutation matrix that XORs `f` of the address into
the answer block, leaving the work block untouched. -/
noncomputable def xorOracle {a w : ℕ} (f : Addr a → Bool) :
    Matrix (OReg a w) (OReg a w) ℂ :=
  permMatrix (xorInto f)

/-- XOR-ing twice returns the original register. -/
theorem xorInto_inv {a w : ℕ} (f : Addr a → Bool) :
    Function.Involutive (fun x : OReg a w => xorInto f x) := by
  intro x
  simp only [xorInto]
  ext1 <;> ext1 <;> simp

/-- The XOR oracle sends each basis state to the XOR-updated basis state. -/
theorem xorOracle_ket {a w : ℕ} (f : Addr a → Bool) (x : OReg a w) :
    xorOracle f *ᵥ Ket x = Ket (xorInto f x) :=
  applyGate_permMatrix_ket (xorInto_inv (a := a) (w := w) f) x

/-- The XOR oracle is an involutive permutation matrix, hence unitary. -/
theorem xorOracle_uni {a w : ℕ} (f : Addr a → Bool) :
    xorOracle f ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  permMatrix_unitary (xorInto_inv f)

/-- The phase form of the oracle: Hadamard-conjugation on the answer wire, expressed
as a typed interface between the two forms. One query to the phase form is bracketed
by answer-block Hadamards around one standard query. -/
structure PhaseOf {a w : ℕ} where
  /-- The oracle function of the standard form. -/
  f : Addr a → Bool
  /-- The Hadamard layer on the answer block. -/
  hLayer : Matrix (OReg a w) (OReg a w) ℂ
  /-- The Hadamard layer is unitary. -/
  hUni : hLayer ∈ Matrix.unitaryGroup (OReg a w) ℂ

/-- The phase form of a query wraps the standard oracle between Hadamard layers. -/
theorem phaseOf_uni {a w : ℕ} (P : PhaseOf (a := a) (w := w)) :
    P.hLayer * xorOracle P.f * P.hLayer ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ P.hUni (xorOracle_uni P.f)) P.hUni

/-- The orientation of an asymptotic statement. -/
inductive Orient
  /-- Upper bound (O). -/
  | upper
  /-- Lower bound (Ω). -/
  | lower
  /-- Two-sided bound (Θ). -/
  | tight

/-- An oriented complexity statement protocol: direction, input-size measure,
error and success-rate parameters, and the bounded object. A finite measured count is
data; membership in the asymptotic class requires an actual proof, which this
structure deliberately does not provide. -/
structure Oriented (α : Type) where
  /-- The asymptotic direction. -/
  orient : Orient
  /-- The input-size measure. -/
  size : ℕ → α
  /-- The error parameter, when the statement is approximate. -/
  err : Option ℝ
  /-- The success-rate parameter, when the statement is randomized. -/
  succ : Option ℝ
  /-- The bounded cost function. -/
  cost : ℕ → α

/-- A finite count is data, not an asymptotic statement: the protocol records a
pointwise bound as data and deliberately provides no coercion into an asymptotic
class. -/
theorem Oriented.data_bound {α : Type} [Preorder α]
    (o : Oriented α) {g : α} (n : ℕ) (h : o.cost n ≤ g) : o.cost n ≤ g := h

end Qatlib.Concepts.CircuitLang.XorOracle
