/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.FinRange
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.ClusterPatterns.PauliNetwork.DeferredPauliNetwork

/-!
# Parity frames and measurement-branch definitions

This module defines Boolean parity operations, the Pauli operator `frame`, ranked graph data in
`Flow`, and the outcome parities `xCorrection` and `zCorrection`. It also defines `join`, the
equatorial measurement coefficient `bra`, and the unnormalized output amplitudes `branch`. The
flow and measurement-calculus setting is described in [DanosKashefi2006] and
[DanosKashefiPanangaden2007].

## Main statements

* `parity`, `bxor`, and `collect` combine Boolean correction data.
* `Flow` records input and output sets, a successor map, and rank conditions for correction
  dependencies.
* `xCorrection` and `zCorrection` collect the designated outcome parities.
* `branch` contracts the measured register against the product of the coefficients `bra`.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
* [Danos, Kashefi, and Panangaden, 2007][DanosKashefiPanangaden2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ParityMbqc.ParityFrames
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib

/-- Computes the XOR of a Boolean list by folding from false, so the empty list has false
parity. -/
def parity (bs : List Bool) : Bool := bs.foldl Bool.xor false
/-- Takes the coordinatewise XOR of two Boolean registers. -/
def bxor {n : ℕ} (x y : Reg n) : Reg n := fun i=>x i ^^ y i
/-- Defines the Boolean-register Pauli frame operator with X label `x` and Z label `z` using
`pauliFrameGateB`. -/
noncomputable def frame {n : ℕ} (x z : Reg n) : Matrix (Reg n) (Reg n) ℂ :=
  Qatlib.Concepts.ClusterPatterns.PauliNetwork.pauliFrameGateB (n:=n) (x,z)

/-- Combines a list of Boolean registers by taking the parity of their values at each
coordinate. -/
def collect {n : ℕ} (xs : List (Reg n)) : Reg n := fun i=>parity (xs.map fun x=>x i)

/-- Records Boolean edge data, input and output vertex sets, a successor map, and a rank
function. For each non-output vertex, the validity field imposes successor adjacency,
exclusion from the input set, and the stated strict rank conditions. -/
structure Flow (n : ℕ) where
 edge : Fin n→Fin n→Bool
 input : Finset (Fin n)
 output : Finset (Fin n)
 f : Fin n→Fin n
 rank : Fin n→ℕ
 valid : ∀ u, u∉output → f u∉input ∧ edge u (f u)=true ∧ rank u < rank (f u) ∧
   ∀ v, edge (f u) v=true → v=u ∨ rank u < rank v

/-- Computes the parity of outcomes at non-output vertices whose flow successor is `v`. -/
def xCorrection {n : ℕ} (F : Flow n) (s : Reg n) (v : Fin n) : Bool :=
  parity ((List.finRange n).filterMap fun u=>if u∉F.output ∧ F.f u=v then some (s u) else none)
/-- Computes the parity of outcomes at non-output vertices `u` distinct from `v` whose flow
successor has a directed edge to `v`. -/
def zCorrection {n : ℕ} (F : Flow n) (s : Reg n) (v : Fin n) : Bool :=
  parity ((List.finRange n).filterMap fun u=>if u∉F.output ∧ u≠v ∧ F.edge (F.f u) v=true then some (s u) else none)

/-- Concatenates a Boolean register of size `m` with one of size `o`, placing the first register
in the initial coordinates. -/
def join {m o : ℕ} (r : Reg m) (z : Reg o) : Reg (m+o) := fun i=>
  if hi : i.val < m then r ⟨i.val,hi⟩ else z ⟨i.val-m,by omega⟩
/-- Defines the equatorial measurement-bra coefficient with angle `θ`, outcome `s`, and
computational input bit `b`. The true input bit contributes the phase `exp (-θ * I)` and the
outcome sign, with normalization by `sqrt 2`. -/
noncomputable def bra (θ : ℝ) (s b : Bool) : ℂ :=
  if b then (if s then -1 else 1)*Complex.exp (-(θ:ℂ)*Complex.I)/(Real.sqrt 2:ℂ) else 1/(Real.sqrt 2:ℂ)
/-- Contracts the measured `m`-qubit register of `ψ` with the product measurement bra for
outcome register `s`. The result is an unnormalized amplitude function on the remaining `o`
qubits. -/
noncomputable def branch {m o : ℕ} (ψ : QState (Reg (m+o))) (θ : Fin m→ℝ) (s : Reg m) : QState (Reg o) :=
  fun z=>∑ r : Reg m, (∏ i, bra (θ i) (s i) (r i))*ψ (join r z)

end Qatlib.Concepts.ParityMbqc.ParityFrames
