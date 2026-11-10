/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.List.FinRange
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.ClusterPatterns.PauliNetwork.DeferredPauliNetwork
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ParityMbqc.ParityFrames
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib

def parity (bs : List Bool) : Bool := bs.foldl Bool.xor false
def bxor {n : ℕ} (x y : Reg n) : Reg n := fun i=>x i ^^ y i
noncomputable def frame {n : ℕ} (x z : Reg n) : Matrix (Reg n) (Reg n) ℂ :=
  Qatlib.Concepts.ClusterPatterns.PauliNetwork.pauliFrameGateB (n:=n) (x,z)

def collect {n : ℕ} (xs : List (Reg n)) : Reg n := fun i=>parity (xs.map fun x=>x i)

structure Flow (n : ℕ) where
 edge : Fin n→Fin n→Bool
 input : Finset (Fin n)
 output : Finset (Fin n)
 f : Fin n→Fin n
 rank : Fin n→ℕ
 valid : ∀ u, u∉output → f u∉input ∧ edge u (f u)=true ∧ rank u < rank (f u) ∧
   ∀ v, edge (f u) v=true → v=u ∨ rank u < rank v

def xCorrection {n : ℕ} (F : Flow n) (s : Reg n) (v : Fin n) : Bool :=
  parity ((List.finRange n).filterMap fun u=>if u∉F.output ∧ F.f u=v then some (s u) else none)
def zCorrection {n : ℕ} (F : Flow n) (s : Reg n) (v : Fin n) : Bool :=
  parity ((List.finRange n).filterMap fun u=>if u∉F.output ∧ u≠v ∧ F.edge (F.f u) v=true then some (s u) else none)

def join {m o : ℕ} (r : Reg m) (z : Reg o) : Reg (m+o) := fun i=>
  if hi : i.val < m then r ⟨i.val,hi⟩ else z ⟨i.val-m,by omega⟩
noncomputable def bra (θ : ℝ) (s b : Bool) : ℂ :=
  if b then (if s then -1 else 1)*Complex.exp (-(θ:ℂ)*Complex.I)/(Real.sqrt 2:ℂ) else 1/(Real.sqrt 2:ℂ)
noncomputable def branch {m o : ℕ} (ψ : QState (Reg (m+o))) (θ : Fin m→ℝ) (s : Reg m) : QState (Reg o) :=
  fun z=>∑ r : Reg m, (∏ i, bra (θ i) (s i) (r i))*ψ (join r z)

end Qatlib.Concepts.ParityMbqc.ParityFrames
