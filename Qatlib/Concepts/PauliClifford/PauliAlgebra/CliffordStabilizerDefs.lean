/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs Matrix

@[ext] structure Row (n : ℕ) where
  x : Reg n
  z : Reg n
  phase : Phase4
  deriving DecidableEq

def letter (x z : Bool) : Pauli1 :=
  match x, z with
  | false, false => .I
  | true, false => .X
  | true, true => .Y
  | false, true => .Z

def Row.decode {n : ℕ} (r : Row n) : PauliElem n :=
  ⟨fun k => letter (r.x k) (r.z k), r.phase⟩

def bitX : Pauli1 → Bool
  | .X | .Y => true
  | .I | .Z => false

def bitZ : Pauli1 → Bool
  | .Y | .Z => true
  | .I | .X => false

def encode {n : ℕ} (p : PauliElem n) : Row n :=
  ⟨fun k => bitX (p.word k), fun k => bitZ (p.word k), p.phase⟩

def Row.bits {n : ℕ} (r : Row n) : List Bool :=
  List.ofFn r.x ++ List.ofFn r.z ++ [r.phase.val.testBit 0, r.phase.val.testBit 1]

def Row.mul {n : ℕ} (r s : Row n) : Row n :=
  ⟨fun k => xor (r.x k) (s.x k), fun k => xor (r.z k) (s.z k),
    r.phase + s.phase + ∑ k, pauliMulPhase (letter (r.x k) (r.z k))
      (letter (s.x k) (s.z k))⟩

def Row.update {n : ℕ} (g : CliffordGate n) (r : Row n) : Row n :=
  match g with
  | .H i => ⟨Function.update r.x i (r.z i), Function.update r.z i (r.x i),
      r.phase + if r.x i && r.z i then 2 else 0⟩
  | .S i => ⟨r.x, Function.update r.z i (xor (r.z i) (r.x i)),
      r.phase + if r.x i && r.z i then 2 else 0⟩
  | .CNOT i j => ⟨Function.update r.x j (xor (r.x j) (r.x i)),
      Function.update r.z i (xor (r.z i) (r.z j)),
      r.phase + if r.x i && r.z j && !(xor (r.x j) (r.z i)) then 2 else 0⟩

abbrev Tableau (n m : ℕ) := Fin m → Row n

def tableauBits {n m : ℕ} (t : Tableau n m) : List Bool :=
  (List.ofFn t).flatMap Row.bits

def update {n m : ℕ} (g : CliffordGate n) (t : Tableau n m) : Tableau n m :=
  fun a => (t a).update g

def run {n m : ℕ} (gs : List (CliffordGate n)) (t : Tableau n m) : Tableau n m :=
  gs.foldl (fun s g => update g s) t

def zeroTableau (n : ℕ) : Tableau n n :=
  fun i => ⟨fun _ => false, fun k => decide (k = i), 0⟩

noncomputable def codeSpace {n m : ℕ} (t : Tableau n m) :
    Submodule ℂ (QState (Reg n)) where
  carrier := {ψ | ∀ a, op (t a).decode *ᵥ ψ = ψ}
  zero_mem' := by simp
  add_mem' := by
    intro ψ φ hψ hφ a
    rw [Matrix.mulVec_add, hψ a, hφ a]
  smul_mem' := by
    intro c ψ hψ a
    rw [Matrix.mulVec_smul, hψ a]

end Qatlib.Concepts.PauliClifford.PauliAlgebra
