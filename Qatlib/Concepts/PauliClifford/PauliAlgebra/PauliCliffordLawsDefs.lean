/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra

def op {n : ℕ} (p : PauliElem n) : Matrix (Reg n) (Reg n) ℂ :=
  (Complex.I ^ p.phase.val : ℂ) • pauliWordOp n p.word

def legalGate {n : ℕ} : CliffordGate n → Prop
  | .H _ => True
  | .S _ => True
  | .CNOT i j => i ≠ j

def cnotPhaseCorrection (a b : Pauli1) : Phase4 :=
  if (a = .X ∧ b = .Z) ∨ (a = .Y ∧ b = .Y) then 2 else 0

def verifiedCliffordAction {n : ℕ} (g : CliffordGate n) (p : PauliElem n) : PauliElem n :=
  match g with
  | .H i =>
    ⟨fun k => if k = i then conjHWord (p.word i) else p.word k,
      p.phase + ∑ k, if k = i then conjHPhase (p.word i) else 0⟩
  | .S i =>
    ⟨fun k => if k = i then conjSWord (p.word i) else p.word k,
      p.phase + ∑ k, if k = i then conjSPhase (p.word i) else 0⟩
  | .CNOT i j =>
    ⟨fun k =>
        if k = i then pauliMul1 (p.word i) (cnotTargetCross (p.word j))
        else if k = j then pauliMul1 (cnotControlCross (p.word i)) (p.word j)
        else p.word k,
      p.phase + cnotPhaseCorrection (p.word i) (p.word j)⟩

def Uword {n : ℕ} (gs : List (CliffordGate n)) : Matrix (Reg n) (Reg n) ℂ :=
  gs.foldl (fun U g => cliffordGateOp n g * U) 1

def actionWord {n : ℕ} (gs : List (CliffordGate n)) (p : PauliElem n) : PauliElem n :=
  gs.foldl (fun q g => verifiedCliffordAction g q) p

end Qatlib.Concepts.PauliClifford.PauliAlgebra
