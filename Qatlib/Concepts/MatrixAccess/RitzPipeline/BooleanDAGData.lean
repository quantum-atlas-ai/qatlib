/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Lean.Elab.Tactic.Omega
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped Classical BigOperators
set_option autoImplicit false

inductive BooleanNode (n : ℕ) where
  | constant (b : Bool)
  | neg (a : Fin n)
  | xor (a b : Fin n)
  | conj (a b : Fin n)

def booleanNodeValue {n : ℕ} : BooleanNode n → Reg n → Bool
  | .constant b, _ => b
  | .neg a, x => !(x a)
  | .xor a b, x => x a ^^ x b
  | .conj a b, x => x a && x b

noncomputable def booleanNodeSteps {n L : ℕ} (node : BooleanNode n)
    (h : n < L) : List (ReflectionGate L) :=
  let src : Fin n → Fin L := Fin.castLE h.le
  let t : Fin L := ⟨n,h⟩
  match node with
  | .constant false => []
  | .constant true => [.inl (t,PauliX)]
  | .neg a => [.inr (src a,t),.inl (t,PauliX)]
  | .xor a b => [.inr (src a,t),.inr (src b,t)]
  | .conj a b => if a=b then [.inr (src a,t)] else toffoliLocalSteps (src a) (src b) t

inductive BooleanDAG (m : ℕ) : ℕ → Type where
  | nil : BooleanDAG m 0
  | snoc {n : ℕ} (previous : BooleanDAG m n) (node : BooleanNode (m+n)) :
      BooleanDAG m (n+1)

def booleanDAGValue {m : ℕ} : {n : ℕ} → BooleanDAG m n → Reg m → Reg (m+n)
  | _, .nil, x => x
  | _, .snoc g node, x =>
    let e := booleanDAGValue g x
    Fin.lastCases (booleanNodeValue node e) e

noncomputable def booleanDAGComputeInto {m L : ℕ} :
    {n : ℕ} → BooleanDAG m n → (m+n ≤ L) → List (ReflectionGate L)
  | _, .nil, _ => []
  | _, .snoc g node, h =>
    booleanDAGComputeInto g (by omega) ++ booleanNodeSteps node (by omega)

noncomputable def booleanDAGCompute {m n : ℕ} (g : BooleanDAG m n) (o : ℕ) :
    List (ReflectionGate (m+n+o)) :=
  booleanDAGComputeInto g (by omega)

noncomputable def booleanDAGCopy (m n o : ℕ) (out : Fin o → Fin (m+n)) :
    List (ReflectionGate (m+n+o)) :=
  (List.finRange o).map fun j => .inr
    (Fin.castLE (by omega) (out j),⟨m+n+j.val,by omega⟩)

noncomputable def booleanDAGSteps {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) : List (ReflectionGate (m+n+o)) :=
  booleanDAGCompute g o ++ booleanDAGCopy m n o out ++ reflectionAdjoint (booleanDAGCompute g o)

def booleanDAGInput (m n o : ℕ) (x : Reg m) (y : Reg o) : Reg (m+n+o) := fun i =>
  if hx : i.val < m then x ⟨i.val,hx⟩
  else if hw : i.val < m+n then false
  else y ⟨i.val-(m+n),by omega⟩

def booleanDAGComputed {m n : ℕ} (g : BooleanDAG m n) (o : ℕ)
    (x : Reg m) (y : Reg o) : Reg (m+n+o) := fun i =>
  if hi : i.val < m+n then booleanDAGValue g x ⟨i.val,hi⟩
  else y ⟨i.val-(m+n),by omega⟩

def booleanDAGOutput {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (x : Reg m) (y : Reg o) : Reg o :=
  fun j => y j ^^ booleanDAGValue g x (out j)

noncomputable def booleanDAGEmbed (m n o : ℕ) (ψ : QState (Reg m × Reg o)) :
    QState (Reg (m+n+o)) :=
  ∑ xy, ψ xy • Ket (booleanDAGInput m n o xy.1 xy.2)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
