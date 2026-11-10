/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.MajoranaShor

inductive sourcePauli : Type
  | I : sourcePauli
  | X : sourcePauli
  | Y : sourcePauli
  | Z : sourcePauli
deriving DecidableEq, Repr

def sourcePauliEntry : sourcePauli → Bool → Bool → ℂ
  | .I, y, x => if y = x then 1 else 0
  | .X, y, x => if y = !x then 1 else 0
  | .Y, y, x => if y = !x then (if x then -Complex.I else Complex.I) else 0
  | .Z, y, x => if y = x then (if x then -1 else 1) else 0

def sourcePauliWordMat {n : ℕ} (w : Fin n → sourcePauli) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => ∏ i, sourcePauliEntry (w i) (y i) (x i)

def sourcePauliWeight {n : ℕ} (w : Fin n → sourcePauli) : ℕ :=
  (Finset.univ.filter (fun i => w i ≠ sourcePauli.I)).card

theorem sourcePauliWeight_identity (n : ℕ) :
    sourcePauliWeight (fun _ : Fin n => sourcePauli.I) = 0 := by
  simp [sourcePauliWeight]

def sourcePauliMul : sourcePauli → sourcePauli → sourcePauli
  | .I, q => q
  | p, .I => p
  | .X, .X => .I
  | .Y, .Y => .I
  | .Z, .Z => .I
  | .X, .Y => .Z
  | .Y, .X => .Z
  | .X, .Z => .Y
  | .Z, .X => .Y
  | .Y, .Z => .X
  | .Z, .Y => .X

def sourcePauliCommute (p q : sourcePauli) : Prop :=
  sourcePauliMul p q = sourcePauliMul q p

def sourceWordMul {n : ℕ} (w v : Fin n → sourcePauli) : Fin n → sourcePauli :=
  fun i => sourcePauliMul (w i) (v i)

def sourceWordCommute {n : ℕ} (w v : Fin n → sourcePauli) : Prop :=
  ∀ i, sourcePauliCommute (w i) (v i)

inductive sourceStabilizerProduct {n : ℕ} (S : Finset (Fin n → sourcePauli)) :
    (Fin n → sourcePauli) → Prop
  | nil : sourceStabilizerProduct S (fun _ => sourcePauli.I)
  | step {s : Fin n → sourcePauli} (hs : s ∈ S) {w : Fin n → sourcePauli}
      (hw : sourceStabilizerProduct S w) :
      sourceStabilizerProduct S (sourceWordMul s w)

def sourceCodeDistance (n : ℕ) (S : Finset (Fin n → sourcePauli)) : ℕ :=
  sInf {w : ℕ | ∃ L : Fin n → sourcePauli,
    (∀ s ∈ S, sourceWordCommute L s) ∧ ¬ sourceStabilizerProduct S L ∧
      sourcePauliWeight L = w}

def sourceZWord (l k : ℕ) : Fin (l * l) → sourcePauli :=
  fun s =>
    if s.val = k * l ∨ s.val = (k + 2) * l - 1 then .X
    else if k * l < s.val ∧ s.val < (k + 2) * l - 1 then .Z
    else .I

def sourceYWord (l k j : ℕ) : Fin (l * l) → sourcePauli :=
  fun s => if s.val = k * l + j ∨ s.val = k * l + j + 1 then .Y else .I

def sourceShorStabilizers (l : ℕ) : Finset (Fin (l * l) → sourcePauli) :=
  ((Finset.range (l - 1)).image (fun k => sourceZWord l k)) ∪
    (((Finset.range l).product (Finset.range (l - 1))).image
      (fun p => sourceYWord l p.1 p.2))

end Qatlib.Papers.FermionicComp00.MainResults.MajoranaShor
