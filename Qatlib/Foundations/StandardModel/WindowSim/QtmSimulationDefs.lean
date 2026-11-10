/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

inductive QtmMove where
  | left : QtmMove
  | stay : QtmMove
  | right : QtmMove
  deriving DecidableEq, Fintype

structure LocalQTM (Q A : Type*) [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] where

  blank : A

  start : Q

  step : Q → A → QtmMove → Q → A → ℂ

  wf_norm : ∀ q a,
      ∑ q' : Q, ∑ b : A, ∑ d : QtmMove, ‖step q a d q' b‖ ^ 2 = 1

  wf_sameCell : ∀ q₁ a₁ q₂ a₂, (q₁, a₁) ≠ (q₂, a₂) →
      ∑ q' : Q, ∑ b : A, ∑ d : QtmMove,
        star (step q₁ a₁ d q' b) * step q₂ a₂ d q' b = 0

  wf_rightStay : ∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A) (c d : A),
      ∑ q' : Q, step q₁ a₁ QtmMove.right q' c
        * star (step q₂ a₂ QtmMove.stay q' d) = 0

  wf_stayLeft : ∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A) (c d : A),
      ∑ q' : Q, step q₁ a₁ QtmMove.stay q' c
        * star (step q₂ a₂ QtmMove.left q' d) = 0

  wf_rightLeft : ∀ (q₁ : Q) (a₁ : A) (q₂ : Q) (a₂ : A) (c d : A),
      ∑ q' : Q, step q₁ a₁ QtmMove.right q' c
        * star (step q₂ a₂ QtmMove.left q' d) = 0

abbrev CellState (Q A : Type*) := Fin 3 × (Option Q × A)

abbrev GWindow (Q A : Type*) := Fin 3 → CellState Q A

def IsTypeI {Q A : Type*} (z : GWindow Q A) : Prop :=
  (z 1).1 ≠ 1 ∧ ∀ j : Fin 3, (z j).1 ≠ 2

def vFamily {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : LocalQTM Q A) (q₀ : Q) (a₀ b c : A) : QState (GWindow Q A) :=
  fun z =>
    ∑ q' : Q, ∑ a' : A,
      M.step q₀ a₀ QtmMove.stay q' a' *
        (if z 0 = (2, some q', a') ∧ z 1 = (0, none, b) ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0) +
    ∑ q' : Q, ∑ a' : A,
      M.step q₀ a₀ QtmMove.right q' a' *
        (if z 0 = (0, none, a') ∧ z 1 = (2, some q', b) ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0)

def uFamily {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A) : QState (GWindow Q A) :=
  fun z =>
    ∑ q' : Q,
      M.step q₀ a₀ QtmMove.right q' a'' *
        (if z 0 = (2, some q', b) ∧ z 1 = (0, none, c) ∧ z 2 = (0, none, d)
          then (1 : ℂ) else 0)

def headBasis {Q A : Type*} [DecidableEq Q] [DecidableEq A]
    (q : Q) (a b c : A) : QState (GWindow Q A) :=
  fun z =>
    if z 1 = (1, some q, a) ∧ z 0 = (0, none, b) ∧ z 2 = (0, none, c)
      then (1 : ℂ) else 0

def stepSuperposition {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (q : Q) (a b c : A) :
    QState (GWindow Q A) :=
  fun z =>
    ∑ q' : Q, ∑ a' : A,
      M.step q a QtmMove.left q' a' *
        (if z 0 = (2, some q', b) ∧ z 1 = (0, none, a') ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0) +
    ∑ q' : Q, ∑ a' : A,
      M.step q a QtmMove.stay q' a' *
        (if z 0 = (0, none, b) ∧ z 1 = (2, some q', a') ∧ z 2 = (0, none, c)
          then (1 : ℂ) else 0) +
    ∑ q' : Q, ∑ a' : A,
      M.step q a QtmMove.right q' a' *
        (if z 0 = (0, none, b) ∧ z 1 = (0, none, a') ∧ z 2 = (2, some q', c)
          then (1 : ℂ) else 0)

def GUnitFixesH {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    Prop :=
  (∀ z : GWindow Q A, IsTypeI z → G *ᵥ Qatlib.Foundations.PureStateMath.Ket z = Qatlib.Foundations.PureStateMath.Ket z) ∧
  (∀ q₀ : Q, ∀ a₀ b c : A, G *ᵥ vFamily M q₀ a₀ b c = vFamily M q₀ a₀ b c) ∧
  (∀ q₀ : Q, ∀ a₀ a'' b c d : A,
    G *ᵥ uFamily M q₀ a₀ a'' b c d = uFamily M q₀ a₀ a'' b c d)

def GUnitSteps {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    Prop :=
  ∀ q : Q, ∀ a b c : A, G *ᵥ headBasis q a b c = stepSuperposition M q a b c

structure WindowCfg (t : ℕ) (Q A : Type*) where

  head : Fin (2 * t + 1)

  state : Q

  tape : Fin (2 * t + 1) → A
  deriving DecidableEq, Fintype

abbrev WReg (t : ℕ) (Q A : Type*) := Fin (2 * t + 1) → CellState Q A

def windowEncode {t : ℕ} {Q A : Type*} (c : WindowCfg t Q A) : WReg t Q A :=
  fun j => if j = c.head then (1, some c.state, c.tape j) else (0, none, c.tape j)

def windowEmbed {t : ℕ} {Q A : Type*} (φ : QState (WindowCfg t Q A)) :
    QState (WReg t Q A) :=
  Function.extend windowEncode φ 0

def moveCell {t : ℕ} (d : QtmMove) (h : Fin (2 * t + 1)) : Option (Fin (2 * t + 1)) :=
  match d with
  | QtmMove.left =>
      if _hh : h.val = 0 then none
      else some ⟨h.val - 1, by have := h.isLt; omega⟩
  | QtmMove.stay => some h
  | QtmMove.right =>
      if hh : h.val = 2 * t then none
      else some ⟨h.val + 1, by have := h.isLt; omega⟩

def windowStep {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) :
    Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ :=
  Matrix.of fun c' c =>
    ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
      if moveCell d c.head = some c'.head ∧ c'.state = q' ∧
          ∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j
      then M.step c.state (c.tape c.head) d q' b else 0

def initWindowCfg {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (n : ℕ) (x : Fin n → A) :
    WindowCfg t Q A where
  head := ⟨t, by omega⟩
  state := M.start
  tape := fun j =>
    if h : t < j.val ∧ j.val ≤ t + n then x ⟨j.val - t - 1, by omega⟩ else M.blank

def gUnitCells (t : ℕ) (k : Fin (2 * t - 1)) : Fin 3 → Fin (2 * t + 1) :=
  ![⟨k.val, by have := k.isLt; omega⟩,
    ⟨k.val + 1, by have := k.isLt; omega⟩,
    ⟨k.val + 2, by have := k.isLt; omega⟩]

def gUnitFull {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (k : Fin (2 * t - 1)) :
    Matrix (WReg t Q A) (WReg t Q A) ℂ :=
  Matrix.of fun x y =>
    if ∀ j : Fin (2 * t + 1), (∀ q : Fin 3, gUnitCells t k q ≠ j) → x j = y j
    then G (fun q => x (gUnitCells t k q)) (fun q => y (gUnitCells t k q))
    else 0

def markSwap {Q A : Type*} (r : CellState Q A) : CellState Q A :=
  if r.1 = 1 then (2, r.2) else if r.1 = 2 then (1, r.2) else r

def iSwapFull (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] : Matrix (WReg t Q A) (WReg t Q A) ℂ :=
  permMatrix fun r : WReg t Q A => fun j => markSwap (r j)

def kRoundCircuit (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    Circuit (WReg t Q A) :=
  (List.finRange (2 * t - 1)).map
    (fun k => Step.gate (gUnitFull G k)) ++ [Step.gate (iSwapFull t)]

end Qatlib.Foundations.StandardDefs.WindowSim
