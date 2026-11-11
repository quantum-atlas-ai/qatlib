/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Window registers for quantum Turing machine simulation

This module defines the local quantum Turing machine data `LocalQTM`, finite configurations
`WindowCfg`, and their cell-register encoding `windowEncode`. Three-cell transition states
specify the contracts `GUnitFixesH` and `GUnitSteps` for a local simulation gate.

The lifted gate `gUnitFull` acts within one three-cell window, while `kRoundCircuit` combines a
sweep of these gates with a marker swap to form a simulation round.

The mathematical background is discussed in [Yao1993].

## Main statements

* `LocalQTM`: transition amplitudes with normalization and local orthogonality conditions.
* `windowStep`: the finite-window transition matrix, excluding moves beyond its boundary.
* `kRoundCircuit`: the local sweep followed by the full marker swap.

## References

* [Yao, 1993][Yao1993]
-/

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

/-- The three possible head directions: left, stationary, and right. -/
inductive QtmMove where
  | left : QtmMove
  | stay : QtmMove
  | right : QtmMove
  deriving DecidableEq, Fintype

/-- A finite-state, finite-alphabet quantum Turing machine with a blank symbol, start state, and
transition amplitudes satisfying normalization and the specified local orthogonality
conditions. -/
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

/-- A tape cell carrying a three-valued marker, an optional internal machine state, and a tape
symbol. -/
abbrev CellState (Q A : Type*) := Fin 3 × (Option Q × A)

/-- A three-cell window of marked tape cell states. -/
abbrev GWindow (Q A : Type*) := Fin 3 → CellState Q A

/-- The condition that a window's central marker is not one and none of its markers is two. -/
def IsTypeI {Q A : Type*} (z : GWindow Q A) : Prop :=
  (z 1).1 ≠ 1 ∧ ∀ j : Fin 3, (z j).1 ≠ 2

/-- The local superposition of stationary and right-moving transitions from a head at the first
cell of a three-cell window. -/
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

/-- The local superposition induced by right-moving transitions with fixed written symbol,
placing the new marked head in the first window cell. -/
def uFamily {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : LocalQTM Q A) (q₀ : Q) (a₀ a'' b c d : A) : QState (GWindow Q A) :=
  fun z =>
    ∑ q' : Q,
      M.step q₀ a₀ QtmMove.right q' a'' *
        (if z 0 = (2, some q', b) ∧ z 1 = (0, none, c) ∧ z 2 = (0, none, d)
          then (1 : ℂ) else 0)

/-- The basis state with marker one and internal state `q` at the central cell, scanned symbol
`a`, and neighboring symbols `b` and `c`. -/
def headBasis {Q A : Type*} [DecidableEq Q] [DecidableEq A]
    (q : Q) (a b c : A) : QState (GWindow Q A) :=
  fun z =>
    if z 1 = (1, some q, a) ∧ z 0 = (0, none, b) ∧ z 2 = (0, none, c)
      then (1 : ℂ) else 0

/-- The three-cell superposition of all local transitions, with the written symbol at the old
head and marker two at the new head. -/
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

/-- The condition that `G` fixes type I basis states and every state in the local families
`vFamily` and `uFamily`. -/
def GUnitFixesH {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    Prop :=
  (∀ z : GWindow Q A, IsTypeI z → G *ᵥ Qatlib.Foundations.PureStateMath.Ket z = Qatlib.Foundations.PureStateMath.Ket z) ∧
  (∀ q₀ : Q, ∀ a₀ b c : A, G *ᵥ vFamily M q₀ a₀ b c = vFamily M q₀ a₀ b c) ∧
  (∀ q₀ : Q, ∀ a₀ a'' b c d : A,
    G *ᵥ uFamily M q₀ a₀ a'' b c d = uFamily M q₀ a₀ a'' b c d)

/-- The condition that `G` sends every central-head basis state to the machine's local
transition superposition. -/
def GUnitSteps {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    Prop :=
  ∀ q : Q, ∀ a b c : A, G *ᵥ headBasis q a b c = stepSuperposition M q a b c

/-- A machine configuration on `2 * t + 1` cells, consisting of a head position, an internal
state, and tape contents. -/
structure WindowCfg (t : ℕ) (Q A : Type*) where

  head : Fin (2 * t + 1)

  state : Q

  tape : Fin (2 * t + 1) → A
  deriving DecidableEq, Fintype

/-- The register of marked cell states on a window of `2 * t + 1` cells. -/
abbrev WReg (t : ℕ) (Q A : Type*) := Fin (2 * t + 1) → CellState Q A

/-- Encode a configuration by marking its head with one and its internal state, leaving every
other cell unmarked. -/
def windowEncode {t : ℕ} {Q A : Type*} (c : WindowCfg t Q A) : WReg t Q A :=
  fun j => if j = c.head then (1, some c.state, c.tape j) else (0, none, c.tape j)

/-- Extend a configuration amplitude function to encoded registers, assigning zero outside the
encoding's image. -/
def windowEmbed {t : ℕ} {Q A : Type*} (φ : QState (WindowCfg t Q A)) :
    QState (WReg t Q A) :=
  Function.extend windowEncode φ 0

/-- Move a finite-window head one cell left or right, or leave it stationary, returning `none`
when a move crosses the boundary. -/
def moveCell {t : ℕ} (d : QtmMove) (h : Fin (2 * t + 1)) : Option (Fin (2 * t + 1)) :=
  match d with
  | QtmMove.left =>
      if _hh : h.val = 0 then none
      else some ⟨h.val - 1, by have := h.isLt; omega⟩
  | QtmMove.stay => some h
  | QtmMove.right =>
      if hh : h.val = 2 * t then none
      else some ⟨h.val + 1, by have := h.isLt; omega⟩

/-- The finite-window transition matrix obtained by summing local transition amplitudes whose
head move and tape update match the output configuration. -/
def windowStep {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) :
    Matrix (WindowCfg t Q A) (WindowCfg t Q A) ℂ :=
  Matrix.of fun c' c =>
    ∑ d : QtmMove, ∑ q' : Q, ∑ b : A,
      if moveCell d c.head = some c'.head ∧ c'.state = q' ∧
          ∀ j : Fin (2 * t + 1), c'.tape j = if j = c.head then b else c.tape j
      then M.step c.state (c.tape c.head) d q' b else 0

/-- Initialize the head at cell `t` in the start state, placing the input symbols immediately to
its right wherever they lie in the window and blanks elsewhere. -/
def initWindowCfg {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) (n : ℕ) (x : Fin n → A) :
    WindowCfg t Q A where
  head := ⟨t, by omega⟩
  state := M.start
  tape := fun j =>
    if h : t < j.val ∧ j.val ≤ t + n then x ⟨j.val - t - 1, by omega⟩ else M.blank

/-- The three consecutive global cell positions starting at `k`. -/
def gUnitCells (t : ℕ) (k : Fin (2 * t - 1)) : Fin 3 → Fin (2 * t + 1) :=
  ![⟨k.val, by have := k.isLt; omega⟩,
    ⟨k.val + 1, by have := k.isLt; omega⟩,
    ⟨k.val + 2, by have := k.isLt; omega⟩]

/-- Lift a three-cell matrix to the full register by requiring equality outside its active
window. -/
def gUnitFull {t : ℕ} {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) (k : Fin (2 * t - 1)) :
    Matrix (WReg t Q A) (WReg t Q A) ℂ :=
  Matrix.of fun x y =>
    if ∀ j : Fin (2 * t + 1), (∀ q : Fin 3, gUnitCells t k q ≠ j) → x j = y j
    then G (fun q => x (gUnitCells t k q)) (fun q => y (gUnitCells t k q))
    else 0

/-- Exchange markers one and two, leaving the optional internal state, tape symbol, and marker
zero unchanged. -/
def markSwap {Q A : Type*} (r : CellState Q A) : CellState Q A :=
  if r.1 = 1 then (2, r.2) else if r.1 = 2 then (1, r.2) else r

/-- The permutation matrix that swaps markers one and two in every register cell. -/
def iSwapFull (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] : Matrix (WReg t Q A) (WReg t Q A) ℂ :=
  permMatrix fun r : WReg t Q A => fun j => markSwap (r j)

/-- One simulation round: a left-to-right sweep of lifted local gates followed by the full
marker swap. -/
def kRoundCircuit (t : ℕ) {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (G : Matrix (GWindow Q A) (GWindow Q A) ℂ) :
    Circuit (WReg t Q A) :=
  (List.finRange (2 * t - 1)).map
    (fun k => Step.gate (gUnitFull G k)) ++ [Step.gate (iSwapFull t)]

end Qatlib.Foundations.StandardDefs.WindowSim
