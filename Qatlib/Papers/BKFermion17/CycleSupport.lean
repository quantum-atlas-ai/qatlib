/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.Relations
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BKFermion17.CycleSupport

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Papers.BKFermion17.H2Edge
open Qatlib.Papers.BKFermion17.H2Edge

theorem stabilizer_compose {n : ℕ} (P Q : Matrix (Reg n) (Reg n) ℂ) (ψ : Reg n → ℂ)
    (hP : P.mulVec ψ = ψ) (hQ : Q.mulVec ψ = ψ) : (P * Q).mulVec ψ = ψ := by
  rw [← Matrix.mulVec_mulVec, hQ, hP]

theorem loop_composition_stabilizes {n : ℕ} (C₁ C₂ : Matrix (Reg n) (Reg n) ℂ)
    (ψ : Reg n → ℂ) (h₁ : C₁.mulVec ψ = ψ) (h₂ : C₂.mulVec ψ = ψ) :
    (C₁ * C₂).mulVec ψ = ψ :=
  stabilizer_compose C₁ C₂ ψ h₁ h₂

def h2EdgeSet : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (1, 2), (2, 3), (0, 3)}

def degreeParity (S : Finset (Fin 4 × Fin 4)) (v : Fin 4) : ℕ :=
  (S.filter (fun e => e.1 = v ∨ e.2 = v)).card % 2

def IsCycleSet (S : Finset (Fin 4 × Fin 4)) : Prop :=
  S ⊆ h2EdgeSet ∧ ∀ v : Fin 4, degreeParity S v = 0

theorem h2EdgeSet_card : h2EdgeSet.card = 4 := by
  decide

theorem h2_vertex_count : Fintype.card (Fin 4) = 4 :=
  Fintype.card_fin 4

theorem h2_independent_loop_count :
    (h2EdgeSet.card : ℤ) - (Fintype.card (Fin 4) : ℤ) + 1 = 1 := by
  rw [h2EdgeSet_card, h2_vertex_count]
  norm_num

theorem h2_cycles_filter :
    h2EdgeSet.powerset.filter (fun S => ∀ v : Fin 4, degreeParity S v = 0) = {∅, h2EdgeSet} := by
  decide

theorem h2_cycle_space (S : Finset (Fin 4 × Fin 4)) (hS : S ∈ h2EdgeSet.powerset)
    (h : ∀ v : Fin 4, degreeParity S v = 0) : S = ∅ ∨ S = h2EdgeSet := by
  have hmem : S ∈ h2EdgeSet.powerset.filter (fun S => ∀ v : Fin 4, degreeParity S v = 0) :=
    Finset.mem_filter.mpr ⟨hS, h⟩
  rw [h2_cycles_filter] at hmem
  simpa using hmem

theorem h2_nonempty_cycles_card :
    (h2EdgeSet.powerset.filter
        (fun S => (∀ v : Fin 4, degreeParity S v = 0) ∧ S ≠ ∅)).card = 1 := by
  decide

theorem h2_unique_loop :
    (h2EdgeSet.powerset.filter
        (fun S => (∀ v : Fin 4, degreeParity S v = 0) ∧ S ≠ ∅)) = {h2EdgeSet} := by
  decide

def h2LoopEdges : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 2), (2, 3), (3, 0)]

def loopProduct : List (Fin 4 × Fin 4) → PauliElem 4
  | [] => 1
  | e :: es => PauliElem.mul (h2A e.1 e.2) (loopProduct es)

theorem h2Loop_eq_loopProduct : h2Loop = loopProduct h2LoopEdges := by
  decide

theorem h2LoopEdges_support :
    h2LoopEdges.toFinset.image (fun e => (min e.1 e.2, max e.1 e.2)) =
      h2EdgeSet.image (fun e => (min e.1 e.2, max e.1 e.2)) := by
  decide

end Qatlib.Papers.BKFermion17.CycleSupport
