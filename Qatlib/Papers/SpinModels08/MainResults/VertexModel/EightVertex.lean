/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.VertexModel.Basic
set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.VertexModel

open Qatlib.Papers.SpinModels08.MainResults

def IsEightVertexShape (w : QWeight 2) : Prop :=
  w 0 0 0 1 = 0 ∧ w 0 0 1 0 = 0 ∧ w 0 1 0 0 = 0 ∧ w 0 1 1 1 = 0 ∧
  w 1 0 0 0 = 0 ∧ w 1 0 1 1 = 0 ∧ w 1 1 0 1 = 0 ∧ w 1 1 1 0 = 0

def IsSixVertexShape (w : QWeight 2) : Prop :=
  IsEightVertexShape w ∧ w 0 0 1 1 = 0 ∧ w 1 1 0 0 = 0

def FreeFermionCond (w : QWeight 2) : Prop :=
  w 0 0 0 0 * w 1 1 1 1 - w 0 0 1 1 * w 1 1 0 0 =
    w 0 1 0 1 * w 1 0 1 0 - w 0 1 1 0 * w 1 0 0 1

theorem eightVertexGate_supported (w : QWeight 2) (h : IsEightVertexShape w)
    (i j k l : Fin 2) (hpar : (i.val + j.val) % 2 ≠ (k.val + l.val) % 2) :
    twoLocalGate w (i, j) (k, l) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [twoLocalGate, IsEightVertexShape]

theorem sixVertexGate_supported (w : QWeight 2) (h : IsSixVertexShape w)
    (i j k l : Fin 2)
    (hbad : (i.val + j.val) % 2 ≠ (k.val + l.val) % 2 ∨ (i = 0 ∧ j = 0 ∧ k = 1 ∧ l = 1)
      ∨ (i = 1 ∧ j = 1 ∧ k = 0 ∧ l = 0)) :
    twoLocalGate w (i, j) (k, l) = 0 := by
  obtain ⟨h8, h0011, h1100⟩ := h
  rcases hbad with hpar | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact eightVertexGate_supported w h8 i j k l hpar
  · simpa [twoLocalGate] using h0011
  · simpa [twoLocalGate] using h1100

theorem evaluator_identity_transfer {q N : ℕ}
    (w : ∀ M : ℕ, Fin M → Fin N → QWeight q)
    (Zval : ∀ M : ℕ, Config q N → Config q N → ℂ)
    (hZ : ∀ (M : ℕ) (L R : Config q N), Zval M L R = vmPartition M (w M) L R) :
    ∀ (M : ℕ) (L R : Config q N), Zval M L R = matElem (vmCircuit M (w M)) L R := by
  intro M L R
  rw [hZ M L R, matElem_eq_apply, vmPartition_eq_vmCircuit]

theorem eightVertex_evaluator_identity {N : ℕ}
    (w : ∀ M : ℕ, Fin M → Fin N → QWeight 2)
    (_hshape : ∀ (M : ℕ) (c : Fin M) (r : Fin N), IsEightVertexShape (w M c r))
    (_hff : ∀ (M : ℕ) (c : Fin M) (r : Fin N), FreeFermionCond (w M c r))
    (Zval : ∀ M : ℕ, Config 2 N → Config 2 N → ℂ)
    (hZ : ∀ (M : ℕ) (L R : Config 2 N), Zval M L R = vmPartition M (w M) L R) :
    ∀ (M : ℕ) (L R : Config 2 N), Zval M L R = matElem (vmCircuit M (w M)) L R :=
  evaluator_identity_transfer w Zval hZ

def threeLocalGate {q : ℕ} (w6 : Fin q → Fin q → Fin q → Fin q → Fin q → Fin q → ℂ) :
    Matrix (Fin q × Fin q × Fin q) (Fin q × Fin q × Fin q) ℂ :=
  fun (i, j, k) (l, m, n) => w6 i j k l m n

theorem threeLocalGate_apply {q : ℕ} (w6 : Fin q → Fin q → Fin q → Fin q → Fin q → Fin q → ℂ)
    (i j k l m n : Fin q) :
    threeLocalGate w6 (i, j, k) (l, m, n) = w6 i j k l m n := rfl

end Qatlib.Papers.SpinModels08.MainResults.VertexModel
