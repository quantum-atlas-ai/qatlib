/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorLocality
import Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian
import Qatlib.Papers.DecisionTrees97.MainResults.ExactCoverGuards
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Papers.DecisionTrees97.MainResults.RaisingHamiltonian
open Qatlib.Papers.DecisionTrees97.MainResults.ExactCoverGuards
open scoped Kronecker

namespace Qatlib.Papers.DecisionTrees97.MainResults.GuardedTerms

theorem tensorLocalOn_mul {N : ℕ} (S : Finset (Fin N))
    {A B : Matrix (Reg N) (Reg N) ℂ} (hA : TensorLocalOn S A) (hB : TensorLocalOn S B) :
    TensorLocalOn S (A * B) := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  refine ⟨a * b, ?_⟩
  change Matrix.reindexAlgEquiv ℂ ℂ (split S).symm
        (a ⊗ₖ (1 : Matrix (Outside N S) (Outside N S) ℂ)) *
      Matrix.reindexAlgEquiv ℂ ℂ (split S).symm
        (b ⊗ₖ (1 : Matrix (Outside N S) (Outside N S) ℂ)) =
    Matrix.reindexAlgEquiv ℂ ℂ (split S).symm
      ((a * b) ⊗ₖ (1 : Matrix (Outside N S) (Outside N S) ℂ))
  rw [← map_mul]
  congr 1
  rw [← Matrix.mul_kronecker_mul a b 1 1]
  simp

def localDiagonal {N : ℕ} (S : Finset (Fin N)) (p : Reg S.card → Bool) :
    Matrix (Reg N) (Reg N) ℂ :=
  partitionLift (split S) (Matrix.diagonal (fun u => if p u then 1 else 0))

theorem localDiagonal_tensor_local {N : ℕ} (S : Finset (Fin N))
    (p : Reg S.card → Bool) : TensorLocalOn S (localDiagonal S p) :=
  ⟨_, rfl⟩

theorem forwardEdge_local_of_subset {n : ℕ} (i : Fin n) (branch : Bool)
    (U : Finset (Fin (2 * n + 1))) (hsub : edgeSupport n i ⊆ U) :
    TensorLocalOn U (forwardEdge n i branch) := by
  apply productMatrix_tensor_local
  intro j hj
  have hje : j ∉ edgeSupport n i := fun h => hj (hsub h)
  have h1 : j ≠ levelWire n i.castSucc := by
    intro h
    exact hje (by simp [edgeSupport, h])
  have h2 : j ≠ levelWire n i.succ := by
    intro h
    exact hje (by simp [edgeSupport, h])
  have h3 : j ≠ pathWire n i := by
    intro h
    exact hje (by simp [edgeSupport, h])
  simp [edgeFactors, wireFactors, h1, h2, h3]

def guardedForward {n : ℕ} (i : Fin n) (branch : Bool)
    (U : Finset (Fin (2 * n + 1))) (p : Reg U.card → Bool) :
    Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  localDiagonal U p * forwardEdge n i branch

theorem guardedForward_local {n : ℕ} (i : Fin n) (branch : Bool)
    (U : Finset (Fin (2 * n + 1))) (hsub : edgeSupport n i ⊆ U)
    (p : Reg U.card → Bool) : TensorLocalOn U (guardedForward i branch U p) :=
  tensorLocalOn_mul U (localDiagonal_tensor_local U p)
    (forwardEdge_local_of_subset i branch U hsub)

def guardedHop {n : ℕ} (i : Fin n) (U : Finset (Fin (2 * n + 1)))
    (pzero pone : Reg U.card → Bool) :
    Matrix (Reg (2 * n + 1)) (Reg (2 * n + 1)) ℂ :=
  -(guardedForward i false U pzero + (guardedForward i false U pzero)ᴴ +
    guardedForward i true U pone + (guardedForward i true U pone)ᴴ)

theorem guardedHop_local {n : ℕ} (i : Fin n) (U : Finset (Fin (2 * n + 1)))
    (hsub : edgeSupport n i ⊆ U) (pzero pone : Reg U.card → Bool) :
    TensorLocalOn U (guardedHop i U pzero pone) := by
  have h0 := guardedForward_local i false U hsub pzero
  have h1 := guardedForward_local i true U hsub pone
  have h := tensorLocalOn_add _
    (tensorLocalOn_add _ (tensorLocalOn_add _ h0 (tensorLocalOn_adjoint _ h0)) h1)
    (tensorLocalOn_adjoint _ h1)
  simpa only [neg_one_smul] using! tensorLocalOn_smul _ h (-1)

theorem guardedHop_hermitian {n : ℕ} (i : Fin n) (U : Finset (Fin (2 * n + 1)))
    (pzero pone : Reg U.card → Bool) :
    (guardedHop i U pzero pone).IsHermitian := by
  change (guardedHop i U pzero pone)ᴴ = guardedHop i U pzero pone
  simp only [guardedHop, Matrix.conjTranspose_neg, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  abel

theorem pathWire_injective (n : ℕ) : Function.Injective (pathWire n) := by
  intro a b h
  have hv : n + 1 + a.val = n + 1 + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

def exactCoverSupport {m n : ℕ} (A : Fin m → Fin n → Bool) (i : Fin n) :
    Finset (Fin (2 * n + 1)) :=
  edgeSupport n i ∪ (guardSupport A i).image (pathWire n)

theorem edgeSupport_subset_exactCover {m n : ℕ} (A : Fin m → Fin n → Bool)
    (i : Fin n) : edgeSupport n i ⊆ exactCoverSupport A i :=
  Finset.subset_union_left

theorem exactCoverSupport_card {m n : ℕ} (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3)
    (hcol : ∀ i, (Finset.univ.filter (fun j : Fin m => A j i = true)).card ≤ 3)
    (i : Fin n) : (exactCoverSupport A i).card ≤ 9 := by
  rw [exactCoverSupport]
  calc (edgeSupport n i ∪ (guardSupport A i).image (pathWire n)).card
      ≤ (edgeSupport n i).card + ((guardSupport A i).image (pathWire n)).card :=
        Finset.card_union_le _ _
    _ ≤ 3 + (guardSupport A i).card :=
        Nat.add_le_add Finset.card_le_three
          (le_of_eq (Finset.card_image_of_injective _ (pathWire_injective n)))
    _ ≤ 3 + 6 := Nat.add_le_add_left (support_card A hrow hcol i) 3
    _ = 9 := by norm_num

def readPath {n : ℕ} (U : Finset (Fin (2 * n + 1))) (u : Reg U.card) (k : Fin n)
    (hk : pathWire n k ∈ U) : Bool :=
  u ((U.orderIsoOfFin rfl).symm ⟨pathWire n k, hk⟩)

def guardOnePredicate {m n : ℕ} (A : Fin m → Fin n → Bool) (i : Fin n)
    (u : Reg (exactCoverSupport A i).card) : Bool :=
  by
    classical
    exact decide (allowedOne A i fun k =>
      if hk : pathWire n k ∈ exactCoverSupport A i then
        readPath (exactCoverSupport A i) u k hk
      else false)

def guardZeroPredicate {m n : ℕ} (A : Fin m → Fin n → Bool) (i : Fin n)
    (u : Reg (exactCoverSupport A i).card) : Bool :=
  by
    classical
    exact decide (allowedZero A i fun k =>
      if hk : pathWire n k ∈ exactCoverSupport A i then
        readPath (exactCoverSupport A i) u k hk
      else false)

theorem exactCover_guardedHop_nine_local {m n : ℕ} (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3)
    (hcol : ∀ i, (Finset.univ.filter (fun j : Fin m => A j i = true)).card ≤ 3)
    (i : Fin n) :
    (exactCoverSupport A i).card ≤ 9 ∧
      TensorLocalOn (exactCoverSupport A i)
        (guardedHop i (exactCoverSupport A i)
          (guardZeroPredicate A i) (guardOnePredicate A i)) :=
  ⟨exactCoverSupport_card A hrow hcol i,
    guardedHop_local i (exactCoverSupport A i) (edgeSupport_subset_exactCover A i) _ _⟩

theorem exactCover_guardedHop_hermitian {m n : ℕ} (A : Fin m → Fin n → Bool)
    (i : Fin n) :
    (guardedHop i (exactCoverSupport A i)
      (guardZeroPredicate A i) (guardOnePredicate A i)).IsHermitian :=
  guardedHop_hermitian i (exactCoverSupport A i) _ _

end Qatlib.Papers.DecisionTrees97.MainResults.GuardedTerms
