/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Concepts.TensorNetwork.CanonicalMPS
import Mathlib.LinearAlgebra.Matrix.Trace
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.MatrixProd07.MainResults

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped BigOperators ComplexConjugate

abbrev BM (D : ℕ) : Type := Matrix (Fin D) (Fin D) ℂ

noncomputable def wordProd {d D : ℕ} (A : Fin d → BM D) (L : ℕ) (w : Fin L → Fin d) : BM D :=
  (List.ofFn w).foldl (fun M i => M * A i) 1

def C1At {d D : ℕ} (A : Fin d → BM D) (L : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (wordProd A L)) = ⊤

def C1 {d D : ℕ} (A : Fin d → BM D) : Prop := ∃ L₀ : ℕ, C1At A L₀

def IsPosFullRankDiag {D : ℕ} (Λ : BM D) : Prop :=
  (∃ v : Fin D → ℝ, (∀ i, 0 < v i) ∧ Λ = Matrix.diagonal (fun i => (v i : ℂ))) ∧
    (Λ.trace).re = 1

def leftIdx {n : ℕ} (dim : ℕ → ℕ) (h0 : 0 < dim 0)
    (β : (i : Fin (n - 1)) → Fin (dim (i.val + 1))) (m : Fin n) : Fin (dim m.val) :=
  if hm : m.val = 0 then ⟨0, by rw [hm]; exact h0⟩
  else
    Fin.cast (by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm)])
      (β ⟨m.val - 1, by have := m.isLt; omega⟩)

def rightIdx {n : ℕ} (dim : ℕ → ℕ) (hn : 0 < dim n)
    (β : (i : Fin (n - 1)) → Fin (dim (i.val + 1))) (m : Fin n) : Fin (dim (m.val + 1)) :=
  if hm : m.val + 1 = n then Fin.cast (by rw [hm]) ⟨0, hn⟩
  else β ⟨m.val, by have := m.isLt; omega⟩

noncomputable def obcAmp {n d : ℕ} (dim : ℕ → ℕ) (h0 : 0 < dim 0) (hn : 0 < dim n)
    (A : (m : Fin n) → Fin d → Matrix (Fin (dim m.val)) (Fin (dim (m.val + 1))) ℂ)
    (x : Fin n → Fin d) : ℂ :=
  ∑ β : (i : Fin (n - 1)) → Fin (dim (i.val + 1)),
    ∏ m : Fin n, A m (x m) (leftIdx dim h0 β m) (rightIdx dim hn β m)

def obcBond (dim : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup dim

def OBCCanonicalForm {n d : ℕ} (dim : ℕ → ℕ)
    (A : (m : Fin n) → Fin d → Matrix (Fin (dim m.val)) (Fin (dim (m.val + 1))) ℂ) : Prop :=
  dim 0 = 1 ∧ dim n = 1 ∧
  (∀ m : Fin n, (∑ x : Fin d, A m x * (A m x)ᴴ) = 1) ∧
  ∃ Λ : (j : Fin (n + 1)) → Matrix (Fin (dim j.val)) (Fin (dim j.val)) ℂ,
    Λ 0 = 1 ∧ Λ (Fin.last n) = 1 ∧
    (∀ m : Fin n,
      (∑ x : Fin d, (A m x)ᴴ * Λ ⟨m.val, Nat.lt_succ_of_lt m.isLt⟩ * A m x)
        = Λ ⟨m.val + 1, Nat.succ_lt_succ m.isLt⟩) ∧
    (∀ j : Fin (n + 1), IsPosFullRankDiag (Λ j))

def rotateConfig {n d : ℕ} [NeZero n] (x : Fin n → Fin d) : Fin n → Fin d :=
  fun i => x ⟨(i.val + n - 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

def IsTICyclic {n d : ℕ} [NeZero n] (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x, ψ (rotateConfig x) = ψ x

noncomputable def tiAmplitude {n d D : ℕ} [NeZero n] [NeZero D] (A : Fin d → BM D)
    (x : Fin n → Fin d) : ℂ :=
  periodicMpsAmplitude (fun (_ : Fin n) => A) x

def IsTIRepresentation {n d D : ℕ} [NeZero n] [NeZero D] (A : Fin d → BM D)
    (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x, tiAmplitude A x = ψ x

noncomputable def cpMap {d D : ℕ} (A : Fin d → BM D) (X : BM D) : BM D :=
  ∑ i, A i * X * (A i)ᴴ

def IsBlockDiagonalDecomp {d D b : ℕ} (P : Fin b → BM D) (A : Fin d → BM D)
    (lam : Fin b → ℝ) : Prop :=
  (∀ j, P j * P j = P j) ∧ (∀ j k, j ≠ k → P j * P k = 0) ∧
  (∑ j, P j = 1) ∧ (∀ i, A i = ∑ j, P j * A i * P j) ∧
  (∀ j, 0 < lam j) ∧ (∀ j, lam j ≤ 1)

def TICanonicalFormWithBlocks {d D : ℕ} (b : ℕ) (A : Fin d → BM D) : Prop :=
  ∃ (_ : 0 < b) (P : Fin b → BM D) (lam : Fin b → ℝ)
      (Ablk : Fin b → Fin d → BM D),
    IsBlockDiagonalDecomp P A lam ∧
    (∀ (j : Fin b) (i : Fin d), P j * A i * P j = (lam j : ℂ) • Ablk j i) ∧
    (∀ j, (∑ i, Ablk j i * (Ablk j i)ᴴ) = P j) ∧
    (∀ j, ∃ Λ : BM D,
        (∑ i, (Ablk j i)ᴴ * Λ * Ablk j i) = Λ ∧
        (∃ v : Fin D → ℝ, (∀ k, 0 < v k) ∧ Λ = Matrix.diagonal (fun k => (v k : ℂ)))) ∧
    (∀ (j : Fin b) (X : BM D), P j * X * P j = X →
        (∑ i, Ablk j i * X * (Ablk j i)ᴴ) = X → X = P j)

def TICanonicalForm {d D : ℕ} (A : Fin d → BM D) : Prop :=
  ∃ b : ℕ, TICanonicalFormWithBlocks b A

def IsUnitary {D : ℕ} (U : BM D) : Prop := U * Uᴴ = 1 ∧ Uᴴ * U = 1

def PolyBudget (p : ℕ → ℕ) : Prop := ∃ (C k : ℕ), ∀ N, p N ≤ C * (N + 1) ^ k

end Qatlib.Papers.MatrixProd07.MainResults
