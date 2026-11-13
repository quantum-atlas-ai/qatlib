/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Concepts.TensorNetwork.CanonicalMPS
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix product state definitions

The module defines bond matrices, word products, open boundary contractions, and translation
invariant amplitudes. `OBCCanonicalForm` and `TICanonicalFormWithBlocks` state the canonical
conditions used by the paper modules, while `C1` records eventual spanning by word products.

`cpMap` is the transfer map associated with the bond matrices, and `PolyBudget` records
polynomial bounds on natural-valued costs. These constructions are associated with
[PerezGarciaEtAl2007].

## Main statements

* `obcAmp`: open boundary amplitude with site-dependent bond dimensions.
* `TICanonicalFormWithBlocks`: block decomposition and transfer fixed point conditions.
* `C1`: existence of a word length spanning the full matrix space.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.MatrixProd07.MainResults

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped BigOperators ComplexConjugate

/-- The type of complex square bond matrices of dimension `D`. -/
abbrev BM (D : ℕ) : Type := Matrix (Fin D) (Fin D) ℂ

/-- The ordered product of the matrices selected by a word of length `L`, starting from the
identity. -/
noncomputable def wordProd {d D : ℕ} (A : Fin d → BM D) (L : ℕ) (w : Fin L → Fin d) : BM D :=
  (List.ofFn w).foldl (fun M i => M * A i) 1

/-- The condition that products of length `L` span the full bond matrix space. -/
def C1At {d D : ℕ} (A : Fin d → BM D) (L : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (wordProd A L)) = ⊤

/-- The condition that products span the full bond matrix space at some word length. -/
def C1 {d D : ℕ} (A : Fin d → BM D) : Prop := ∃ L₀ : ℕ, C1At A L₀

/-- The condition that a matrix is diagonal with strictly positive real diagonal entries and
real trace one. -/
def IsPosFullRankDiag {D : ℕ} (Λ : BM D) : Prop :=
  (∃ v : Fin D → ℝ, (∀ i, 0 < v i) ∧ Λ = Matrix.diagonal (fun i => (v i : ℂ))) ∧
    (Λ.trace).re = 1

/-- The left bond index at a site, using the zeroth boundary index at the initial site and an
internal index elsewhere. -/
def leftIdx {n : ℕ} (dim : ℕ → ℕ) (h0 : 0 < dim 0)
    (β : (i : Fin (n - 1)) → Fin (dim (i.val + 1))) (m : Fin n) : Fin (dim m.val) :=
  if hm : m.val = 0 then ⟨0, by rw [hm]; exact h0⟩
  else
    Fin.cast (by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm)])
      (β ⟨m.val - 1, by have := m.isLt; omega⟩)

/-- The right bond index at a site, using the zeroth boundary index at the final site and an
internal index elsewhere. -/
def rightIdx {n : ℕ} (dim : ℕ → ℕ) (hn : 0 < dim n)
    (β : (i : Fin (n - 1)) → Fin (dim (i.val + 1))) (m : Fin n) : Fin (dim (m.val + 1)) :=
  if hm : m.val + 1 = n then Fin.cast (by rw [hm]) ⟨0, hn⟩
  else β ⟨m.val, by have := m.isLt; omega⟩

/-- The open boundary amplitude obtained by summing products of site tensor entries over all
internal bond indices. -/
noncomputable def obcAmp {n d : ℕ} (dim : ℕ → ℕ) (h0 : 0 < dim 0) (hn : 0 < dim n)
    (A : (m : Fin n) → Fin d → Matrix (Fin (dim m.val)) (Fin (dim (m.val + 1))) ℂ)
    (x : Fin n → Fin d) : ℂ :=
  ∑ β : (i : Fin (n - 1)) → Fin (dim (i.val + 1)),
    ∏ m : Fin n, A m (x m) (leftIdx dim h0 β m) (rightIdx dim hn β m)

/-- The maximum bond dimension among positions zero through `n`. -/
def obcBond (dim : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup dim

/-- The open boundary canonical conditions: one-dimensional boundaries, site normalization, and
strictly positive diagonal bond matrices satisfying the transfer relations. -/
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

/-- Rotates a configuration by one cyclic predecessor step. -/
def rotateConfig {n d : ℕ} [NeZero n] (x : Fin n → Fin d) : Fin n → Fin d :=
  fun i => x ⟨(i.val + n - 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- The condition that an amplitude function is unchanged by `rotateConfig`. -/
def IsTICyclic {n d : ℕ} [NeZero n] (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x, ψ (rotateConfig x) = ψ x

/-- The periodic matrix product amplitude formed from a single tensor family repeated at every
site. -/
noncomputable def tiAmplitude {n d D : ℕ} [NeZero n] [NeZero D] (A : Fin d → BM D)
    (x : Fin n → Fin d) : ℂ :=
  periodicMpsAmplitude (fun (_ : Fin n) => A) x

/-- The predicate that `A` represents `ψ` through its translation invariant periodic amplitude. -/
def IsTIRepresentation {n d D : ℕ} [NeZero n] [NeZero D] (A : Fin d → BM D)
    (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x, tiAmplitude A x = ψ x

/-- The transfer map `X ↦ ∑ i, A i * X * (A i)ᴴ`. -/
noncomputable def cpMap {d D : ℕ} (A : Fin d → BM D) (X : BM D) : BM D :=
  ∑ i, A i * X * (A i)ᴴ

/-- The condition that pairwise annihilating idempotents sum to the identity, decompose every `A
i` into diagonal blocks, and have associated weights in `(0, 1]`. -/
def IsBlockDiagonalDecomp {d D b : ℕ} (P : Fin b → BM D) (A : Fin d → BM D)
    (lam : Fin b → ℝ) : Prop :=
  (∀ j, P j * P j = P j) ∧ (∀ j k, j ≠ k → P j * P k = 0) ∧
  (∑ j, P j = 1) ∧ (∀ i, A i = ∑ j, P j * A i * P j) ∧
  (∀ j, 0 < lam j) ∧ (∀ j, lam j ≤ 1)

/-- The canonical block condition with positive block count, weighted tensor blocks,
normalization, positive diagonal dual fixed matrices, and the stated uniqueness condition
for fixed matrices supported in each block. -/
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

/-- The condition that some number of blocks satisfies `TICanonicalFormWithBlocks`. -/
def TICanonicalForm {d D : ℕ} (A : Fin d → BM D) : Prop :=
  ∃ b : ℕ, TICanonicalFormWithBlocks b A

/-- The condition that a matrix multiplied by its conjugate transpose in either order equals the
identity. -/
def IsUnitary {D : ℕ} (U : BM D) : Prop := U * Uᴴ = 1 ∧ Uᴴ * U = 1

/-- The predicate that a natural-valued function is bounded by `C * (N + 1) ^ k` for some
natural constants `C` and `k`. -/
def PolyBudget (p : ℕ → ℕ) : Prop := ∃ (C k : ℕ), ∀ N, p N ≤ C * (N + 1) ^ k

end Qatlib.Papers.MatrixProd07.MainResults
