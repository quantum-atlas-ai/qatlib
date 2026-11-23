/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ReadManyQry11.MainResults.SourceModel

@[expose] public section


/-!
Concrete Boolean semiring matrix-product verification definitions retained from arXiv:1112.0548v1. Operational query bounds and adversary lower bounds remain deferred.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.ReadManyQry11.MainResults

open scoped BigOperators Real

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.ReadManyQry11.MainResults

/-- Bounded-error query upper bounds for functions on an arbitrary finite input type
`I` (not necessarily a Boolean cube `Fin n → Bool`); the matrix product instance
`BmpvInstance n` is such a type.  Same content as `BoundedErrorQueryAtMost` of
`Qatlib/Papers/ReadManyQry11/MainResults/SourceModel.lean`, generalised over the input type. -/
def BoundedErrorQueryAtMostOn (I : Type) [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (b : ℝ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W),
    ∃ P : DecisionProgram I W, P.BoundedFor f ∧ (QueryCount P.circuit : ℝ) ≤ b

/-- Bounded-error query lower bounds for functions on an arbitrary finite input type
`I`; the matrix product instance `BmpvInstance n` is such a type. -/
def BoundedErrorQueryLowerBoundOn (I : Type) [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (b : ℝ) : Prop :=
  ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (P : DecisionProgram I W), P.BoundedFor f → b ≤ (QueryCount P.circuit : ℝ)

/-- The Boolean vector product verification function `bvpv_A` (p. 10): the monotone
depth-2 formula `∧_i ∨_j (A_ij ∧ v_j)`, i.e. `A v = 1` over the Boolean semiring.  The
matrix `A` is part of the problem specification, not of the input. -/
def bvpv {n : ℕ} (A : Fin n → Fin n → Bool) (v : Fin n → Bool) : Bool :=
  (List.finRange n).all (fun i => (List.finRange n).any (fun j => A i j && v j))

/-- Boolean matrix product over the Boolean semiring: `∨_k (A_ik ∧ B_kj)`. -/
def boolMatMul {n : ℕ} (A B : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  fun i j => (List.finRange n).any (fun k => A i k && B k j)

/-- An input of the Boolean matrix product verification problem: three `n × n` Boolean
matrices `A`, `B`, `C` (p. 10). -/
structure BmpvInstance (n : ℕ) where
  /-- The left factor. -/
  A : Fin n → Fin n → Bool
  /-- The right factor. -/
  B : Fin n → Fin n → Bool
  /-- The claimed product. -/
  C : Fin n → Fin n → Bool

/-- Boolean matrix product verification `bmpv` (p. 10): decide whether
`C_ij = ⋁_k (A_ik ∧ B_kj)` for all `i, j ∈ [n]`. -/
def bmpv {n : ℕ} (M : BmpvInstance n) : Bool :=
  (List.finRange n).all (fun i => (List.finRange n).all (fun j =>
    boolMatMul M.A M.B i j == M.C i j))

/-- The input index type of the `bmpv` Boolean function: the `3n²` entries of the three
`n × n` matrices, tagged by which matrix they belong to (p. 10: the input consists of
`A`, `B`, `C` given by entry oracles). -/
def BmpvIndex (n : ℕ) : Type :=
  (Fin n × Fin n) ⊕ (Fin n × Fin n) ⊕ (Fin n × Fin n)

instance (n : ℕ) : Fintype (BmpvIndex n) := by unfold BmpvIndex; infer_instance

instance (n : ℕ) : DecidableEq (BmpvIndex n) := by unfold BmpvIndex; infer_instance

/-- A positive matrix dimension gives a concrete input index for the three tagged
matrix-entry oracles. -/
theorem bmpvIndex_nonempty {n : ℕ} (hn : 0 < n) : Nonempty (BmpvIndex n) := by
  exact ⟨Sum.inl (⟨0, hn⟩, ⟨0, hn⟩)⟩

/-- The `A` entries of a `bmpv` input bit string. -/
def decodeA {n : ℕ} (bits : BmpvIndex n → Bool) : Fin n → Fin n → Bool :=
  fun i j => bits (Sum.inl (i, j))

/-- The `B` entries of a `bmpv` input bit string. -/
def decodeB {n : ℕ} (bits : BmpvIndex n → Bool) : Fin n → Fin n → Bool :=
  fun i j => bits (Sum.inr (Sum.inl (i, j)))

/-- The `C` entries of a `bmpv` input bit string. -/
def decodeC {n : ℕ} (bits : BmpvIndex n → Bool) : Fin n → Fin n → Bool :=
  fun i j => bits (Sum.inr (Sum.inr (i, j)))

/-- Boolean matrix product verification as a Boolean function on the `3n²`-bit input
cube `BmpvIndex n → Bool` (p. 10). -/
def bmpvFun {n : ℕ} (bits : BmpvIndex n → Bool) : Bool :=
  bmpv { A := decodeA bits, B := decodeB bits, C := decodeC bits }

/-! The following theorems make the Boolean-semiring model executable and usable by
consumers.  They expose the exact finite-index semantics instead of treating the
matrix-product predicate as an opaque wrapper. -/

/-- The list encoding of `Fin n` turns a Boolean existential into `List.any`. -/
private theorem any_finRange_iff {n : ℕ} {p : Fin n → Bool} :
    (List.finRange n).any p = true ↔ ∃ k, p k = true := by
  simp [List.any_eq_true]

/-- A Boolean existential over `Fin n` is witnessed by an entry of `finRange n`. -/
private theorem boolMatMul_entry_iff {n : ℕ} (A B : Fin n → Fin n → Bool)
    (i j : Fin n) :
    boolMatMul A B i j = true ↔ ∃ k, A i k = true ∧ B k j = true := by
  rw [boolMatMul, any_finRange_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa [Bool.and_eq_true] using hk⟩
  · rintro ⟨k, hA, hB⟩
    exact ⟨k, by simp [hA, hB]⟩

/-- A Boolean matrix-product entry is true exactly when some intermediate index
has true entries in both factors. -/
theorem boolMatMul_entry_eq_true_iff {n : ℕ} (A B : Fin n → Fin n → Bool)
    (i j : Fin n) :
    boolMatMul A B i j = true ↔ ∃ k, A i k = true ∧ B k j = true := by
  exact boolMatMul_entry_iff A B i j

/-- The verification predicate accepts precisely when every claimed entry equals
the Boolean-semiring product of the two input matrices. -/
theorem bmpv_eq_true_iff {n : ℕ} (M : BmpvInstance n) :
    bmpv M = true ↔ ∀ i j, boolMatMul M.A M.B i j = M.C i j := by
  simp [bmpv]

/-- Decoding the three tagged entry oracles preserves the matrix-product
verification predicate exactly. -/
theorem bmpvFun_decode_eq_true_iff {n : ℕ} (M : BmpvInstance n) :
    bmpvFun (fun x => match x with
      | Sum.inl ij => M.A ij.1 ij.2
      | Sum.inr (Sum.inl ij) => M.B ij.1 ij.2
      | Sum.inr (Sum.inr ij) => M.C ij.1 ij.2) = true ↔
      ∀ i j, boolMatMul M.A M.B i j = M.C i j := by
  rw [bmpvFun, bmpv_eq_true_iff]
  constructor <;> intro h i j <;>
    unfold boolMatMul at h <;>
    exact h i j


end Qatlib.Papers.ReadManyQry11.MainResults
