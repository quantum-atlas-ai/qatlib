/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs

/-!
# Canonical matrix product representations and bond bounds

Cut ranks are bounded by `d ^ (n / 2)`, yielding a left-canonical matrix
product representation of every normalized nonempty finite chain with bond
dimension at most that value. The module also defines the open-boundary
canonical-completeness proposition and a gauge-chain proposition; those
definitions state the desired properties rather than prove them.

The source is [PerezGarciaEtAl2007]; tensor-network background is
[Schollwöck, matrix product states][Schollwock2011]. The bound is exponential
in chain length for fixed local dimension; no polynomial bond claim is needed.
-/
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.CanonicalOBC

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

/-- For positive local dimension and a cut `c < n`, the cut rank is at most `d ^ (n / 2)`. See
[PerezGarciaEtAl2007]. -/
theorem cutRank_le_half {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) {c : ℕ} (hc : c < n)
    (hd : 0 < d) : cutRank n d ψ c ≤ d ^ (n / 2) := by
  have h1 := cutRank_le_pow_left ψ c
  have h2 := cutRank_le_pow_right ψ c
  by_cases hcl : c ≤ n / 2
  · exact le_trans h1 (pow_le_pow_right' (by omega : 1 ≤ d) hcl)
  · have hnc : n - c ≤ n / 2 := by omega
    exact le_trans h2 (pow_le_pow_right' (by omega : 1 ≤ d) hnc)

/-- Every normalized nonempty chain has a left-canonical MPS representation
with bond dimension at most `d ^ (n / 2)`; compare
[Pérez-García et al., matrix product representations][PerezGarciaEtAl2007]. -/
theorem theorem1_poly_bond {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (hd : 0 < d) (hn : 1 ≤ n)
    (hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∃ (D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation n d D hD A ψ ∧ LeftCanonical A ∧ D ≤ d ^ (n / 2) := by
  obtain ⟨D, hD, A, hrep, hlc, hDmax⟩ := clause2_clause2 n d ψ hnorm hn
  refine ⟨D, hD, A, hrep, hlc, ?_⟩
  rw [hDmax]
  refine Nat.max_le.mpr ⟨Nat.one_le_pow (n / 2) d hd, ?_⟩
  exact Finset.sup_le fun c hc => cutRank_le_half ψ (Finset.mem_range.mp hc) hd

/-- The proposition that a normalized state on a nonempty chain has an open boundary canonical
representation with bond dimension at most `d ^ (n / 2)`. -/
def theorem1_completeness_canonical  {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (_hd : 0 < d)
    (_hn : 1 ≤ n) (_hnorm : ∑ x, Complex.normSq (ψ x) = 1) : Prop :=
  ∃ (dim : ℕ → ℕ) (h0 : 0 < dim 0) (hN : 0 < dim n)
      (A : (m : Fin n) → Fin d → Matrix (Fin (dim m.val)) (Fin (dim (m.val + 1))) ℂ),
      OBCCanonicalForm dim A ∧ (∀ x, obcAmp dim h0 hN A x = ψ x) ∧
        obcBond dim n ≤ d ^ (n / 2)

/-- The gauge chain condition requiring `Y j * Z j = 1` and expressing each tensor of `A` as the
corresponding tensor of `B` multiplied by adjacent gauge matrices. -/
def IsGaugeChain {n d : ℕ} (dimB dimA : ℕ → ℕ)
    (Y : (j : Fin (n + 1)) → Matrix (Fin (dimA j.val)) (Fin (dimB j.val)) ℂ)
    (Z : (j : Fin (n + 1)) → Matrix (Fin (dimB j.val)) (Fin (dimA j.val)) ℂ)
    (B : (m : Fin n) → Fin d → Matrix (Fin (dimB m.val)) (Fin (dimB (m.val + 1))) ℂ)
    (A : (m : Fin n) → Fin d → Matrix (Fin (dimA m.val)) (Fin (dimA (m.val + 1))) ℂ) : Prop :=
  (∀ j, Y j * Z j = 1) ∧
    ∀ (m : Fin n) (x : Fin d),
      A m x = Y ⟨m.val, Nat.lt_succ_of_lt m.isLt⟩ * B m x *
        Z ⟨m.val + 1, Nat.succ_lt_succ m.isLt⟩

/-- The proposition that an open boundary representation of `ψ` can be related by `IsGaugeChain`
to a canonical representation of the same amplitude function. -/
def theorem2_freedom  {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)
    (dimB : ℕ → ℕ) (hb0 : 0 < dimB 0) (hbn : 0 < dimB n)
    (B : (m : Fin n) → Fin d → Matrix (Fin (dimB m.val)) (Fin (dimB (m.val + 1))) ℂ)
    (_hrep : ∀ x, obcAmp dimB hb0 hbn B x = ψ x) : Prop :=
  ∃ (dimA : ℕ → ℕ) (ha0 : 0 < dimA 0) (haN : 0 < dimA n)
      (A : (m : Fin n) → Fin d → Matrix (Fin (dimA m.val)) (Fin (dimA (m.val + 1))) ℂ)
      (Y : (j : Fin (n + 1)) → Matrix (Fin (dimA j.val)) (Fin (dimB j.val)) ℂ)
      (Z : (j : Fin (n + 1)) → Matrix (Fin (dimB j.val)) (Fin (dimA j.val)) ℂ),
      IsGaugeChain dimB dimA Y Z B A ∧ OBCCanonicalForm dimA A ∧
        ∀ x, obcAmp dimA ha0 haN A x = ψ x
end Qatlib.Papers.MatrixProd07.MainResults.CanonicalOBC
