/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Bipartite states and finite local protocol definitions

This module defines bipartite coefficient matrices, `schmidtRank`, product and entangled
vectors, the Bell family, partial transpose, and two finite convex-decomposition notions of
separability. These provide the finite-dimensional language of entanglement used in
[Nielsen1999] and [Wilde2017].

`LoccProtocol` describes finite trees of local Kraus operations with outcome-dependent
continuations; `LoccComplete`, `LoccChannel`, and `LoccBits` record completeness, summed-branch
semantics, and communication charges. The remaining definitions describe local branches,
spectral entropy, descending prefix sums, and the predicate `Majorizes`.

## Main definitions

* `IsSeparableState` and `IsSeparableMixed`: separability using product projectors or product
  density operators.
* `LoccProtocol` and `LoccChannel`: finite local protocol syntax and branch-sum semantics.
* `entanglementEntropy`: entropy of the first reduced operator's spectrum.
* `Majorizes`: comparison of descending prefix sums.

## References

* [Nielsen, 1999][Nielsen1999]
* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Matrix

variable {D E : ℕ}

/-- The coefficient matrix of a bipartite pure state, with the first subsystem indexing rows. -/
def bipartiteMatrix (ψ : QState (Fin D × Fin E)) : Matrix (Fin D) (Fin E) ℂ :=
  Matrix.of fun i j => ψ (i, j)

/-- The matrix rank of the coefficient matrix of a bipartite pure state. -/
noncomputable def schmidtRank (ψ : QState (Fin D × Fin E)) : ℕ := (bipartiteMatrix ψ).rank

/-- The property of being a tensor product of two subsystem vectors. -/
def IsProductState (ψ : QState (Fin D × Fin E)) : Prop :=
  ∃ (a : QState (Fin D)) (b : QState (Fin E)), ψ = TensorState a b

/-- The property of being normalized and not a product state. -/
def IsEntangled (ψ : QState (Fin D × Fin E)) : Prop :=
  Normalized ψ ∧ ¬ IsProductState ψ

/-- The Bell vector selected by two Boolean labels for its basis pairing and relative sign. -/
noncomputable def bell (s : Bool × Bool) : QState (Fin 2 × Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (Ket ((⟨0, by omega⟩ : Fin 2), if s.1 then (1 : Fin 2) else 0) +
      (if s.2 then (-1 : ℂ) else 1) •
        Ket ((⟨1, by omega⟩ : Fin 2), if !s.1 then (1 : Fin 2) else 0))

/-- Transpose the second subsystem indices of a bipartite operator. -/
def PartialTranspose (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  Matrix.of fun p q => A (p.1, q.2) (q.1, p.2)

/-- The property of being a finite convex combination of projectors onto normalized product
vectors. -/
def IsSeparableState (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (a : Fin n → QState (Fin D)) (b : Fin n → QState (Fin E)),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, Normalized (a i)) ∧ (∀ i, Normalized (b i)) ∧
      ρ = ∑ i, (p i : ℂ) • outerProduct (TensorState (a i) (b i))

/-- The property of being a finite convex combination of tensor products of density operators. -/
def IsSeparableMixed (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Operator D) (τ : Fin n → Operator E),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, IsDensityOperator (σ i)) ∧
      (∀ i, IsDensityOperator (τ i)) ∧ ρ = ∑ i, (p i : ℂ) • TensorGate (σ i) (τ i)

/-- The completeness condition that the sum of `Kᴴ * K` over a list of Kraus operators is the
identity. -/
def IsKrausList (ks : List (Operator D)) : Prop :=
  (ks.map fun K => Kᴴ * K).sum = 1

/-- Apply the listed Kraus operators to the first subsystem and sum the resulting branches. -/
noncomputable def ApplyFirstKraus (ks : List (Operator D))
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  (ks.map fun K => TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E))ᴴ).sum

/-- A finite protocol tree whose steps apply a local Kraus family on either subsystem and
continue according to its outcome. -/
inductive LoccProtocol (D E : ℕ) : Type
  | halt : LoccProtocol D E
  | stepA (n : ℕ) (ks : Fin n → Operator D)
    (next : Fin n → LoccProtocol D E) : LoccProtocol D E
  | stepB (n : ℕ) (ks : Fin n → Operator E)
    (next : Fin n → LoccProtocol D E) : LoccProtocol D E

/-- The recursive requirement that every local Kraus family in a protocol is complete. -/
def LoccComplete : LoccProtocol D E → Prop
  | .halt => True
  | .stepA n ks next => (∑ i, (ks i)ᴴ * ks i = 1) ∧ ∀ i, LoccComplete (next i)
  | .stepB n ks next => (∑ i, (ks i)ᴴ * ks i = 1) ∧ ∀ i, LoccComplete (next i)

/-- The sum of the output branches of a finite local protocol. -/
noncomputable def LoccChannel : LoccProtocol D E →
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ
  | .halt, ρ => ρ
  | .stepA n ks next, ρ =>
      ∑ i, LoccChannel (next i) (TensorGate (ks i) (1 : Operator E) * ρ *
        (TensorGate (ks i) (1 : Operator E))ᴴ)
  | .stepB n ks next, ρ =>
      ∑ i, LoccChannel (next i) (TensorGate (1 : Operator D) (ks i) * ρ *
        (TensorGate (1 : Operator D) (ks i))ᴴ)

/-- The recursive communication charge obtained by adding the ceiling of the base two logarithm
of each outcome count and taking the largest continuation charge. -/
noncomputable def LoccBits : LoccProtocol D E → ℕ
  | .halt => 0
  | .stepA n _ next => Nat.ceil (Real.log ((n : ℝ)) / Real.log 2) +
      Finset.univ.sup fun i => LoccBits (next i)
  | .stepB n _ next => Nat.ceil (Real.log ((n : ℝ)) / Real.log 2) +
      Finset.univ.sup fun i => LoccBits (next i)

/-- The real trace of the branch obtained by applying `K` on the first subsystem. -/
noncomputable def branchMassA (K : Operator D)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : ℝ :=
  (TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E))ᴴ).trace.re

/-- The unnormalized pure branch obtained by applying `K` on the first subsystem. -/
noncomputable def branchStateA (K : Operator D)
    (ψ : QState (Fin D × Fin E)) : QState (Fin D × Fin E) :=
  TensorGate K 1 *ᵥ ψ

/-- The real trace of the branch obtained by applying `K` on the second subsystem. -/
noncomputable def branchMassB (K : Operator E)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : ℝ :=
  (TensorGate (1 : Operator D) K * ρ * (TensorGate (1 : Operator D) K)ᴴ).trace.re

/-- The unnormalized pure branch obtained by applying `K` on the second subsystem. -/
noncomputable def branchStateB (K : Operator E)
    (ψ : QState (Fin D × Fin E)) : QState (Fin D × Fin E) :=
  TensorGate 1 K *ᵥ ψ

/-- The spectral entropy expression `-∑ i, w i * Real.log (w i)` using natural logarithms. -/
noncomputable def SpectrumEntropy (w : Fin D → ℝ) : ℝ :=
  -∑ i, w i * Real.log (w i)

/-- The spectral entropy of the first reduced operator of a pure state, using the supplied
Hermitian witness. -/
noncomputable def entanglementEntropy (ψ : QState (Fin D × Fin E))
    (h : (PartialTrace (outerProduct ψ)).IsHermitian) : ℝ :=
  SpectrumEntropy h.eigenvalues

/-- The list of entries of a finite real vector sorted in descending order. -/
noncomputable def sortedDesc {n : ℕ} (a : Fin n → ℝ) : List ℝ :=
  (Finset.univ.val.map a).toList.mergeSort (fun x y => decide (y < x))

/-- The sum of the first `k` entries of a real list. -/
def prefixSum (l : List ℝ) (k : ℕ) : ℝ := (l.take k).sum

/-- The condition that every descending prefix sum of `b` is bounded by the corresponding prefix
sum of `a`. -/
def Majorizes {n : ℕ} (a b : Fin n → ℝ) : Prop :=
  ∀ k, k ≤ n → prefixSum (sortedDesc b) k ≤ prefixSum (sortedDesc a) k

end Qatlib.Concepts.FiniteLocc.LOCCProgram
