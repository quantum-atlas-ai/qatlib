/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Completely bounded tensors and query biases

This module defines real tensors, ordered matrix substitutions, tensor and form completely
bounded norms, and contraction sandwich factorizations. It also defines a phase query model for
sign biases and the approximation parameter `cbDeg`; background on completely bounded maps and
matrix amplification is given in [Paulsen2002].

## Main statements

* `HasCbFactorization`: represent tensor evaluation by a sandwich of contractions and diagonal
  substitutions.
* `ComputesBiasOn`: express approximation of a Boolean input function by a query circuit's sign
  bias.
* `cbDeg`: take the natural infimum of feasible positive budgets for symmetric completely
  bounded forms.

## References

* [Paulsen, 2002][Paulsen2002]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator

section Tensor

variable {κ : Type} [Fintype κ] {s : ℕ}

/-- A real tensor of order `s`, represented by its coefficients indexed by functions from `Fin
s` to `κ`. -/
abbrev RealTensor (κ : Type) [Fintype κ] (s : ℕ) : Type := (Fin s → κ) → ℝ

/-- Evaluate a real tensor on `s` complex vectors by summing each coefficient times the
corresponding product of coordinates. -/
noncomputable def tensorEval (T : RealTensor κ s) (z : Fin s → κ → ℂ) : ℂ :=
  ∑ i : Fin s → κ, T i * ∏ j, z j (i j)

/-- The ordered product of a family of matrices indexed by `Fin s`. -/
noncomputable def matProdFin {m : Type} [Fintype m] [DecidableEq m] (s : ℕ)
    (M : Fin s → Matrix m m ℂ) : Matrix m m ℂ :=
  ((List.finRange s).map M).prod

/-- The supremum of the operator norms obtained by substituting finite complex contraction
matrices into the ordered tensor expression. -/
noncomputable def tensorCbNorm (T : RealTensor κ s) : ℝ :=
  sSup {r : ℝ | ∃ (d : ℕ) (A : Fin s → κ → Matrix (Fin d) (Fin d) ℂ),
    (∀ j i, ‖A j i‖ ≤ 1) ∧ r = ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖}

/-- Permute the tensor slots by precomposing each coefficient index with `π`. -/
def permTensor (T : RealTensor κ s) (π : Equiv.Perm (Fin s)) : RealTensor κ s :=
  fun i => T (i ∘ π)

/-- The condition that a tensor is invariant under every permutation of its slots. -/
def IsSymmTensor (T : RealTensor κ s) : Prop :=
  ∀ π : Equiv.Perm (Fin s), permTensor T π = T

/-- The real homogeneous form obtained by substituting the same real vector into every tensor
slot. -/
noncomputable def formValue (T : RealTensor κ s) (y : κ → ℝ) : ℝ :=
  ∑ i : Fin s → κ, T i * ∏ j, y (i j)

/-- The infimum of sums of tensor completely bounded norms over decompositions of the
coefficients into permuted component tensors. -/
noncomputable def formCbNorm (T : RealTensor κ s) : ℝ :=
  sInf {c : ℝ | ∃ D : Equiv.Perm (Fin s) → RealTensor κ s,
    (∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ)) ∧
      c = ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ)}

end Tensor

section Sandwich

variable {κ : Type} [Fintype κ] {R : Type} [Fintype R] [DecidableEq R] {s : ℕ}

/-- The diagonal matrix with entry one at unlabelled indices and entry `w k` at indices labelled
by `some k`. -/
noncomputable def cbDelta (δ : R → Option κ) (w : κ → ℂ) : Matrix R R ℂ :=
  Matrix.diagonal fun r => match δ r with | none => 1 | some k => w k

/-- The ordered product of alternating matrices `W` and diagonal coordinate substitutions,
ending with the last matrix `W`. -/
noncomputable def cbSandwichMatrix (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (z : Fin s → κ → ℂ) : Matrix R R ℂ :=
  (matProdFin s (fun j => W j.castSucc * cbDelta δ (z j))) * W (Fin.last s)

/-- The inner product of `u` with the image of `v` under `cbSandwichMatrix`. -/
noncomputable def cbSandwich (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (u v : QState R) (z : Fin s → κ → ℂ) : ℂ :=
  Inner u ((cbSandwichMatrix W δ z).mulVec v)

/-- The existence of a finite matrix sandwich representation of a tensor evaluation using
normalized boundary states and contraction matrices. -/
def HasCbFactorization (T : RealTensor κ s) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (δ : R → Option κ)
    (u v : QState R) (W : Fin (s + 1) → Matrix R R ℂ),
    Normalized u ∧ Normalized v ∧ (∀ j, ‖W j‖ ≤ 1) ∧
      ∀ z : Fin s → κ → ℂ, tensorEval T z = cbSandwich W δ u v z

end Sandwich

section Model

variable {n : ℕ} {s : ℕ}

/-- The oracle phase equal to the input sign at left summand labels and one at right summand or
unlabelled positions. -/
def cbPhaseEntry (x : Fin n → Bool) : Option (Fin n ⊕ Fin n) → ℂ
  | none => 1
  | some (Sum.inl i) => if x i then 1 else -1
  | some (Sum.inr _) => 1

/-- The diagonal phase oracle determined by `cbPhaseEntry` and the coordinate labels `δ`. -/
noncomputable def cbPhaseOracle {R : Type} [Fintype R] [DecidableEq R]
    (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) : Matrix R R ℂ :=
  Matrix.diagonal fun r => cbPhaseEntry x (δ r)

/-- The difference between the probability of an event and the probability of its complement. -/
noncomputable def signBias {R : Type} [Fintype R] [DecidableEq R] (ψ : QState R)
    (E : Finset R) : ℝ :=
  MeasureProb ψ E - MeasureProb ψ Eᶜ

/-- The existence of a unitary phase query circuit with normalized input and at most `t` queries
whose sign bias equals `β` on every input. -/
def HasSignAlgorithm (β : (Fin n → Bool) → ℝ) (t : ℕ) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (δ : R → Option (Fin n ⊕ Fin n))
    (C : Circuit R) (ψ : QState R) (E : Finset R),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x : Fin n → Bool, signBias (Run (cbPhaseOracle δ x) C ψ) E = β x

/-- The existence of a unitary phase query circuit with normalized input and at most `t` queries
whose sign bias differs from `f` by at most 2ε on `D`. -/
def ComputesBiasOn (D : Finset (Fin n → Bool)) (f : (Fin n → Bool) → ℝ) (ε : ℝ)
    (t : ℕ) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (δ : R → Option (Fin n ⊕ Fin n))
    (C : Circuit R) (ψ : QState R) (E : Finset R),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x ∈ D, |signBias (Run (cbPhaseOracle δ x) C ψ) E - f x| ≤ 2 * ε

/-- The complex vector consisting of the Boolean input signs on the left summand and ones on the
right summand. -/
def signVecC (x : Fin n → Bool) : (Fin n ⊕ Fin n) → ℂ :=
  Sum.elim (fun i => if x i then 1 else -1) 1

/-- The real vector consisting of the Boolean input signs on the left summand and ones on the
right summand. -/
def signVecR (x : Fin n → Bool) : (Fin n ⊕ Fin n) → ℝ :=
  Sum.elim (fun i => if x i then 1 else -1) 1

/-- The real part of the tensor evaluation with the Boolean sign vector in every slot. -/
noncomputable def tensorBias (T : RealTensor (Fin n ⊕ Fin n) s) (x : Fin n → Bool) : ℝ :=
  (tensorEval T (fun _ => signVecC x)).re

/-- The real homogeneous form evaluated at the Boolean sign vector. -/
noncomputable def formBias (T : RealTensor (Fin n ⊕ Fin n) s) (x : Fin n → Bool) : ℝ :=
  formValue T (signVecR x)

/-- The existence of a tensor with a completely bounded factorization whose Boolean tensor bias
equals the given form bias. -/
def HasCbFormCertificate (T : RealTensor (Fin n ⊕ Fin n) s) : Prop :=
  ∃ S : RealTensor (Fin n ⊕ Fin n) s,
    HasCbFactorization S ∧ ∀ x : Fin n → Bool, tensorBias S x = formBias T x

/-- The natural infimum of positive budgets `t` for which a symmetric tensor of order 2t has
form completely bounded norm at most one and approximates `f` on `D` within 2ε. -/
noncomputable def cbDeg (D : Finset (Fin n → Bool)) (f : (Fin n → Bool) → ℝ) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | 1 ≤ t ∧ ∃ S : RealTensor (Fin n ⊕ Fin n) (2 * t),
    IsSymmTensor S ∧ formCbNorm S ≤ 1 ∧ ∀ x ∈ D, |formBias S x - f x| ≤ 2 * ε}

end Model

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
