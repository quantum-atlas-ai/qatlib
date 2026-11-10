/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator

section Tensor

variable {κ : Type} [Fintype κ] {s : ℕ}

abbrev RealTensor (κ : Type) [Fintype κ] (s : ℕ) : Type := (Fin s → κ) → ℝ

noncomputable def tensorEval (T : RealTensor κ s) (z : Fin s → κ → ℂ) : ℂ :=
  ∑ i : Fin s → κ, T i * ∏ j, z j (i j)

noncomputable def matProdFin {m : Type} [Fintype m] [DecidableEq m] (s : ℕ)
    (M : Fin s → Matrix m m ℂ) : Matrix m m ℂ :=
  ((List.finRange s).map M).prod

noncomputable def tensorCbNorm (T : RealTensor κ s) : ℝ :=
  sSup {r : ℝ | ∃ (d : ℕ) (A : Fin s → κ → Matrix (Fin d) (Fin d) ℂ),
    (∀ j i, ‖A j i‖ ≤ 1) ∧ r = ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖}

def permTensor (T : RealTensor κ s) (π : Equiv.Perm (Fin s)) : RealTensor κ s :=
  fun i => T (i ∘ π)

def IsSymmTensor (T : RealTensor κ s) : Prop :=
  ∀ π : Equiv.Perm (Fin s), permTensor T π = T

noncomputable def formValue (T : RealTensor κ s) (y : κ → ℝ) : ℝ :=
  ∑ i : Fin s → κ, T i * ∏ j, y (i j)

noncomputable def formCbNorm (T : RealTensor κ s) : ℝ :=
  sInf {c : ℝ | ∃ D : Equiv.Perm (Fin s) → RealTensor κ s,
    (∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ)) ∧
      c = ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ)}

end Tensor

section Sandwich

variable {κ : Type} [Fintype κ] {R : Type} [Fintype R] [DecidableEq R] {s : ℕ}

noncomputable def cbDelta (δ : R → Option κ) (w : κ → ℂ) : Matrix R R ℂ :=
  Matrix.diagonal fun r => match δ r with | none => 1 | some k => w k

noncomputable def cbSandwichMatrix (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (z : Fin s → κ → ℂ) : Matrix R R ℂ :=
  (matProdFin s (fun j => W j.castSucc * cbDelta δ (z j))) * W (Fin.last s)

noncomputable def cbSandwich (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ)
    (u v : QState R) (z : Fin s → κ → ℂ) : ℂ :=
  Inner u ((cbSandwichMatrix W δ z).mulVec v)

def HasCbFactorization (T : RealTensor κ s) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (δ : R → Option κ)
    (u v : QState R) (W : Fin (s + 1) → Matrix R R ℂ),
    Normalized u ∧ Normalized v ∧ (∀ j, ‖W j‖ ≤ 1) ∧
      ∀ z : Fin s → κ → ℂ, tensorEval T z = cbSandwich W δ u v z

end Sandwich

section Model

variable {n : ℕ} {s : ℕ}

def cbPhaseEntry (x : Fin n → Bool) : Option (Fin n ⊕ Fin n) → ℂ
  | none => 1
  | some (Sum.inl i) => if x i then 1 else -1
  | some (Sum.inr _) => 1

noncomputable def cbPhaseOracle {R : Type} [Fintype R] [DecidableEq R]
    (δ : R → Option (Fin n ⊕ Fin n)) (x : Fin n → Bool) : Matrix R R ℂ :=
  Matrix.diagonal fun r => cbPhaseEntry x (δ r)

noncomputable def signBias {R : Type} [Fintype R] [DecidableEq R] (ψ : QState R)
    (E : Finset R) : ℝ :=
  MeasureProb ψ E - MeasureProb ψ Eᶜ

def HasSignAlgorithm (β : (Fin n → Bool) → ℝ) (t : ℕ) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (δ : R → Option (Fin n ⊕ Fin n))
    (C : Circuit R) (ψ : QState R) (E : Finset R),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x : Fin n → Bool, signBias (Run (cbPhaseOracle δ x) C ψ) E = β x

def ComputesBiasOn (D : Finset (Fin n → Bool)) (f : (Fin n → Bool) → ℝ) (ε : ℝ)
    (t : ℕ) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (_ : DecidableEq R) (δ : R → Option (Fin n ⊕ Fin n))
    (C : Circuit R) (ψ : QState R) (E : Finset R),
    IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C ≤ t ∧
      ∀ x ∈ D, |signBias (Run (cbPhaseOracle δ x) C ψ) E - f x| ≤ 2 * ε

def signVecC (x : Fin n → Bool) : (Fin n ⊕ Fin n) → ℂ :=
  Sum.elim (fun i => if x i then 1 else -1) 1

def signVecR (x : Fin n → Bool) : (Fin n ⊕ Fin n) → ℝ :=
  Sum.elim (fun i => if x i then 1 else -1) 1

noncomputable def tensorBias (T : RealTensor (Fin n ⊕ Fin n) s) (x : Fin n → Bool) : ℝ :=
  (tensorEval T (fun _ => signVecC x)).re

noncomputable def formBias (T : RealTensor (Fin n ⊕ Fin n) s) (x : Fin n → Bool) : ℝ :=
  formValue T (signVecR x)

def HasCbFormCertificate (T : RealTensor (Fin n ⊕ Fin n) s) : Prop :=
  ∃ S : RealTensor (Fin n ⊕ Fin n) s,
    HasCbFactorization S ∧ ∀ x : Fin n → Bool, tensorBias S x = formBias T x

noncomputable def cbDeg (D : Finset (Fin n → Bool)) (f : (Fin n → Bool) → ℝ) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | 1 ≤ t ∧ ∃ S : RealTensor (Fin n ⊕ Fin n) (2 * t),
    IsSymmTensor S ∧ formCbNorm S ≤ 1 ∧ ∀ x ∈ D, |formBias S x - f x| ≤ 2 * ε}

end Model

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
