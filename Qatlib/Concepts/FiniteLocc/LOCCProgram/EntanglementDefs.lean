/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Matrix

variable {D E : ℕ}

def bipartiteMatrix (ψ : QState (Fin D × Fin E)) : Matrix (Fin D) (Fin E) ℂ :=
  Matrix.of fun i j => ψ (i, j)

noncomputable def schmidtRank (ψ : QState (Fin D × Fin E)) : ℕ := (bipartiteMatrix ψ).rank

def IsProductState (ψ : QState (Fin D × Fin E)) : Prop :=
  ∃ (a : QState (Fin D)) (b : QState (Fin E)), ψ = TensorState a b

def IsEntangled (ψ : QState (Fin D × Fin E)) : Prop :=
  Normalized ψ ∧ ¬ IsProductState ψ

noncomputable def bell (s : Bool × Bool) : QState (Fin 2 × Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (Ket ((⟨0, by omega⟩ : Fin 2), if s.1 then (1 : Fin 2) else 0) +
      (if s.2 then (-1 : ℂ) else 1) •
        Ket ((⟨1, by omega⟩ : Fin 2), if !s.1 then (1 : Fin 2) else 0))

def PartialTranspose (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  Matrix.of fun p q => A (p.1, q.2) (q.1, p.2)

def IsSeparableState (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (a : Fin n → QState (Fin D)) (b : Fin n → QState (Fin E)),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, Normalized (a i)) ∧ (∀ i, Normalized (b i)) ∧
      ρ = ∑ i, (p i : ℂ) • outerProduct (TensorState (a i) (b i))

def IsSeparableMixed (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Operator D) (τ : Fin n → Operator E),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, IsDensityOperator (σ i)) ∧
      (∀ i, IsDensityOperator (τ i)) ∧ ρ = ∑ i, (p i : ℂ) • TensorGate (σ i) (τ i)

def IsKrausList (ks : List (Operator D)) : Prop :=
  (ks.map fun K => Kᴴ * K).sum = 1

noncomputable def ApplyFirstKraus (ks : List (Operator D))
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  (ks.map fun K => TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E))ᴴ).sum

inductive LoccProtocol (D E : ℕ) : Type
  | halt : LoccProtocol D E
  | stepA (n : ℕ) (ks : Fin n → Operator D)
    (next : Fin n → LoccProtocol D E) : LoccProtocol D E
  | stepB (n : ℕ) (ks : Fin n → Operator E)
    (next : Fin n → LoccProtocol D E) : LoccProtocol D E

def LoccComplete : LoccProtocol D E → Prop
  | .halt => True
  | .stepA n ks next => (∑ i, (ks i)ᴴ * ks i = 1) ∧ ∀ i, LoccComplete (next i)
  | .stepB n ks next => (∑ i, (ks i)ᴴ * ks i = 1) ∧ ∀ i, LoccComplete (next i)

noncomputable def LoccChannel : LoccProtocol D E →
    Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ
  | .halt, ρ => ρ
  | .stepA n ks next, ρ =>
      ∑ i, LoccChannel (next i) (TensorGate (ks i) (1 : Operator E) * ρ *
        (TensorGate (ks i) (1 : Operator E))ᴴ)
  | .stepB n ks next, ρ =>
      ∑ i, LoccChannel (next i) (TensorGate (1 : Operator D) (ks i) * ρ *
        (TensorGate (1 : Operator D) (ks i))ᴴ)

noncomputable def LoccBits : LoccProtocol D E → ℕ
  | .halt => 0
  | .stepA n _ next => Nat.ceil (Real.log ((n : ℝ)) / Real.log 2) +
      Finset.univ.sup fun i => LoccBits (next i)
  | .stepB n _ next => Nat.ceil (Real.log ((n : ℝ)) / Real.log 2) +
      Finset.univ.sup fun i => LoccBits (next i)

noncomputable def branchMassA (K : Operator D)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : ℝ :=
  (TensorGate K (1 : Operator E) * ρ * (TensorGate K (1 : Operator E))ᴴ).trace.re

noncomputable def branchStateA (K : Operator D)
    (ψ : QState (Fin D × Fin E)) : QState (Fin D × Fin E) :=
  TensorGate K 1 *ᵥ ψ

noncomputable def branchMassB (K : Operator E)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : ℝ :=
  (TensorGate (1 : Operator D) K * ρ * (TensorGate (1 : Operator D) K)ᴴ).trace.re

noncomputable def branchStateB (K : Operator E)
    (ψ : QState (Fin D × Fin E)) : QState (Fin D × Fin E) :=
  TensorGate 1 K *ᵥ ψ

noncomputable def SpectrumEntropy (w : Fin D → ℝ) : ℝ :=
  -∑ i, w i * Real.log (w i)

noncomputable def entanglementEntropy (ψ : QState (Fin D × Fin E))
    (h : (PartialTrace (outerProduct ψ)).IsHermitian) : ℝ :=
  SpectrumEntropy h.eigenvalues

noncomputable def sortedDesc {n : ℕ} (a : Fin n → ℝ) : List ℝ :=
  (Finset.univ.val.map a).toList.mergeSort (fun x y => decide (y < x))

def prefixSum (l : List ℝ) (k : ℕ) : ℝ := (l.take k).sum

def Majorizes {n : ℕ} (a b : Fin n → ℝ) : Prop :=
  ∀ k, k ≤ n → prefixSum (sortedDesc b) k ≤ prefixSum (sortedDesc a) k

end Qatlib.Concepts.FiniteLocc.LOCCProgram
