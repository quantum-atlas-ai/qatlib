/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
import Mathlib.Analysis.Normed.Algebra.Exponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.Amplification

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def prepareAccess {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (UA UB : Matrix H H ℂ)
    (L : Matrix H I ℂ) (ω : QState H) (ψ : QState I) (αA : ℝ) : Prop :=
  0 < αA ∧ ‖A‖ ≤ αA ∧ ProjectedUnitaryEncoding ((αA : ℂ)⁻¹ • A) UA L L ∧
  UB ∈ Matrix.unitaryGroup H ℂ ∧ UB *ᵥ ω=L *ᵥ ψ ∧ Normalized ψ

def realSpectrum {I : Type} [Fintype I] [DecidableEq I]
    (A S : Matrix I I ℂ) (lam : I → ℝ) (κ : ℝ) : Prop :=
  S*S⁻¹=1 ∧ S⁻¹*S=1 ∧ A=S*Matrix.diagonal (fun i =>  (lam i : ℂ))*S⁻¹ ∧
  (∀ i, Normalized (fun j =>  S j i)) ∧ 1 ≤ κ ∧ ‖S‖*‖S⁻¹‖ ≤ κ

def expAction {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) (ψ : QState I) : QState I :=
  NormedSpace.exp ((t : ℂ) • A) *ᵥ ψ

def odeBPrice (αexp αb : ℝ) : ℝ := αexp/αb
def odeAPrice (αA t αexp αbmax αb ε : ℝ) : ℝ :=
  (αbmax/αb)*αexp*(if t=0 then 0 else max 1 (αA*t))*logPrice (αexp/αb)*
    logPrice (logPrice (αexp/αb)/ε)*logPrice (αA*t/ε)

def chebT (x : ℝ) : ℕ → ℝ
  | 0 =>  1
  | 1 =>  x
  | k+2 =>  2*x*chebT x (k+1)-chebT x k

def chebMatrix {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 =>  1
  | 1 =>  A
  | k+2 =>  (2 : ℂ) • (A*chebMatrix A (k+1))-chebMatrix A k

def chebValue {n : ℕ} (c : Fin n → ℂ) (x : ℝ) : ℂ :=
  ∑ k, c k * (if k.val=0 then (1/2 : ℂ) else (chebT x k.val : ℂ))

def chebOperator {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (c : Fin n → ℂ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ k, c k • (if k.val=0 then (1/2 : ℂ) • 1 else chebMatrix A k.val)

def polynomialSup {n : ℕ} (c : Fin n → ℂ) (a : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, -a ≤ x ∧ x ≤ a ∧ y=‖chebValue c x‖}

def extendCoefficient {n : ℕ} (c : Fin n → ℂ) (k : ℕ) : ℂ :=
  if h : k < n then c ⟨k,h⟩ else 0

def differenceNorm {n : ℕ} (c : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ k : Fin n, ‖c k-extendCoefficient c (k.val+2)‖^2)

def polynomialBPrice (n : ℕ) (P κ α : ℝ) : ℝ := P*κ*logPrice n/α
def polynomialAPrice (n : ℕ) (P κ α ε : ℝ) : ℝ :=
  P*κ^2*n*logPrice n/α*logPrice (P*κ*logPrice n/α)*
    logPrice (logPrice (P*κ*logPrice n/α)/ε)
def groundDegreePrice (αA δ κ g ε : ℝ) : ℝ := αA/δ*logPrice (κ/(g*ε))
def groundBPrice (αA δ κ g ε : ℝ) : ℝ := κ/g*logPrice (groundDegreePrice αA δ κ g ε)

def groundAPrice (d : ℕ) (αA δ κ g ε : ℝ) : ℝ :=
  κ^2/g*αA/δ*(logPrice (groundDegreePrice αA δ κ g ε))^d
def blockPolynomialPrice (n : ℕ) (P κ α ε : ℝ) : ℝ :=
  P*n*κ^2/α*logPrice (P*κ/(α*ε))*logPrice (1/ε)

def measuredEstimateMass {H : Type} [Fintype H] {r : ℕ}
    (decode : Fin r → ℝ) (ψ : QState (Space H r)) (truth c : ℝ) : ℝ :=
  ∑ k : Fin r, if decode k/c < truth ∧ truth < c*decode k then
    normVec (fun h =>  ψ (h,k))^2 else 0

def eigenEstimateMass {H : Type} [Fintype H] {r : ℕ}
    (decode : Fin r → ℝ) (ψ : QState (Space H r)) (truth ε : ℝ) : ℝ :=
  ∑ k : Fin r, if abs (decode k-truth) ≤ ε then normVec (fun h =>  ψ (h,k))^2 else 0

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
