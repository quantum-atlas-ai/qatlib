/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Models for walk-based linear-algebra applications

This module defines preparation access and real-spectrum hypotheses, Chebyshev scalar and matrix
evaluation, and the coefficient-difference norm used in polynomial bounds. It also records
resource-price expressions for differential equations, polynomial processing, and ground-state
preparation, together with readout event masses. Related mathematical background is given in
[LowSu2026].

## Main statements

* `prepareAccess`: Block-encoding and input-preparation conditions.
* `chebValue`: Chebyshev evaluation with a half-weighted constant coefficient.
* `differenceNorm`: Euclidean norm of coefficient differences two indices apart.

## References

* [Low and Su, 2026][LowSu2026]
-/

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

/-- The preparation-access condition combining a positive matrix-norm bound, a projected unitary
encoding of the scaled matrix, and a unitary preparation of the embedded normalized input. -/
def prepareAccess {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (UA UB : Matrix H H ℂ)
    (L : Matrix H I ℂ) (ω : QState H) (ψ : QState I) (αA : ℝ) : Prop :=
  0 < αA ∧ ‖A‖ ≤ αA ∧ ProjectedUnitaryEncoding ((αA : ℂ)⁻¹ • A) UA L L ∧
  UB ∈ Matrix.unitaryGroup H ℂ ∧ UB *ᵥ ω=L *ᵥ ψ ∧ Normalized ψ

/-- The condition that `A` has a real diagonalization by an invertible matrix with normalized
columns and condition-number bound `κ ≥ 1`. -/
def realSpectrum {I : Type} [Fintype I] [DecidableEq I]
    (A S : Matrix I I ℂ) (lam : I → ℝ) (κ : ℝ) : Prop :=
  S*S⁻¹=1 ∧ S⁻¹*S=1 ∧ A=S*Matrix.diagonal (fun i =>  (lam i : ℂ))*S⁻¹ ∧
  (∀ i, Normalized (fun j =>  S j i)) ∧ 1 ≤ κ ∧ ‖S‖*‖S⁻¹‖ ≤ κ

/-- The action of the matrix exponential of `t` times `A` on the state `ψ`. -/
def expAction {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) (ψ : QState I) : QState I :=
  NormedSpace.exp ((t : ℂ) • A) *ᵥ ψ

/-- The input-preparation price ratio `αexp / αb` for the differential-equation model. -/
def odeBPrice (αexp αb : ℝ) : ℝ := αexp/αb
/-- The matrix-oracle price expression for the differential-equation model, including its
normalization, time, and logarithmic precision factors. -/
def odeAPrice (αA t αexp αbmax αb ε : ℝ) : ℝ :=
  (αbmax/αb)*αexp*(if t=0 then 0 else max 1 (αA*t))*logPrice (αexp/αb)*
    logPrice (logPrice (αexp/αb)/ε)*logPrice (αA*t/ε)

/-- The first-kind Chebyshev polynomials evaluated at `x`, defined by their three-term
recurrence. -/
def chebT (x : ℝ) : ℕ → ℝ
  | 0 =>  1
  | 1 =>  x
  | k+2 =>  2*x*chebT x (k+1)-chebT x k

/-- The matrix-valued first-kind Chebyshev recurrence with initial terms the identity and `A`. -/
def chebMatrix {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 =>  1
  | 1 =>  A
  | k+2 =>  (2 : ℂ) • (A*chebMatrix A (k+1))-chebMatrix A k

/-- The finite Chebyshev expansion with the constant coefficient weighted by one half. -/
def chebValue {n : ℕ} (c : Fin n → ℂ) (x : ℝ) : ℂ :=
  ∑ k, c k * (if k.val=0 then (1/2 : ℂ) else (chebT x k.val : ℂ))

/-- The matrix Chebyshev expansion with the constant coefficient multiplying half the identity. -/
def chebOperator {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (c : Fin n → ℂ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ k, c k • (if k.val=0 then (1/2 : ℂ) • 1 else chebMatrix A k.val)

/-- The supremum of the norm of the Chebyshev expansion over the interval from `-a` to `a`. -/
def polynomialSup {n : ℕ} (c : Fin n → ℂ) (a : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, -a ≤ x ∧ x ≤ a ∧ y=‖chebValue c x‖}

/-- The extension of a finite coefficient vector to natural indices by zero outside its range. -/
def extendCoefficient {n : ℕ} (c : Fin n → ℂ) (k : ℕ) : ℂ :=
  if h : k < n then c ⟨k,h⟩ else 0

/-- The square root of the sum of squared norms of the differences between each coefficient and
the coefficient two indices later, using zero extension. -/
def differenceNorm {n : ℕ} (c : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ k : Fin n, ‖c k-extendCoefficient c (k.val+2)‖^2)

/-- The input-preparation price `P * κ * logPrice n / α` for polynomial processing. -/
def polynomialBPrice (n : ℕ) (P κ α : ℝ) : ℝ := P*κ*logPrice n/α
/-- The matrix-oracle price expression for polynomial processing with the specified degree,
conditioning, normalization, and precision factors. -/
def polynomialAPrice (n : ℕ) (P κ α ε : ℝ) : ℝ :=
  P*κ^2*n*logPrice n/α*logPrice (P*κ*logPrice n/α)*
    logPrice (logPrice (P*κ*logPrice n/α)/ε)
/-- The ground-state polynomial degree price `αA / δ * logPrice (κ / (g * ε))`. -/
def groundDegreePrice (αA δ κ g ε : ℝ) : ℝ := αA/δ*logPrice (κ/(g*ε))
/-- The ground-state input-preparation price obtained from `κ / g` times the logarithmic degree
price. -/
def groundBPrice (αA δ κ g ε : ℝ) : ℝ := κ/g*logPrice (groundDegreePrice αA δ κ g ε)

/-- The ground-state matrix-oracle price with conditioning and gap factors and the `d`th power
of the logarithmic degree price. -/
def groundAPrice (d : ℕ) (αA δ κ g ε : ℝ) : ℝ :=
  κ^2/g*αA/δ*(logPrice (groundDegreePrice αA δ κ g ε))^d
/-- The block-polynomial price expression with degree, conditioning, normalization, and
logarithmic precision factors. -/
def blockPolynomialPrice (n : ℕ) (P κ α ε : ℝ) : ℝ :=
  P*n*κ^2/α*logPrice (P*κ/(α*ε))*logPrice (1/ε)

/-- The total squared branch norm over decoded estimates satisfying `decode k / c < truth < c *
decode k`. -/
def measuredEstimateMass {H : Type} [Fintype H] {r : ℕ}
    (decode : Fin r → ℝ) (ψ : QState (Space H r)) (truth c : ℝ) : ℝ :=
  ∑ k : Fin r, if decode k/c < truth ∧ truth < c*decode k then
    normVec (fun h =>  ψ (h,k))^2 else 0

/-- The total squared branch norm over decoded estimates within additive error `ε` of `truth`. -/
def eigenEstimateMass {H : Type} [Fintype H] {r : ℕ}
    (decode : Fin r → ℝ) (ψ : QState (Space H r)) (truth ε : ℝ) : ℝ :=
  ∑ k : Fin r, if abs (decode k-truth) ≤ ε then normVec (fun h =>  ψ (h,k))^2 else 0

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
