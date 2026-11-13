/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2FiniteSDP
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm

/-!
# Rational SDP witnesses and consumer contracts

This module defines rational SDP inputs, rounded primal and dual data, quantitative
certification predicates, Slater conditions, and objective regularization. `ProgramTransport`
specifies linear maps between primal and dual variables, while the consumer predicates describe
filtered γ₂, state-conversion, and diamond-norm realizations.

`WitnessGenerator.sound` and `diamondEllipsoidBridge` state proposed global contracts; their
definitions do not establish their existence or validity. For semidefinite programming and
diamond-norm background, see [Watrous2018].

## Main statements

* `RoundedWitness.certified`: Error bounds and comparisons with feasible primal and dual scores.
* `slaterOrRegularization`: Primal Slater, dual Slater, or regularization-limit conditions.
* `ProgramTransport.legal`: Feasibility and score-error requirements for primal and dual
  transport.
* `WitnessGenerator.sound`: The universal certification and resource-bound contract for a
  generator.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.DyadicFloor.FloorRounding.Program
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix Filter Topology
open Qatlib.Concepts.DyadicFloor.FloorRounding
open scoped ComplexOrder

/-- The residual tolerance `ε`, independent of the size parameter. -/
def residualBound (_N : ℕ) (ε : ℝ) : ℝ := ε

/-- The Hermitian-defect tolerance `ε`, independent of the size parameter. -/
def hermDefectBound (_N : ℕ) (ε : ℝ) : ℝ := ε

/-- The positivity-defect tolerance `ε`, independent of the size parameter. -/
def psdDefectBound (_N : ℕ) (ε : ℝ) : ℝ := ε

/-- The objective-gap tolerance `(N + 1) * ε`. -/
noncomputable def objectiveGapBound (N : ℕ) (ε : ℝ) : ℝ := ((N + 1 : ℕ) : ℝ) * ε

/-- The trace-mass tolerance `(N + 1) * ε`. -/
noncomputable def traceMassBound (N : ℕ) (ε : ℝ) : ℝ := ((N + 1 : ℕ) : ℝ) * ε

/-- The repair-distance bound `(N + 1) * ε / r`. -/
noncomputable def equalityRepairBound (N : ℕ) (ε r : ℝ) : ℝ := ((N + 1 : ℕ) : ℝ) * ε / r

/-- Rational primal and dual tables together with rational residual, Hermitian-defect,
positivity-defect, objective-gap, and trace-mass data. -/
structure RoundedWitness (n k : ℕ) where

  primalTable : Matrix (Fin n) (Fin n) GaussianRational

  dualTable : Fin k → ℚ

  residual : ℚ

  hermDefect : ℚ

  psdDefect : ℚ

  objectiveGap : ℚ

  traceMass : ℚ

/-- The Hermitian part of the complex embedding of a Gaussian-rational matrix, formed by
averaging it with its conjugate transpose. -/
noncomputable def roundedHermitianDecode {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational) :
    HermitianMat (Fin n) ℂ :=
  ⟨(1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ), by
    change ((1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ))ᴴ =
      (1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ)
    simp [Matrix.conjTranspose_smul, add_comm]⟩

/-- The Hermitian matrix obtained by symmetrizing the complex embedding of the witness's primal
table. -/
noncomputable def RoundedWitness.decode {n k : ℕ} (W : RoundedWitness n k) :
    HermitianMat (Fin n) ℂ :=
  roundedHermitianDecode W.primalTable

/-- The entrywise complex embedding of the witness's primal table before Hermitian
symmetrization. -/
noncomputable def RoundedWitness.rawDecode {n k : ℕ} (W : RoundedWitness n k) :
    Matrix (Fin n) (Fin n) ℂ :=
  gaussianRationalMatrix W.primalTable

/-- The real Euclidean vector obtained by casting the witness's rational dual table
coordinatewise. -/
def RoundedWitness.dualDecode {n k : ℕ} (W : RoundedWitness n k) :
    EuclideanSpace ℝ (Fin k) :=
  (WithLp.toLp 2 (fun i => (W.dualTable i : ℝ)) : EuclideanSpace ℝ (Fin k))

/-- The real part of the trace of the product of two Hermitian matrices. -/
noncomputable def traceObjective {n : ℕ} (C X : HermitianMat (Fin n) ℂ) : ℝ :=
  (Matrix.trace (C.mat * X.mat)).re

/-- The condition that adding `ε` times the identity makes the candidate positive semidefinite
and its equality-constraint residual has norm at most `ε`. -/
def epsilonFeasible {n k : ℕ} (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (ε : ℝ) (X : HermitianMat (Fin n) ℂ) : Prop :=
  0 ≤ X + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ) ∧ ‖P.constraint X - P.rhs‖ ≤ ε

/-- Certification at positive tolerance by nonnegative bounded error data, Hermitian and
positivity defects, residual, trace, objective, and primal-dual gap estimates. It also
requires the decoded scores to approximate the extremal scores of all feasible primal and
dual points. -/
def RoundedWitness.certified {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (ε : ℝ) (W : RoundedWitness n k) : Prop :=
  0 < ε ∧
  0 ≤ W.residual ∧ 0 ≤ W.hermDefect ∧ 0 ≤ W.psdDefect ∧
  0 ≤ W.objectiveGap ∧ 0 ≤ W.traceMass ∧
  (W.residual : ℝ) ≤ residualBound (n + k) ε ∧
  (W.hermDefect : ℝ) ≤ hermDefectBound (n + k) ε ∧
  (W.psdDefect : ℝ) ≤ psdDefectBound (n + k) ε ∧
  (W.objectiveGap : ℝ) ≤ objectiveGapBound (n + k) ε ∧
  (W.traceMass : ℝ) ≤ traceMassBound (n + k) ε ∧
  (∀ i j, ‖W.rawDecode i j - star (W.rawDecode j i)‖ ≤ (W.hermDefect : ℝ)) ∧
  (0 ≤ W.decode + (W.psdDefect : ℝ) • (1 : HermitianMat (Fin n) ℂ)) ∧
  ‖P.constraint W.decode - P.rhs‖ ≤ (W.residual : ℝ) ∧
  |HermitianMat.trace W.decode| ≤ (W.traceMass : ℝ) ∧
  |traceObjective P.objective W.decode| ≤
    ‖P.objective‖ * ((W.traceMass : ℝ) + ((n : ℕ) : ℝ) * (W.psdDefect : ℝ)) ∧
  P.primalScore W.decode ≤ P.dualScore W.dualDecode + (W.objectiveGap : ℝ) ∧
  (∀ X, P.PrimalFeasible X → P.primalScore X ≤ P.primalScore W.decode + ε) ∧
  (∀ y, P.DualFeasible y → P.dualScore W.dualDecode - ε ≤ P.dualScore y)

/-- The five upper bounds on the witness's recorded residual, Hermitian defect, positivity
defect, objective gap, and trace mass at size `N` and tolerance `ε`. -/
def RoundedWitness.boundedBy {n k : ℕ} (W : RoundedWitness n k) (N : ℕ) (ε : ℝ) : Prop :=
  (W.residual : ℝ) ≤ residualBound N ε ∧
  (W.hermDefect : ℝ) ≤ hermDefectBound N ε ∧
  (W.psdDefect : ℝ) ≤ psdDefectBound N ε ∧
  (W.objectiveGap : ℝ) ≤ objectiveGapBound N ε ∧
  (W.traceMass : ℝ) ≤ traceMassBound N ε

/-- A Hermitian candidate for a primal interior point together with a real radius. -/
structure SlaterInterior (n : ℕ) where

  center : HermitianMat (Fin n) ℂ

  radius : ℝ

/-- The condition that the radius is positive, the center is primal feasible, and the center
dominates the radius times the identity. -/
def SlaterInterior.legal {n k : ℕ} (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (S : SlaterInterior n) : Prop :=
  0 < S.radius ∧ P.PrimalFeasible S.center ∧
    ((S.radius : ℝ) • (1 : HermitianMat (Fin n) ℂ) ≤ S.center)

/-- A real Euclidean candidate for a dual interior point together with a real radius. -/
structure DualSlaterInterior (n k : ℕ) where

  center : EuclideanSpace ℝ (Fin k)

  radius : ℝ

/-- The condition that the radius is positive and the dual slack at the center dominates the
radius times the identity. -/
def DualSlaterInterior.legal {n k : ℕ} (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (S : DualSlaterInterior n k) : Prop :=
  0 < S.radius ∧
    ((S.radius : ℝ) • (1 : HermitianMat (Fin n) ℂ) ≤
      P.constraint.adjoint S.center - P.objective)

/-- The existence of an exactly primal-feasible matrix within the specified repair-distance
bound of the decoded witness. -/
noncomputable def repairedToExact {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (S : SlaterInterior n) (W : RoundedWitness n k) : Prop :=
  ∃ X : HermitianMat (Fin n) ℂ, P.PrimalFeasible X ∧
    ‖X - W.decode‖ ≤
      equalityRepairBound (n + k)
        (max (W.residual : ℝ) (W.psdDefect : ℝ)) S.radius

/-- The program obtained by adding `δ` times the identity to the objective while preserving the
constraint map and right-hand side. -/
noncomputable def regularizedProgram {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) (δ : ℝ) :
    Program (Fin n) (EuclideanSpace ℝ (Fin k)) where
  constraint := P.constraint
  rhs := P.rhs
  objective := P.objective + (δ : ℝ) • (1 : HermitianMat (Fin n) ℂ)

/-- Certification of a rounded witness for the program whose objective is shifted by `δ` times
the identity. -/
def RoundedWitness.certifiedRegularized {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (δ ε : ℝ) (W : RoundedWitness n k) : Prop :=
  RoundedWitness.certified (regularizedProgram P δ) ε W

/-- The condition that every positive rational tolerance has a certified approximately feasible
witness for some positive objective regularization, and that regularized primal suprema
converge from the right to the original supremum. -/
noncomputable def regularizationLimit {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  (∀ ε : ℚ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∃ W : RoundedWitness n k,
        RoundedWitness.certified (regularizedProgram P δ) (ε : ℝ) W ∧
        epsilonFeasible (regularizedProgram P δ) (ε : ℝ) W.decode) ∧
  Tendsto (fun δ : ℝ => sSup (regularizedProgram P δ).primalValues)
    (𝓝[>] (0 : ℝ)) (𝓝 (sSup P.primalValues))

/-- The disjunction of a primal Slater condition with dual attainment and witness repair, a dual
Slater condition with primal attainment, or the specified regularization-limit condition. -/
def slaterOrRegularization {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  (∃ S : SlaterInterior n,
    SlaterInterior.legal P S ∧
      (∃ y : EuclideanSpace ℝ (Fin k), P.DualFeasible y) ∧
      (∃ v : ℝ, IsLUB P.primalValues v ∧ IsGLB P.dualValues v ∧
        ∃ y : EuclideanSpace ℝ (Fin k), P.DualFeasible y ∧ P.dualScore y = v) ∧
      (∀ ε : ℚ, 0 < ε → ∀ W : RoundedWitness n k,
        RoundedWitness.certified P (ε : ℝ) W → repairedToExact P S W)) ∨
  (∃ Sd : DualSlaterInterior n k,
    DualSlaterInterior.legal P Sd ∧
      (∃ X₀ : HermitianMat (Fin n) ℂ, P.PrimalFeasible X₀) ∧
      (∃ v : ℝ, IsLUB P.primalValues v ∧ IsGLB P.dualValues v ∧
        ∃ X : HermitianMat (Fin n) ℂ, P.PrimalFeasible X ∧ P.primalScore X = v)) ∨
  regularizationLimit P

/-- A finite SDP input given by Gaussian-rational constraint matrices, a rational right-hand
side, and a Gaussian-rational objective matrix. -/
structure RationalSDPInput (n k : ℕ) where

  constraints : Fin k → Matrix (Fin n) (Fin n) GaussianRational

  rhs : Fin k → ℚ

  objective : Matrix (Fin n) (Fin n) GaussianRational

/-- The condition that the program's constraints are the real trace pairings with the input
matrices, its right-hand side is the cast rational vector, and its objective is the
Hermitian decoding of the input objective. -/
def RationalSDPInput.realizes {n k : ℕ} (I : RationalSDPInput n k)
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  (∀ X : HermitianMat (Fin n) ℂ,
      P.constraint X =
        (WithLp.toLp 2
          (fun i => (Matrix.trace (gaussianRationalMatrix (I.constraints i) * X.mat)).re) :
          EuclideanSpace ℝ (Fin k))) ∧
  (P.rhs = (WithLp.toLp 2 (fun i => (I.rhs i : ℝ)) : EuclideanSpace ℝ (Fin k))) ∧
  (P.objective = roundedHermitianDecode I.objective)

/-- The sum of the binary sizes of a rational number's absolute numerator and denominator. -/
def rationalBitSize (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size

/-- The sum of the rational bit sizes of the real and imaginary parts of a Gaussian-rational
number. -/
def gaussianRationalBitSize (z : GaussianRational) : ℕ :=
  rationalBitSize z.re + rationalBitSize z.im

/-- The input-size measure combining a dimension-dependent overhead with bit sizes of every
constraint, objective, and right-hand-side entry. -/
def RationalSDPInput.size {n k : ℕ} (I : RationalSDPInput n k) : ℕ :=
  (n + 1) * (n + 1) * (k + 1) + 2 * k +
    (∑ i : Fin k, ∑ r : Fin n, ∑ c : Fin n,
      gaussianRationalBitSize (I.constraints i r c)) +
    (∑ r : Fin n, ∑ c : Fin n, gaussianRationalBitSize (I.objective r c)) +
    (∑ i : Fin k, rationalBitSize (I.rhs i)) + 2

/-- The sum of the binary sizes of the absolute numerator and denominator of the rational
precision parameter. -/
def precisionBits (ε : ℚ) : ℕ := ε.num.natAbs.size + ε.den.size

/-- The oracle-call bound `2 ^ (16 + 2 * (N + p))` as a function of input size and precision
size. -/
def callBound (N p : ℕ) : ℕ := 2 ^ (16 + 2 * (N + p))

/-- The bit-operation bound `2 ^ (64 + 4 * (N + p) + (N + p) * (N + p))`. -/
def bitBound (N p : ℕ) : ℕ := 2 ^ (64 + 4 * (N + p) + (N + p) * (N + p))

/-- The peak-space bound `2 ^ (64 + 4 * (N + p) + (N + p) * (N + p))`. -/
def spaceBound (N p : ℕ) : ℕ := 2 ^ (64 + 4 * (N + p) + (N + p) * (N + p))

/-- Gaussian-rational target and filter matrices for a filtered γ₂ instance. -/
structure RationalFilteredInstance (X : Type) (n : ℕ) where

  A : Matrix X X GaussianRational

  Z : Fin n → Matrix X X GaussianRational

/-- A Boolean input encoding, rational tolerance, and Gaussian-rational source and target
matrices for state conversion. -/
structure RationalStateConversionInstance (X : Type) (n : ℕ) where

  input : X → Fin n → Bool

  delta : ℚ

  rho : Matrix X X GaussianRational

  sigma : Matrix X X GaussianRational

/-- A Gaussian-rational candidate Choi matrix for the specified input and output dimensions. -/
structure RationalDiamondInstance (D E : ℕ) where

  J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational

/-- Real-linear maps taking source primal matrices to target primal matrices and target dual
vectors to source dual vectors. -/
structure ProgramTransport {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁]
    [Fintype I₂] [DecidableEq I₂] {F₁ F₂ : Type}
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]
    (P : Program I₁ F₁) (Q : Program I₂ F₂) where

  toPrimal : HermitianMat I₁ ℂ →ₗ[ℝ] HermitianMat I₂ ℂ

  toDual : F₂ →ₗ[ℝ] F₁

/-- The condition that transport preserves primal and dual feasibility in their respective
directions and changes each feasible score by at most the nonnegative error bound. -/
def ProgramTransport.legal {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁]
    [Fintype I₂] [DecidableEq I₂] {F₁ F₂ : Type}
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [CompleteSpace F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [CompleteSpace F₂]
    {P : Program I₁ F₁} {Q : Program I₂ F₂}
    (err : ℝ) (T : ProgramTransport P Q) : Prop :=
  0 ≤ err ∧
  (∀ X : HermitianMat I₁ ℂ, P.PrimalFeasible X →
    Q.PrimalFeasible (T.toPrimal X) ∧
    |Q.primalScore (T.toPrimal X) - P.primalScore X| ≤ err) ∧
  (∀ y : F₂, Q.DualFeasible y →
    P.DualFeasible (T.toDual y) ∧
    |P.dualScore (T.toDual y) - Q.dualScore y| ≤ err)

/-- An exact realization of the filtered γ₂ primal and dual constraints through the supplied
decoders, including surjectivity onto feasible data and the specified negative objective
pairings. -/
def filteredGamma2Realizes {X : Type} [Fintype X] [DecidableEq X] {n N k : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ)
    (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
    (φ : HermitianMat (Fin N) ℂ → Gamma2FixedFamily X n × ℝ)
    (ψ : EuclideanSpace ℝ (Fin k) → (X → ℝ) × (X → ℝ) × Matrix X X ℂ) : Prop :=
  (∀ Xh, P.PrimalFeasible Xh ↔
    ((∀ j, Matrix.PosSemidef ((φ Xh).1 j)) ∧ gamma2SDPImage Z (φ Xh).1 = A ∧
      (∀ z, ∑ j, ((((φ Xh).1) j) z z).re ≤ (φ Xh).2))) ∧
  (∀ Xh, P.PrimalFeasible Xh → P.primalScore Xh = -((φ Xh).2)) ∧
  (∀ (B : Gamma2FixedFamily X n) (t : ℝ),
    ((∀ j, Matrix.PosSemidef (B j)) ∧ gamma2SDPImage Z B = A ∧
        (∀ z, ∑ j, (B j z z).re ≤ t)) →
    ∃ Xh, P.PrimalFeasible Xh ∧ φ Xh = (B, t)) ∧
  (∀ y, P.DualFeasible y ↔
    ((∀ x, 0 ≤ (ψ y).1 x) ∧ (∀ x, 0 ≤ (ψ y).2.1 x) ∧
      (∀ j, Matrix.PosSemidef (gamma2SDPDualBlock (ψ y).1 (ψ y).2.1 (Z j) (ψ y).2.2)) ∧
      (∑ x, (ψ y).1 x) + (∑ x, (ψ y).2.1 x) ≤ 1)) ∧
  (∀ y, P.DualFeasible y → P.dualScore y = -(gamma2SDPPairing A (ψ y).2.2)) ∧
  (∀ (a b : X → ℝ) (Nm : Matrix X X ℂ),
    (∀ x, 0 ≤ a x) → (∀ x, 0 ≤ b x) →
      (∀ j, Matrix.PosSemidef (gamma2SDPDualBlock a b (Z j) Nm)) →
      (∑ x, a x) + (∑ x, b x) ≤ 1 →
      ∃ y, P.DualFeasible y ∧ ψ y = (a, b, Nm))

/-- A realization of state-conversion primal feasibility and its negative cost through the
supplied decoder, with coverage of feasible data and both stated comparisons to the
state-conversion value. -/
def stateConversionRealizes {X : Type} [Fintype X] [DecidableEq X] {n N k : ℕ}
    (input : X → Fin n → Bool) (δ : ℝ) (ρ σ : Matrix X X ℂ)
    (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
    (φ : HermitianMat (Fin N) ℂ → Matrix X X ℂ × Gamma2FixedFamily X n × ℝ) : Prop :=
  (∀ Xh, P.PrimalFeasible Xh ↔
    (Matrix.PosSemidef (φ Xh).1 ∧
      gramFilteredCert ((φ Xh).1 - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ ∧
      (∀ j, Matrix.PosSemidef ((φ Xh).2.1 j)) ∧
      gamma2SDPImage (gramFilterDelta input) (φ Xh).2.1 = ρ - (φ Xh).1 ∧
      (∀ z, ∑ j, ((((φ Xh).2.1) j) z z).re ≤ (φ Xh).2.2))) ∧
  (∀ Xh, P.PrimalFeasible Xh → P.primalScore Xh = -((φ Xh).2.2)) ∧
  (∀ (σ' : Matrix X X ℂ) (B : Gamma2FixedFamily X n) (t : ℝ),
    Matrix.PosSemidef σ' →
      gramFilteredCert (σ' - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ →
      (∀ j, Matrix.PosSemidef (B j)) →
      gamma2SDPImage (gramFilterDelta input) B = ρ - σ' →
      (∀ z, ∑ j, (B j z z).re ≤ t) →
      ∃ Xh, P.PrimalFeasible Xh ∧ φ Xh = (σ', B, t)) ∧
  (∀ W : ℝ, (stateConversionSDP input δ ρ σ) < ENNReal.ofReal W →
    ∃ Xh, P.PrimalFeasible Xh ∧ -(P.primalScore Xh) < W) ∧
  (∀ Xh, P.PrimalFeasible Xh →
    (stateConversionSDP input δ ρ σ) ≤ ENNReal.ofReal (-P.primalScore Xh))

/-- A score-preserving correspondence between a fixed intermediate-state layer and a filtered γ₂
program, together with the stated value characterization and state-conversion upper bound. -/
def stateConversionLayerTransport {X : Type} [Fintype X] [DecidableEq X]
    {n N k N' k' : ℕ}
    (input : X → Fin n → Bool) (δ : ℝ) (ρ σ σ' : Matrix X X ℂ)
    (P : Program (Fin N) (EuclideanSpace ℝ (Fin k)))
    (φ : HermitianMat (Fin N) ℂ → Matrix X X ℂ × Gamma2FixedFamily X n × ℝ)
    (P' : Program (Fin N') (EuclideanSpace ℝ (Fin k')))
    (φ' : HermitianMat (Fin N') ℂ → Gamma2FixedFamily X n × ℝ) : Prop :=
  (∀ Xh, P.PrimalFeasible Xh → (φ Xh).1 = σ' →
    ∃ Xh', P'.PrimalFeasible Xh' ∧
      φ' Xh' = ((φ Xh).2.1, (φ Xh).2.2) ∧
      P'.primalScore Xh' = P.primalScore Xh) ∧
  (∀ Xh', P'.PrimalFeasible Xh' →
    ∃ Xh, P.PrimalFeasible Xh ∧ (φ Xh).1 = σ' ∧
      φ Xh = (σ', (φ' Xh').1, (φ' Xh').2) ∧
      P.primalScore Xh = P'.primalScore Xh') ∧
  (∀ W : ℝ,
    (filteredGamma2 (ρ - σ') (gramFilterDelta input)) < ENNReal.ofReal W ↔
      ∃ Xh', P'.PrimalFeasible Xh' ∧ -(P'.primalScore Xh') < W) ∧
  (Matrix.PosSemidef σ' →
    gramFilteredCert (σ' - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ →
    (stateConversionSDP input δ ρ σ) ≤
      filteredGamma2 (ρ - σ') (gramFilterDelta input))

/-- The condition that the rational matrix is the map's Choi matrix, a zero-error program
transport to its diamond SDP exists, and a real diamond-norm representative is the common
primal and dual optimal value. -/
def diamondConsumerRealizes {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    {N k : ℕ} (P : Program (Fin N) (EuclideanSpace ℝ (Fin k))) : Prop :=
  gaussianRationalMatrix J = MatrixMap.choi_matrix T ∧
  (∃ Tq : ProgramTransport P (diamondProgram T), Tq.legal 0) ∧
  (∃ α : ℝ, finiteDiamondNorm T = ENNReal.ofReal α ∧
    IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α)

/-- A procedure producing rounded witnesses from rational SDP inputs and tolerances, together
with oracle-call, bit-operation, and peak-space count functions. -/
structure WitnessGenerator where

  run : (n k : ℕ) → RationalSDPInput n k → ℚ → RoundedWitness n k

  oracleCalls : ℕ → ℕ → ℕ

  bitOps : ℕ → ℕ → ℕ

  peakSpace : ℕ → ℕ → ℕ

/-- The universal requirement that every realized rational SDP input at positive rational
tolerance yields a certified, size-bounded witness and resource counts below the stated
bounds. -/
def WitnessGenerator.sound (G : WitnessGenerator) : Prop :=
  ∀ (n k : ℕ) (I : RationalSDPInput n k)
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) (ε : ℚ),
    0 < ε → I.realizes P →
    RoundedWitness.certified P (ε : ℝ) (G.run n k I ε) ∧
    RoundedWitness.boundedBy (G.run n k I ε) I.size (ε : ℝ) ∧
    G.oracleCalls I.size (precisionBits ε) ≤ callBound I.size (precisionBits ε) ∧
    G.bitOps I.size (precisionBits ε) ≤ bitBound I.size (precisionBits ε) ∧
    G.peakSpace I.size (precisionBits ε) ≤ spaceBound I.size (precisionBits ε)

/-- The requirement that the generator produce certified, size-bounded witnesses for the
specified input and program at every positive rational tolerance. -/
def generationDelivers {n k : ℕ} (G : WitnessGenerator) (I : RationalSDPInput n k)
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    RoundedWitness.certified P (ε : ℝ) (G.run n k I ε) ∧
    RoundedWitness.boundedBy (G.run n k I ε) I.size (ε : ℝ)

/-- The requirement that every positive rational tolerance and rational threshold yield a
noninvalid ellipsoid outcome, with either a decoded dual-feasible threshold certificate or
the stated exhausted-outcome comparison for every real diamond-norm representative. -/
def diamondEllipsoidBridge {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∀ γ : ℚ,
    (diamondEllipsoidSolve J γ ε).outcome ≠ EllipsoidRunOutcome.invalid ∧
    (((diamondEllipsoidSolve J γ ε).outcome = EllipsoidRunOutcome.feasible ∧
        (diamondProgram T).DualFeasible
          (diamondRationalDecode (diamondEllipsoidSolve J γ ε).state.center) ∧
        (diamondProgram T).dualScore
          (diamondRationalDecode (diamondEllipsoidSolve J γ ε).state.center) ≤ (γ : ℝ)) ∨
      ((diamondEllipsoidSolve J γ ε).outcome = EllipsoidRunOutcome.exhausted ∧
        ∀ α : ℝ, finiteDiamondNorm T = ENNReal.ofReal α → (γ : ℝ) < α + (ε : ℝ)))

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
