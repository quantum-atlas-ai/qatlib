/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2FiniteSDP
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

def residualBound (_N : ℕ) (ε : ℝ) : ℝ := ε

def hermDefectBound (_N : ℕ) (ε : ℝ) : ℝ := ε

def psdDefectBound (_N : ℕ) (ε : ℝ) : ℝ := ε

noncomputable def objectiveGapBound (N : ℕ) (ε : ℝ) : ℝ := ((N + 1 : ℕ) : ℝ) * ε

noncomputable def traceMassBound (N : ℕ) (ε : ℝ) : ℝ := ((N + 1 : ℕ) : ℝ) * ε

noncomputable def equalityRepairBound (N : ℕ) (ε r : ℝ) : ℝ := ((N + 1 : ℕ) : ℝ) * ε / r

structure RoundedWitness (n k : ℕ) where

  primalTable : Matrix (Fin n) (Fin n) GaussianRational

  dualTable : Fin k → ℚ

  residual : ℚ

  hermDefect : ℚ

  psdDefect : ℚ

  objectiveGap : ℚ

  traceMass : ℚ

noncomputable def roundedHermitianDecode {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational) :
    HermitianMat (Fin n) ℂ :=
  ⟨(1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ), by
    change ((1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ))ᴴ =
      (1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ)
    simp [Matrix.conjTranspose_smul, add_comm]⟩

noncomputable def RoundedWitness.decode {n k : ℕ} (W : RoundedWitness n k) :
    HermitianMat (Fin n) ℂ :=
  roundedHermitianDecode W.primalTable

noncomputable def RoundedWitness.rawDecode {n k : ℕ} (W : RoundedWitness n k) :
    Matrix (Fin n) (Fin n) ℂ :=
  gaussianRationalMatrix W.primalTable

def RoundedWitness.dualDecode {n k : ℕ} (W : RoundedWitness n k) :
    EuclideanSpace ℝ (Fin k) :=
  (WithLp.toLp 2 (fun i => (W.dualTable i : ℝ)) : EuclideanSpace ℝ (Fin k))

noncomputable def traceObjective {n : ℕ} (C X : HermitianMat (Fin n) ℂ) : ℝ :=
  (Matrix.trace (C.mat * X.mat)).re

def epsilonFeasible {n k : ℕ} (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (ε : ℝ) (X : HermitianMat (Fin n) ℂ) : Prop :=
  0 ≤ X + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ) ∧ ‖P.constraint X - P.rhs‖ ≤ ε

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

def RoundedWitness.boundedBy {n k : ℕ} (W : RoundedWitness n k) (N : ℕ) (ε : ℝ) : Prop :=
  (W.residual : ℝ) ≤ residualBound N ε ∧
  (W.hermDefect : ℝ) ≤ hermDefectBound N ε ∧
  (W.psdDefect : ℝ) ≤ psdDefectBound N ε ∧
  (W.objectiveGap : ℝ) ≤ objectiveGapBound N ε ∧
  (W.traceMass : ℝ) ≤ traceMassBound N ε

structure SlaterInterior (n : ℕ) where

  center : HermitianMat (Fin n) ℂ

  radius : ℝ

def SlaterInterior.legal {n k : ℕ} (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (S : SlaterInterior n) : Prop :=
  0 < S.radius ∧ P.PrimalFeasible S.center ∧
    ((S.radius : ℝ) • (1 : HermitianMat (Fin n) ℂ) ≤ S.center)

structure DualSlaterInterior (n k : ℕ) where

  center : EuclideanSpace ℝ (Fin k)

  radius : ℝ

def DualSlaterInterior.legal {n k : ℕ} (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (S : DualSlaterInterior n k) : Prop :=
  0 < S.radius ∧
    ((S.radius : ℝ) • (1 : HermitianMat (Fin n) ℂ) ≤
      P.constraint.adjoint S.center - P.objective)

noncomputable def repairedToExact {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (S : SlaterInterior n) (W : RoundedWitness n k) : Prop :=
  ∃ X : HermitianMat (Fin n) ℂ, P.PrimalFeasible X ∧
    ‖X - W.decode‖ ≤
      equalityRepairBound (n + k)
        (max (W.residual : ℝ) (W.psdDefect : ℝ)) S.radius

noncomputable def regularizedProgram {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) (δ : ℝ) :
    Program (Fin n) (EuclideanSpace ℝ (Fin k)) where
  constraint := P.constraint
  rhs := P.rhs
  objective := P.objective + (δ : ℝ) • (1 : HermitianMat (Fin n) ℂ)

def RoundedWitness.certifiedRegularized {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k)))
    (δ ε : ℝ) (W : RoundedWitness n k) : Prop :=
  RoundedWitness.certified (regularizedProgram P δ) ε W

noncomputable def regularizationLimit {n k : ℕ}
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  (∀ ε : ℚ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∃ W : RoundedWitness n k,
        RoundedWitness.certified (regularizedProgram P δ) (ε : ℝ) W ∧
        epsilonFeasible (regularizedProgram P δ) (ε : ℝ) W.decode) ∧
  Tendsto (fun δ : ℝ => sSup (regularizedProgram P δ).primalValues)
    (𝓝[>] (0 : ℝ)) (𝓝 (sSup P.primalValues))

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

structure RationalSDPInput (n k : ℕ) where

  constraints : Fin k → Matrix (Fin n) (Fin n) GaussianRational

  rhs : Fin k → ℚ

  objective : Matrix (Fin n) (Fin n) GaussianRational

def RationalSDPInput.realizes {n k : ℕ} (I : RationalSDPInput n k)
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  (∀ X : HermitianMat (Fin n) ℂ,
      P.constraint X =
        (WithLp.toLp 2
          (fun i => (Matrix.trace (gaussianRationalMatrix (I.constraints i) * X.mat)).re) :
          EuclideanSpace ℝ (Fin k))) ∧
  (P.rhs = (WithLp.toLp 2 (fun i => (I.rhs i : ℝ)) : EuclideanSpace ℝ (Fin k))) ∧
  (P.objective = roundedHermitianDecode I.objective)

def rationalBitSize (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size

def gaussianRationalBitSize (z : GaussianRational) : ℕ :=
  rationalBitSize z.re + rationalBitSize z.im

def RationalSDPInput.size {n k : ℕ} (I : RationalSDPInput n k) : ℕ :=
  (n + 1) * (n + 1) * (k + 1) + 2 * k +
    (∑ i : Fin k, ∑ r : Fin n, ∑ c : Fin n,
      gaussianRationalBitSize (I.constraints i r c)) +
    (∑ r : Fin n, ∑ c : Fin n, gaussianRationalBitSize (I.objective r c)) +
    (∑ i : Fin k, rationalBitSize (I.rhs i)) + 2

def precisionBits (ε : ℚ) : ℕ := ε.num.natAbs.size + ε.den.size

def callBound (N p : ℕ) : ℕ := 2 ^ (16 + 2 * (N + p))

def bitBound (N p : ℕ) : ℕ := 2 ^ (64 + 4 * (N + p) + (N + p) * (N + p))

def spaceBound (N p : ℕ) : ℕ := 2 ^ (64 + 4 * (N + p) + (N + p) * (N + p))

structure RationalFilteredInstance (X : Type) (n : ℕ) where

  A : Matrix X X GaussianRational

  Z : Fin n → Matrix X X GaussianRational

structure RationalStateConversionInstance (X : Type) (n : ℕ) where

  input : X → Fin n → Bool

  delta : ℚ

  rho : Matrix X X GaussianRational

  sigma : Matrix X X GaussianRational

structure RationalDiamondInstance (D E : ℕ) where

  J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational

structure ProgramTransport {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁]
    [Fintype I₂] [DecidableEq I₂] {F₁ F₂ : Type}
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]
    (P : Program I₁ F₁) (Q : Program I₂ F₂) where

  toPrimal : HermitianMat I₁ ℂ →ₗ[ℝ] HermitianMat I₂ ℂ

  toDual : F₂ →ₗ[ℝ] F₁

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

def diamondConsumerRealizes {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    {N k : ℕ} (P : Program (Fin N) (EuclideanSpace ℝ (Fin k))) : Prop :=
  gaussianRationalMatrix J = MatrixMap.choi_matrix T ∧
  (∃ Tq : ProgramTransport P (diamondProgram T), Tq.legal 0) ∧
  (∃ α : ℝ, finiteDiamondNorm T = ENNReal.ofReal α ∧
    IsLUB (diamondProgram T).primalValues α ∧ IsGLB (diamondProgram T).dualValues α)

structure WitnessGenerator where

  run : (n k : ℕ) → RationalSDPInput n k → ℚ → RoundedWitness n k

  oracleCalls : ℕ → ℕ → ℕ

  bitOps : ℕ → ℕ → ℕ

  peakSpace : ℕ → ℕ → ℕ

def WitnessGenerator.sound (G : WitnessGenerator) : Prop :=
  ∀ (n k : ℕ) (I : RationalSDPInput n k)
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) (ε : ℚ),
    0 < ε → I.realizes P →
    RoundedWitness.certified P (ε : ℝ) (G.run n k I ε) ∧
    RoundedWitness.boundedBy (G.run n k I ε) I.size (ε : ℝ) ∧
    G.oracleCalls I.size (precisionBits ε) ≤ callBound I.size (precisionBits ε) ∧
    G.bitOps I.size (precisionBits ε) ≤ bitBound I.size (precisionBits ε) ∧
    G.peakSpace I.size (precisionBits ε) ≤ spaceBound I.size (precisionBits ε)

def generationDelivers {n k : ℕ} (G : WitnessGenerator) (I : RationalSDPInput n k)
    (P : Program (Fin n) (EuclideanSpace ℝ (Fin k))) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    RoundedWitness.certified P (ε : ℝ) (G.run n k I ε) ∧
    RoundedWitness.boundedBy (G.run n k I ε) I.size (ε : ℝ)

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
