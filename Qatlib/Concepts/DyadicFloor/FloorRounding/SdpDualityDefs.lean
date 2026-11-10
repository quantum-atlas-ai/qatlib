/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.Proj
import QuantumInfo.ForMathlib.HermitianMat.Sqrt
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Group.Uniform
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import QuantumInfo.Channels.MatrixMap
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import Init.Data.BitVec.Lemmas
import Mathlib.Algebra.QuadraticAlgebra.Basic
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.DyadicFloor.FloorRounding
open Matrix
open scoped InnerProductSpace ComplexOrder ENNReal

def psdCone (I : Type*) [Fintype I] [DecidableEq I] :
    ProperCone ℝ (HermitianMat I ℂ) := ProperCone.positive ℝ _

structure Program (I F : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  constraint : HermitianMat I ℂ →L[ℝ] F
  rhs : F
  objective : HermitianMat I ℂ

namespace Program
variable {I F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def PrimalFeasible (P : Program I F) (X : HermitianMat I ℂ) : Prop :=
  0 ≤ X ∧ P.constraint X = P.rhs

def DualFeasible (P : Program I F) (y : F) : Prop :=
  0 ≤ P.constraint.adjoint y - P.objective

def primalScore (P : Program I F) (X : HermitianMat I ℂ) : ℝ := ⟪P.objective, X⟫_ℝ

def dualScore (P : Program I F) (y : F) : ℝ := ⟪P.rhs, y⟫_ℝ

def primalValues (P : Program I F) : Set ℝ := P.primalScore '' {X | P.PrimalFeasible X}

def dualValues (P : Program I F) : Set ℝ := P.dualScore '' {y | P.DualFeasible y}

def primalSuperlevel (P : Program I F) (a : ℝ) : Set (HermitianMat I ℂ) :=
  {X | P.PrimalFeasible X ∧ a ≤ P.primalScore X}

def PrimalSlater (P : Program I F) : Prop :=
  ∃ X : HermitianMat I ℂ, X.mat.PosDef ∧ P.constraint X = P.rhs

def DualSlater (P : Program I F) : Prop :=
  ∃ y : F, (P.constraint.adjoint y - P.objective).mat.PosDef

def perturbationMap (P : Program I F) : (HermitianMat I ℂ × ℝ) →L[ℝ] (F × ℝ) :=
  (P.constraint.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((innerSL ℝ P.objective).comp (ContinuousLinearMap.fst ℝ _ _) -
      ContinuousLinearMap.snd ℝ _ _)

def dualSlackProgram (P : Program I F) (X₀ : HermitianMat I ℂ) :
    Program I (LinearMap.ker P.constraint.toLinearMap) where
  constraint := (LinearMap.ker P.constraint.toLinearMap).orthogonalProjection
  rhs := -(LinearMap.ker P.constraint.toLinearMap).orthogonalProjection P.objective
  objective := -X₀

end Program

def blockDiagonal {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  ⟨Matrix.fromBlocks P.mat 0 0 Q.mat,
    Matrix.IsHermitian.fromBlocks P.H (by simp) Q.H⟩

def offDiagonal {I : Type*} [Fintype I] (X : Matrix I I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  ⟨Matrix.fromBlocks 0 X Xᴴ 0,
    Matrix.IsHermitian.fromBlocks (by simp) rfl (by simp)⟩

def blockPinch {I : Type*} [Fintype I] : HermitianMat (I ⊕ I) ℂ →L[ℝ] HermitianMat (I ⊕ I) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ⟨fun r c => match r, c with
        | Sum.inl i, Sum.inl j => X.mat (Sum.inl i) (Sum.inl j)
        | Sum.inr i, Sum.inr j => X.mat (Sum.inr i) (Sum.inr j)
        | _, _ => 0,
        by
          ext r c
          cases r <;> cases c
          · exact X.H.apply _ _
          · change star (0 : ℂ) = 0; exact star_zero ℂ
          · change star (0 : ℂ) = 0; exact star_zero ℂ
          · exact X.H.apply _ _⟩
      map_add' := by
        intro X Y
        apply HermitianMat.ext
        ext r c
        change (match r, c with
          | Sum.inl i, Sum.inl j => X.mat (Sum.inl i) (Sum.inl j) + Y.mat (Sum.inl i) (Sum.inl j)
          | Sum.inr i, Sum.inr j => X.mat (Sum.inr i) (Sum.inr j) + Y.mat (Sum.inr i) (Sum.inr j)
          | _, _ => 0) = (match r, c with
          | Sum.inl i, Sum.inl j => X.mat (Sum.inl i) (Sum.inl j)
          | Sum.inr i, Sum.inr j => X.mat (Sum.inr i) (Sum.inr j)
          | _, _ => 0) + (match r, c with
          | Sum.inl i, Sum.inl j => Y.mat (Sum.inl i) (Sum.inl j)
          | Sum.inr i, Sum.inr j => Y.mat (Sum.inr i) (Sum.inr j)
          | _, _ => 0)
        cases r <;> cases c <;> simp only [add_zero]
      map_smul' := by
        intro t X
        apply HermitianMat.ext
        ext r c
        change (match r, c with
          | Sum.inl i, Sum.inl j => t • X.mat (Sum.inl i) (Sum.inl j)
          | Sum.inr i, Sum.inr j => t • X.mat (Sum.inr i) (Sum.inr j)
          | _, _ => 0) = t • (match r, c with
          | Sum.inl i, Sum.inl j => X.mat (Sum.inl i) (Sum.inl j)
          | Sum.inr i, Sum.inr j => X.mat (Sum.inr i) (Sum.inr j)
          | _, _ => 0)
        cases r <;> cases c <;> simp only [smul_zero] }

def fidelityProgram {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : Program (I ⊕ I) (HermitianMat (I ⊕ I) ℂ) where
  constraint := blockPinch
  rhs := blockDiagonal P Q
  objective := (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)

def fidelityPrimalBlock {I : Type*} [Fintype I]
    (P Q : HermitianMat I ℂ) (X : Matrix I I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  ⟨Matrix.fromBlocks P.mat X Xᴴ Q.mat, Matrix.IsHermitian.fromBlocks P.H rfl Q.H⟩

def fidelityDualBlock {I : Type*} [Fintype I] [DecidableEq I]
    (Y Z : HermitianMat I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  blockDiagonal Y Z - offDiagonal (1 : Matrix I I ℂ)

def principalBlock {I J : Type*} [Fintype I] [Fintype J]
    (X : HermitianMat J ℂ) (e : I → J) : HermitianMat I ℂ :=
  ⟨X.mat.submatrix e e, X.H.submatrix e⟩

def fidelityPrimalValues {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ) : Set ℝ :=
  {a | ∃ X : Matrix I I ℂ,
    (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧ (Matrix.trace X).re = a}

def fidelityDualValues {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : Set ℝ :=
  {a | ∃ Y Z : HermitianMat I ℂ, 0 ≤ fidelityDualBlock Y Z ∧
    (1/2 : ℝ) * ⟪P,Y⟫_ℝ + (1/2 : ℝ) * ⟪Q,Z⟫_ℝ = a}

def inverseSqrtOnSupport {I : Type*} [Fintype I] [DecidableEq I]
    (P : HermitianMat I ℂ) : HermitianMat I ℂ := P.cfc (fun x => (Real.sqrt x)⁻¹)

def rootFidelity {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : ℝ := Matrix.traceNorm (P.sqrt.mat * Q.sqrt.mat)

def weightedBlockProgram {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    Program (I ⊕ I) (HermitianMat (I ⊕ I) ℂ) where
  constraint := blockPinch
  rhs := blockDiagonal P Q
  objective := (1/2 : ℝ) • offDiagonal C

def weightedDualBlock {I : Type*} [Fintype I]
    (C : Matrix I I ℂ) (Y Z : HermitianMat I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  blockDiagonal Y Z - offDiagonal C

def sandwichedTraceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (P.sqrt.mat * C * Q.sqrt.mat)

def weightedBlockPrimalValues {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ)
    (C : Matrix I I ℂ) : Set ℝ :=
  {a | ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
    (Matrix.trace (Cᴴ * X)).re = a}

def weightedBlockDualValues {I : Type*} [Fintype I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) : Set ℝ :=
  {a | ∃ Y Z : HermitianMat I ℂ, 0 ≤ weightedDualBlock C Y Z ∧
    (1/2 : ℝ) * ⟪P,Y⟫_ℝ + (1/2 : ℝ) * ⟪Q,Z⟫_ℝ = a}

def inputGram {I : Type*} [Fintype I] (A : Matrix I I ℂ) : HermitianMat I ℂ :=
  ⟨Aᴴ * A, (Matrix.posSemidef_conjTranspose_mul_self A).1⟩

def inputFrame {D R : ℕ} (u : Fin D × Fin R → ℂ) : Matrix (Fin R) (Fin D) ℂ :=
  fun r i => u (i,r)

abbrev DensityInput (D : ℕ) :=
  {ρ : HermitianMat (Fin D) ℂ // 0 ≤ ρ ∧ ρ.trace = (1 : ℝ)}

def densityVector {D : ℕ} (ρ : DensityInput D) : Fin D × Fin D → ℂ :=
  fun a => ρ.val.sqrt.mat a.2 a.1

def diamondChoiScore {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : DensityInput D) : ℝ :=
  Matrix.traceNorm (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat *
    MatrixMap.choi_matrix T * Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat)

def diamondChoiValue {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ ρ : DensityInput D, ⨆ σ : DensityInput D, ENNReal.ofReal (diamondChoiScore T ρ σ)

def directSum {I J : Type*} [Fintype I] [Fintype J]
    (P : HermitianMat I ℂ) (Q : HermitianMat J ℂ) : HermitianMat (I ⊕ J) ℂ :=
  ⟨Matrix.fromBlocks P.mat 0 0 Q.mat,
    Matrix.IsHermitian.fromBlocks P.H (by simp) Q.H⟩

def densityLift {D E : ℕ} (ρ : HermitianMat (Fin D) ℂ) : HermitianMat (Fin E × Fin D) ℂ :=
  HermitianMat.kronecker (1 : HermitianMat (Fin E) ℂ) ρ

abbrev DiamondRegister (D E : ℕ) :=
  (Fin D ⊕ Fin D) ⊕ ((Fin E × Fin D) ⊕ (Fin E × Fin D))

abbrev DiamondConstraints (D E : ℕ) := WithLp 2
  (WithLp 2 (ℝ × ℝ) × WithLp 2
    (HermitianMat (Fin E × Fin D) ℂ × HermitianMat (Fin E × Fin D) ℂ))

def principalLinear {I J : Type*} [Fintype I] [Fintype J] (e : I → J) :
    HermitianMat J ℂ →ₗ[ℝ] HermitianMat I ℂ where
  toFun X := principalBlock X e
  map_add' _ _ := by apply HermitianMat.ext; rfl
  map_smul' _ _ := by apply HermitianMat.ext; rfl

noncomputable def traceLinear (I : Type*) [Fintype I] : HermitianMat I ℂ →ₗ[ℝ] ℝ where
  toFun := HermitianMat.trace
  map_add' := HermitianMat.trace_add
  map_smul' t X := HermitianMat.trace_smul X t

def densityLiftLinear (D E : ℕ) : HermitianMat (Fin D) ℂ →ₗ[ℝ] HermitianMat (Fin E × Fin D) ℂ where
  toFun := densityLift
  map_add' := HermitianMat.kronecker_add 1
  map_smul' t X := by
    apply HermitianMat.ext
    simp only [densityLift, HermitianMat.kronecker_mat, HermitianMat.mat_smul]
    exact Matrix.kronecker_smul t _ _

def hilbertPair {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℝ A] [Module ℝ B] [Module ℝ C] (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C) :
    A →ₗ[ℝ] WithLp 2 (B × C) :=
  (WithLp.linearEquiv 2 ℝ (B × C)).symm.toLinearMap.comp (f.prod g)

set_option backward.isDefEq.respectTransparency false in

def diamondEqMap (D E : ℕ) : HermitianMat (DiamondRegister D E) ℂ →L[ℝ] DiamondConstraints D E :=
  let A₀ := principalLinear (fun i : Fin D => (Sum.inl (Sum.inl i) : DiamondRegister D E))
  let A₁ := principalLinear (fun i : Fin D => (Sum.inl (Sum.inr i) : DiamondRegister D E))
  let Z₀ := principalLinear (fun i : Fin E × Fin D => (Sum.inr (Sum.inl i) : DiamondRegister D E))
  let Z₁ := principalLinear (fun i : Fin E × Fin D => (Sum.inr (Sum.inr i) : DiamondRegister D E))
  LinearMap.toContinuousLinearMap (hilbertPair
    (hilbertPair ((traceLinear _).comp A₀) ((traceLinear _).comp A₁))
    (hilbertPair (Z₀ - (densityLiftLinear D E).comp A₀)
      (Z₁ - (densityLiftLinear D E).comp A₁)))

def diamondDualData {D E : ℕ} (a b : ℝ)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ) : DiamondConstraints D E :=
  WithLp.toLp 2 (WithLp.toLp 2 (a,b), WithLp.toLp 2 (Y,Z))

def diamondProgram {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Program (DiamondRegister D E) (DiamondConstraints D E) where
  constraint := diamondEqMap D E
  rhs := diamondDualData 1 1 0 0
  objective := directSum (0 : HermitianMat (Fin D ⊕ Fin D) ℂ)
    ((1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T))

def diamondPrimalData {D E : ℕ} (ρ σ : HermitianMat (Fin D) ℂ)
    (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : HermitianMat (DiamondRegister D E) ℂ :=
  directSum (blockDiagonal ρ σ) (fidelityPrimalBlock (densityLift ρ) (densityLift σ) X)

def diamondAdjointData {D E : ℕ} (a b : ℝ)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ) : HermitianMat (DiamondRegister D E) ℂ :=
  directSum (blockDiagonal (a • 1 - Y.traceLeft) (b • 1 - Z.traceLeft)) (blockDiagonal Y Z)

open scoped Matrix.Norms.L2Operator in

def diamondDualObjective {D E : ℕ} (Y Z : HermitianMat (Fin E × Fin D) ℂ) : ℝ :=
  (1/2 : ℝ) * ‖Y.traceLeft.mat‖ + (1/2 : ℝ) * ‖Z.traceLeft.mat‖

def diamondSourceDualValues {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Set ℝ :=
  {a | ∃ Y Z : HermitianMat (Fin E × Fin D) ℂ,
    0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) Y Z ∧ diamondDualObjective Y Z = a}

def diamondSourcePrimalValues {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Set ℝ :=
  {a | ∃ (ρ σ : DensityInput D) (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ),
    (fidelityPrimalBlock (densityLift ρ.val) (densityLift σ.val) X).mat.PosSemidef ∧
      (Matrix.trace ((MatrixMap.choi_matrix T)ᴴ * X)).re = a}

def frameGram {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℂ) : HermitianMat I ℂ :=
  ⟨Aᴴ * A, (Matrix.posSemidef_conjTranspose_mul_self A).1⟩

def stinespringCross {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Operator D →ₗ[ℂ] Operator E where
  toFun X := (A * X * Bᴴ).traceRight
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.traceRight_add]
  map_smul' r X := by
    rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.traceRight_smul]

def stinespringComplement {D E : ℕ} {Z : Type*} [Fintype Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (ρ : HermitianMat (Fin D) ℂ) : HermitianMat Z ℂ :=
  (ρ.conj A).traceLeft

def maxOutputRootFidelity {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : ℝ≥0∞ :=
  ⨆ ρ : DensityInput D, ⨆ σ : DensityInput D,
    ENNReal.ofReal (rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val))

def hermitianTranspose {I : Type*} [Fintype I] (P : HermitianMat I ℂ) : HermitianMat I ℂ :=
  ⟨P.matᵀ,P.H.transpose⟩

def stinespringFrame {D E : ℕ} {Z : Type*} [Fintype Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (ρ : DensityInput D) : Matrix (Fin E × Fin D) Z ℂ :=
  fun p z => ∑ i, A (p.1,z) i * ρ.val.sqrt.mat p.2 i

def stinespringFactor {D E : ℕ} {Z : Type*}
    (A : Matrix (Fin E × Z) (Fin D) ℂ) : Matrix (Fin E × Fin D) Z ℂ :=
  fun p z => A (p.1,z) p.2

def canonicalStinespringLeft {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Matrix (Fin E × (Fin E × Fin D)) (Fin D) ℂ :=
  fun p i => MatrixMap.choi_matrix T (p.1,i) p.2

def canonicalStinespringRight (D E : ℕ) : Matrix (Fin E × (Fin E × Fin D)) (Fin D) ℂ :=
  fun p i => (1 : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) (p.1,i) p.2

def partialTraceLeftLinear (I J : Type*) [Fintype I] [Fintype J] :
    HermitianMat (I × J) ℂ →ₗ[ℝ] HermitianMat J ℂ where
  toFun := HermitianMat.traceLeft
  map_add' := HermitianMat.traceLeft_add
  map_smul' r X := HermitianMat.traceLeft_smul X r

set_option backward.isDefEq.respectTransparency false in

def stinespringComplementLinear {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) :
    HermitianMat (Fin D) ℂ →L[ℝ] HermitianMat Z ℂ :=
  LinearMap.toContinuousLinearMap
    ((partialTraceLeftLinear (Fin E) Z).comp (HermitianMat.conjLinear ℝ A))

abbrev StinespringRegister (D : ℕ) (Z : Type*) := (Fin D ⊕ Fin D) ⊕ (Z ⊕ Z)

abbrev StinespringConstraints (Z : Type*) := WithLp 2
  (WithLp 2 (ℝ × ℝ) × WithLp 2 (HermitianMat Z ℂ × HermitianMat Z ℂ))

def stinespringDualData {Z : Type*} (a b : ℝ) (Y W : HermitianMat Z ℂ) : StinespringConstraints Z :=
  WithLp.toLp 2 (WithLp.toLp 2 (a,b),WithLp.toLp 2 (Y,W))

set_option backward.isDefEq.respectTransparency false in

def stinespringEqMap {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    HermitianMat (StinespringRegister D Z) ℂ →L[ℝ] StinespringConstraints Z :=
  let A₀ := principalLinear (fun i : Fin D => (Sum.inl (Sum.inl i) : StinespringRegister D Z))
  let A₁ := principalLinear (fun i : Fin D => (Sum.inl (Sum.inr i) : StinespringRegister D Z))
  let Z₀ := principalLinear (fun z : Z => (Sum.inr (Sum.inl z) : StinespringRegister D Z))
  let Z₁ := principalLinear (fun z : Z => (Sum.inr (Sum.inr z) : StinespringRegister D Z))
  LinearMap.toContinuousLinearMap (hilbertPair
    (hilbertPair ((traceLinear _).comp A₀) ((traceLinear _).comp A₁))
    (hilbertPair (Z₀ - (stinespringComplementLinear A).toLinearMap.comp A₀)
      (Z₁ - (stinespringComplementLinear B).toLinearMap.comp A₁)))

def stinespringProgram {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    Program (StinespringRegister D Z) (StinespringConstraints Z) where
  constraint := stinespringEqMap A B
  rhs := stinespringDualData 1 1 0 0
  objective := directSum (0 : HermitianMat (Fin D ⊕ Fin D) ℂ)
    ((1/2 : ℝ) • offDiagonal (1 : Matrix Z Z ℂ))

def stinespringPrimalData {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : HermitianMat (Fin D) ℂ) (X : Matrix Z Z ℂ) :
    HermitianMat (StinespringRegister D Z) ℂ :=
  directSum (blockDiagonal ρ σ)
    (fidelityPrimalBlock (stinespringComplement A ρ) (stinespringComplement B σ) X)

def stinespringAdjointData {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ) :
    HermitianMat (StinespringRegister D Z) ℂ :=
  directSum (blockDiagonal (a • 1 - (stinespringComplementLinear A).adjoint Y)
    (b • 1 - (stinespringComplementLinear B).adjoint W)) (blockDiagonal Y W)

def stinespringSourcePrimalValues {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Set ℝ :=
  {a | ∃ (ρ σ : DensityInput D) (X : Matrix Z Z ℂ),
    (fidelityPrimalBlock (stinespringComplement A ρ.val) (stinespringComplement B σ.val) X).mat.PosSemidef ∧
      (Matrix.trace X).re = a}

open scoped Matrix.Norms.L2Operator in

def stinespringBlockDualObjective {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (Y W : HermitianMat Z ℂ) : ℝ :=
  (1/2 : ℝ) * ‖((stinespringComplementLinear A).adjoint Y).mat‖ +
    (1/2 : ℝ) * ‖((stinespringComplementLinear B).adjoint W).mat‖

def stinespringBlockDualValues {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Set ℝ :=
  {a | ∃ Y W : HermitianMat Z ℂ, 0 ≤ fidelityDualBlock Y W ∧
    stinespringBlockDualObjective A B Y W = a}

def stinespringInverseDualValues {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Set ℝ :=
  {a | ∃ Y : HermitianMat Z ℂ, Y.mat.PosDef ∧ stinespringBlockDualObjective A B Y Y⁻¹ = a}

namespace Program
variable {I F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def DualInteriorBall (P : Program I F) (y : F) (r : ℝ) : Prop :=
  ∀ h : F, ‖h‖ ≤ r → P.DualFeasible (y + h)
end Program

open scoped Matrix.Norms.L2Operator in

def stinespringDualCenter {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : StinespringConstraints Z :=
  stinespringDualData ((1/2 : ℝ) + ‖((stinespringComplementLinear A).adjoint 1).mat‖)
    ((1/2 : ℝ) + ‖((stinespringComplementLinear B).adjoint 1).mat‖) 1 1

open scoped Matrix.Norms.L2Operator in

def stinespringPerturbationScale {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : ℝ :=
  1 + ‖((stinespringComplementLinear A).adjoint 1).mat‖ +
    ‖((stinespringComplementLinear B).adjoint 1).mat‖

def stinespringInteriorRadius {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : ℝ :=
  (4 * stinespringPerturbationScale A B)⁻¹

open scoped Matrix.Norms.L2Operator in

def diamondDualCenter {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : DiamondConstraints D E :=
  let a : ℝ := ‖MatrixMap.choi_matrix T‖ / 2 + 1
  diamondDualData (1 + a * E) (1 + a * E)
    (a • (1 : HermitianMat (Fin E × Fin D) ℂ)) (a • 1)

def diamondInteriorRadius (E : ℕ) : ℝ := (2 * (max 1 E : ℕ) : ℝ)⁻¹

def diamondRegularizedDual {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (θ : ℝ) (y : DiamondConstraints D E) : DiamondConstraints D E :=
  (1-θ) • y + θ • diamondDualCenter T

open scoped Matrix.Norms.L2Operator in

def diamondRegularizationWeight {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℝ :=
  min 1 (ε / (2 * (3 + (‖MatrixMap.choi_matrix T‖ + 2) * E)))

def diamondRoundingRadius {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℝ :=
  diamondRegularizationWeight T ε / (2 * (1 + E))

abbrev GaussianDyadicPayload (I : Type*) := Matrix I I (ℤ × ℤ)

def gaussianDyadicDecode {I : Type*} (p : ℕ) (P : GaussianDyadicPayload I) : Matrix I I ℂ :=
  fun i j => ⟨((P i j).1 : ℝ) / (2 : ℝ)^p, ((P i j).2 : ℝ) / (2 : ℝ)^p⟩

def complexDyadicPayload {I : Type*} (p : ℕ) (A : Matrix I I ℂ) : GaussianDyadicPayload I :=
  fun i j => (⌊(2 : ℝ)^p * (A i j).re⌋,⌊(2 : ℝ)^p * (A i j).im⌋)

def rationalDyadicPayload {I : Type*} (p : ℕ) (A : Matrix I I (ℚ × ℚ)) : GaussianDyadicPayload I :=
  fun i j => (⌊(2 : ℚ)^p * (A i j).1⌋,⌊(2 : ℚ)^p * (A i j).2⌋)

def gaussianRatMatrix {I : Type*} (A : Matrix I I (ℚ × ℚ)) : Matrix I I ℂ :=
  fun i j => ⟨(A i j).1,(A i j).2⟩

def hermitianDyadicDecode {I : Type*} [Fintype I] (p : ℕ) (P : GaussianDyadicPayload I) : HermitianMat I ℂ :=
  ⟨(1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ), by
    change ((1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ))ᴴ =
      (1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ)
    simp [Matrix.conjTranspose_smul,add_comm]⟩

def hermitianDyadicRatDecode {I : Type*} (p : ℕ) (P : GaussianDyadicPayload I) : Matrix I I (ℚ × ℚ) :=
  fun i j => (((P i j).1 + (P j i).1 : ℤ) / (2 : ℚ)^(p+1),
    ((P i j).2 - (P j i).2 : ℤ) / (2 : ℚ)^(p+1))

structure DiamondDyadicData (D E : ℕ) where
  scalar0 : ℤ
  scalar1 : ℤ
  block0 : GaussianDyadicPayload (Fin E × Fin D)
  block1 : GaussianDyadicPayload (Fin E × Fin D)

def diamondDyadicDecode {D E : ℕ} (p : ℕ) (P : DiamondDyadicData D E) : DiamondConstraints D E :=
  diamondDualData ((P.scalar0 : ℝ) / (2 : ℝ)^p) ((P.scalar1 : ℝ) / (2 : ℝ)^p)
    (hermitianDyadicDecode p P.block0) (hermitianDyadicDecode p P.block1)

def diamondDyadicPayload {D E : ℕ} (p : ℕ) (y : DiamondConstraints D E) : DiamondDyadicData D E where
  scalar0 := ⌊(2 : ℝ)^p * (WithLp.ofLp (WithLp.ofLp y).1).1⌋
  scalar1 := ⌊(2 : ℝ)^p * (WithLp.ofLp (WithLp.ofLp y).1).2⌋
  block0 := complexDyadicPayload p (WithLp.ofLp (WithLp.ofLp y).2).1.mat
  block1 := complexDyadicPayload p (WithLp.ofLp (WithLp.ofLp y).2).2.mat

def dyadicPrecision (q : ℕ) : ℕ := q.log2 + 1

def diamondDyadicPrecision {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℕ :=
  dyadicPrecision ⌈(2 + 4 * (E : ℝ) * D) / diamondRoundingRadius T ε⌉₊

def gaussianDyadicWordCount (D E : ℕ) : ℕ := (E*D)*(E*D)*2

def gaussianDyadicWordIndex (D E : ℕ) :
    (((Fin E × Fin D) × (Fin E × Fin D)) × Fin 2) ≃ Fin (gaussianDyadicWordCount D E) :=
  (Equiv.prodCongr ((Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv)
    (Equiv.refl (Fin 2))).trans finProdFinEquiv

def gaussianDyadicWord {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D))
    (k : Fin (gaussianDyadicWordCount D E)) : ℤ :=
  let t := (gaussianDyadicWordIndex D E).symm k
  if t.2 = 0 then (P t.1.1 t.1.2).1 else (P t.1.1 t.1.2).2

def gaussianDyadicWords {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D)) : List ℤ :=
  List.ofFn (gaussianDyadicWord P)

def gaussianDyadicFromWords (D E : ℕ) (xs : List ℤ) : GaussianDyadicPayload (Fin E × Fin D) :=
  fun i j => ((xs[(gaussianDyadicWordIndex D E ((i,j),0)).val]?).getD 0,
    (xs[(gaussianDyadicWordIndex D E ((i,j),1)).val]?).getD 0)

def diamondDyadicWordCount (D E : ℕ) : ℕ := 2 + 2 * gaussianDyadicWordCount D E

def diamondDyadicWords {D E : ℕ} (P : DiamondDyadicData D E) : List ℤ :=
  [P.scalar0,P.scalar1] ++ gaussianDyadicWords P.block0 ++ gaussianDyadicWords P.block1

def diamondDyadicFromWords (D E : ℕ) (xs : List ℤ) : Option (DiamondDyadicData D E) :=
  if xs.length = diamondDyadicWordCount D E then some {
    scalar0 := (xs[0]?).getD 0
    scalar1 := (xs[1]?).getD 0
    block0 := gaussianDyadicFromWords D E ((xs.drop 2).take (gaussianDyadicWordCount D E))
    block1 := gaussianDyadicFromWords D E ((xs.drop 2).drop (gaussianDyadicWordCount D E)) }
  else none

def dyadicWordWidth (p : ℕ) (R : ℝ) : ℕ := dyadicPrecision ⌈(2 : ℝ)^p*R + 1⌉₊

def rationalDyadicWordWidth (p : ℕ) (R : ℚ) : ℕ := dyadicPrecision ⌈(2 : ℚ)^p*R + 1⌉₊

def DiamondDyadicData.WordBound {D E : ℕ} (P : DiamondDyadicData D E) (b : ℕ) : Prop :=
  ∀ n ∈ diamondDyadicWords P, n.natAbs < 2^b

open scoped Matrix.Norms.L2Operator in
def diamondDyadicOuterSize {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℝ :=
  (D+1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖ + ε)

def diamondDyadicWordWidth {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℕ :=
  dyadicWordWidth (diamondDyadicPrecision T ε) (diamondDyadicOuterSize T ε)

def dyadicBitVecBits {w : ℕ} (v : BitVec w) : List Bool :=
  List.ofFn (fun k : Fin w => v.getLsbD k.val)

def signedDyadicWordBits (b : ℕ) (n : ℤ) : List Bool :=
  dyadicBitVecBits (BitVec.ofInt (b+1) n)

def signedDyadicWordFromBits (bs : List Bool) : ℤ := (BitVec.ofBoolListLE bs).toInt

def signedDyadicWordsBits (b : ℕ) (xs : List ℤ) : List Bool :=
  xs.flatMap (signedDyadicWordBits b)

def signedDyadicWordsRead (b : ℕ) : ℕ → List Bool → List ℤ
  | 0,_ => []
  | n+1,bs => signedDyadicWordFromBits (bs.take (b+1)) :: signedDyadicWordsRead b n (bs.drop (b+1))

def diamondDyadicBitCount (D E b : ℕ) : ℕ := diamondDyadicWordCount D E * (b+1)

def diamondDyadicBits {D E : ℕ} (b : ℕ) (P : DiamondDyadicData D E) : List Bool :=
  signedDyadicWordsBits b (diamondDyadicWords P)

def diamondDyadicFromBits (D E b : ℕ) (bs : List Bool) : Option (DiamondDyadicData D E) :=
  if bs.length = diamondDyadicBitCount D E b then
    diamondDyadicFromWords D E (signedDyadicWordsRead b (diamondDyadicWordCount D E) bs)
  else none

abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

instance gaussianRationalNoRoot : Fact (∀ r : ℚ, r^2 ≠ (-1 : ℚ) + 0*r) :=
  ⟨by intro r h; nlinarith [sq_nonneg r]⟩

def gaussianRationalEmbed : GaussianRational →+* ℂ where
  toFun z := ⟨(z.re : ℝ),(z.im : ℝ)⟩
  map_zero' := by apply Complex.ext <;> norm_num
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by
    apply Complex.ext <;> simp [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add]
  map_mul' z w := by
    apply Complex.ext <;> simp
        [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,Complex.mul_re,Complex.mul_im,sub_eq_add_neg]

def gaussianRationalMatrix {I : Type*} (Q : Matrix I I GaussianRational) : Matrix I I ℂ :=
    Q.map gaussianRationalEmbed

def gaussianRationalTail {n : ℕ} (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) : Matrix (Fin n) (Fin n) GaussianRational :=
  fun i j => Q i.succ j.succ

def gaussianRationalSchur {n : ℕ} (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) : Matrix (Fin n) (Fin n) GaussianRational :=
  fun i j => Q i.succ j.succ - Q i.succ 0 * (Q 0 0)⁻¹ * Q 0 j.succ

abbrev GaussianRationalTable (n : ℕ) := Vector (Vector GaussianRational n) n

def gaussianRationalTable {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational) : GaussianRationalTable n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => Q i j))

def gaussianRationalTableMatrix {n : ℕ} (A : GaussianRationalTable n) : Matrix (Fin n) (Fin n) GaussianRational :=
  fun i j => A[i][j]

def gaussianRationalPsdCore : (n : ℕ) → GaussianRationalTable n → Bool
  | 0,_ => true
  | n+1,A =>
    let Q := gaussianRationalTableMatrix A
    if Q.IsHermitian then
      if (Q 0 0).re < 0 then false
      else if (Q 0 0).re = 0 then
        if ∀ j : Fin n, Q 0 j.succ = 0 then
          gaussianRationalPsdCore n (gaussianRationalTable (gaussianRationalTail Q))
        else false
      else gaussianRationalPsdCore n (gaussianRationalTable (gaussianRationalSchur Q))
    else false

def gaussianRationalPsdCheck {n : ℕ} (A : GaussianRationalTable n) : Bool :=
  gaussianRationalPsdCore n A

def gaussianRationalOfPair (z : ℚ × ℚ) : GaussianRational := ⟨z.1,z.2⟩

def rationalPairPsdCheck {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ)) : Bool :=
  gaussianRationalPsdCheck (gaussianRationalTable (Q.map gaussianRationalOfPair))

def dyadicBlockPsdCheck (D E p : ℕ) (P : GaussianDyadicPayload (Fin E × Fin D)) : Bool :=
  rationalPairPsdCheck ((hermitianDyadicRatDecode p P).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)

def gaussianRationalQuadratic {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational)
    (v : Fin n → GaussianRational) : GaussianRational := star v ⬝ᵥ (Q *ᵥ v)

def gaussianRationalSchurLift {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (v : Fin n → GaussianRational) : Fin (n+1) → GaussianRational :=
  Fin.cons (-(Q 0 0)⁻¹ * ∑ j, Q 0 j.succ * v j) v

def gaussianRationalCrossVector {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (j : Fin n) : Fin (n+1) → GaussianRational :=
  Fin.cons (-(Q j.succ j.succ + 1) / (2 * star (Q 0 j.succ))) (Pi.single j 1)

def gaussianRationalNegativeCore : (n : ℕ) → GaussianRationalTable n → Option (Vector GaussianRational n)
  | 0,_ => none
  | n+1,A =>
    let Q := gaussianRationalTableMatrix A
    if (Q 0 0).re < 0 then some (Vector.ofFn (Pi.single 0 1))
    else if (Q 0 0).re = 0 then
      match Fin.find? (fun j : Fin n => decide (Q 0 j.succ ≠ 0)) with
      | some j => some (Vector.ofFn (gaussianRationalCrossVector Q j))
      | none => (gaussianRationalNegativeCore n (gaussianRationalTable (gaussianRationalTail Q))).map
          (fun v => Vector.ofFn (Fin.cons 0 (fun i => v[i])))
    else (gaussianRationalNegativeCore n (gaussianRationalTable (gaussianRationalSchur Q))).map
          (fun v => Vector.ofFn (gaussianRationalSchurLift Q (fun i => v[i])))

inductive GaussianRationalPsdResult (n : ℕ) where
  | nonHermitian
  | psd
  | negative (direction : Vector GaussianRational n)

def gaussianRationalPsdSeparate {n : ℕ} (A : GaussianRationalTable n) : GaussianRationalPsdResult n :=
  if (gaussianRationalTableMatrix A).IsHermitian then
    match gaussianRationalNegativeCore n A with
    | none => .psd
    | some v => .negative v
  else .nonHermitian

def rationalPairPsdSeparate {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ)) : GaussianRationalPsdResult n :=
  gaussianRationalPsdSeparate (gaussianRationalTable (Q.map gaussianRationalOfPair))

def diamondRationalRegisterEquiv (D E : ℕ) : DiamondRegister D E ≃ Fin ((D+D)+(E*D+E*D)) :=
  (Equiv.sumCongr finSumFinEquiv ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def diamondRationalSlack {D E : ℕ} (J Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (a b : ℚ) : Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin D => (a : GaussianRational)) - Y.traceLeft) 0 0
      (Matrix.diagonal (fun _ : Fin D => (b : GaussianRational)) - Z.traceLeft)) 0 0
    (Matrix.fromBlocks Y (-(1/2 : GaussianRational) • J) (-(1/2 : GaussianRational) • Jᴴ) Z)

def diamondDyadicRationalSlack {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  diamondRationalSlack J ((hermitianDyadicRatDecode p P.block0).map gaussianRationalOfPair)
    ((hermitianDyadicRatDecode p P.block1).map gaussianRationalOfPair)
    ((P.scalar0 : ℚ) / 2^p) ((P.scalar1 : ℚ) / 2^p)

def diamondDyadicSlackTable {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : GaussianRationalTable ((D+D)+(E*D+E*D)) :=
  gaussianRationalTable ((diamondDyadicRationalSlack J p P).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm)

def diamondDyadicFeasibleCheck {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : Bool :=
  gaussianRationalPsdCheck (diamondDyadicSlackTable J p P)

def diamondDyadicFeasibleSeparate {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : GaussianRationalPsdResult ((D+D)+(E*D+E*D)) :=
  gaussianRationalPsdSeparate (diamondDyadicSlackTable J p P)

def diamondDyadicBinaryFeasibleCheck {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p b : ℕ) (bs : List Bool) : Option Bool :=
  (diamondDyadicFromBits D E b bs).map (diamondDyadicFeasibleCheck J p)

def gaussianRationalNormBound {I : Type*} [Fintype I] (J : Matrix I I GaussianRational) : ℚ :=
  ∑ i, ∑ j, (|(J i j).re| + |(J i j).im|)

def diamondRationalWeight {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  min 1 (ε / (2 * (3 + (gaussianRationalNormBound J + 2) * E)))

def diamondRationalRadius {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  diamondRationalWeight J ε / (2 * (1 + E))

def diamondRationalPrecision {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℕ :=
  dyadicPrecision ⌈(2 + 4 * (E : ℚ) * D) / diamondRationalRadius J ε⌉₊

def diamondRationalOuterSize {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  (D+1 : ℚ) * (E * gaussianRationalNormBound J + ε)

def diamondRationalWidth {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℕ :=
  rationalDyadicWordWidth (diamondRationalPrecision J ε) (diamondRationalOuterSize J ε)

def diamondRationalCenterScale {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : ℚ :=
  gaussianRationalNormBound J / 2 + 1

def diamondRationalCenterScalar {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : ℚ :=
  1 + diamondRationalCenterScale J * E

def diamondRationalCenterSlack {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) :
    Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  diamondRationalSlack J (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))
    (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))
    (diamondRationalCenterScalar J) (diamondRationalCenterScalar J)

noncomputable def diamondRationalCenter {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : DiamondConstraints D E :=
  diamondDualData (diamondRationalCenterScalar J : ℝ) (diamondRationalCenterScalar J : ℝ)
    ((diamondRationalCenterScale J : ℝ) • 1) ((diamondRationalCenterScale J : ℝ) • 1)

def diamondRationalInteriorRadius (E : ℕ) : ℚ := (2 * (1 + E))⁻¹

abbrev DiamondRationalCoordinates (D E : ℕ) := Fin (diamondDyadicWordCount D E) → ℚ

def diamondRationalScalarIndex (D E : ℕ) (k : Fin 2) : Fin (diamondDyadicWordCount D E) :=
  ⟨k.val,by have hk := k.isLt; unfold diamondDyadicWordCount; omega⟩

def diamondRationalBlockIndex (D E : ℕ) (b : Bool)
    (i j : Fin E × Fin D) (part : Fin 2) : Fin (diamondDyadicWordCount D E) :=
  let k := gaussianDyadicWordIndex D E ((i,j),part)
  ⟨2 + (if b then gaussianDyadicWordCount D E else 0) + k.val, by
    have hk := k.isLt
    unfold diamondDyadicWordCount
    split <;> omega⟩

def diamondRationalRawBlock {D E : ℕ} (b : Bool) (x : DiamondRationalCoordinates D E) :
    Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational :=
  fun i j => gaussianRationalOfPair (x (diamondRationalBlockIndex D E b i j 0),
    x (diamondRationalBlockIndex D E b i j 1))

def gaussianRationalSymmetrize {I : Type*} (Q : Matrix I I GaussianRational) : Matrix I I GaussianRational :=
  (1/2 : GaussianRational) • (Q + Qᴴ)

def diamondRationalSymBlock {D E : ℕ} (b : Bool) (x : DiamondRationalCoordinates D E) :
    Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational :=
  gaussianRationalSymmetrize (diamondRationalRawBlock b x)

def diamondRationalCandidateSlack {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  diamondRationalSlack J (diamondRationalSymBlock false x) (diamondRationalSymBlock true x)
    (x (diamondRationalScalarIndex D E 0)) (x (diamondRationalScalarIndex D E 1))

noncomputable def gaussianRationalHermitianDecode {I : Type*} [Fintype I]
    (Q : Matrix I I GaussianRational) : HermitianMat I ℂ :=
  ⟨(1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ), by
    change ((1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ))ᴴ =
      (1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ)
    simp [Matrix.conjTranspose_smul,add_comm]⟩

noncomputable def diamondRationalDecode {D E : ℕ} (x : DiamondRationalCoordinates D E) : DiamondConstraints D E :=
  diamondDualData (x (diamondRationalScalarIndex D E 0) : ℝ) (x (diamondRationalScalarIndex D E 1) : ℝ)
    (gaussianRationalHermitianDecode (diamondRationalRawBlock false x))
    (gaussianRationalHermitianDecode (diamondRationalRawBlock true x))

structure RationalAffineCut (n : ℕ) where
  coefficients : Vector ℚ n
  bound : ℚ

def RationalAffineCut.eval {n : ℕ} (C : RationalAffineCut n) (x : Fin n → ℚ) : ℚ :=
  ∑ k, C.coefficients[k] * x k

def diamondRationalSeparationCut {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) : RationalAffineCut (diamondDyadicWordCount D E) where
  coefficients := Vector.ofFn (fun k => (gaussianRationalQuadratic
    ((diamondRationalCandidateSlack 0 (Pi.single k 1)).submatrix
      (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm) (fun i => v[i])).re)
  bound := -(gaussianRationalQuadratic ((diamondRationalCandidateSlack J 0).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm) (fun i => v[i])).re

def diamondRationalCandidateTable {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    GaussianRationalTable ((D+D)+(E*D+E*D)) :=
  gaussianRationalTable ((diamondRationalCandidateSlack J x).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm)

def diamondRationalCandidateSeparate {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    GaussianRationalPsdResult ((D+D)+(E*D+E*D)) :=
  gaussianRationalPsdSeparate (diamondRationalCandidateTable J x)

inductive RationalSeparationResult (n : ℕ) where
  | feasible
  | cut (C : RationalAffineCut n)
  | invalid

def diamondRationalSeparationOracle {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    RationalSeparationResult (diamondDyadicWordCount D E) :=
  match diamondRationalCandidateSeparate J x with
  | .psd => .feasible
  | .negative v => .cut (diamondRationalSeparationCut J v)
  | .nonHermitian => .invalid

def gaussianRationalCoordinateWord {D E : ℕ}
    (Q : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (k : Fin (gaussianDyadicWordCount D E)) : ℚ :=
  let t := (gaussianDyadicWordIndex D E).symm k
  if t.2 = 0 then (Q t.1.1 t.1.2).re else (Q t.1.1 t.1.2).im

def diamondRationalPack {D E : ℕ} (a b : ℚ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : DiamondRationalCoordinates D E := fun k =>
  if h : k.val < 2 then if k.val = 0 then a else b
  else if h0 : k.val < 2 + gaussianDyadicWordCount D E then
    gaussianRationalCoordinateWord Y ⟨k.val-2,by have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩
  else gaussianRationalCoordinateWord Z ⟨k.val-(2+gaussianDyadicWordCount D E),by
    have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩

def diamondRationalCenterCoordinates {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : DiamondRationalCoordinates D E :=
  diamondRationalPack (diamondRationalCenterScalar J) (diamondRationalCenterScalar J)
    (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))
    (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))

abbrev DiamondRealCoordinates (D E : ℕ) := Fin (diamondDyadicWordCount D E) → ℝ

def diamondRealRawBlock {D E : ℕ} (b : Bool) (x : DiamondRealCoordinates D E) :
    Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ :=
  fun i j => ⟨x (diamondRationalBlockIndex D E b i j 0),x (diamondRationalBlockIndex D E b i j 1)⟩

def diamondRealHermitianBlock {D E : ℕ} (b : Bool) (x : DiamondRealCoordinates D E) :
    HermitianMat (Fin E × Fin D) ℂ :=
  ⟨(1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ),by
    change ((1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ))ᴴ =
      (1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ)
    simp [Matrix.conjTranspose_smul,add_comm]⟩

def diamondRealDecode {D E : ℕ} (x : DiamondRealCoordinates D E) : DiamondConstraints D E :=
  diamondDualData (x (diamondRationalScalarIndex D E 0)) (x (diamondRationalScalarIndex D E 1))
    (diamondRealHermitianBlock false x) (diamondRealHermitianBlock true x)

def diamondRationalCoordinatesReal {D E : ℕ} (x : DiamondRationalCoordinates D E) : DiamondRealCoordinates D E :=
  fun k => (x k : ℝ)

def RationalAffineCut.evalReal {n : ℕ} (C : RationalAffineCut n) (x : Fin n → ℝ) : ℝ :=
  ∑ k, ((C.coefficients[k] : ℚ) : ℝ) * x k

def diamondRationalScore {D E : ℕ} (x : DiamondRationalCoordinates D E) : ℚ :=
  x (diamondRationalScalarIndex D E 0) + x (diamondRationalScalarIndex D E 1)

def diamondRealScore {D E : ℕ} (x : DiamondRealCoordinates D E) : ℝ :=
  x (diamondRationalScalarIndex D E 0) + x (diamondRationalScalarIndex D E 1)

def diamondRationalObjectiveCut (D E : ℕ) (γ : ℚ) : RationalAffineCut (diamondDyadicWordCount D E) where
  coefficients := Vector.ofFn (fun k => (if k = diamondRationalScalarIndex D E 0 then -1 else 0) +
    (if k = diamondRationalScalarIndex D E 1 then -1 else 0))
  bound := -γ

def diamondRationalSublevelOracle {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ : ℚ) (x : DiamondRationalCoordinates D E) :
    RationalSeparationResult (diamondDyadicWordCount D E) :=
  if diamondRationalScore x ≤ γ then diamondRationalSeparationOracle J x
  else .cut (diamondRationalObjectiveCut D E γ)

def diamondRealCoordinateWord {D E : ℕ} (Q : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ)
    (k : Fin (gaussianDyadicWordCount D E)) : ℝ :=
  let t := (gaussianDyadicWordIndex D E).symm k
  if t.2 = 0 then (Q t.1.1 t.1.2).re else (Q t.1.1 t.1.2).im

def diamondRealPack {D E : ℕ} (a b : ℝ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : DiamondRealCoordinates D E := fun k =>
  if h : k.val < 2 then if k.val = 0 then a else b
  else if h0 : k.val < 2 + gaussianDyadicWordCount D E then
    diamondRealCoordinateWord Y ⟨k.val-2,by have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩
  else diamondRealCoordinateWord Z ⟨k.val-(2+gaussianDyadicWordCount D E),by
    have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩

def diamondRealEncode {D E : ℕ} (y : DiamondConstraints D E) : DiamondRealCoordinates D E :=
  diamondRealPack (WithLp.ofLp (WithLp.ofLp y).1).1 (WithLp.ofLp (WithLp.ofLp y).1).2
    (WithLp.ofLp (WithLp.ofLp y).2).1.mat (WithLp.ofLp (WithLp.ofLp y).2).2.mat

def diamondRealSublevel {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (γ : ℝ) : Set (DiamondRealCoordinates D E) :=
  {x | (diamondProgram T).DualFeasible (diamondRealDecode x) ∧
    (diamondProgram T).dualScore (diamondRealDecode x) ≤ γ}

def diamondCoordinateNorm {D E : ℕ} (x : DiamondRealCoordinates D E) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)))‖

def diamondCoordinateLipschitz (D E : ℕ) : ℚ := 2 + 4 * (E : ℚ) * D

def diamondCoordinateInnerRadius {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  diamondRationalRadius J ε / diamondCoordinateLipschitz D E

def diamondCoordinateOuterRadius {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  (diamondDyadicWordCount D E : ℚ) * diamondRationalOuterSize J ε + 1

def diamondCoordinateBall {D E : ℕ} (c : DiamondRealCoordinates D E) (r : ℝ) : Set (DiamondRealCoordinates D E) :=
  {x | diamondCoordinateNorm (x-c) ≤ r}

def RationalAffineCut.euclideanNormal {n : ℕ} (C : RationalAffineCut n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => ((C.coefficients[k] : ℚ) : ℝ))

def RationalAffineCut.unitNormal {n : ℕ} (C : RationalAffineCut n) : EuclideanSpace ℝ (Fin n) :=
  ‖C.euclideanNormal‖⁻¹ • C.euclideanNormal

def euclideanCentralCutCenter {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1/((n : ℝ)+1)) • u

def euclideanCentralCutEllipsoid {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ((n : ℝ)^2-1)*‖x-euclideanCentralCutCenter u‖^2 +
    2*((n : ℝ)+1)*⟪u,x-euclideanCentralCutCenter u⟫_ℝ^2 ≤ (n : ℝ)^2}

def euclideanCentralCutShape {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ)^2/((n : ℝ)^2-1)) •
    (1 - (2/((n : ℝ)+1)) • Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u))

def euclideanMatrixApply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)

def euclideanShapeEllipsoid {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | WithLp.ofLp (x-c) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp (x-c)) ≤ 1}

def euclideanPullbackUnit {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ‖euclideanMatrixApply Sᵀ g‖⁻¹ • euclideanMatrixApply Sᵀ g

def euclideanAffineCutCenter {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  c+euclideanMatrixApply S (euclideanCentralCutCenter (euclideanPullbackUnit S g))

def euclideanAffineCutShape {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := S * euclideanCentralCutShape (euclideanPullbackUnit S g) * Sᵀ

def euclideanEllipsoidCutCenter {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  c + (1/(((n : ℝ)+1)*Real.sqrt (WithLp.ofLp g ⬝ᵥ (A *ᵥ WithLp.ofLp g)))) • euclideanMatrixApply A g

def euclideanEllipsoidCutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ)^2/((n : ℝ)^2-1)) •
    (A - (2/(((n : ℝ)+1)*(WithLp.ofLp g ⬝ᵥ (A *ᵥ WithLp.ofLp g)))) •
      Matrix.vecMulVec (A *ᵥ WithLp.ofLp g) (A *ᵥ WithLp.ofLp g))

def rationalEllipsoidShapeReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (algebraMap ℚ ℝ)

def rationalEllipsoidCutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ)^2/((n : ℚ)^2-1)) •
    (A - (2/(((n : ℚ)+1)*(g ⬝ᵥ (A *ᵥ g)))) • Matrix.vecMulVec (A *ᵥ g) (A *ᵥ g))

def rationalSqrtUpper (s : ℚ) (p : ℕ) : ℚ :=
  ((Nat.sqrt ⌊s*(2 : ℚ)^(2*p)⌋₊+1 : ℕ) : ℚ)/(2 : ℚ)^p

def rationalSqrtPrecision (s η : ℚ) : ℕ :=
  dyadicPrecision ⌈1/(η*min s 1)⌉₊

def euclideanApproxCutCenter {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (r : ℝ) : EuclideanSpace ℝ (Fin n) :=
  c+(1/(((n : ℝ)+1)*r)) • euclideanMatrixApply A g

def rationalEllipsoidCutCenter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c g : Fin n → ℚ) (η : ℚ) : Fin n → ℚ :=
  let s := g ⬝ᵥ (A *ᵥ g)
  let r := rationalSqrtUpper s (rationalSqrtPrecision s η)
  c + (1/(((n : ℚ)+1)*r)) • (A *ᵥ g)

def rationalEllipsoidInflatedShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) (η : ℚ) :
    Matrix (Fin n) (Fin n) ℚ := (1+η/(n : ℚ))^2 • rationalEllipsoidCutShape A g

def rationalEllipsoidStepTolerance (n : ℕ) : ℚ := 1/(16*(n : ℚ))

structure RationalEllipsoidState (n : ℕ) where
  centerData : Vector ℚ n
  shapeData : Vector (Vector ℚ n) n

def RationalEllipsoidState.center {n : ℕ} (s : RationalEllipsoidState n) : Fin n → ℚ :=
    fun i => s.centerData[i]
def RationalEllipsoidState.shape {n : ℕ} (s : RationalEllipsoidState n) :
    Matrix (Fin n) (Fin n) ℚ := fun i j => s.shapeData[i][j]
def RationalEllipsoidState.ofFunctions {n : ℕ} (c : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) : RationalEllipsoidState n :=
  ⟨Vector.ofFn c,Vector.ofFn (fun i => Vector.ofFn (A i))⟩

def RationalEllipsoidState.cut {n : ℕ} (s : RationalEllipsoidState n) (C : RationalAffineCut n) : RationalEllipsoidState n :=
  let η := rationalEllipsoidStepTolerance n
  let g : Fin n → ℚ := fun i => C.coefficients[i]
  let ag := Vector.ofFn (s.shape *ᵥ g)
  let σ := ∑ i : Fin n, g i*ag[i]
  let r := rationalSqrtUpper σ (rationalSqrtPrecision σ η)
  let centerScale := 1/(((n : ℚ)+1)*r)
  let shapeScale := (1+η/(n : ℚ))^2*((n : ℚ)^2/((n : ℚ)^2-1))
  let rankScale := 2/(((n : ℚ)+1)*σ)
  ⟨Vector.ofFn (fun i => s.centerData[i]+centerScale*ag[i]),
    Vector.ofFn (fun i => Vector.ofFn (fun j => shapeScale*(s.shapeData[i][j]-rankScale*(ag[i]*ag[j]))))⟩

def RationalEllipsoidState.region {n : ℕ} (s : RationalEllipsoidState n) : Set (EuclideanSpace ℝ (Fin n)) :=
  euclideanShapeEllipsoid (WithLp.toLp 2 (fun k => (s.center k : ℝ))) (rationalEllipsoidShapeReal s.shape)

inductive EllipsoidRunOutcome where
  | feasible | exhausted | invalid
  deriving DecidableEq, Repr

structure RationalEllipsoidRunResult (n : ℕ) where
  state : RationalEllipsoidState n
  outcome : EllipsoidRunOutcome
  trace : List (RationalEllipsoidState n × RationalSeparationResult n)

def rationalEllipsoidTraceCutCount {n : ℕ}
    (tr : List (RationalEllipsoidState n × RationalSeparationResult n)) : ℕ :=
  tr.countP (fun t => match t.2 with | .cut _ => true | _ => false)

def diamondEllipsoidRun {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ : ℚ) :
    ℕ → RationalEllipsoidState (diamondDyadicWordCount D E) → RationalEllipsoidRunResult (diamondDyadicWordCount D E)
  | 0,s => ⟨s,.exhausted,[]⟩
  | k+1,s =>
    match diamondRationalSublevelOracle J γ s.center with
    | .feasible => ⟨s,.feasible,[(s,.feasible)]⟩
    | .invalid => ⟨s,.invalid,[(s,.invalid)]⟩
    | .cut C =>
      let out := diamondEllipsoidRun J γ k (s.cut C)
      ⟨out.state,out.outcome,(s,.cut C)::out.trace⟩

def rationalEllipsoidSearchBudget (n : ℕ) (R r : ℚ) : ℕ :=
  2*(n+1)*(2*n*dyadicPrecision ⌈R/r⌉₊+1)

def diamondEllipsoidInitialState (D E : ℕ) (R : ℚ) : RationalEllipsoidState (diamondDyadicWordCount D E) :=
  RationalEllipsoidState.ofFunctions 0 (R^2 • 1)

def diamondEllipsoidSolve {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ ε : ℚ) :
    RationalEllipsoidRunResult (diamondDyadicWordCount D E) :=
  diamondEllipsoidRun J γ
    (rationalEllipsoidSearchBudget (diamondDyadicWordCount D E) (diamondCoordinateOuterRadius J ε) (diamondCoordinateInnerRadius J ε))
    (diamondEllipsoidInitialState D E (diamondCoordinateOuterRadius J ε))

end Qatlib.Concepts.DyadicFloor.FloorRounding
