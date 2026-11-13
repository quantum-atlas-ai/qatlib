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

/-!
# Semidefinite programs and rational diamond-norm data

`Program` packages Hermitian semidefinite programs with primal and dual feasibility, objective
values, and strict feasibility conditions. Block constructions specialize these data to
fidelity, weighted trace norms, Choi matrices, and Stinespring representations in the
quantum-information setting of [Watrous2018].

The module also defines dyadic payloads, signed binary serialization, Gaussian rational
positivity tests and separation procedures, and a rational ellipsoid runner for diamond-program
sublevels. These finite-precision constructions are relevant to semidefinite-programming
algorithms such as [BrandaoSvore2017].

## Main statements

* `Program`: primal and dual semidefinite-program data.
* `fidelityProgram`, `diamondProgram`, `stinespringProgram`: block program constructions.
* `DiamondDyadicData`: finite integer payloads for dual candidates.
* `gaussianRationalPsdSeparate`: rational matrix classification with a possible negative
  direction.
* `diamondRationalSeparationOracle`: affine-cut generation for candidate slacks.
* `diamondEllipsoidSolve`: a bounded rational ellipsoid search.

## References

* [Watrous, 2018][Watrous2018]
* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.DyadicFloor.FloorRounding
open Matrix
open scoped InnerProductSpace ComplexOrder ENNReal

/-- The proper cone of positive semidefinite complex Hermitian matrices, viewed over the reals. -/
def psdCone (I : Type*) [Fintype I] [DecidableEq I] :
    ProperCone ℝ (HermitianMat I ℂ) := ProperCone.positive ℝ _

/-- A semidefinite program specified by a continuous linear equality constraint, a right-hand
side, and a Hermitian objective matrix. -/
structure Program (I F : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  constraint : HermitianMat I ℂ →L[ℝ] F
  rhs : F
  objective : HermitianMat I ℂ

namespace Program
variable {I F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Primal feasibility: the matrix is positive semidefinite and satisfies the equality
constraint. -/
def PrimalFeasible (P : Program I F) (X : HermitianMat I ℂ) : Prop :=
  0 ≤ X ∧ P.constraint X = P.rhs

/-- Dual feasibility: the adjoint constraint applied to the dual variable dominates the
objective matrix. -/
def DualFeasible (P : Program I F) (y : F) : Prop :=
  0 ≤ P.constraint.adjoint y - P.objective

/-- The real inner product of the objective matrix with a primal matrix. -/
def primalScore (P : Program I F) (X : HermitianMat I ℂ) : ℝ := ⟪P.objective, X⟫_ℝ

/-- The real inner product of the constraint right-hand side with a dual variable. -/
def dualScore (P : Program I F) (y : F) : ℝ := ⟪P.rhs, y⟫_ℝ

/-- The set of objective values attained by primal feasible matrices. -/
def primalValues (P : Program I F) : Set ℝ := P.primalScore '' {X | P.PrimalFeasible X}

/-- The set of objective values attained by dual feasible variables. -/
def dualValues (P : Program I F) : Set ℝ := P.dualScore '' {y | P.DualFeasible y}

/-- The primal feasible matrices whose objective score is at least the specified threshold. -/
def primalSuperlevel (P : Program I F) (a : ℝ) : Set (HermitianMat I ℂ) :=
  {X | P.PrimalFeasible X ∧ a ≤ P.primalScore X}

/-- The existence of a positive definite matrix satisfying the primal equality constraint. -/
def PrimalSlater (P : Program I F) : Prop :=
  ∃ X : HermitianMat I ℂ, X.mat.PosDef ∧ P.constraint X = P.rhs

/-- The existence of a dual variable whose slack matrix is positive definite. -/
def DualSlater (P : Program I F) : Prop :=
  ∃ y : F, (P.constraint.adjoint y - P.objective).mat.PosDef

/-- The continuous linear map sending a matrix and a scalar to its constraint image and its
objective score minus that scalar. -/
def perturbationMap (P : Program I F) : (HermitianMat I ℂ × ℝ) →L[ℝ] (F × ℝ) :=
  (P.constraint.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((innerSL ℝ P.objective).comp (ContinuousLinearMap.fst ℝ _ _) -
      ContinuousLinearMap.snd ℝ _ _)

/-- The auxiliary program on the kernel of the constraint map, using orthogonal projection and
objective `-X₀`. -/
def dualSlackProgram (P : Program I F) (X₀ : HermitianMat I ℂ) :
    Program I (LinearMap.ker P.constraint.toLinearMap) where
  constraint := (LinearMap.ker P.constraint.toLinearMap).orthogonalProjection
  rhs := -(LinearMap.ker P.constraint.toLinearMap).orthogonalProjection P.objective
  objective := -X₀

end Program

/-- The Hermitian block diagonal matrix with diagonal blocks `P` and `Q`. -/
def blockDiagonal {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  ⟨Matrix.fromBlocks P.mat 0 0 Q.mat,
    Matrix.IsHermitian.fromBlocks P.H (by simp) Q.H⟩

/-- The Hermitian matrix with off-diagonal blocks `X` and its conjugate transpose and zero
diagonal blocks. -/
def offDiagonal {I : Type*} [Fintype I] (X : Matrix I I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  ⟨Matrix.fromBlocks 0 X Xᴴ 0,
    Matrix.IsHermitian.fromBlocks (by simp) rfl (by simp)⟩

/-- The continuous real-linear pinching map that keeps the two diagonal blocks and sets the
off-diagonal blocks to zero. -/
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

/-- The block semidefinite program with fixed diagonal blocks `P`, `Q` and objective given by
half the off-diagonal identity. -/
def fidelityProgram {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : Program (I ⊕ I) (HermitianMat (I ⊕ I) ℂ) where
  constraint := blockPinch
  rhs := blockDiagonal P Q
  objective := (1/2 : ℝ) • offDiagonal (1 : Matrix I I ℂ)

/-- The Hermitian block matrix with diagonal blocks `P`, `Q` and off-diagonal blocks `X`, `Xᴴ`. -/
def fidelityPrimalBlock {I : Type*} [Fintype I]
    (P Q : HermitianMat I ℂ) (X : Matrix I I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  ⟨Matrix.fromBlocks P.mat X Xᴴ Q.mat, Matrix.IsHermitian.fromBlocks P.H rfl Q.H⟩

/-- The fidelity dual block matrix with diagonal blocks `Y`, `Z` and negative identity
off-diagonal blocks. -/
def fidelityDualBlock {I : Type*} [Fintype I] [DecidableEq I]
    (Y Z : HermitianMat I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  blockDiagonal Y Z - offDiagonal (1 : Matrix I I ℂ)

/-- The Hermitian matrix obtained by selecting the same row and column indices along `e`. -/
def principalBlock {I J : Type*} [Fintype I] [Fintype J]
    (X : HermitianMat J ℂ) (e : I → J) : HermitianMat I ℂ :=
  ⟨X.mat.submatrix e e, X.H.submatrix e⟩

/-- The real traces of off-diagonal blocks that make the block matrix with diagonals `P` and `Q`
positive semidefinite. -/
def fidelityPrimalValues {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ) : Set ℝ :=
  {a | ∃ X : Matrix I I ℂ,
    (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧ (Matrix.trace X).re = a}

/-- The half-weighted pairings with `P` and `Q` attained by pairs whose fidelity dual block is
positive semidefinite. -/
def fidelityDualValues {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : Set ℝ :=
  {a | ∃ Y Z : HermitianMat I ℂ, 0 ≤ fidelityDualBlock Y Z ∧
    (1/2 : ℝ) * ⟪P,Y⟫_ℝ + (1/2 : ℝ) * ⟪Q,Z⟫_ℝ = a}

/-- The spectral function applying the reciprocal square root to `P`, with value zero at zero. -/
def inverseSqrtOnSupport {I : Type*} [Fintype I] [DecidableEq I]
    (P : HermitianMat I ℂ) : HermitianMat I ℂ := P.cfc (fun x => (Real.sqrt x)⁻¹)

/-- The trace norm of the product of the Hermitian square roots of `P` and `Q`. -/
def rootFidelity {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) : ℝ := Matrix.traceNorm (P.sqrt.mat * Q.sqrt.mat)

/-- The block semidefinite program with diagonal blocks `P`, `Q` and objective given by half
`offDiagonal C`. -/
def weightedBlockProgram {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) :
    Program (I ⊕ I) (HermitianMat (I ⊕ I) ℂ) where
  constraint := blockPinch
  rhs := blockDiagonal P Q
  objective := (1/2 : ℝ) • offDiagonal C

/-- The Hermitian block matrix with diagonals `Y`, `Z` and off-diagonal blocks `-C`, `-Cᴴ`. -/
def weightedDualBlock {I : Type*} [Fintype I]
    (C : Matrix I I ℂ) (Y Z : HermitianMat I ℂ) : HermitianMat (I ⊕ I) ℂ :=
  blockDiagonal Y Z - offDiagonal C

/-- The trace norm of `C` sandwiched between the Hermitian square roots of `P` and `Q`. -/
def sandwichedTraceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (P.sqrt.mat * C * Q.sqrt.mat)

/-- The attainable real traces of `Cᴴ * X` subject to positivity of the block matrix with
diagonals `P` and `Q`. -/
def weightedBlockPrimalValues {I : Type*} [Fintype I] (P Q : HermitianMat I ℂ)
    (C : Matrix I I ℂ) : Set ℝ :=
  {a | ∃ X : Matrix I I ℂ, (Matrix.fromBlocks P.mat X Xᴴ Q.mat).PosSemidef ∧
    (Matrix.trace (Cᴴ * X)).re = a}

/-- The half-weighted pairings with `P` and `Q` attained by pairs with positive semidefinite
weighted dual block. -/
def weightedBlockDualValues {I : Type*} [Fintype I]
    (P Q : HermitianMat I ℂ) (C : Matrix I I ℂ) : Set ℝ :=
  {a | ∃ Y Z : HermitianMat I ℂ, 0 ≤ weightedDualBlock C Y Z ∧
    (1/2 : ℝ) * ⟪P,Y⟫_ℝ + (1/2 : ℝ) * ⟪Q,Z⟫_ℝ = a}

/-- The Hermitian Gram matrix `Aᴴ * A` of a square complex matrix. -/
def inputGram {I : Type*} [Fintype I] (A : Matrix I I ℂ) : HermitianMat I ℂ :=
  ⟨Aᴴ * A, (Matrix.posSemidef_conjTranspose_mul_self A).1⟩

/-- Reshapes a vector indexed by input and reference registers into a matrix with reference rows
and input columns. -/
def inputFrame {D R : ℕ} (u : Fin D × Fin R → ℂ) : Matrix (Fin R) (Fin D) ℂ :=
  fun r i => u (i,r)

/-- The type of positive semidefinite Hermitian input matrices with trace one. -/
abbrev DensityInput (D : ℕ) :=
  {ρ : HermitianMat (Fin D) ℂ // 0 ≤ ρ ∧ ρ.trace = (1 : ℝ)}

/-- The vector obtained by reshaping the square root of a density input with the specified index
order. -/
def densityVector {D : ℕ} (ρ : DensityInput D) : Fin D × Fin D → ℂ :=
  fun a => ρ.val.sqrt.mat a.2 a.1

/-- The trace norm of the Choi matrix sandwiched by the identity tensored with the square roots
of two density inputs. -/
def diamondChoiScore {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ σ : DensityInput D) : ℝ :=
  Matrix.traceNorm (Matrix.kronecker (1 : Operator E) ρ.val.sqrt.mat *
    MatrixMap.choi_matrix T * Matrix.kronecker (1 : Operator E) σ.val.sqrt.mat)

/-- The extended nonnegative supremum of `diamondChoiScore` over pairs of density inputs. -/
def diamondChoiValue {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ ρ : DensityInput D, ⨆ σ : DensityInput D, ENNReal.ofReal (diamondChoiScore T ρ σ)

/-- The Hermitian direct sum of two matrices with possibly different index types. -/
def directSum {I J : Type*} [Fintype I] [Fintype J]
    (P : HermitianMat I ℂ) (Q : HermitianMat J ℂ) : HermitianMat (I ⊕ J) ℂ :=
  ⟨Matrix.fromBlocks P.mat 0 0 Q.mat,
    Matrix.IsHermitian.fromBlocks P.H (by simp) Q.H⟩

/-- The Hermitian tensor product of the output identity matrix with the input matrix. -/
def densityLift {D E : ℕ} (ρ : HermitianMat (Fin D) ℂ) : HermitianMat (Fin E × Fin D) ℂ :=
  HermitianMat.kronecker (1 : HermitianMat (Fin E) ℂ) ρ

/-- The sum of register index types used for the two density blocks and the two Choi-space
blocks of the diamond program. -/
abbrev DiamondRegister (D E : ℕ) :=
  (Fin D ⊕ Fin D) ⊕ ((Fin E × Fin D) ⊕ (Fin E × Fin D))

/-- The Hilbert product space of two scalar constraints and two Hermitian block constraints for
the diamond program. -/
abbrev DiamondConstraints (D E : ℕ) := WithLp 2
  (WithLp 2 (ℝ × ℝ) × WithLp 2
    (HermitianMat (Fin E × Fin D) ℂ × HermitianMat (Fin E × Fin D) ℂ))

/-- Principal-block extraction along `e`, packaged as a real-linear map. -/
def principalLinear {I J : Type*} [Fintype I] [Fintype J] (e : I → J) :
    HermitianMat J ℂ →ₗ[ℝ] HermitianMat I ℂ where
  toFun X := principalBlock X e
  map_add' _ _ := by apply HermitianMat.ext; rfl
  map_smul' _ _ := by apply HermitianMat.ext; rfl

/-- The trace of a Hermitian matrix, packaged as a real-linear map. -/
noncomputable def traceLinear (I : Type*) [Fintype I] : HermitianMat I ℂ →ₗ[ℝ] ℝ where
  toFun := HermitianMat.trace
  map_add' := HermitianMat.trace_add
  map_smul' t X := HermitianMat.trace_smul X t

/-- Tensoring an input matrix with the output identity, packaged as a real-linear map. -/
def densityLiftLinear (D E : ℕ) : HermitianMat (Fin D) ℂ →ₗ[ℝ] HermitianMat (Fin E × Fin D) ℂ where
  toFun := densityLift
  map_add' := HermitianMat.kronecker_add 1
  map_smul' t X := by
    apply HermitianMat.ext
    simp only [densityLift, HermitianMat.kronecker_mat, HermitianMat.mat_smul]
    exact Matrix.kronecker_smul t _ _

/-- Pairs two real-linear maps into their product equipped with the `WithLp 2` representation. -/
def hilbertPair {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℝ A] [Module ℝ B] [Module ℝ C] (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C) :
    A →ₗ[ℝ] WithLp 2 (B × C) :=
  (WithLp.linearEquiv 2 ℝ (B × C)).symm.toLinearMap.comp (f.prod g)

set_option backward.isDefEq.respectTransparency false in

/-- The continuous linear map recording the density-block traces and deviations from their
lifted Choi-space blocks. -/
def diamondEqMap (D E : ℕ) : HermitianMat (DiamondRegister D E) ℂ →L[ℝ] DiamondConstraints D E :=
  let A₀ := principalLinear (fun i : Fin D => (Sum.inl (Sum.inl i) : DiamondRegister D E))
  let A₁ := principalLinear (fun i : Fin D => (Sum.inl (Sum.inr i) : DiamondRegister D E))
  let Z₀ := principalLinear (fun i : Fin E × Fin D => (Sum.inr (Sum.inl i) : DiamondRegister D E))
  let Z₁ := principalLinear (fun i : Fin E × Fin D => (Sum.inr (Sum.inr i) : DiamondRegister D E))
  LinearMap.toContinuousLinearMap (hilbertPair
    (hilbertPair ((traceLinear _).comp A₀) ((traceLinear _).comp A₁))
    (hilbertPair (Z₀ - (densityLiftLinear D E).comp A₀)
      (Z₁ - (densityLiftLinear D E).comp A₁)))

/-- Packages two real scalars and two Hermitian matrices as diamond constraint data. -/
def diamondDualData {D E : ℕ} (a b : ℝ)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ) : DiamondConstraints D E :=
  WithLp.toLp 2 (WithLp.toLp 2 (a,b), WithLp.toLp 2 (Y,Z))

/-- The semidefinite program with two trace-one input blocks and Choi-matrix off-diagonal
objective. -/
def diamondProgram {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Program (DiamondRegister D E) (DiamondConstraints D E) where
  constraint := diamondEqMap D E
  rhs := diamondDualData 1 1 0 0
  objective := directSum (0 : HermitianMat (Fin D ⊕ Fin D) ℂ)
    ((1/2 : ℝ) • offDiagonal (MatrixMap.choi_matrix T))

/-- Packages two input Hermitian matrices and a connecting block into the primal block matrix
for the diamond program. -/
def diamondPrimalData {D E : ℕ} (ρ σ : HermitianMat (Fin D) ℂ)
    (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : HermitianMat (DiamondRegister D E) ℂ :=
  directSum (blockDiagonal ρ σ) (fidelityPrimalBlock (densityLift ρ) (densityLift σ) X)

/-- The block matrix formed from `a • 1 - Y.traceLeft`, `b • 1 - Z.traceLeft`, `Y`, and `Z`. -/
def diamondAdjointData {D E : ℕ} (a b : ℝ)
    (Y Z : HermitianMat (Fin E × Fin D) ℂ) : HermitianMat (DiamondRegister D E) ℂ :=
  directSum (blockDiagonal (a • 1 - Y.traceLeft) (b • 1 - Z.traceLeft)) (blockDiagonal Y Z)

open scoped Matrix.Norms.L2Operator in

/-- Half the sum of the operator norms of the left partial traces of the two dual blocks. -/
def diamondDualObjective {D E : ℕ} (Y Z : HermitianMat (Fin E × Fin D) ℂ) : ℝ :=
  (1/2 : ℝ) * ‖Y.traceLeft.mat‖ + (1/2 : ℝ) * ‖Z.traceLeft.mat‖

/-- The dual objective values of pairs with positive semidefinite Choi-weighted dual block. -/
def diamondSourceDualValues {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Set ℝ :=
  {a | ∃ Y Z : HermitianMat (Fin E × Fin D) ℂ,
    0 ≤ weightedDualBlock (MatrixMap.choi_matrix T) Y Z ∧ diamondDualObjective Y Z = a}

/-- The real Choi pairings attained by positive semidefinite connecting blocks over pairs of
density inputs. -/
def diamondSourcePrimalValues {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : Set ℝ :=
  {a | ∃ (ρ σ : DensityInput D) (X : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ),
    (fidelityPrimalBlock (densityLift ρ.val) (densityLift σ.val) X).mat.PosSemidef ∧
      (Matrix.trace ((MatrixMap.choi_matrix T)ᴴ * X)).re = a}

/-- The Hermitian Gram matrix `Aᴴ * A` of a rectangular complex matrix. -/
def frameGram {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℂ) : HermitianMat I ℂ :=
  ⟨Aᴴ * A, (Matrix.posSemidef_conjTranspose_mul_self A).1⟩

/-- The complex-linear map sending `X` to the partial trace over `Z` of `A * X * Bᴴ`. -/
def stinespringCross {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Operator D →ₗ[ℂ] Operator E where
  toFun X := (A * X * Bᴴ).traceRight
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.traceRight_add]
  map_smul' r X := by
    rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.traceRight_smul]

/-- The complementary Hermitian output obtained by conjugating by `A` and tracing out the output
register. -/
def stinespringComplement {D E : ℕ} {Z : Type*} [Fintype Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (ρ : HermitianMat (Fin D) ℂ) : HermitianMat Z ℂ :=
  (ρ.conj A).traceLeft

/-- The extended nonnegative supremum of root fidelities between complementary outputs over
pairs of density inputs. -/
def maxOutputRootFidelity {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : ℝ≥0∞ :=
  ⨆ ρ : DensityInput D, ⨆ σ : DensityInput D,
    ENNReal.ofReal (rootFidelity (stinespringComplement A ρ.val) (stinespringComplement B σ.val))

/-- The transpose of a complex Hermitian matrix, bundled as a Hermitian matrix. -/
def hermitianTranspose {I : Type*} [Fintype I] (P : HermitianMat I ℂ) : HermitianMat I ℂ :=
  ⟨P.matᵀ,P.H.transpose⟩

/-- The matrix obtained by contracting the input index of `A` against the transposed indexing of
the density square root. -/
def stinespringFrame {D E : ℕ} {Z : Type*} [Fintype Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) (ρ : DensityInput D) : Matrix (Fin E × Fin D) Z ℂ :=
  fun p z => ∑ i, A (p.1,z) i * ρ.val.sqrt.mat p.2 i

/-- Reshapes a Stinespring matrix into a matrix with combined output-input rows and environment
columns. -/
def stinespringFactor {D E : ℕ} {Z : Type*}
    (A : Matrix (Fin E × Z) (Fin D) ℂ) : Matrix (Fin E × Fin D) Z ℂ :=
  fun p z => A (p.1,z) p.2

/-- The left canonical Stinespring factor obtained by reshaping the Choi matrix of `T`. -/
def canonicalStinespringLeft {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Matrix (Fin E × (Fin E × Fin D)) (Fin D) ℂ :=
  fun p i => MatrixMap.choi_matrix T (p.1,i) p.2

/-- The right canonical Stinespring factor obtained by reshaping the identity on output-input
indices. -/
def canonicalStinespringRight (D E : ℕ) : Matrix (Fin E × (Fin E × Fin D)) (Fin D) ℂ :=
  fun p i => (1 : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) (p.1,i) p.2

/-- Left partial trace of Hermitian matrices, packaged as a real-linear map. -/
def partialTraceLeftLinear (I J : Type*) [Fintype I] [Fintype J] :
    HermitianMat (I × J) ℂ →ₗ[ℝ] HermitianMat J ℂ where
  toFun := HermitianMat.traceLeft
  map_add' := HermitianMat.traceLeft_add
  map_smul' r X := HermitianMat.traceLeft_smul X r

set_option backward.isDefEq.respectTransparency false in

/-- The complementary output associated with `A`, packaged as a continuous real-linear map. -/
def stinespringComplementLinear {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix (Fin E × Z) (Fin D) ℂ) :
    HermitianMat (Fin D) ℂ →L[ℝ] HermitianMat Z ℂ :=
  LinearMap.toContinuousLinearMap
    ((partialTraceLeftLinear (Fin E) Z).comp (HermitianMat.conjLinear ℝ A))

/-- The sum of index types for two input blocks and two environment blocks in the Stinespring
program. -/
abbrev StinespringRegister (D : ℕ) (Z : Type*) := (Fin D ⊕ Fin D) ⊕ (Z ⊕ Z)

/-- The Hilbert product space of two scalar constraints and two Hermitian environment
constraints. -/
abbrev StinespringConstraints (Z : Type*) := WithLp 2
  (WithLp 2 (ℝ × ℝ) × WithLp 2 (HermitianMat Z ℂ × HermitianMat Z ℂ))

/-- Packages two scalars and two environment matrices as Stinespring constraint data. -/
def stinespringDualData {Z : Type*} (a b : ℝ) (Y W : HermitianMat Z ℂ) : StinespringConstraints Z :=
  WithLp.toLp 2 (WithLp.toLp 2 (a,b),WithLp.toLp 2 (Y,W))

set_option backward.isDefEq.respectTransparency false in

/-- The continuous linear map recording input-block traces and deviations from the corresponding
complementary outputs. -/
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

/-- The semidefinite program with trace-one input blocks and a fidelity objective on
complementary outputs. -/
def stinespringProgram {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) :
    Program (StinespringRegister D Z) (StinespringConstraints Z) where
  constraint := stinespringEqMap A B
  rhs := stinespringDualData 1 1 0 0
  objective := directSum (0 : HermitianMat (Fin D ⊕ Fin D) ℂ)
    ((1/2 : ℝ) • offDiagonal (1 : Matrix Z Z ℂ))

/-- Packages two input matrices and an environment connecting block into the Stinespring primal
matrix. -/
def stinespringPrimalData {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (ρ σ : HermitianMat (Fin D) ℂ) (X : Matrix Z Z ℂ) :
    HermitianMat (StinespringRegister D Z) ℂ :=
  directSum (blockDiagonal ρ σ)
    (fidelityPrimalBlock (stinespringComplement A ρ) (stinespringComplement B σ) X)

/-- The direct-sum block expression using the adjoints of the two complementary maps and the
environment dual blocks. -/
def stinespringAdjointData {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (a b : ℝ) (Y W : HermitianMat Z ℂ) :
    HermitianMat (StinespringRegister D Z) ℂ :=
  directSum (blockDiagonal (a • 1 - (stinespringComplementLinear A).adjoint Y)
    (b • 1 - (stinespringComplementLinear B).adjoint W)) (blockDiagonal Y W)

/-- The real traces attained by positive semidefinite fidelity blocks for complementary outputs
of density inputs. -/
def stinespringSourcePrimalValues {D E : ℕ} {Z : Type*} [Fintype Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Set ℝ :=
  {a | ∃ (ρ σ : DensityInput D) (X : Matrix Z Z ℂ),
    (fidelityPrimalBlock (stinespringComplement A ρ.val) (stinespringComplement B σ.val) X).mat.PosSemidef ∧
      (Matrix.trace X).re = a}

open scoped Matrix.Norms.L2Operator in

/-- Half the sum of the operator norms of the two complementary-map adjoints applied to their
dual blocks. -/
def stinespringBlockDualObjective {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) (Y W : HermitianMat Z ℂ) : ℝ :=
  (1/2 : ℝ) * ‖((stinespringComplementLinear A).adjoint Y).mat‖ +
    (1/2 : ℝ) * ‖((stinespringComplementLinear B).adjoint W).mat‖

/-- The Stinespring block dual objective values attained by pairs with positive semidefinite
fidelity dual block. -/
def stinespringBlockDualValues {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Set ℝ :=
  {a | ∃ Y W : HermitianMat Z ℂ, 0 ≤ fidelityDualBlock Y W ∧
    stinespringBlockDualObjective A B Y W = a}

/-- The Stinespring dual objective values obtained from a positive definite matrix and its
inverse. -/
def stinespringInverseDualValues {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : Set ℝ :=
  {a | ∃ Y : HermitianMat Z ℂ, Y.mat.PosDef ∧ stinespringBlockDualObjective A B Y Y⁻¹ = a}

namespace Program
variable {I F : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The condition that every perturbation of norm at most `r` around `y` remains dual feasible. -/
def DualInteriorBall (P : Program I F) (y : F) (r : ℝ) : Prop :=
  ∀ h : F, ‖h‖ ≤ r → P.DualFeasible (y + h)
end Program

open scoped Matrix.Norms.L2Operator in

/-- The specified Stinespring dual center with identity environment blocks and scalar components
determined by adjoint operator norms. -/
def stinespringDualCenter {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : StinespringConstraints Z :=
  stinespringDualData ((1/2 : ℝ) + ‖((stinespringComplementLinear A).adjoint 1).mat‖)
    ((1/2 : ℝ) + ‖((stinespringComplementLinear B).adjoint 1).mat‖) 1 1

open scoped Matrix.Norms.L2Operator in

/-- One plus the sum of the operator norms of the complementary-map adjoints applied to the
identity. -/
def stinespringPerturbationScale {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : ℝ :=
  1 + ‖((stinespringComplementLinear A).adjoint 1).mat‖ +
    ‖((stinespringComplementLinear B).adjoint 1).mat‖

/-- The reciprocal of four times the Stinespring perturbation scale. -/
def stinespringInteriorRadius {D E : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A B : Matrix (Fin E × Z) (Fin D) ℂ) : ℝ :=
  (4 * stinespringPerturbationScale A B)⁻¹

open scoped Matrix.Norms.L2Operator in

/-- The specified diamond dual center with scalar identity blocks scaled by the Choi operator
norm. -/
def diamondDualCenter {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : DiamondConstraints D E :=
  let a : ℝ := ‖MatrixMap.choi_matrix T‖ / 2 + 1
  diamondDualData (1 + a * E) (1 + a * E)
    (a • (1 : HermitianMat (Fin E × Fin D) ℂ)) (a • 1)

/-- The radius `1 / (2 * max 1 E)` used for the diamond dual center. -/
def diamondInteriorRadius (E : ℕ) : ℝ := (2 * (max 1 E : ℕ) : ℝ)⁻¹

/-- The affine combination of `y` and the designated diamond dual center with weights `1 - θ`
and `θ`. -/
def diamondRegularizedDual {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (θ : ℝ) (y : DiamondConstraints D E) : DiamondConstraints D E :=
  (1-θ) • y + θ • diamondDualCenter T

open scoped Matrix.Norms.L2Operator in

/-- The regularization weight given by the minimum of one and the specified error-to-size ratio. -/
def diamondRegularizationWeight {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℝ :=
  min 1 (ε / (2 * (3 + (‖MatrixMap.choi_matrix T‖ + 2) * E)))

/-- The diamond regularization weight divided by twice `1 + E`. -/
def diamondRoundingRadius {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℝ :=
  diamondRegularizationWeight T ε / (2 * (1 + E))

/-- A matrix of integer pairs encoding real and imaginary dyadic numerators. -/
abbrev GaussianDyadicPayload (I : Type*) := Matrix I I (ℤ × ℤ)

/-- Decodes integer numerator pairs into complex entries with common denominator `2 ^ p`. -/
def gaussianDyadicDecode {I : Type*} (p : ℕ) (P : GaussianDyadicPayload I) : Matrix I I ℂ :=
  fun i j => ⟨((P i j).1 : ℝ) / (2 : ℝ)^p, ((P i j).2 : ℝ) / (2 : ℝ)^p⟩

/-- Encodes a complex matrix by flooring its real and imaginary parts after multiplication by `2
^ p`. -/
def complexDyadicPayload {I : Type*} (p : ℕ) (A : Matrix I I ℂ) : GaussianDyadicPayload I :=
  fun i j => (⌊(2 : ℝ)^p * (A i j).re⌋,⌊(2 : ℝ)^p * (A i j).im⌋)

/-- Encodes rational real-imaginary pairs by flooring each component after multiplication by `2
^ p`. -/
def rationalDyadicPayload {I : Type*} (p : ℕ) (A : Matrix I I (ℚ × ℚ)) : GaussianDyadicPayload I :=
  fun i j => (⌊(2 : ℚ)^p * (A i j).1⌋,⌊(2 : ℚ)^p * (A i j).2⌋)

/-- Interprets a matrix of rational pairs as a complex matrix. -/
def gaussianRatMatrix {I : Type*} (A : Matrix I I (ℚ × ℚ)) : Matrix I I ℂ :=
  fun i j => ⟨(A i j).1,(A i j).2⟩

/-- Decodes a Gaussian dyadic payload and averages it with its conjugate transpose to obtain a
Hermitian matrix. -/
def hermitianDyadicDecode {I : Type*} [Fintype I] (p : ℕ) (P : GaussianDyadicPayload I) : HermitianMat I ℂ :=
  ⟨(1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ), by
    change ((1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ))ᴴ =
      (1/2 : ℝ) • (gaussianDyadicDecode p P + (gaussianDyadicDecode p P)ᴴ)
    simp [Matrix.conjTranspose_smul,add_comm]⟩

/-- The rational real-imaginary pair representation of the Hermitian symmetrization of a dyadic
payload. -/
def hermitianDyadicRatDecode {I : Type*} (p : ℕ) (P : GaussianDyadicPayload I) : Matrix I I (ℚ × ℚ) :=
  fun i j => (((P i j).1 + (P j i).1 : ℤ) / (2 : ℚ)^(p+1),
    ((P i j).2 - (P j i).2 : ℤ) / (2 : ℚ)^(p+1))

/-- Integer payload data for the two scalar coordinates and two complex matrix blocks of a
diamond dual candidate. -/
structure DiamondDyadicData (D E : ℕ) where
  scalar0 : ℤ
  scalar1 : ℤ
  block0 : GaussianDyadicPayload (Fin E × Fin D)
  block1 : GaussianDyadicPayload (Fin E × Fin D)

/-- Decodes diamond dyadic data into two real scalars and two Hermitian dual blocks. -/
def diamondDyadicDecode {D E : ℕ} (p : ℕ) (P : DiamondDyadicData D E) : DiamondConstraints D E :=
  diamondDualData ((P.scalar0 : ℝ) / (2 : ℝ)^p) ((P.scalar1 : ℝ) / (2 : ℝ)^p)
    (hermitianDyadicDecode p P.block0) (hermitianDyadicDecode p P.block1)

/-- Encodes the scalar and matrix components of diamond constraint data by dyadic floor
rounding. -/
def diamondDyadicPayload {D E : ℕ} (p : ℕ) (y : DiamondConstraints D E) : DiamondDyadicData D E where
  scalar0 := ⌊(2 : ℝ)^p * (WithLp.ofLp (WithLp.ofLp y).1).1⌋
  scalar1 := ⌊(2 : ℝ)^p * (WithLp.ofLp (WithLp.ofLp y).1).2⌋
  block0 := complexDyadicPayload p (WithLp.ofLp (WithLp.ofLp y).2).1.mat
  block1 := complexDyadicPayload p (WithLp.ofLp (WithLp.ofLp y).2).2.mat

/-- The binary precision parameter `q.log2 + 1`. -/
def dyadicPrecision (q : ℕ) : ℕ := q.log2 + 1

/-- The dyadic precision selected from the dimensions and the diamond rounding radius. -/
def diamondDyadicPrecision {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℕ :=
  dyadicPrecision ⌈(2 + 4 * (E : ℝ) * D) / diamondRoundingRadius T ε⌉₊

/-- The number `2 * (E * D) ^ 2` of integer components in one Gaussian dyadic block. -/
def gaussianDyadicWordCount (D E : ℕ) : ℕ := (E*D)*(E*D)*2

/-- The equivalence flattening two block indices and a real-imaginary selector into a single
word index. -/
def gaussianDyadicWordIndex (D E : ℕ) :
    (((Fin E × Fin D) × (Fin E × Fin D)) × Fin 2) ≃ Fin (gaussianDyadicWordCount D E) :=
  (Equiv.prodCongr ((Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv)
    (Equiv.refl (Fin 2))).trans finProdFinEquiv

/-- Reads the real or imaginary integer numerator at the flattened block word index. -/
def gaussianDyadicWord {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D))
    (k : Fin (gaussianDyadicWordCount D E)) : ℤ :=
  let t := (gaussianDyadicWordIndex D E).symm k
  if t.2 = 0 then (P t.1.1 t.1.2).1 else (P t.1.1 t.1.2).2

/-- The ordered list of all integer words in a Gaussian dyadic block. -/
def gaussianDyadicWords {D E : ℕ} (P : GaussianDyadicPayload (Fin E × Fin D)) : List ℤ :=
  List.ofFn (gaussianDyadicWord P)

/-- Reconstructs a Gaussian dyadic block from its integer words, using zero for missing
positions. -/
def gaussianDyadicFromWords (D E : ℕ) (xs : List ℤ) : GaussianDyadicPayload (Fin E × Fin D) :=
  fun i j => ((xs[(gaussianDyadicWordIndex D E ((i,j),0)).val]?).getD 0,
    (xs[(gaussianDyadicWordIndex D E ((i,j),1)).val]?).getD 0)

/-- The number of words for two scalar coordinates and two Gaussian dyadic blocks. -/
def diamondDyadicWordCount (D E : ℕ) : ℕ := 2 + 2 * gaussianDyadicWordCount D E

/-- Serializes diamond dyadic data as two scalar words followed by the words of its two blocks. -/
def diamondDyadicWords {D E : ℕ} (P : DiamondDyadicData D E) : List ℤ :=
  [P.scalar0,P.scalar1] ++ gaussianDyadicWords P.block0 ++ gaussianDyadicWords P.block1

/-- Parses diamond dyadic data from a word list of exactly the required length. -/
def diamondDyadicFromWords (D E : ℕ) (xs : List ℤ) : Option (DiamondDyadicData D E) :=
  if xs.length = diamondDyadicWordCount D E then some {
    scalar0 := (xs[0]?).getD 0
    scalar1 := (xs[1]?).getD 0
    block0 := gaussianDyadicFromWords D E ((xs.drop 2).take (gaussianDyadicWordCount D E))
    block1 := gaussianDyadicFromWords D E ((xs.drop 2).drop (gaussianDyadicWordCount D E)) }
  else none

/-- The precision parameter derived from the natural ceiling of `2 ^ p * R + 1`. -/
def dyadicWordWidth (p : ℕ) (R : ℝ) : ℕ := dyadicPrecision ⌈(2 : ℝ)^p*R + 1⌉₊

/-- The rational version of the precision parameter derived from the ceiling of `2 ^ p * R + 1`. -/
def rationalDyadicWordWidth (p : ℕ) (R : ℚ) : ℕ := dyadicPrecision ⌈(2 : ℚ)^p*R + 1⌉₊

/-- The condition that every serialized integer word has absolute value strictly below `2 ^ b`. -/
def DiamondDyadicData.WordBound {D E : ℕ} (P : DiamondDyadicData D E) (b : ℕ) : Prop :=
  ∀ n ∈ diamondDyadicWords P, n.natAbs < 2^b

open scoped Matrix.Norms.L2Operator in
/-- The size expression `(D + 1) * (E * ‖choi_matrix T‖ + ε)`. -/
def diamondDyadicOuterSize {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℝ :=
  (D+1 : ℝ) * (E * ‖MatrixMap.choi_matrix T‖ + ε)

/-- The word-width parameter obtained from the selected diamond precision and outer size. -/
def diamondDyadicWordWidth {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (ε : ℝ) : ℕ :=
  dyadicWordWidth (diamondDyadicPrecision T ε) (diamondDyadicOuterSize T ε)

/-- Lists the bits of a bit vector in order from least significant to most significant. -/
def dyadicBitVecBits {w : ℕ} (v : BitVec w) : List Bool :=
  List.ofFn (fun k : Fin w => v.getLsbD k.val)

/-- Encodes an integer in `b + 1` bits using `BitVec.ofInt`, in least-significant-bit order. -/
def signedDyadicWordBits (b : ℕ) (n : ℤ) : List Bool :=
  dyadicBitVecBits (BitVec.ofInt (b+1) n)

/-- Decodes a little-endian Boolean list as the signed integer of its bit vector. -/
def signedDyadicWordFromBits (bs : List Bool) : ℤ := (BitVec.ofBoolListLE bs).toInt

/-- Concatenates the fixed-width signed encodings of an integer word list. -/
def signedDyadicWordsBits (b : ℕ) (xs : List ℤ) : List Bool :=
  xs.flatMap (signedDyadicWordBits b)

/-- Reads the specified number of signed words by repeatedly taking blocks of `b + 1` bits. -/
def signedDyadicWordsRead (b : ℕ) : ℕ → List Bool → List ℤ
  | 0,_ => []
  | n+1,bs => signedDyadicWordFromBits (bs.take (b+1)) :: signedDyadicWordsRead b n (bs.drop (b+1))

/-- The number of bits used for all diamond payload words at signed width `b + 1`. -/
def diamondDyadicBitCount (D E b : ℕ) : ℕ := diamondDyadicWordCount D E * (b+1)

/-- The concatenated signed bit encoding of a diamond dyadic payload. -/
def diamondDyadicBits {D E : ℕ} (b : ℕ) (P : DiamondDyadicData D E) : List Bool :=
  signedDyadicWordsBits b (diamondDyadicWords P)

/-- Parses a diamond dyadic payload from a bit list of exactly the required length. -/
def diamondDyadicFromBits (D E b : ℕ) (bs : List Bool) : Option (DiamondDyadicData D E) :=
  if bs.length = diamondDyadicBitCount D E b then
    diamondDyadicFromWords D E (signedDyadicWordsRead b (diamondDyadicWordCount D E) bs)
  else none

/-- The quadratic algebra of Gaussian rationals with defining relation `i ^ 2 = -1`. -/
abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

scoped instance gaussianRationalNoRoot : Fact (∀ r : ℚ, r^2 ≠ (-1 : ℚ) + 0*r) :=
  ⟨by intro r h; nlinarith [sq_nonneg r]⟩

/-- The ring homomorphism embedding Gaussian rationals into the complex numbers. -/
def gaussianRationalEmbed : GaussianRational →+* ℂ where
  toFun z := ⟨(z.re : ℝ),(z.im : ℝ)⟩
  map_zero' := by apply Complex.ext <;> norm_num
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by
    apply Complex.ext <;> simp [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add]
  map_mul' z w := by
    apply Complex.ext <;> simp
        [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,Complex.mul_re,Complex.mul_im,sub_eq_add_neg]

/-- Embeds a Gaussian rational matrix into the complex numbers entrywise. -/
def gaussianRationalMatrix {I : Type*} (Q : Matrix I I GaussianRational) : Matrix I I ℂ :=
    Q.map gaussianRationalEmbed

/-- The trailing principal submatrix obtained by removing row and column zero. -/
def gaussianRationalTail {n : ℕ} (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) : Matrix (Fin n) (Fin n) GaussianRational :=
  fun i j => Q i.succ j.succ

/-- The Schur-complement expression for the leading scalar entry of a Gaussian rational matrix. -/
def gaussianRationalSchur {n : ℕ} (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) : Matrix (Fin n) (Fin n) GaussianRational :=
  fun i j => Q i.succ j.succ - Q i.succ 0 * (Q 0 0)⁻¹ * Q 0 j.succ

/-- A square Gaussian rational matrix stored as a vector of row vectors. -/
abbrev GaussianRationalTable (n : ℕ) := Vector (Vector GaussianRational n) n

/-- Stores a function-valued Gaussian rational matrix as a vector of row vectors. -/
def gaussianRationalTable {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational) : GaussianRationalTable n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => Q i j))

/-- Recovers the function-valued matrix from a vector table. -/
def gaussianRationalTableMatrix {n : ℕ} (A : GaussianRationalTable n) : Matrix (Fin n) (Fin n) GaussianRational :=
  fun i j => A[i][j]

/-- A recursive Boolean positivity test using Hermitian symmetry, the leading diagonal entry,
and trailing or Schur-complement recursion. -/
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

/-- The Boolean positive semidefiniteness test applied to a Gaussian rational table. -/
def gaussianRationalPsdCheck {n : ℕ} (A : GaussianRationalTable n) : Bool :=
  gaussianRationalPsdCore n A

/-- Constructs a Gaussian rational from its rational real and imaginary parts. -/
def gaussianRationalOfPair (z : ℚ × ℚ) : GaussianRational := ⟨z.1,z.2⟩

/-- Runs the Gaussian rational positivity test on a matrix of rational real-imaginary pairs. -/
def rationalPairPsdCheck {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ)) : Bool :=
  gaussianRationalPsdCheck (gaussianRationalTable (Q.map gaussianRationalOfPair))

/-- Tests the rational Hermitian decoding of a dyadic block after flattening its product
indices. -/
def dyadicBlockPsdCheck (D E p : ℕ) (P : GaussianDyadicPayload (Fin E × Fin D)) : Bool :=
  rationalPairPsdCheck ((hermitianDyadicRatDecode p P).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)

/-- The Gaussian rational quadratic form `vᴴ * Q * v`, written using vector products. -/
def gaussianRationalQuadratic {n : ℕ} (Q : Matrix (Fin n) (Fin n) GaussianRational)
    (v : Fin n → GaussianRational) : GaussianRational := star v ⬝ᵥ (Q *ᵥ v)

/-- Extends a vector by the leading coordinate determined by the Schur-complement elimination
formula. -/
def gaussianRationalSchurLift {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (v : Fin n → GaussianRational) : Fin (n+1) → GaussianRational :=
  Fin.cons (-(Q 0 0)⁻¹ * ∑ j, Q 0 j.succ * v j) v

/-- The two-coordinate vector expression used when a leading zero diagonal has a nonzero cross
entry. -/
def gaussianRationalCrossVector {n : ℕ}
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) GaussianRational) (j : Fin n) : Fin (n+1) → GaussianRational :=
  Fin.cons (-(Q j.succ j.succ + 1) / (2 * star (Q 0 j.succ))) (Pi.single j 1)

/-- Recursively searches for a Gaussian rational direction using a negative pivot, a nonzero
cross entry, or Schur-complement recursion. -/
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

/-- A positivity-test result distinguishing a non-Hermitian matrix, a positive classification,
and a returned negative direction. -/
inductive GaussianRationalPsdResult (n : ℕ) where
  | nonHermitian
  | psd
  | negative (direction : Vector GaussianRational n)

/-- Checks Hermitian symmetry and classifies a Gaussian rational table using the recursive
direction search. -/
def gaussianRationalPsdSeparate {n : ℕ} (A : GaussianRationalTable n) : GaussianRationalPsdResult n :=
  if (gaussianRationalTableMatrix A).IsHermitian then
    match gaussianRationalNegativeCore n A with
    | none => .psd
    | some v => .negative v
  else .nonHermitian

/-- Runs the Gaussian rational separation procedure on a matrix of rational pairs. -/
def rationalPairPsdSeparate {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ℚ × ℚ)) : GaussianRationalPsdResult n :=
  gaussianRationalPsdSeparate (gaussianRationalTable (Q.map gaussianRationalOfPair))

/-- The equivalence flattening all diamond register blocks into a single finite index type. -/
def diamondRationalRegisterEquiv (D E : ℕ) : DiamondRegister D E ≃ Fin ((D+D)+(E*D+E*D)) :=
  (Equiv.sumCongr finSumFinEquiv ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

/-- The Gaussian rational diamond dual slack matrix with scalar-minus-partial-trace blocks and
Choi off-diagonal blocks. -/
def diamondRationalSlack {D E : ℕ} (J Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (a b : ℚ) : Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin D => (a : GaussianRational)) - Y.traceLeft) 0 0
      (Matrix.diagonal (fun _ : Fin D => (b : GaussianRational)) - Z.traceLeft)) 0 0
    (Matrix.fromBlocks Y (-(1/2 : GaussianRational) • J) (-(1/2 : GaussianRational) • Jᴴ) Z)

/-- The rational diamond dual slack built from the decoded dyadic scalar and matrix payloads. -/
def diamondDyadicRationalSlack {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  diamondRationalSlack J ((hermitianDyadicRatDecode p P.block0).map gaussianRationalOfPair)
    ((hermitianDyadicRatDecode p P.block1).map gaussianRationalOfPair)
    ((P.scalar0 : ℚ) / 2^p) ((P.scalar1 : ℚ) / 2^p)

/-- The finite vector table of the dyadic diamond slack after flattening register indices. -/
def diamondDyadicSlackTable {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : GaussianRationalTable ((D+D)+(E*D+E*D)) :=
  gaussianRationalTable ((diamondDyadicRationalSlack J p P).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm)

/-- Runs the Gaussian rational positivity check on the dyadic diamond slack table. -/
def diamondDyadicFeasibleCheck {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : Bool :=
  gaussianRationalPsdCheck (diamondDyadicSlackTable J p P)

/-- Runs the Gaussian rational separation procedure on the dyadic diamond slack table. -/
def diamondDyadicFeasibleSeparate {D E : ℕ} (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p : ℕ) (P : DiamondDyadicData D E) : GaussianRationalPsdResult ((D+D)+(E*D+E*D)) :=
  gaussianRationalPsdSeparate (diamondDyadicSlackTable J p P)

/-- Parses a binary diamond payload and, on successful parsing, checks its rational dual slack. -/
def diamondDyadicBinaryFeasibleCheck {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (p b : ℕ) (bs : List Bool) : Option Bool :=
  (diamondDyadicFromBits D E b bs).map (diamondDyadicFeasibleCheck J p)

/-- The sum over matrix entries of the absolute values of their rational real and imaginary
parts. -/
def gaussianRationalNormBound {I : Type*} [Fintype I] (J : Matrix I I GaussianRational) : ℚ :=
  ∑ i, ∑ j, (|(J i j).re| + |(J i j).im|)

/-- The rational regularization weight using `gaussianRationalNormBound` in the specified
error-to-size ratio. -/
def diamondRationalWeight {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  min 1 (ε / (2 * (3 + (gaussianRationalNormBound J + 2) * E)))

/-- The rational regularization weight divided by twice `1 + E`. -/
def diamondRationalRadius {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  diamondRationalWeight J ε / (2 * (1 + E))

/-- The dyadic precision selected from the rational diamond rounding radius and register
dimensions. -/
def diamondRationalPrecision {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℕ :=
  dyadicPrecision ⌈(2 + 4 * (E : ℚ) * D) / diamondRationalRadius J ε⌉₊

/-- The rational outer-size expression based on the Gaussian rational entrywise norm bound. -/
def diamondRationalOuterSize {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  (D+1 : ℚ) * (E * gaussianRationalNormBound J + ε)

/-- The rational dyadic word-width parameter determined by the precision and outer size. -/
def diamondRationalWidth {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℕ :=
  rationalDyadicWordWidth (diamondRationalPrecision J ε) (diamondRationalOuterSize J ε)

/-- Half the Gaussian rational norm bound plus one, used to scale the center blocks. -/
def diamondRationalCenterScale {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : ℚ :=
  gaussianRationalNormBound J / 2 + 1

/-- The scalar `1 + E * diamondRationalCenterScale J` for the rational dual center. -/
def diamondRationalCenterScalar {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : ℚ :=
  1 + diamondRationalCenterScale J * E

/-- The rational diamond slack at the scalar-identity center blocks. -/
def diamondRationalCenterSlack {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) :
    Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  diamondRationalSlack J (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))
    (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))
    (diamondRationalCenterScalar J) (diamondRationalCenterScalar J)

/-- The real diamond constraint data obtained from the rational center scalars and identity
blocks. -/
noncomputable def diamondRationalCenter {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : DiamondConstraints D E :=
  diamondDualData (diamondRationalCenterScalar J : ℝ) (diamondRationalCenterScalar J : ℝ)
    ((diamondRationalCenterScale J : ℝ) • 1) ((diamondRationalCenterScale J : ℝ) • 1)

/-- The rational radius `1 / (2 * (1 + E))`. -/
def diamondRationalInteriorRadius (E : ℕ) : ℚ := (2 * (1 + E))⁻¹

/-- The rational coordinate space with one coordinate for every serialized diamond word. -/
abbrev DiamondRationalCoordinates (D E : ℕ) := Fin (diamondDyadicWordCount D E) → ℚ

/-- The coordinate index of either of the two scalar components. -/
def diamondRationalScalarIndex (D E : ℕ) (k : Fin 2) : Fin (diamondDyadicWordCount D E) :=
  ⟨k.val,by have hk := k.isLt; unfold diamondDyadicWordCount; omega⟩

/-- The coordinate index of a block entry and its real-imaginary component, with a Boolean
selecting the block. -/
def diamondRationalBlockIndex (D E : ℕ) (b : Bool)
    (i j : Fin E × Fin D) (part : Fin 2) : Fin (diamondDyadicWordCount D E) :=
  let k := gaussianDyadicWordIndex D E ((i,j),part)
  ⟨2 + (if b then gaussianDyadicWordCount D E else 0) + k.val, by
    have hk := k.isLt
    unfold diamondDyadicWordCount
    split <;> omega⟩

/-- Reconstructs one Gaussian rational matrix block from its rational coordinates. -/
def diamondRationalRawBlock {D E : ℕ} (b : Bool) (x : DiamondRationalCoordinates D E) :
    Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational :=
  fun i j => gaussianRationalOfPair (x (diamondRationalBlockIndex D E b i j 0),
    x (diamondRationalBlockIndex D E b i j 1))

/-- The Hermitian symmetrization `(Q + Qᴴ) / 2` over the Gaussian rationals. -/
def gaussianRationalSymmetrize {I : Type*} (Q : Matrix I I GaussianRational) : Matrix I I GaussianRational :=
  (1/2 : GaussianRational) • (Q + Qᴴ)

/-- The symmetrized Gaussian rational block reconstructed from the selected coordinates. -/
def diamondRationalSymBlock {D E : ℕ} (b : Bool) (x : DiamondRationalCoordinates D E) :
    Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational :=
  gaussianRationalSymmetrize (diamondRationalRawBlock b x)

/-- The rational diamond slack matrix reconstructed from scalar coordinates and symmetrized
block coordinates. -/
def diamondRationalCandidateSlack {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    Matrix (DiamondRegister D E) (DiamondRegister D E) GaussianRational :=
  diamondRationalSlack J (diamondRationalSymBlock false x) (diamondRationalSymBlock true x)
    (x (diamondRationalScalarIndex D E 0)) (x (diamondRationalScalarIndex D E 1))

/-- Embeds a Gaussian rational matrix into the complexes and symmetrizes it as a Hermitian
matrix. -/
noncomputable def gaussianRationalHermitianDecode {I : Type*} [Fintype I]
    (Q : Matrix I I GaussianRational) : HermitianMat I ℂ :=
  ⟨(1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ), by
    change ((1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ))ᴴ =
      (1/2 : ℝ) • (gaussianRationalMatrix Q + (gaussianRationalMatrix Q)ᴴ)
    simp [Matrix.conjTranspose_smul,add_comm]⟩

/-- Decodes rational diamond coordinates as real scalars and Hermitian complex blocks. -/
noncomputable def diamondRationalDecode {D E : ℕ} (x : DiamondRationalCoordinates D E) : DiamondConstraints D E :=
  diamondDualData (x (diamondRationalScalarIndex D E 0) : ℝ) (x (diamondRationalScalarIndex D E 1) : ℝ)
    (gaussianRationalHermitianDecode (diamondRationalRawBlock false x))
    (gaussianRationalHermitianDecode (diamondRationalRawBlock true x))

/-- A rational affine-cut description consisting of a coefficient vector and a scalar bound. -/
structure RationalAffineCut (n : ℕ) where
  coefficients : Vector ℚ n
  bound : ℚ

/-- The linear form obtained by pairing the cut coefficients with rational coordinates. -/
def RationalAffineCut.eval {n : ℕ} (C : RationalAffineCut n) (x : Fin n → ℚ) : ℚ :=
  ∑ k, C.coefficients[k] * x k

/-- The affine cut obtained from the real part of the slack quadratic form in the supplied
direction. -/
def diamondRationalSeparationCut {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (v : Vector GaussianRational ((D+D)+(E*D+E*D))) : RationalAffineCut (diamondDyadicWordCount D E) where
  coefficients := Vector.ofFn (fun k => (gaussianRationalQuadratic
    ((diamondRationalCandidateSlack 0 (Pi.single k 1)).submatrix
      (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm) (fun i => v[i])).re)
  bound := -(gaussianRationalQuadratic ((diamondRationalCandidateSlack J 0).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm) (fun i => v[i])).re

/-- The vector table of the rational candidate slack after flattening register indices. -/
def diamondRationalCandidateTable {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    GaussianRationalTable ((D+D)+(E*D+E*D)) :=
  gaussianRationalTable ((diamondRationalCandidateSlack J x).submatrix
    (diamondRationalRegisterEquiv D E).symm (diamondRationalRegisterEquiv D E).symm)

/-- Classifies the rational candidate slack using the Gaussian rational separation procedure. -/
def diamondRationalCandidateSeparate {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    GaussianRationalPsdResult ((D+D)+(E*D+E*D)) :=
  gaussianRationalPsdSeparate (diamondRationalCandidateTable J x)

/-- A separation result consisting of feasibility, an affine cut, or an invalid classification. -/
inductive RationalSeparationResult (n : ℕ) where
  | feasible
  | cut (C : RationalAffineCut n)
  | invalid

/-- The diamond separation procedure that converts a returned negative direction into a rational
affine cut. -/
def diamondRationalSeparationOracle {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (x : DiamondRationalCoordinates D E) :
    RationalSeparationResult (diamondDyadicWordCount D E) :=
  match diamondRationalCandidateSeparate J x with
  | .psd => .feasible
  | .negative v => .cut (diamondRationalSeparationCut J v)
  | .nonHermitian => .invalid

/-- Reads a real or imaginary rational component of a Gaussian rational matrix by flattened word
index. -/
def gaussianRationalCoordinateWord {D E : ℕ}
    (Q : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational)
    (k : Fin (gaussianDyadicWordCount D E)) : ℚ :=
  let t := (gaussianDyadicWordIndex D E).symm k
  if t.2 = 0 then (Q t.1.1 t.1.2).re else (Q t.1.1 t.1.2).im

/-- Packs two rational scalars and two Gaussian rational blocks into diamond coordinates. -/
def diamondRationalPack {D E : ℕ} (a b : ℚ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : DiamondRationalCoordinates D E := fun k =>
  if h : k.val < 2 then if k.val = 0 then a else b
  else if h0 : k.val < 2 + gaussianDyadicWordCount D E then
    gaussianRationalCoordinateWord Y ⟨k.val-2,by have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩
  else gaussianRationalCoordinateWord Z ⟨k.val-(2+gaussianDyadicWordCount D E),by
    have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩

/-- The rational coordinate representation of the designated diamond center. -/
def diamondRationalCenterCoordinates {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) : DiamondRationalCoordinates D E :=
  diamondRationalPack (diamondRationalCenterScalar J) (diamondRationalCenterScalar J)
    (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))
    (Matrix.diagonal (fun _ => (diamondRationalCenterScale J : GaussianRational)))

/-- The real coordinate space with one coordinate for every serialized diamond word. -/
abbrev DiamondRealCoordinates (D E : ℕ) := Fin (diamondDyadicWordCount D E) → ℝ

/-- Reconstructs a complex matrix block from its real coordinate components. -/
def diamondRealRawBlock {D E : ℕ} (b : Bool) (x : DiamondRealCoordinates D E) :
    Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ :=
  fun i j => ⟨x (diamondRationalBlockIndex D E b i j 0),x (diamondRationalBlockIndex D E b i j 1)⟩

/-- The Hermitian symmetrization of the selected complex block reconstructed from real
coordinates. -/
def diamondRealHermitianBlock {D E : ℕ} (b : Bool) (x : DiamondRealCoordinates D E) :
    HermitianMat (Fin E × Fin D) ℂ :=
  ⟨(1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ),by
    change ((1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ))ᴴ =
      (1/2 : ℝ) • (diamondRealRawBlock b x + (diamondRealRawBlock b x)ᴴ)
    simp [Matrix.conjTranspose_smul,add_comm]⟩

/-- Decodes real diamond coordinates into scalar components and Hermitian matrix blocks. -/
def diamondRealDecode {D E : ℕ} (x : DiamondRealCoordinates D E) : DiamondConstraints D E :=
  diamondDualData (x (diamondRationalScalarIndex D E 0)) (x (diamondRationalScalarIndex D E 1))
    (diamondRealHermitianBlock false x) (diamondRealHermitianBlock true x)

/-- Casts every rational diamond coordinate to a real coordinate. -/
def diamondRationalCoordinatesReal {D E : ℕ} (x : DiamondRationalCoordinates D E) : DiamondRealCoordinates D E :=
  fun k => (x k : ℝ)

/-- The real linear form obtained by casting the rational cut coefficients and pairing them with
real coordinates. -/
def RationalAffineCut.evalReal {n : ℕ} (C : RationalAffineCut n) (x : Fin n → ℝ) : ℝ :=
  ∑ k, ((C.coefficients[k] : ℚ) : ℝ) * x k

/-- The sum of the two rational scalar coordinates. -/
def diamondRationalScore {D E : ℕ} (x : DiamondRationalCoordinates D E) : ℚ :=
  x (diamondRationalScalarIndex D E 0) + x (diamondRationalScalarIndex D E 1)

/-- The sum of the two real scalar coordinates. -/
def diamondRealScore {D E : ℕ} (x : DiamondRealCoordinates D E) : ℝ :=
  x (diamondRationalScalarIndex D E 0) + x (diamondRationalScalarIndex D E 1)

/-- The cut with coefficients minus one on the scalar coordinates and bound `-γ`, expressing a
score upper bound. -/
def diamondRationalObjectiveCut (D E : ℕ) (γ : ℚ) : RationalAffineCut (diamondDyadicWordCount D E) where
  coefficients := Vector.ofFn (fun k => (if k = diamondRationalScalarIndex D E 0 then -1 else 0) +
    (if k = diamondRationalScalarIndex D E 1 then -1 else 0))
  bound := -γ

/-- Checks the rational score bound first, returning its objective cut on failure and otherwise
invoking the feasibility separation procedure. -/
def diamondRationalSublevelOracle {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ : ℚ) (x : DiamondRationalCoordinates D E) :
    RationalSeparationResult (diamondDyadicWordCount D E) :=
  if diamondRationalScore x ≤ γ then diamondRationalSeparationOracle J x
  else .cut (diamondRationalObjectiveCut D E γ)

/-- Reads the real or imaginary part of a complex block entry by flattened coordinate index. -/
def diamondRealCoordinateWord {D E : ℕ} (Q : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ)
    (k : Fin (gaussianDyadicWordCount D E)) : ℝ :=
  let t := (gaussianDyadicWordIndex D E).symm k
  if t.2 = 0 then (Q t.1.1 t.1.2).re else (Q t.1.1 t.1.2).im

/-- Packs two real scalars and two complex matrix blocks into real diamond coordinates. -/
def diamondRealPack {D E : ℕ} (a b : ℝ)
    (Y Z : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : DiamondRealCoordinates D E := fun k =>
  if h : k.val < 2 then if k.val = 0 then a else b
  else if h0 : k.val < 2 + gaussianDyadicWordCount D E then
    diamondRealCoordinateWord Y ⟨k.val-2,by have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩
  else diamondRealCoordinateWord Z ⟨k.val-(2+gaussianDyadicWordCount D E),by
    have hk := k.isLt; unfold diamondDyadicWordCount at hk; omega⟩

/-- Encodes diamond constraint data as two scalar coordinates followed by the real and imaginary
block entries. -/
def diamondRealEncode {D E : ℕ} (y : DiamondConstraints D E) : DiamondRealCoordinates D E :=
  diamondRealPack (WithLp.ofLp (WithLp.ofLp y).1).1 (WithLp.ofLp (WithLp.ofLp y).1).2
    (WithLp.ofLp (WithLp.ofLp y).2).1.mat (WithLp.ofLp (WithLp.ofLp y).2).2.mat

/-- The real diamond coordinates whose decoded dual data are feasible and have dual score at
most `γ`. -/
def diamondRealSublevel {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) (γ : ℝ) : Set (DiamondRealCoordinates D E) :=
  {x | (diamondProgram T).DualFeasible (diamondRealDecode x) ∧
    (diamondProgram T).dualScore (diamondRealDecode x) ≤ γ}

/-- The Euclidean norm of the real diamond coordinate vector. -/
def diamondCoordinateNorm {D E : ℕ} (x : DiamondRealCoordinates D E) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (diamondDyadicWordCount D E)))‖

/-- The rational dimension-dependent factor `2 + 4 * E * D`. -/
def diamondCoordinateLipschitz (D E : ℕ) : ℚ := 2 + 4 * (E : ℚ) * D

/-- The rational diamond radius divided by the coordinate Lipschitz factor. -/
def diamondCoordinateInnerRadius {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  diamondRationalRadius J ε / diamondCoordinateLipschitz D E

/-- The coordinate-count multiple of the rational outer size, plus one. -/
def diamondCoordinateOuterRadius {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (ε : ℚ) : ℚ :=
  (diamondDyadicWordCount D E : ℚ) * diamondRationalOuterSize J ε + 1

/-- The set of coordinate vectors at distance at most `r` from `c` in `diamondCoordinateNorm`. -/
def diamondCoordinateBall {D E : ℕ} (c : DiamondRealCoordinates D E) (r : ℝ) : Set (DiamondRealCoordinates D E) :=
  {x | diamondCoordinateNorm (x-c) ≤ r}

/-- The cut coefficient vector interpreted as a real Euclidean vector. -/
def RationalAffineCut.euclideanNormal {n : ℕ} (C : RationalAffineCut n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => ((C.coefficients[k] : ℚ) : ℝ))

/-- The Euclidean cut normal scaled by the inverse of its norm. -/
def RationalAffineCut.unitNormal {n : ℕ} (C : RationalAffineCut n) : EuclideanSpace ℝ (Fin n) :=
  ‖C.euclideanNormal‖⁻¹ • C.euclideanNormal

/-- The central-cut center expression `u / (n + 1)` in Euclidean space. -/
def euclideanCentralCutCenter {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1/((n : ℝ)+1)) • u

/-- The quadratic sublevel set defining the specified central-cut ellipsoid around
`euclideanCentralCutCenter u`. -/
def euclideanCentralCutEllipsoid {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ((n : ℝ)^2-1)*‖x-euclideanCentralCutCenter u‖^2 +
    2*((n : ℝ)+1)*⟪u,x-euclideanCentralCutCenter u⟫_ℝ^2 ≤ (n : ℝ)^2}

/-- The central-cut shape matrix obtained by scaling the identity minus a rank-one matrix in
direction `u`. -/
def euclideanCentralCutShape {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ)^2/((n : ℝ)^2-1)) •
    (1 - (2/((n : ℝ)+1)) • Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp u))

/-- Real matrix-vector multiplication transported to the Euclidean-space representation. -/
def euclideanMatrixApply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)

/-- The quadratic sublevel set at level one defined by the inverse shape matrix and displacement
from `c`. -/
def euclideanShapeEllipsoid {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | WithLp.ofLp (x-c) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp (x-c)) ≤ 1}

/-- The vector `Sᵀ * g` scaled by the inverse of its Euclidean norm. -/
def euclideanPullbackUnit {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ‖euclideanMatrixApply Sᵀ g‖⁻¹ • euclideanMatrixApply Sᵀ g

/-- The affine image of the central-cut center, translated by `c`. -/
def euclideanAffineCutCenter {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  c+euclideanMatrixApply S (euclideanCentralCutCenter (euclideanPullbackUnit S g))

/-- The congruence by `S` of the central-cut shape in the pulled-back normal direction. -/
def euclideanAffineCutShape {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := S * euclideanCentralCutShape (euclideanPullbackUnit S g) * Sᵀ

/-- The ellipsoid cut-center expression using `A * g` and the square root of the quadratic form
`gᵀ * A * g`. -/
def euclideanEllipsoidCutCenter {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  c + (1/(((n : ℝ)+1)*Real.sqrt (WithLp.ofLp g ⬝ᵥ (A *ᵥ WithLp.ofLp g)))) • euclideanMatrixApply A g

/-- The ellipsoid cut-shape expression obtained from `A` by a scaled rank-one correction in
direction `A * g`. -/
def euclideanEllipsoidCutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ)^2/((n : ℝ)^2-1)) •
    (A - (2/(((n : ℝ)+1)*(WithLp.ofLp g ⬝ᵥ (A *ᵥ WithLp.ofLp g)))) •
      Matrix.vecMulVec (A *ᵥ WithLp.ofLp g) (A *ᵥ WithLp.ofLp g))

/-- The entrywise real interpretation of a rational ellipsoid shape matrix. -/
def rationalEllipsoidShapeReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (algebraMap ℚ ℝ)

/-- The rational ellipsoid cut-shape formula using the quadratic form of `g` against `A`. -/
def rationalEllipsoidCutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ)^2/((n : ℚ)^2-1)) •
    (A - (2/(((n : ℚ)+1)*(g ⬝ᵥ (A *ᵥ g)))) • Matrix.vecMulVec (A *ᵥ g) (A *ᵥ g))

/-- The dyadic rational `(Nat.sqrt ⌊s * 2 ^ (2 * p)⌋₊ + 1) / 2 ^ p`. -/
def rationalSqrtUpper (s : ℚ) (p : ℕ) : ℚ :=
  ((Nat.sqrt ⌊s*(2 : ℚ)^(2*p)⌋₊+1 : ℕ) : ℚ)/(2 : ℚ)^p

/-- The dyadic precision parameter derived from the ceiling of `1 / (η * min s 1)`. -/
def rationalSqrtPrecision (s η : ℚ) : ℕ :=
  dyadicPrecision ⌈1/(η*min s 1)⌉₊

/-- The cut-center expression using a supplied scalar `r` in place of the square-root
denominator. -/
def euclideanApproxCutCenter {n : ℕ} (c : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (r : ℝ) : EuclideanSpace ℝ (Fin n) :=
  c+(1/(((n : ℝ)+1)*r)) • euclideanMatrixApply A g

/-- The rational cut-center update using `rationalSqrtUpper` at the precision selected by
`rationalSqrtPrecision`. -/
def rationalEllipsoidCutCenter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c g : Fin n → ℚ) (η : ℚ) : Fin n → ℚ :=
  let s := g ⬝ᵥ (A *ᵥ g)
  let r := rationalSqrtUpper s (rationalSqrtPrecision s η)
  c + (1/(((n : ℚ)+1)*r)) • (A *ᵥ g)

/-- The rational cut shape multiplied by the inflation factor `(1 + η / n) ^ 2`. -/
def rationalEllipsoidInflatedShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (g : Fin n → ℚ) (η : ℚ) :
    Matrix (Fin n) (Fin n) ℚ := (1+η/(n : ℚ))^2 • rationalEllipsoidCutShape A g

/-- The dimension-dependent rational tolerance `1 / (16 * n)`. -/
def rationalEllipsoidStepTolerance (n : ℕ) : ℚ := 1/(16*(n : ℚ))

/-- An ellipsoid state storing its rational center and shape matrix in finite vectors. -/
structure RationalEllipsoidState (n : ℕ) where
  centerData : Vector ℚ n
  shapeData : Vector (Vector ℚ n) n

/-- The rational center function represented by an ellipsoid state's center vector. -/
def RationalEllipsoidState.center {n : ℕ} (s : RationalEllipsoidState n) : Fin n → ℚ :=
    fun i => s.centerData[i]
/-- The rational shape matrix represented by an ellipsoid state's row vectors. -/
def RationalEllipsoidState.shape {n : ℕ} (s : RationalEllipsoidState n) :
    Matrix (Fin n) (Fin n) ℚ := fun i j => s.shapeData[i][j]
/-- Stores a rational center function and shape matrix as a vector-based ellipsoid state. -/
def RationalEllipsoidState.ofFunctions {n : ℕ} (c : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) : RationalEllipsoidState n :=
  ⟨Vector.ofFn c,Vector.ofFn (fun i => Vector.ofFn (A i))⟩

/-- Computes the rational center and inflated shape updates for the supplied cut using the
dimension-dependent tolerance. -/
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

/-- The real quadratic region represented by the state's rational center and shape matrix. -/
def RationalEllipsoidState.region {n : ℕ} (s : RationalEllipsoidState n) : Set (EuclideanSpace ℝ (Fin n)) :=
  euclideanShapeEllipsoid (WithLp.toLp 2 (fun k => (s.center k : ℝ))) (rationalEllipsoidShapeReal s.shape)

/-- The termination classification of an ellipsoid run: feasibility, budget exhaustion, or
invalid separation. -/
inductive EllipsoidRunOutcome where
  | feasible | exhausted | invalid
  deriving DecidableEq, Repr

/-- The final ellipsoid state, termination outcome, and recorded sequence of states and
separation results. -/
structure RationalEllipsoidRunResult (n : ℕ) where
  state : RationalEllipsoidState n
  outcome : EllipsoidRunOutcome
  trace : List (RationalEllipsoidState n × RationalSeparationResult n)

/-- Counts the affine-cut results in a recorded ellipsoid trace. -/
def rationalEllipsoidTraceCutCount {n : ℕ}
    (tr : List (RationalEllipsoidState n × RationalSeparationResult n)) : ℕ :=
  tr.countP (fun t => match t.2 with | .cut _ => true | _ => false)

/-- Runs the diamond sublevel separation procedure with a finite budget, updating on cuts and
recording each queried state. -/
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

/-- The explicit search budget determined by the coordinate dimension and the dyadic precision
of the radius ratio. -/
def rationalEllipsoidSearchBudget (n : ℕ) (R r : ℚ) : ℕ :=
  2*(n+1)*(2*n*dyadicPrecision ⌈R/r⌉₊+1)

/-- The zero-centered ellipsoid state with shape matrix `R ^ 2 • 1`. -/
def diamondEllipsoidInitialState (D E : ℕ) (R : ℚ) : RationalEllipsoidState (diamondDyadicWordCount D E) :=
  RationalEllipsoidState.ofFunctions 0 (R^2 • 1)

/-- Runs the rational diamond ellipsoid search with the designated inner and outer radii,
initial state, and search budget. -/
def diamondEllipsoidSolve {D E : ℕ}
    (J : Matrix (Fin E × Fin D) (Fin E × Fin D) GaussianRational) (γ ε : ℚ) :
    RationalEllipsoidRunResult (diamondDyadicWordCount D E) :=
  diamondEllipsoidRun J γ
    (rationalEllipsoidSearchBudget (diamondDyadicWordCount D E) (diamondCoordinateOuterRadius J ε) (diamondCoordinateInnerRadius J ε))
    (diamondEllipsoidInitialState D E (diamondCoordinateOuterRadius J ε))

end Qatlib.Concepts.DyadicFloor.FloorRounding
