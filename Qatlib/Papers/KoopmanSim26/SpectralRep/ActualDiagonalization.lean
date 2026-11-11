/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.DiagonalizedLCHS
import Qatlib.Concepts.KoopmanFlow.FlowAction
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Actual spectral diagonalization for LCHS

This module constructs the unitary eigenbasis `frequencyBasis` and real eigenvalues
`frequencyValues` of each Hermitian frequency matrix `H + k L`. The matrix `diagonalizedUnitary`
conjugates the corresponding diagonal phase evolution back to the original basis and equals
`spectralUnitary`.

The result `actual_diagonalized_lchs` realizes the diagonalized representation in Theorem 1 of
[ZhangEtAl2026], including matrix and entrywise integrability. The definitions `generatorL` and
`generatorH` also decompose an arbitrary complex matrix into its two Hermitian components.

## Main statements

* `hermitian_exp_spectral` expresses the exponential of a complex multiple of a Hermitian matrix
  in an eigenbasis.
* `frequency_diagonalization` and `diagonalizedUnitary_eq` give the actual frequency
  decomposition and phase evolution.
- `generator_reconstruction` proves `generatorL A + i generatorH A = A`.
* `actual_diagonalized_lchs` identifies the Cauchy integral of diagonalized unitaries with the
  dissipative propagator.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder
open Qatlib.Papers.KoopmanSim26.SpectralRep

namespace Qatlib.Papers.KoopmanSim26.SpectralRep
variable {I : Type} [Fintype I] [DecidableEq I]

/-- For a Hermitian matrix `G` and any complex scalar `z`, `exp(z G)` is its unitary eigenbasis
conjugating the diagonal entries `exp(z lambda_j)`. -/
theorem hermitian_exp_spectral (G : Matrix I I ℂ) (hG : G.IsHermitian) (z : ℂ) :
    NormedSpace.exp (z • G) = (hG.eigenvectorUnitary : Matrix I I ℂ) *
      diagonal (fun j => Complex.exp (z * (hG.eigenvalues j : ℂ))) *
      (hG.eigenvectorUnitary : Matrix I I ℂ).conjTranspose := by
  let U := Unitary.toUnits hG.eigenvectorUnitary
  have hs : z • G = (U : Matrix I I ℂ) *
      diagonal (fun j => z * (hG.eigenvalues j : ℂ)) * (↑U⁻¹ : Matrix I I ℂ) := by
    have hd : G = (U : Matrix I I ℂ) * diagonal (fun j => (hG.eigenvalues j : ℂ)) *
        (↑U⁻¹ : Matrix I I ℂ) := hG.spectral_theorem
    conv_lhs => rw [hd]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    apply congrArg (fun D : Matrix I I ℂ => (U : Matrix I I ℂ) * D * (↑U⁻¹ : Matrix I I ℂ))
    apply congrArg (diagonal : (I → ℂ) → Matrix I I ℂ)
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hs, Matrix.exp_units_conj, Matrix.exp_diagonal]
  change (U : Matrix I I ℂ) * diagonal (NormedSpace.exp _) * (↑U⁻¹ : Matrix I I ℂ) = _
  have hd : diagonal (NormedSpace.exp (fun j : I => z * (hG.eigenvalues j : ℂ))) =
      diagonal (fun j => Complex.exp (z * (hG.eigenvalues j : ℂ))) := by
    congr 1
    funext j
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rw [hd]
  rfl

/-- The frequency matrix `H + k L` is Hermitian whenever `L` and `H` are Hermitian and `k` is
real. -/
def frequency_hermitian (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (k : ℝ) : (H + k • L).IsHermitian :=
  hH.add (hL.smul (R := ℝ) (IsSelfAdjoint.all k))

/-- The matrix `frequencyBasis` is the unitary eigenvector matrix selected by the spectral
theorem for the Hermitian frequency matrix `H + k L`. -/
def frequencyBasis (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (k : ℝ) : Matrix.unitaryGroup I ℂ := (frequency_hermitian L H hL hH k).eigenvectorUnitary

/-- The function `frequencyValues` gives the real eigenvalues of the Hermitian frequency matrix
`H + k L`, indexed by the matrix basis. -/
def frequencyValues (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (k : ℝ) : I → ℝ := (frequency_hermitian L H hL hH k).eigenvalues

/-- The matrix `diagonalizedUnitary` conjugates the diagonal phases `exp(i t lambda_j(k))` from
the frequency eigenbasis back to the original basis. -/
def diagonalizedUnitary (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (t k : ℝ) : Matrix I I ℂ :=
  (frequencyBasis L H hL hH k : Matrix I I ℂ) *
    diagonal (fun j => Complex.exp ((Complex.I * (t : ℂ)) * (frequencyValues L H hL hH k j : ℂ))) *
    (frequencyBasis L H hL hH k : Matrix I I ℂ).conjTranspose

/-- The frequency matrix `H + k L` equals its unitary eigenbasis conjugating the diagonal matrix
of `frequencyValues`. -/
theorem frequency_diagonalization (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (k : ℝ) : H+k • L = (frequencyBasis L H hL hH k : Matrix I I ℂ) *
      diagonal (fun j => (frequencyValues L H hL hH k j : ℂ)) *
      (frequencyBasis L H hL hH k : Matrix I I ℂ).conjTranspose :=
  (frequency_hermitian L H hL hH k).spectral_theorem

/-- The explicit eigenbasis construction `diagonalizedUnitary` equals the matrix exponential
`spectralUnitary`. -/
theorem diagonalizedUnitary_eq (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (t k : ℝ) : diagonalizedUnitary L H hL hH t k = spectralUnitary L H t k := by
  exact (hermitian_exp_spectral (H+k • L) (frequency_hermitian L H hL hH k)
    (Complex.I * (t:ℂ))).symm

/-- The matrix `generatorL A` is the Hermitian part of `A`, defined as `(A + A†) / 2`. -/
def generatorL (A : Matrix I I ℂ) : Matrix I I ℂ := (1/2:ℝ) • (A+A.conjTranspose)

/-- The matrix `generatorH A` is the Hermitian matrix `(A - A†) / (2 i)` whose imaginary
multiple is the skew-Hermitian part of `A`. -/
def generatorH (A : Matrix I I ℂ) : Matrix I I ℂ := (-Complex.I/2) • (A-A.conjTranspose)

/-- The complex scalar `-i / 2` equals the reciprocal of `2 i`, identifying the two coefficient
conventions for `generatorH`. -/
theorem generatorH_coefficient : -Complex.I/2 = (2*Complex.I)⁻¹ := by
  rw [_root_.mul_inv_rev]
  simp [div_eq_mul_inv]

omit [Fintype I] [DecidableEq I] in

/-- The Hermitian part `generatorL A` is Hermitian for every complex square matrix `A`. -/
theorem generatorL_hermitian (A : Matrix I I ℂ) : (generatorL A).IsHermitian := by
  change (generatorL A).conjTranspose=generatorL A
  simp only [generatorL, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm A.conjTranspose A]

omit [Fintype I] [DecidableEq I] in

/-- The matrix `generatorH A` is Hermitian for every complex square matrix `A`. -/
theorem generatorH_hermitian (A : Matrix I I ℂ) : (generatorH A).IsHermitian := by
  change (generatorH A).conjTranspose=generatorH A
  simp only [generatorH, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  have hs : star (-Complex.I/2) = Complex.I/2 := by simp
  rw [hs]
  module

omit [Fintype I] [DecidableEq I] in

/-- The two Hermitian components reconstruct the original matrix as `generatorL A + i generatorH
A`. -/
theorem generator_reconstruction (A : Matrix I I ℂ) : generatorL A+Complex.I • generatorH A=A := by
  unfold generatorL generatorH
  rw [smul_smul]
  have hi : Complex.I * (-Complex.I/2) = (1/2:ℂ) := by
    calc
      _ = -(Complex.I^2)/2 := by ring
      _ = _ := by rw [Complex.I_sq]; norm_num
  rw [hi]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
  push_cast
  ring

/-- If `-L` is positive semidefinite, then `L` is Hermitian. -/
def dissipativeHermitian (L : Matrix I I ℂ) (hL : (-L).PosSemidef) : L.IsHermitian := by
  simpa using hL.isHermitian.neg

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix I I ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

set_option backward.isDefEq.respectTransparency false in

/-- For Hermitian `L` and `H` and any real time, the Cauchy-weighted spectral-unitary function
is integrable as a matrix-valued function. -/
theorem spectral_integrand_integrable (L H : Matrix I I ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian) (t : ℝ) :
    Integrable (fun k : ℝ => (1/(Real.pi*(1+k^2))) • spectralUnitary L H t k) := by
  have hd : Integrable (fun k : ℝ => 1/(Real.pi*(1+k^2))) := by
    simpa only [div_eq_mul_inv, _root_.mul_inv_rev, one_mul, mul_comm] using
      integrable_inv_one_add_sq.const_mul Real.pi⁻¹
  have hc : Continuous (spectralUnitary L H t) := by
    letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    unfold spectralUnitary
    have h1 : Continuous (fun k : ℝ => (Complex.I * (t : ℂ)) • (H + k • L)) := by fun_prop
    exact NormedSpace.exp_continuous.comp h1
  have hn (k : ℝ) : ‖spectralUnitary L H t k‖ ≤ 1 := by
    rw [spectralUnitary_eq_hamiltonianEvolution]
    exact Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one
      (Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary
        (hH.neg.add (hL.neg.smul (R := ℝ) (IsSelfAdjoint.all k))) t)
  exact hd.smul_bdd 1 hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)

set_option backward.isDefEq.respectTransparency false in

/-- For nonnegative time, positive semidefinite `-L`, and Hermitian `H`, the Cauchy-weighted
explicitly diagonalized unitaries are integrable as matrices and entrywise, and their
integral equals `propagator L H t`. This realizes the actual spectral-basis representation
in Theorem 1 of [ZhangEtAl2026]. -/
theorem actual_diagonalized_lchs (L H : Matrix I I ℂ) (t : ℝ)
    (hL : (-L).PosSemidef) (hH : H.IsHermitian) (ht : 0 ≤ t) :
    Integrable (fun k : ℝ => (1/(Real.pi*(1+k^2))) •
      diagonalizedUnitary L H (dissipativeHermitian L hL) hH t k) ∧
    (∀ i j : I, Integrable (fun k : ℝ => ((1/(Real.pi*(1+k^2)) : ℝ) : ℂ) *
      diagonalizedUnitary L H (dissipativeHermitian L hL) hH t k i j)) ∧
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) •
      diagonalizedUnitary L H (dissipativeHermitian L hL) hH t k) = propagator L H t := by
  simp only [diagonalizedUnitary_eq]
  exact ⟨spectral_integrand_integrable L H (dissipativeHermitian L hL) hH t,
    diagonalized_lchs_spectral_representation L H t hL hH ht⟩

end Qatlib.Papers.KoopmanSim26.SpectralRep
