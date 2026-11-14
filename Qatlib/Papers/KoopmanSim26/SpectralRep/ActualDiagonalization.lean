/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KoopmanSim26.SpectralRep.DiagonalizedLCHS
public import Qatlib.Concepts.KoopmanFlow.FlowAction
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

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

omit [Fintype I] [DecidableEq I] in

/-- The frequency matrix `H + k L` is Hermitian whenever `L` and `H` are Hermitian and `k` is
real. -/
theorem frequency_hermitian (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
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

omit [Fintype I] [DecidableEq I] in

/-- If `-L` is positive semidefinite, then `L` is Hermitian. -/
theorem dissipativeHermitian (L : Matrix I I ℂ) (hL : (-L).PosSemidef) : L.IsHermitian := by
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
    let _hNormedAlgebra : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
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
