/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAWord
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoefficientLCU
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorDuhamel

/-!
# Linear-combination encodings of multi-product formulas

This module constructs the branch unitaries, coefficient preparation frame, and SELECT operator
encoding the normalized `actualMPF`. A padding rotation adjusts the encoded amplitude to the
selected sine value, and `amplified` evaluates the corresponding amplification word for the
implementation setting of [AftabAnTrivisa2026].

When the commutator root profile vanishes, the amplified Chebyshev construction exactly encodes
the target exponential.

## Main statements

* `lcu_encoding`: encodes the multi-product formula divided by its absolute coefficient mass.
* `padded_encoding`: adjusts the compression to the chosen sine amplitude.
* `zero_profile_encoding`: gives exact target encoding when the root profile is zero.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAALCU

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator
open MPFMomentSeries MPFRootProfile
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
set_option warningAsError false

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The real multi-product weights regarded as complex coefficients. -/
def coefficients (a : K → ℝ) : K → ℂ := fun j => (a j : ℂ)

/-- The sum of the absolute real multi-product weights. -/
def mass (a : K → ℝ) : ℝ := ∑ j, |a j|

omit [DecidableEq K] in

/-- Weights summing to 1 have absolute mass at least 1. -/
theorem mass_lower (a : K → ℝ) (ha : ∑ j, a j = 1) : 1 ≤ mass a := by
  have h := norm_sum_le Finset.univ a
  rw [ha, norm_one] at h
  simpa only [Real.norm_eq_abs] using! h

omit [DecidableEq K] in

/-- The complex coefficient mass equals the absolute mass of the original real weights. -/
theorem coefficient_mass (a : K → ℝ) : coefficientMass (coefficients a) = mass a := by
  simp only [coefficientMass, coefficients, Complex.norm_real, Real.norm_eq_abs, mass]

/-- The qⱼ-th power of the level-zero Suzuki exponential word at time t/qⱼ. -/
def branch (xs : List (Matrix I I ℂ)) (q : K → ℕ) (t : ℝ) (j : K) : Matrix I I ℂ :=
  suzukiExponentialWord (recursiveSuzukiGenerators (xs.map (fun X => (-Complex.I) • X)) 0)
    (t / q j) ^ q j

omit [Fintype K] [DecidableEq K] in

/-- Each repeated product-formula branch is unitary for Hermitian input generators. -/
theorem branch_unitary (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (t : ℝ) (j : K) : branch xs q t j ∈ unitaryGroup I ℂ := by
  apply (unitaryGroup I ℂ).pow_mem
  apply pf_word_unitary
  apply recursiveSuzukiGenerators_antiHermitian
  intro A hA
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
  simp [Matrix.conjTranspose_smul, hxs B hB]

/-- The SELECT matrix for the branch family after absorbing coefficient phases. -/
def lcu (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) : Matrix (K × I) (K × I) ℂ :=
  select (phaseAbsorbed (coefficients a) (branch xs q t))

/-- The preparation lift determined by the coefficient amplitudes. -/
def frame (a : K → ℝ) : Matrix (K × I) I ℂ := prepareLift (coefficientAmplitude (coefficients a))

/-- For Hermitian generators and weights summing to 1, the SELECT construction is a projected
unitary encoding of the actual multi-product formula divided by its coefficient mass
[AftabAnTrivisa2026]. -/
theorem lcu_encoding (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (a : K → ℝ) (ha : ∑ j, a j = 1) (t : ℝ) :
    ProjectedUnitaryEncoding ((mass a : ℂ)⁻¹ • actualMPF xs q a t) (lcu xs q a t) (frame a) (frame a) := by
  have hm : 0 < coefficientMass (coefficients a) := by
    rw [coefficient_mass]; linarith [mass_lower a ha]
  have h :=
      coefficientLCU_projectedEncoding (coefficients a) (branch xs q t) hm
      (branch_unitary xs hxs q t)
  have he : (∑ j, (coefficients a j / (coefficientMass (coefficients a) : ℂ)) • branch xs q t j) =
      (mass a : ℂ)⁻¹ • actualMPF xs q a t := by
    rw [coefficient_mass, actualMPF, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change ((a j : ℂ) / (mass a : ℂ)) • branch xs q t j =
      (mass a : ℂ)⁻¹ • ((a j : ℝ) • branch xs q t j)
    ext i k
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he] at h
  exact h

/-- The tensor product of the mass-dependent padding rotation with the multi-product SELECT
matrix. -/
def padded (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) :
    Matrix (Bool × (K × I)) (Bool × (K × I)) ℂ := TensorGate (MPFOAAPadding.rotation (mass a)) (lcu xs q a t)

/-- The padded construction encodes the actual multi-product formula multiplied by the selected
sine amplitude in the scaled frame. -/
theorem padded_encoding (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (a : K → ℝ) (ha : ∑ j, a j = 1) (t : ℝ) :
    ProjectedUnitaryEncoding ((Real.sin (MPFOAAChoice.angle (MPFOAAChoice.queries (mass a))) : ℂ) •
      actualMPF xs q a t) (padded xs q a t) (scaleEightFrame (frame a)) (scaleEightFrame (frame a)) :=
  MPFOAAPadding.padded_encoding (mass a) (mass_lower a ha) _ _ _ (lcu_encoding xs hxs q a ha t)

/-- The operator obtained by evaluating the selected amplification word on the padded
multi-product encoding. -/
def amplified (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) :
    Matrix (Bool × (K × I)) (Bool × (K × I)) ℂ :=
  evaluate (padded xs q a t) (MPFOAAWord.word (mass a) (scaleEightFrame (frame a)))

/-- For Hermitian generators and positive order with zero root profile, the amplified Chebyshev
construction exactly encodes the target exponential. -/
theorem zero_profile_encoding (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (hz : mu xs m = 0) (t : ℝ) :
    ProjectedUnitaryEncoding (NormedSpace.exp (t • ((-Complex.I) • xs.sum)))
      (amplified xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) t)
      (scaleEightFrame (frame (I := I) (ChebyshevNodes.weight m)))
      (scaleEightFrame (frame (I := I) (ChebyshevNodes.weight m))) := by
  have ha : ∑ j : Fin m, ChebyshevNodes.weight m j = 1 := by
    simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm
  have he := MPFRootStep.chebyshev_exact_of_mu_zero xs hxs m hm hz t
  have hV := general_trotter_exp_unitary _ 1 (BCHPerturbation.target_skew xs hxs t)
  simp only [one_smul] at hV
  have h := padded_encoding xs hxs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) ha t
  rw [he] at h
  exact MPFOAAWord.word_encoding _ _ _ _ hV h

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAALCU
