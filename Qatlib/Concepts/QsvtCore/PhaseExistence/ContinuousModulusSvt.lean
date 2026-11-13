/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.ContinuousModulusQuantization

/-!
# Continuous-modulus stability of singular transforms

This module transfers the Hermitian functional-calculus bound `Th20MainBound` to odd and right
even singular transforms of rectangular contractions [GilyenSuLowWiebe2019]. Clamping the scalar
response to `[-1, 1]` converts parity on that interval into global parity while preserving the
relevant transforms and modulus of continuity.

It also identifies the right singular transform with functional calculus of the Gram matrix and
determines its action on the kernel.

## Main statements

* `right_as_gram`: expresses the right singular transform through `Aᴴ * A` and the square root.
* `odd_bound`: bounds the odd singular-transform difference.
* `frontier1`: packages the Hermitian bound and both rectangular stability estimates.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.ContinuousModulusSvt

/-- Clamping to [-1, 1] commutes with negation. -/
theorem clampUnit_neg (x : ℝ) : clampUnit (-x) = -clampUnit x := by
  by_cases hx : x ≤ -1
  · rw [clampUnit_of_le_neg_one hx,clampUnit_of_one_le (by linarith)]
    norm_num
  · by_cases hy : 1 ≤ x
    · rw [clampUnit_of_one_le hy,clampUnit_of_le_neg_one (by linarith)]
    · rw [clampUnit_eq ⟨by linarith,by linarith⟩,
        clampUnit_eq ⟨by linarith,by linarith⟩]

/-- If f is odd on [-1, 1], then `clampResponse f` is odd on all real inputs. -/
theorem odd_clamp (f : ℝ → ℂ)
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, f (-x) = -f x) : IsOddFunction (clampResponse f) := by
  intro x
  simp only [clampResponse,clampUnit_neg]
  exact h _ (clampUnit_mem x)

/-- If f is even on [-1, 1], then `clampResponse f` is even on all real inputs. -/
theorem even_clamp (f : ℝ → ℂ)
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, f (-x) = f x) : IsEvenFunction (clampResponse f) := by
  intro x
  simp only [clampResponse,clampUnit_neg]
  exact h _ (clampUnit_mem x)

/-- Clamping the input of a response preserves its modulus-of-continuity condition. -/
theorem modulus_clamp (f : ℝ → ℂ) (ω : ℝ → ℝ) (h : ModulusOfContinuity f ω) :
    ModulusOfContinuity (clampResponse f) ω := by
  refine ⟨h.mono,h.at_zero,?_⟩
  intro x y hx hy
  rw [clampResponse_eq hx,clampResponse_eq hy]
  exact h.dominates x y hx hy

variable {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

omit [DecidableEq O] in

/-- Every singular value of a rectangular contraction, including the natural-index extension,
lies in [0, 1]. -/
theorem singular_interval (A : Matrix O I ℂ) (hA : ‖A‖ ≤ 1) (i : ℕ) :
    matrixSingularValues A i ∈ Set.Icc (0:ℝ) 1 :=
  ⟨matrixSingularValues_nonneg A i,(matrixSingularValues_le_spectralNorm A i).trans hA⟩

omit [DecidableEq O] in

/-- Clamping the scalar response to [-1, 1] leaves the odd singular transform of a contraction
unchanged. -/
theorem odd_clamp_eq (A : Matrix O I ℂ) (hA : ‖A‖ ≤ 1) (f : ℝ → ℂ) :
    oddSingularTransform A (clampResponse f) = oddSingularTransform A f := by
  apply oddSingularTransform_congr_positive
  intro i _
  exact clampResponse_eq ⟨(by linarith [matrixSingularValues_nonneg A i]),
    (matrixSingularValues_le_spectralNorm A i).trans hA⟩

omit [DecidableEq O] in

/-- Clamping the scalar response to [-1, 1] leaves the right singular transform of a contraction
unchanged. -/
theorem right_clamp_eq (A : Matrix O I ℂ) (hA : ‖A‖ ≤ 1) (f : ℝ → ℂ) :
    rightSingularTransform A (clampResponse f) = rightSingularTransform A f := by
  unfold rightSingularTransform
  congr 1
  funext i
  exact clampResponse_eq ⟨(by linarith [matrixSingularValues_nonneg A i]),
    (matrixSingularValues_le_spectralNorm A i).trans hA⟩

/-- The right singular transform of A by f equals the Hermitian functional calculus of `Aᴴ * A`
with scalar response x ↦ f(√x). -/
theorem right_as_gram (A : Matrix O I ℂ) (f : ℝ → ℂ) :
    rightSingularTransform A f = hermitianFunction (Aᴴ*A)
      (Matrix.isHermitian_conjTranspose_mul_self A) (fun x => f (Real.sqrt x)) := by
  have h := hermitianFunction_eq_of_eigenColumns (Aᴴ*A)
    (Matrix.isHermitian_conjTranspose_mul_self A) (fun x => f (Real.sqrt x))
    (basisColumns (rightSingularBasis A)) (fun i => (matrixSingularValues A i)^2)
    (basisColumns_mul_adjoint _) (fun i => by
      have hi := congrArg (fun v : EuclideanSpace ℂ I => v.ofLp) (gram_apply_rightSingularBasis A i)
      simpa [Matrix.ofLp_toLpLin,Complex.ofReal_pow] using! hi)
  simpa only [Real.sqrt_sq (matrixSingularValues_nonneg A _),rightSingularTransform,
    spectralDiagonal] using! h

/-- On a vector in the kernel of A, the right singular transform by f acts as multiplication by
f(0). -/
theorem right_kernel (A : Matrix O I ℂ) (f : ℝ → ℂ) (v : I → ℂ) (hv : A *ᵥ v = 0) :
    rightSingularTransform A f *ᵥ v = f 0 • v := by
  rw [right_as_gram]
  have hg : (Aᴴ*A)*ᵥv = (0:ℂ) • v := by rw [← Matrix.mulVec_mulVec,hv]; simp
  simpa only [Real.sqrt_zero] using! hermitianFunction_eigenvector (Aᴴ*A)
    (Matrix.isHermitian_conjTranspose_mul_self A) (fun x => f (Real.sqrt x)) 0 v hg

/-- For rectangular contractions at positive distance and a response odd on [-1, 1] with modulus
ω, bounds the odd singular-transform difference by `modulusRobustnessFactor ‖A - B‖ * ω ‖A -
B‖` [GilyenSuLowWiebe2019]. -/
theorem odd_bound (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω)
    (hf : ∀ x ∈ Set.Icc (-1:ℝ) 1, f (-x) = -f x) (hδ : 0 < ‖A-B‖) :
    ‖oddSingularTransform A f-oddSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A-B‖ * ω ‖A-B‖ := by
  have h := odd_singularTransform_bound_of_th20 th20_main A B (clampResponse f) ω
    hA hB (modulus_clamp f ω hω) (odd_clamp f hf) hδ
  rwa [odd_clamp_eq A hA,odd_clamp_eq B hB] at h

/-- For rectangular contractions at positive distance and a response even on [-1, 1] with
modulus ω, bounds the right singular-transform difference by `modulusRobustnessFactor ‖A -
B‖ * ω ‖A - B‖` [GilyenSuLowWiebe2019]. -/
theorem right_even_bound (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω)
    (hf : ∀ x ∈ Set.Icc (-1:ℝ) 1, f (-x) = f x) (hδ : 0 < ‖A-B‖) :
    ‖rightSingularTransform A f-rightSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A-B‖ * ω ‖A-B‖ := by
  have h := rightEven_singularTransform_bound_of_th20 th20_main A B (clampResponse f) ω
    hA hB (modulus_clamp f ω hω) (even_clamp f hf) hδ
  rwa [right_clamp_eq A hA,right_clamp_eq B hB] at h

omit [DecidableEq O] in

/-- Rectangular matrices at zero operator-norm distance have equal odd and right singular
transforms for every response. -/
theorem rectangular_zero (A B : Matrix O I ℂ) (f : ℝ → ℂ) (hδ : ‖A-B‖ = 0) :
    oddSingularTransform A f = oddSingularTransform B f ∧
      rightSingularTransform A f = rightSingularTransform B f := by
  have h : A = B := sub_eq_zero.mp (norm_eq_zero.mp hδ)
  subst B
  exact ⟨rfl,rfl⟩

/-- Hermitian matrices at zero operator-norm distance have equal functional-calculus responses. -/
theorem hermitian_zero (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℂ) (hδ : ‖A-B‖ = 0) :
    hermitianFunction A hA f = hermitianFunction B hB f := by
  have h : A = B := sub_eq_zero.mp (norm_eq_zero.mp hδ)
  subst B
  rfl

/-- Packages `Th20MainBound` together with the modulus-of-continuity estimates for odd and right
even singular transforms of rectangular contractions. The rectangular estimates require
positive matrix distance and the corresponding parity only on [-1, 1]
[GilyenSuLowWiebe2019]. -/
theorem frontier1 : Th20MainBound ∧
    (∀ (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → 0 < ‖A-B‖ →
      ((∀ x ∈ Set.Icc (-1:ℝ) 1, f (-x) = -f x) →
        ‖oddSingularTransform A f-oddSingularTransform B f‖ ≤
          modulusRobustnessFactor ‖A-B‖ * ω ‖A-B‖) ∧
      ((∀ x ∈ Set.Icc (-1:ℝ) 1, f (-x) = f x) →
        ‖rightSingularTransform A f-rightSingularTransform B f‖ ≤
          modulusRobustnessFactor ‖A-B‖ * ω ‖A-B‖)) := by
  refine ⟨th20_main,?_⟩
  intro A B f ω hA hB hω hδ
  exact ⟨fun hf => odd_bound A B f ω hA hB hω hf hδ,
    fun hf => right_even_bound A B f ω hA hB hω hf hδ⟩

end Qatlib.Concepts.QsvtCore.PhaseExistence.ContinuousModulusSvt
