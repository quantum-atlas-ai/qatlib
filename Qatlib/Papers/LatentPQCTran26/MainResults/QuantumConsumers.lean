/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.ActualContract
import Qatlib.Foundations.MatrixAlgebra.ParamWord.PhysicalWord
import Qatlib.Papers.LatentPQCTran26.MainResults.NativePreserve
import Qatlib.Papers.LatentPQCTran26.MainResults.NativeCoverage

/-!
# Latent trainability estimates for exponential circuit words

These results instantiate the latent-decoder estimates for `exponentialWord` and its observable
loss `wordLoss`, with Hermitian generators of norm at most one, unitary interleaving matrices, a
unit input state, and a bounded observable. They provide parameter perturbation bounds,
tanh-decoder gradient estimates, reference and routed coverage, and a warm-start mean bound. See
[TranEtAl2026] for the paper context.

## Main statements

* `actual_word_perturbation`: With Hermitian generators of norm at most one and unitary
  interleaving matrices, the exponential circuit word is Lipschitz in its Euclidean parameters
  with constant `K`.
* `actual_tanh_meta_gradient`: Under the stated circuit hypotheses with positive `K`,
  concentration radius `0 ≤ gamma ≤ g / (8 * K ^ 2)` preserves a tanh-decoder bias meta-gradient
  norm of at least `g / 2`, which is at most the full meta-gradient norm.
* `actual_warm_mean`: Under the stated bounded circuit hypotheses and `lam ≤ 1`, the tagged
  warm-start prior is a probability measure and its routed mean squared gradient is at least
  `lam * mu0` when the reference mean is at least `mu0`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option warningAsError false

noncomputable section
open MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.LatentPQCTran26.MainResults.QuantumConsumers
open Qatlib.Foundations.MatrixAlgebra.ParamWord
open EuclideanLayer LinearMetaGrad ConcentratedMLP NoBiasBarrenPlateau NativePreserve NativeCoverage
local instance {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] :
    CStarAlgebra (Matrix I I ℂ) where
local instance {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] :
    NormedAlgebra ℝ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- With Hermitian generators of norm at most one and unitary interleaving matrices, the
exponential circuit word is Lipschitz in its Euclidean parameters with constant `K`
[TranEtAl2026]. -/
theorem actual_word_perturbation
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K : ℕ}
    (G W : Fin K → Matrix I I ℂ) (hG : ∀ j, (G j).IsHermitian)
    (hGn : ∀ j, ‖G j‖ ≤ 1) (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ)
    (theta eta : EuclideanSpace ℝ (Fin K)) :
    ‖exponentialWord G W theta-exponentialWord G W eta‖ ≤ (K:ℝ)*‖theta-eta‖ := by
  have hl := paramWord_lipschitz (fun j => expSlot (G j) (W j) j)
    (fun j => expSlotD (G j) (W j) j)
    (fun j x => (expSlot_norm (G j) (W j) j (hG j) (hW j) x).le)
    (fun j x => expSlotD_norm (G j) (W j) j (hG j) (hGn j) (hW j) x)
    (fun j x => expSlot_hasFDerivAt (G j) (W j) j x) (List.finRange K)
  simpa [exponentialWord] using hl.norm_sub_le theta eta

/-- For a unit input state, Hermitian generators of norm at most one, unitary interleaving
matrices, and an observable of norm at most one, the squared gradient norm of `wordLoss` is
integrable under any Borel probability measure on parameter space. -/
theorem actual_word_gradient_sq_integrable
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin K))] [BorelSpace (EuclideanSpace ℝ (Fin K))]
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (mu : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure mu] :
    Integrable (fun x => ‖gradient (wordLoss G W O psi) x‖^2) mu := by
  obtain ⟨_,hcont,_,hderiv,_⟩ := actual_word_loss_contract G W O psi hpsi hG hGn hW hO
  apply (integrable_const ((2*(K:ℝ))^2)).mono'
    (squaredGradient_continuous _ hcont).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),nativeGradient_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (hderiv x) 2

/-- Under the stated circuit hypotheses with positive `K`, concentration radius `0 ≤ gamma ≤ g /
(8 * K ^ 2)` preserves a tanh-decoder bias meta-gradient norm of at least `g / 2`, which is
at most the full meta-gradient norm [TranEtAl2026]. -/
theorem actual_tanh_meta_gradient
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K d : ℕ} (hK : 0 < K)
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (r : Measure (Fin d → ℝ)) [IsProbabilityMeasure r]
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (theta v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (gamma g : ℝ) (hgamma0 : 0 ≤ gamma)
    (hg : g ≤ ‖gradient (wordLoss G W O psi) theta‖)
    (hgamma : gamma ≤ g/(2*(4*(K:ℝ)^2))) :
    g/2  ≤  ‖gradient (fun b : EuclideanSpace ℝ (Fin K) =>
      expectedLoss r (feature a c) (wordLoss G W O psi)
        (weights theta v gamma + bias K 1 b)) 0‖ ∧
      ‖gradient (fun b : EuclideanSpace ℝ (Fin K) =>
        expectedLoss r (feature a c) (wordLoss G W O psi)
          (weights theta v gamma + bias K 1 b)) 0‖  ≤
        ‖gradient (expectedLoss r (feature a c) (wordLoss G W O psi))
          (weights theta v gamma)‖ := by
  obtain ⟨hd,hcont,hbound,hderiv,hlip⟩ := actual_word_loss_contract G W O psi hpsi hG hGn hW hO
  exact tanh_meta_gradient r a c _ hd hcont 1 (2*(K:ℝ)) hbound hderiv theta v hv
    (4*(K:ℝ)^2) gamma g (by positivity) hgamma0 hlip hg hgamma

/-- Under the stated circuit hypotheses with positive `K` and nonnegative `g`, tanh-decoder
concentration within radius `0 ≤ gamma ≤ g / (8 * K ^ 2)` gives expected squared
circuit-loss gradient at least `g ^ 2 / 4` [TranEtAl2026]. -/
theorem actual_tanh_expected
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K d : ℕ} (hK : 0 < K)
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (r : Measure (Fin d → ℝ)) [IsProbabilityMeasure r]
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (theta v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (gamma g : ℝ) (hgamma0 : 0 ≤ gamma) (hg0 : 0 ≤ g)
    (hg : g ≤ ‖gradient (wordLoss G W O psi) theta‖)
    (hgamma : gamma ≤ g/(2*(4*(K:ℝ)^2))) :
    g^2/4  ≤  ∫ z, ‖gradient (wordLoss G W O psi)
      (decoder K 1 (feature a c z) (weights theta v gamma))‖^2 ∂r := by
  obtain ⟨_,hcont,_,hderiv,hlip⟩ := actual_word_loss_contract G W O psi hpsi hG hGn hW hO
  exact tanh_expected r a c _ hcont (2*(K:ℝ)) hderiv theta v hv (4*(K:ℝ)^2)
    gamma g (by positivity) hgamma0 hg0 hlip hg hgamma

/-- Under the stated bounded circuit hypotheses with positive `K`, a reference mean squared
gradient of at least `mu0` yields a tanh-decoder center and gradient-dependent radius with
expected squared gradient at least `mu0 / 4` [TranEtAl2026]. -/
theorem actual_reference_initialization
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K d : ℕ} (hK : 0 < K)
    [MeasurableSpace (EuclideanSpace ℝ (Fin K))] [BorelSpace (EuclideanSpace ℝ (Fin K))]
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (r : Measure (Fin d → ℝ)) [IsProbabilityMeasure r]
    (nu : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure nu]
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (mu0 : ℝ) (hmean : mu0 ≤ ∫ x, ‖gradient (wordLoss G W O psi) x‖^2 ∂nu) :
    ∃ theta : EuclideanSpace ℝ (Fin K), mu0/4  ≤
      ∫ z, ‖gradient (wordLoss G W O psi) (decoder K 1 (feature a c z)
        (weights theta v (‖gradient (wordLoss G W O psi) theta‖/(2*(4*(K:ℝ)^2)))))‖^2 ∂r := by
  obtain ⟨_,hcont,_,hderiv,hlip⟩ := actual_word_loss_contract G W O psi hpsi hG hGn hW hO
  exact reference_initialization r nu a c _ hcont (2*(K:ℝ)) hderiv v hv (4*(K:ℝ)^2)
    (by positivity) hlip (actual_word_gradient_sq_integrable G W O psi hpsi hG hGn hW hO nu) mu0 hmean

/-- For the stated bounded circuit model with positive `K` and reference mean squared gradient
at least nonnegative `mu0`, the routed mixture gives real measure at least `lam * mu0 / (8 *
K ^ 2)` to parameters with squared gradient at least `mu0 / 2` [TranEtAl2026]. -/
theorem actual_routed_coverage
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K : ℕ} (hK : 0 < K)
    [MeasurableSpace (EuclideanSpace ℝ (Fin K))] [BorelSpace (EuclideanSpace ℝ (Fin K))]
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (nu train : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure nu]
    [IsProbabilityMeasure train] (lam : NNReal) (mu0 : ℝ) (hmu : 0 ≤ mu0)
    (hmean : mu0 ≤ ∫ x, ‖gradient (wordLoss G W O psi) x‖^2 ∂nu) :
    (lam:ℝ)*(mu0/(8*(K:ℝ)^2))  ≤
      ((ActualWarmRoute.prior nu train lam).map ActualWarmRoute.route).real
        (Overlap.gradRichSet (fun x => ‖gradient (wordLoss G W O psi) x‖^2) (mu0/2)) := by
  obtain ⟨_,hcont,_,hderiv,_⟩ := actual_word_loss_contract G W O psi hpsi hG hGn hW hO
  have hupper : (∫ x, ‖gradient (wordLoss G W O psi) x‖^2 ∂nu) ≤ (2*(K:ℝ))^2 := by
    have hb := integral_mono_ae
      (actual_word_gradient_sq_integrable G W O psi hpsi hG hGn hW hO nu)
      (integrable_const ((2*(K:ℝ))^2))
      (Filter.Eventually.of_forall (fun x => by
        change ‖gradient (wordLoss G W O psi) x‖^2 ≤ (2*(K:ℝ))^2
        rw [nativeGradient_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hderiv x) 2))
    simpa using hb
  have hsml : mu0/2 < (2*(K:ℝ))^2 := by
    have hp : 0 < (2*(K:ℝ))^2 := by positivity
    linarith
  have hr := routed_coverage nu train lam (wordLoss G W O psi) hcont
    (2*(K:ℝ)) mu0 (by positivity) hmu hderiv hmean hsml
  convert hr using 1; congr 2; ring

/-- For the stated bounded circuit model with positive `K` and reference mean squared gradient
at least nonnegative `mu0`, the reference real measure of parameters with squared gradient
at least `mu0 / 2` is at least `mu0 / (8 * K ^ 2)` [TranEtAl2026]. -/
theorem actual_reference_coverage
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K : ℕ} (hK : 0 < K)
    [MeasurableSpace (EuclideanSpace ℝ (Fin K))] [BorelSpace (EuclideanSpace ℝ (Fin K))]
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (nu : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure nu]
    (mu0 : ℝ) (hmu : 0 ≤ mu0)
    (hmean : mu0 ≤ ∫ x, ‖gradient (wordLoss G W O psi) x‖^2 ∂nu) :
    mu0/(8*(K:ℝ)^2) ≤ nu.real
      (Overlap.gradRichSet (fun x => ‖gradient (wordLoss G W O psi) x‖^2) (mu0/2)) := by
  have hr := actual_routed_coverage hK G W O psi hpsi hG hGn hW hO
    nu nu 1 mu0 hmu hmean
  simpa [ActualWarmRoute.pushforward] using hr

/-- Under the stated bounded circuit hypotheses and `lam ≤ 1`, the tagged warm-start prior is a
probability measure and its routed mean squared gradient is at least `lam * mu0` when the
reference mean is at least `mu0` [TranEtAl2026]. -/
theorem actual_warm_mean
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {K : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin K))] [BorelSpace (EuclideanSpace ℝ (Fin K))]
    (G W : Fin K → Matrix I I ℂ) (O : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (hpsi : ‖psi‖=1) (hG : ∀ j, (G j).IsHermitian) (hGn : ∀ j, ‖G j‖ ≤ 1)
    (hW : ∀ j, W j ∈ Matrix.unitaryGroup I ℂ) (hO : ‖O‖ ≤ 1)
    (nu train : Measure (EuclideanSpace ℝ (Fin K))) [IsProbabilityMeasure nu]
    [IsProbabilityMeasure train] (lam : NNReal) (hlam : lam ≤ 1)
    (mu0 : ℝ) (hmean : mu0 ≤ ∫ x, ‖gradient (wordLoss G W O psi) x‖^2 ∂nu) :
    IsProbabilityMeasure (ActualWarmRoute.prior nu train lam) ∧
      (lam:ℝ)*mu0  ≤  ∫ z, ‖gradient (wordLoss G W O psi) (ActualWarmRoute.route z)‖^2
        ∂ActualWarmRoute.prior nu train lam := by
  obtain ⟨_,hcont,_,_,_⟩ := actual_word_loss_contract G W O psi hpsi hG hGn hW hO
  refine ⟨ActualWarmRoute.prior_isProbability nu train lam hlam,?_⟩
  exact ActualWarmRoute.native_gradient_transfer nu train lam (wordLoss G W O psi)
    (actual_word_gradient_sq_integrable G W O psi hpsi hG hGn hW hO nu)
    (actual_word_gradient_sq_integrable G W O psi hpsi hG hGn hW hO train)
    (squaredGradient_continuous _ hcont).aestronglyMeasurable mu0 hmean

end Qatlib.Papers.LatentPQCTran26.MainResults.QuantumConsumers
