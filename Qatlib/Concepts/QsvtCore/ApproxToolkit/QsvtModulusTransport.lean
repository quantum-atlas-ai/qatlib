/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCore
import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferSamp
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreAuxiliary
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.LinearAlgebra.Lagrange
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureMeasurement
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureNaimark
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.ChannelTheory.TwirlChannel
import Qatlib.Concepts.WalkSearch.Spectral.Approximation
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse

/-!
# Modulus bounds for spectral and singular value transforms

This module transports scalar moduli of continuity to Hermitian functional calculus and singular
value transforms. It proves special cases of the bound with `modulusRobustnessFactor`, gives
polynomial interpolation and Hermitian dilation identities, and derives the general transport
conclusions under `PrintedLipschitzTransport` or `Th20MainBound`. The mathematical background is
developed in [GilyenSuLowWiebe2019].

## Main statements

* `clause33_conj3`: a rank dependent modulus estimate for Hermitian contractions.
* `clause33_of_printed_lipschitz_transport`: the three modulus conclusions under the stated
  Lipschitz transport hypothesis.
* `tunableGoal_of_th20`: conditional singular value bounds and dilation block identities.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open scoped BigOperators

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit
open Matrix Polynomial
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator Classical BigOperators
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

/-- A modulus of continuity is nonnegative at every nonnegative argument. -/
theorem modulus_nonneg {f : ℝ → ℂ} {ω : ℝ → ℝ} (hω : ModulusOfContinuity f ω)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ω t := by
  have h := hω.mono ht
  rw [hω.at_zero] at h
  exact h

/-- The modulus robustness factor is at least four for nonnegative perturbation size. -/
theorem four_le_modulusRobustnessFactor {δ : ℝ} (hδ : 0 ≤ δ) :
    4 ≤ modulusRobustnessFactor δ := by
  unfold modulusRobustnessFactor
  have h2δ : (0:ℝ) ≤ 2 / δ := div_nonneg (by norm_num) hδ
  have hle : (1:ℝ) ≤ 2 / δ + 1 := by linarith
  have hlog : (0:ℝ) ≤ Real.log (2 / δ + 1) := Real.log_nonneg hle
  have hx : (1:ℝ) ≤ Real.log (2 / δ + 1) + 1 := by linarith
  have hnn : (0:ℝ) ≤ Real.log (2 / δ + 1) + 1 := by linarith
  have hsq : (1:ℝ) ≤ (Real.log (2 / δ + 1) + 1) ^ 2 := by
    have := mul_le_mul hx hx (by norm_num) hnn
    simpa [pow_two] using! this
  have := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 4)
  simpa using! this

/-- The norm of the difference of two matrix contractions is at most two. -/
theorem norm_sub_le_two {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A - B‖ ≤ 2 := by
  have h := norm_sub_le A B
  have hn : ‖(-B : Matrix I I ℂ)‖ = ‖B‖ := norm_neg B
  have h2 : ‖A‖ + ‖B‖ ≤ 2 := by linarith
  exact h.trans h2

/-- The modulus robustness factor is at least eleven for perturbation sizes in `(0, 2]`. -/
theorem eleven_le_modulusRobustnessFactor {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    (11:ℝ) ≤ modulusRobustnessFactor δ := by
  have hdiv : (1:ℝ) ≤ 2 / δ := by
    rw [one_le_div₀ hδ]
    linarith
  have hx : (2:ℝ) ≤ 2 / δ + 1 := by linarith
  have hlog : Real.log 2 ≤ Real.log (2 / δ + 1) :=
    Real.log_le_log (by norm_num) hx
  have h1 : (1 + Real.log 2 : ℝ) ≤ Real.log (2 / δ + 1) + 1 := by linarith
  have hnn1 : (0:ℝ) ≤ 1 + Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hnn2 : (0:ℝ) ≤ Real.log (2 / δ + 1) + 1 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hsq : ((1 + Real.log 2 : ℝ) ^ 2) ≤ (Real.log (2 / δ + 1) + 1) ^ 2 :=
    (sq_le_sq₀ hnn1 hnn2).mpr h1
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h169 : (1.69 : ℝ) ≤ 1 + Real.log 2 := by linarith
  have hsq2 : ((1.69 : ℝ) ^ 2) ≤ (1 + Real.log 2) ^ 2 := (sq_le_sq₀ (by norm_num) hnn1).mpr h169
  have h4 : (11.4244 : ℝ) ≤ 4 * (1 + Real.log 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq2 (by norm_num : (0:ℝ) ≤ 4)
    have hcalc : (4:ℝ) * (1.69:ℝ) ^ 2 = 11.4244 := by norm_num
    rw [hcalc] at h
    exact h
  have h5 : 4 * (1 + Real.log 2) ^ 2 ≤ 4 * (Real.log (2 / δ + 1) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 4)
  unfold modulusRobustnessFactor
  linarith

/-- Hermitian functional calculus gives the same matrix when the norm of the difference of its
matrix arguments is zero. -/
theorem clause33_conj2 :
    ∀ (H : Type) [Fintype H] [DecidableEq H] (A B : Matrix H H ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ),
    ‖A - B‖ = 0 → hermitianFunction A hA f = hermitianFunction B hB f := by
  intro H _ _ A B hA hB f h
  exact hermitianFunction_eq_of_norm_sub_zero A B hA hB f h

/-- There is a positive universal constant giving a modulus bound for Hermitian contractions
with a logarithmic weight in the smaller rank. -/
theorem clause33_conj3 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
        (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ),
        ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω →
          ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
            (2 + c₀ * hermitianRankLogWeight (min A.rank B.rank)) * ω ‖A - B‖ :=
  modulus_rankLog_stability

/-- At positive matrix separation, the swept clamped response is scalar Lipschitz on the pair of
spectra with constant `ω ‖A - B‖ / ‖A - B‖`. -/
theorem linearSweep_pair_lipschitz {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℂ) (ω : ℝ → ℝ) (hω : ModulusOfContinuity f ω)
    (hδpos : 0 < ‖A - B‖) :
    hermitianPairScalarLipschitz A hA B hB
      (linearSweep ‖A - B‖ (clampResponse f)) (ω ‖A - B‖ / ‖A - B‖) := by
  intro x _ y _
  exact linearSweep_lipschitz hδpos (clampResponse_dominates hω) hω.mono x y

/-- A bound `M` for the swept responses yields a bound of `2 * ω ‖A - B‖ + M` for the original
Hermitian responses. -/
theorem modulus_main_of_middle {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖) (M : ℝ)
    (hM : ‖hermitianFunction A hA (linearSweep ‖A - B‖ (clampResponse f)) -
        hermitianFunction B hB (linearSweep ‖A - B‖ (clampResponse f))‖ ≤ M) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      2 * ω ‖A - B‖ + M := by
  set F : ℝ → ℂ := clampResponse f
  set G : ℝ → ℂ := linearSweep ‖A - B‖ F
  have hdom : ∀ x y : ℝ, ‖F x - F y‖ ≤ ω |x - y| := fun x y => clampResponse_dominates hω x y
  have hωδ : 0 ≤ ω ‖A - B‖ := modulus_nonneg hω (norm_nonneg _)
  have hclose : ∀ x : ℝ, ‖F x - G x‖ ≤ ω ‖A - B‖ :=
    fun x => linearSweep_close hδpos hdom hω.mono x
  have hF : hermitianFunction A hA f = hermitianFunction A hA F :=
    hermitianFunction_clampResponse A hA f hA1
  have hFB : hermitianFunction B hB f = hermitianFunction B hB F :=
    hermitianFunction_clampResponse B hB f hB1
  have hAclose : ‖hermitianFunction A hA F - hermitianFunction A hA G‖ ≤ ω ‖A - B‖ := by
    rw [hermitianFunction_sub]
    exact hermitianFunction_norm_le A hA _ hωδ (fun i => hclose _)
  have hBclose : ‖hermitianFunction B hB G - hermitianFunction B hB F‖ ≤ ω ‖A - B‖ := by
    rw [hermitianFunction_sub]
    exact hermitianFunction_norm_le B hB _ hωδ (fun i => by
      have := hclose (orderedHermitianValues hB i)
      simpa [norm_sub_rev] using! this)
  have hdecomp : hermitianFunction A hA f - hermitianFunction B hB f =
      (hermitianFunction A hA F - hermitianFunction A hA G) +
        (hermitianFunction A hA G - hermitianFunction B hB G) +
        (hermitianFunction B hB G - hermitianFunction B hB F) := by
    rw [hF, hFB]
    module
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  have hboth : (‖hermitianFunction A hA F - hermitianFunction A hA G‖ +
        ‖hermitianFunction A hA G - hermitianFunction B hB G‖) +
      ‖hermitianFunction B hB G - hermitianFunction B hB F‖ ≤
        (ω ‖A - B‖ + M) + ω ‖A - B‖ :=
    add_le_add (add_le_add hAclose hM) hBclose
  have hsum : (ω ‖A - B‖ + M) + ω ‖A - B‖ = 2 * ω ‖A - B‖ + M := by ring
  exact hboth.trans (le_of_eq hsum)

/-- The modulus robustness bound holds for distinct Hermitian contractions when at least one has
rank zero. -/
theorem modulus_printed_of_minRankZero {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (hr : min A.rank B.rank = 0) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have hδne : ‖A - B‖ ≠ 0 := ne_of_gt hδpos
  have hωδ : 0 ≤ ω ‖A - B‖ := modulus_nonneg hω (norm_nonneg _)
  have hL : 0 ≤ ω ‖A - B‖ / ‖A - B‖ := div_nonneg hωδ (le_of_lt hδpos)
  have hpair := linearSweep_pair_lipschitz A B hA hB f ω hω hδpos
  have hstab := hermitianFunction_operator_stability_min_rank_zero A B hA hB hr
    (linearSweep ‖A - B‖ (clampResponse f)) (ω ‖A - B‖ / ‖A - B‖) hL hpair
  have hw : hermitianRankLogWeight 0 = 1 := by
    unfold hermitianRankLogWeight
    rw [Nat.cast_zero, _root_.add_zero, Real.log_one, _root_.add_zero]
  rw [hr, hw] at hstab
  have hmid : ‖hermitianFunction A hA (linearSweep ‖A - B‖ (clampResponse f)) -
      hermitianFunction B hB (linearSweep ‖A - B‖ (clampResponse f))‖ ≤ ω ‖A - B‖ := by
    refine hstab.trans ?_
    have h1 : (1:ℝ) * (ω ‖A - B‖ / ‖A - B‖) * ‖A - B‖ = ω ‖A - B‖ := by
      rw [one_mul, div_mul_cancel₀ _ hδne]
    exact le_of_eq h1
  have h3 := modulus_main_of_middle A B hA hB hA1 hB1 f ω hω hδpos (ω ‖A - B‖) hmid
  have h3' : ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤ 3 * ω ‖A - B‖ := by
    have hsum : 2 * ω ‖A - B‖ + ω ‖A - B‖ = 3 * ω ‖A - B‖ := by ring
    exact h3.trans (le_of_eq hsum)
  have hfac := four_le_modulusRobustnessFactor (norm_nonneg (A - B))
  have hle : (3:ℝ) ≤ modulusRobustnessFactor ‖A - B‖ := by linarith
  have hmul : 3 * ω ‖A - B‖ ≤ modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ :=
    mul_le_mul_of_nonneg_right hle hωδ
  exact h3'.trans hmul

/-- The spectral Frobenius norm is bounded by the operator norm times the square root of the
matrix dimension. -/
theorem spectralFrobenius_le_sqrt_card_mul_norm {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : spectralFrobenius X ≤ Real.sqrt (Fintype.card I) * ‖X‖ := by
  have hcol (j : I) : ∑ i : I, Complex.normSq (X i j) ≤ ‖X‖ ^ 2 := by
    have hv := Matrix.l2_opNorm_mulVec X (EuclideanSpace.single j (1:ℂ))
    change ‖X.toEuclideanLin (EuclideanSpace.single j (1:ℂ))‖ ≤
      ‖X‖ * ‖EuclideanSpace.single j (1:ℂ)‖ at hv
    have hnorm : ‖EuclideanSpace.single j (1:ℂ)‖ = 1 := by
      simp
    rw [hnorm, mul_one] at hv
    have hentry (i : I) : X.toEuclideanLin (EuclideanSpace.single j (1:ℂ)) i = X i j := by
      simp [Matrix.toEuclideanLin]
    have hsq : ‖X.toEuclideanLin (EuclideanSpace.single j (1:ℂ))‖ ^ 2 =
        ∑ i : I, ‖X.toEuclideanLin (EuclideanSpace.single j (1:ℂ)) i‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    have hle : ‖X.toEuclideanLin (EuclideanSpace.single j (1:ℂ))‖ ^ 2 ≤ ‖X‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hv
    have hconv : (∑ i : I, Complex.normSq (X i j)) = ∑ i : I, ‖X i j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Complex.normSq_eq_norm_sq (X i j)
    have hpoint : (∑ i : I, ‖X i j‖ ^ 2 : ℝ) =
        ∑ i : I, ‖X.toEuclideanLin (EuclideanSpace.single j (1:ℂ)) i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hentry]
    rw [hconv, hpoint, ← hsq]
    exact hle
  have hsum : (∑ j : I, ∑ i : I, Complex.normSq (X i j)) ≤
      (∑ j : I, (‖X‖ ^ 2 : ℝ)) := Finset.sum_le_sum (fun j _ => hcol j)
  have hconst : (∑ j : I, (‖X‖ ^ 2 : ℝ)) = (Fintype.card I : ℝ) * ‖X‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Real.sqrt (Fintype.card I : ℝ)) ^ 2 = (Fintype.card I : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hroot : (0:ℝ) ≤ Real.sqrt (Fintype.card I : ℝ) := Real.sqrt_nonneg _
  have hnn : (0:ℝ) ≤ Real.sqrt (Fintype.card I : ℝ) * ‖X‖ :=
    mul_nonneg hroot (norm_nonneg _)
  apply (sq_le_sq₀ (spectralFrobenius_nonneg _) hnn).mp
  rw [spectralFrobenius_sq, mul_pow, hN, Finset.sum_comm]
  exact hsum.trans (le_of_eq hconst)

/-- The modulus robustness bound holds when its factor dominates two plus the square root of the
dimension. -/
theorem modulus_printed_of_card_bound {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (hcard : 2 + Real.sqrt (Fintype.card I) ≤ modulusRobustnessFactor ‖A - B‖) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have hδne : ‖A - B‖ ≠ 0 := ne_of_gt hδpos
  have hωδ : 0 ≤ ω ‖A - B‖ := modulus_nonneg hω (norm_nonneg _)
  have hL : 0 ≤ ω ‖A - B‖ / ‖A - B‖ := div_nonneg hωδ (le_of_lt hδpos)
  have hlip : ∀ x y : ℝ, ‖linearSweep ‖A - B‖ (clampResponse f) x -
      linearSweep ‖A - B‖ (clampResponse f) y‖ ≤ (ω ‖A - B‖ / ‖A - B‖) * |x - y| :=
    fun x y => linearSweep_lipschitz hδpos (clampResponse_dominates hω) hω.mono x y
  have hfrob := hermitian_spectral_function_frobenius_stability I A B hA hB
    (linearSweep ‖A - B‖ (clampResponse f)) (ω ‖A - B‖ / ‖A - B‖) hL (fun i j => hlip _ _)
  have hop := spectral_operator_norm_le_frobenius
    (hermitianFunction A hA (linearSweep ‖A - B‖ (clampResponse f)) -
      hermitianFunction B hB (linearSweep ‖A - B‖ (clampResponse f)))
  have hfroAB := spectralFrobenius_le_sqrt_card_mul_norm (A - B)
  have hmid : ‖hermitianFunction A hA (linearSweep ‖A - B‖ (clampResponse f)) -
      hermitianFunction B hB (linearSweep ‖A - B‖ (clampResponse f))‖ ≤
        Real.sqrt (Fintype.card I) * ω ‖A - B‖ := by
    refine hop.trans ?_
    refine hfrob.trans ?_
    have h1 : (ω ‖A - B‖ / ‖A - B‖) * spectralFrobenius (A - B) ≤
        (ω ‖A - B‖ / ‖A - B‖) * (Real.sqrt (Fintype.card I) * ‖A - B‖) :=
      mul_le_mul_of_nonneg_left hfroAB hL
    have h2 : (ω ‖A - B‖ / ‖A - B‖) * (Real.sqrt (Fintype.card I) * ‖A - B‖) =
        Real.sqrt (Fintype.card I) * ω ‖A - B‖ := by
      have h2a : ω ‖A - B‖ / ‖A - B‖ * (Real.sqrt (Fintype.card I) * ‖A - B‖) =
          ω ‖A - B‖ / ‖A - B‖ * ‖A - B‖ * Real.sqrt (Fintype.card I) := by ring
      rw [h2a, div_mul_cancel₀ _ hδne]
      ring
    exact h1.trans (le_of_eq h2)
  have h3 := modulus_main_of_middle A B hA hB hA1 hB1 f ω hω hδpos
    (Real.sqrt (Fintype.card I) * ω ‖A - B‖) hmid
  have h3' : ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      (2 + Real.sqrt (Fintype.card I)) * ω ‖A - B‖ := by
    have hsum : 2 * ω ‖A - B‖ + Real.sqrt (Fintype.card I) * ω ‖A - B‖ =
        (2 + Real.sqrt (Fintype.card I)) * ω ‖A - B‖ := by ring
    exact h3.trans (le_of_eq hsum)
  have hmul : (2 + Real.sqrt (Fintype.card I)) * ω ‖A - B‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ :=
    mul_le_mul_of_nonneg_right hcard hωδ
  exact h3'.trans hmul

/-- The modulus robustness bound holds for distinct Hermitian contractions of dimension at most
eighty-one. -/
theorem modulus_printed_of_card_le_eighty_one {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity f ω) (hδpos : 0 < ‖A - B‖)
    (hcard : Fintype.card I ≤ 81) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  apply modulus_printed_of_card_bound A B hA hB hA1 hB1 f ω hω hδpos
  have hδ2 : ‖A - B‖ ≤ 2 := norm_sub_le_two A B hA1 hB1
  have hfac := eleven_le_modulusRobustnessFactor hδpos hδ2
  have hsqrt : Real.sqrt (Fintype.card I) ≤ 9 := by
    have h : (Fintype.card I : ℝ) ≤ 81 := by exact_mod_cast hcard
    have h9 : Real.sqrt (81:ℝ) = 9 := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
    calc Real.sqrt (Fintype.card I) ≤ Real.sqrt 81 := Real.sqrt_le_sqrt h
      _ = 9 := h9
  have h11 : Real.sqrt (Fintype.card I) + 2 ≤ (11:ℝ) := by linarith
  linarith

/-- The Hermitian functional calculus of a constant response is that constant times the identity
matrix. -/
theorem hermitianFunction_const {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (c : ℂ) :
    hermitianFunction A hA (fun _ : ℝ => c) = c • (1 : Matrix I I ℂ) := by
  unfold hermitianFunction
  exact spectralDiagonal_const _ _

/-- Constant responses satisfy the modulus robustness bound for any two Hermitian matrices. -/
theorem modulus_printed_of_const_response {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (c : ℂ) (ω : ℝ → ℝ) (hω : ModulusOfContinuity (fun _ : ℝ => c) ω) :
    ‖hermitianFunction A hA (fun _ : ℝ => c) - hermitianFunction B hB (fun _ : ℝ => c)‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  rw [hermitianFunction_const, hermitianFunction_const, sub_self, norm_zero]
  exact mul_nonneg (le_trans (by norm_num) (four_le_modulusRobustnessFactor (norm_nonneg _)))
    (modulus_nonneg hω (norm_nonneg _))

/-- Hermitian functional calculus sends the affine response `c + m * x` to `c • 1 + m • A`. -/
theorem hermitianFunction_affine {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (c m : ℂ) :
    hermitianFunction A hA (fun x : ℝ => c + m * (x:ℂ)) =
      c • (1 : Matrix I I ℂ) + m • A := by
  have hadd : hermitianFunction A hA (fun x : ℝ => c + m * (x:ℂ)) =
      hermitianFunction A hA (fun _ : ℝ => c) + hermitianFunction A hA (fun x : ℝ => m * (x:ℂ)) :=
    hermitianFunction_add hA (fun _ : ℝ => c) (fun x : ℝ => m * (x:ℂ))
  have hmul := hermitianFunction_mul hA m (fun x : ℝ => (x:ℂ))
  have hid : hermitianFunction A hA (fun x : ℝ => (x:ℂ)) = A :=
    (orderedHermitian_diagonal hA).symm
  rw [hadd, hermitianFunction_const, hmul, hid]

/-- Affine responses satisfy the modulus robustness bound for distinct Hermitian contractions. -/
theorem modulus_printed_of_affine_response {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (c m : ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity (fun x : ℝ => c + m * (x:ℂ)) ω) (hδpos : 0 < ‖A - B‖) :
    ‖hermitianFunction A hA (fun x : ℝ => c + m * (x:ℂ)) -
      hermitianFunction B hB (fun x : ℝ => c + m * (x:ℂ))‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have hdiff : hermitianFunction A hA (fun x : ℝ => c + m * (x:ℂ)) -
      hermitianFunction B hB (fun x : ℝ => c + m * (x:ℂ)) = m • (A - B) := by
    rw [hermitianFunction_affine, hermitianFunction_affine, smul_sub]
    abel
  have hnorm : ‖hermitianFunction A hA (fun x : ℝ => c + m * (x:ℂ)) -
      hermitianFunction B hB (fun x : ℝ => c + m * (x:ℂ))‖ = ‖m‖ * ‖A - B‖ := by
    rw [hdiff, norm_smul]
  have hδ2 : ‖A - B‖ ≤ 2 := norm_sub_le_two A B hA1 hB1
  have hx : (‖A - B‖ / 2 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> (try dsimp only)
    · nlinarith
    · nlinarith
  have hy : (-(‖A - B‖ / 2) : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> (try dsimp only)
    · nlinarith
    · nlinarith
  have hdom := hω.dominates (‖A - B‖ / 2) (-(‖A - B‖ / 2)) hx hy
  have habs : |(‖A - B‖ / 2) - (-(‖A - B‖ / 2))| = ‖A - B‖ := by
    have h : (‖A - B‖ / 2) - (-(‖A - B‖ / 2)) = ‖A - B‖ := by ring
    rw [h, abs_of_nonneg (norm_nonneg _)]
  have hfm : (fun x : ℝ => c + m * (x:ℂ)) (‖A - B‖ / 2) -
      (fun x : ℝ => c + m * (x:ℂ)) (-(‖A - B‖ / 2)) = m * ((‖A - B‖ : ℝ) : ℂ) := by
    push_cast
    ring
  have hfmn : ‖(fun x : ℝ => c + m * (x:ℂ)) (‖A - B‖ / 2) -
      (fun x : ℝ => c + m * (x:ℂ)) (-(‖A - B‖ / 2))‖ = ‖m‖ * ‖A - B‖ := by
    rw [hfm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hdom' : ‖(fun x : ℝ => c + m * (x:ℂ)) (‖A - B‖ / 2) -
      (fun x : ℝ => c + m * (x:ℂ)) (-(‖A - B‖ / 2))‖ ≤ ω ‖A - B‖ := by
    have := hdom
    rw [habs] at this
    exact this
  have hm : ‖m‖ * ‖A - B‖ ≤ ω ‖A - B‖ := by
    rw [← hfmn]
    exact hdom'
  have hωδ : 0 ≤ ω ‖A - B‖ := modulus_nonneg hω (norm_nonneg _)
  have hfac := four_le_modulusRobustnessFactor (norm_nonneg (A - B))
  have h1 : ‖m‖ * ‖A - B‖ ≤ modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
    have hge : ω ‖A - B‖ ≤ modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
      have := mul_le_mul_of_nonneg_right (by linarith [hfac] : (1:ℝ) ≤
        modulusRobustnessFactor ‖A - B‖) hωδ
      simpa using! this
    exact hm.trans hge
  rw [hnorm]
  exact h1

/-- Every natural power of a matrix contraction has norm at most one. -/
theorem norm_pow_le_one {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : ‖A‖ ≤ 1) (k : ℕ) : ‖A ^ k‖ ≤ 1 := by
  induction k with
  | zero =>
    simp only [pow_zero]
    apply Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis.l2_opNorm_le_of_inner_le
      (1 : Matrix I I ℂ) zero_le_one
    intro u v hu hv
    have hmap : ((1 : Matrix I I ℂ).toEuclideanLin) v = v := by
      simp [Matrix.toEuclideanLin]
    rw [hmap]
    have hii : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    rw [hu, hv, mul_one] at hii
    exact hii
  | succ k ih =>
    rw [pow_succ]
    exact (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul ih hA (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul (1:ℝ))))

/-- The difference of the `k`th powers of two matrix contractions has norm at most `k * ‖A -
B‖`. -/
theorem pow_sub_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (k : ℕ) :
    ‖A ^ k - B ^ k‖ ≤ (k : ℝ) * ‖A - B‖ := by
  induction k with
  | zero =>
    simp only [pow_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul]
    exact le_rfl
  | succ k ih =>
    have hkey : A ^ (k + 1) - B ^ (k + 1) =
        A ^ k * (A - B) + (A ^ k - B ^ k) * B := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul]
      abel
    rw [hkey]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖A ^ k * (A - B)‖ ≤ ‖A - B‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        ((mul_le_mul_of_nonneg_right (norm_pow_le_one A hA k) (norm_nonneg _)).trans
          (le_of_eq (one_mul _)))
    have h2 : ‖(A ^ k - B ^ k) * B‖ ≤ (k : ℝ) * ‖A - B‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        ((mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans (le_of_eq (mul_one _)) |>.trans ih)
    have h3 : ‖A - B‖ + (k : ℝ) * ‖A - B‖ = ((k + 1 : ℕ) : ℝ) * ‖A - B‖ := by
      push_cast
      ring
    have := add_le_add h1 h2
    exact this.trans (le_of_eq h3)

/-- Polynomial functional calculus on Hermitian contractions is Lipschitz with constant bounded
by the sum of `k * |p.coeff k|`. -/
theorem polynomial_sub_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (p : Polynomial ℝ) :
    ‖hermitianFunction A hA (fun x => ((p.eval x : ℝ) : ℂ)) -
      hermitianFunction B hB (fun x => ((p.eval x : ℝ) : ℂ))‖ ≤
      (∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k|) * ‖A - B‖ := by
  rw [hermitian_spectral_polynomial_evaluation, hermitian_spectral_polynomial_evaluation]
  rw [Polynomial.aeval_eq_sum_range (A : Matrix I I ℂ), Polynomial.aeval_eq_sum_range B]
  have hinj : Function.Injective (⇑Complex.ofRealHom) := by
    intro a b h
    exact Complex.ofReal_injective h
  have hdeg : (p.map Complex.ofRealHom).natDegree = p.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hinj p]
  have hsum : (∑ i ∈ Finset.range ((p.map Complex.ofRealHom).natDegree + 1),
        (p.map Complex.ofRealHom).coeff i • A ^ i) -
      (∑ i ∈ Finset.range ((p.map Complex.ofRealHom).natDegree + 1),
        (p.map Complex.ofRealHom).coeff i • B ^ i) =
      ∑ i ∈ Finset.range ((p.map Complex.ofRealHom).natDegree + 1),
        (p.map Complex.ofRealHom).coeff i • (A ^ i - B ^ i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_sub]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm (i : ℕ) :
      ‖(p.map Complex.ofRealHom).coeff i • (A ^ i - B ^ i)‖ ≤
        |p.coeff i| * ((i : ℝ) * ‖A - B‖) := by
    have hc : (p.map Complex.ofRealHom).coeff i = ((p.coeff i : ℝ) : ℂ) :=
      Polynomial.coeff_map Complex.ofRealHom i
    rw [hc, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_sub_norm_le A B hA1 hB1 i) (abs_nonneg _)
  have hsumle : (∑ i ∈ Finset.range ((p.map Complex.ofRealHom).natDegree + 1),
      ‖(p.map Complex.ofRealHom).coeff i • (A ^ i - B ^ i)‖) ≤
      ∑ i ∈ Finset.range ((p.map Complex.ofRealHom).natDegree + 1),
        |p.coeff i| * ((i : ℝ) * ‖A - B‖) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  refine hsumle.trans ?_
  have hre : (∑ i ∈ Finset.range ((p.map Complex.ofRealHom).natDegree + 1),
      |p.coeff i| * ((i : ℝ) * ‖A - B‖)) =
      (∑ i ∈ Finset.range (p.natDegree + 1), (i : ℝ) * |p.coeff i|) * ‖A - B‖ := by
    rw [hdeg]
    have hrow (i : ℕ) : |p.coeff i| * ((i : ℝ) * ‖A - B‖) =
        ((i : ℝ) * |p.coeff i|) * ‖A - B‖ := by ring
    have hsum' : (∑ i ∈ Finset.range (p.natDegree + 1),
        |p.coeff i| * ((i : ℝ) * ‖A - B‖)) =
        ∑ i ∈ Finset.range (p.natDegree + 1),
          ((i : ℝ) * |p.coeff i|) * ‖A - B‖ :=
      Finset.sum_congr rfl (fun i _ => hrow i)
    rw [hsum', ← Finset.sum_mul]
  rw [hre]

/-- A coefficient bound dominated by the target modulus estimate yields the modulus robustness
bound for a real polynomial response. -/
theorem modulus_printed_of_polynomial_response {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (p : Polynomial ℝ) (ω : ℝ → ℝ)
    (_hω : ModulusOfContinuity (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) ω)
    (hcmp : (∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k|) * ‖A - B‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖) :
    ‖hermitianFunction A hA (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      hermitianFunction B hB (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ :=
  (polynomial_sub_norm_le A B hA hB hA1 hB1 p).trans hcmp

/-- A modulus bound with coefficient `K` implies the robustness bound when `K` is at most
`modulusRobustnessFactor ‖A - B‖`. -/
theorem modulus_printed_of_uniform_constant {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℂ) (ω : ℝ → ℝ) (hω : ModulusOfContinuity f ω) (K : ℝ)
    (hK : ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤ K * ω ‖A - B‖)
    (hcmp : K ≤ modulusRobustnessFactor ‖A - B‖) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ :=
  hK.trans (mul_le_mul_of_nonneg_right hcmp (modulus_nonneg hω (norm_nonneg (A - B))))

/-- A universal rank logarithm estimate yields the robustness bound when its coefficient is
dominated by the robustness factor for this pair. -/
theorem modulus_printed_of_rankLog_comparison {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity f ω)
    (h : ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ (J : Type) [Fintype J] [DecidableEq J] (A' B' : Matrix J J ℂ)
        (hA' : A'.IsHermitian) (hB' : B'.IsHermitian) (f' : ℝ → ℂ) (ω' : ℝ → ℝ),
        ‖A'‖ ≤ 1 → ‖B'‖ ≤ 1 → ModulusOfContinuity f' ω' →
          ‖hermitianFunction A' hA' f' - hermitianFunction B' hB' f'‖ ≤
            (2 + c₀ * hermitianRankLogWeight (min A'.rank B'.rank)) * ω' ‖A' - B'‖) ∧
      2 + c₀ * hermitianRankLogWeight (min A.rank B.rank) ≤
        modulusRobustnessFactor ‖A - B‖) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  obtain ⟨c₀, _, hap, hcmp⟩ := h
  exact modulus_printed_of_uniform_constant A B hA hB f ω hω
    (2 + c₀ * hermitianRankLogWeight (min A.rank B.rank))
    (hap I A B hA hB f ω hA1 hB1 hω) hcmp

/-- The assertion that scalar Lipschitz control on the spectra of distinct Hermitian
contractions yields operator control with coefficient `modulusRobustnessFactor ‖A - B‖ - 2`. -/
def PrintedLipschitzTransport : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (A B : Matrix J J ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (g : ℝ → ℂ) (L : ℝ),
    0 ≤ L → ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → 0 < ‖A - B‖ →
    hermitianPairScalarLipschitz A hA B hB g L →
    ‖hermitianFunction A hA g - hermitianFunction B hB g‖ ≤
      (modulusRobustnessFactor ‖A - B‖ - 2) * L * ‖A - B‖

/-- The Lipschitz transport hypothesis implies the modulus robustness bound for distinct
Hermitian contractions. -/
theorem clause33_conj1_of_printed_lipschitz_transport (hgap : PrintedLipschitzTransport) :
    ∀ (H : Type) [Fintype H] [DecidableEq H] (A B : Matrix H H ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → 0 < ‖A - B‖ →
      ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
        modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  intro H _ _ A B hA hB f ω hA1 hB1 hω hδpos
  have hδne : ‖A - B‖ ≠ 0 := ne_of_gt hδpos
  have hωδ : 0 ≤ ω ‖A - B‖ := modulus_nonneg hω (norm_nonneg (A - B))
  have hL : 0 ≤ ω ‖A - B‖ / ‖A - B‖ := div_nonneg hωδ (le_of_lt hδpos)
  have hpair := linearSweep_pair_lipschitz A B hA hB f ω hω hδpos
  have hgap' := hgap H A B hA hB (linearSweep ‖A - B‖ (clampResponse f))
    (ω ‖A - B‖ / ‖A - B‖) hL hA1 hB1 hδpos hpair
  have hmid : ‖hermitianFunction A hA (linearSweep ‖A - B‖ (clampResponse f)) -
      hermitianFunction B hB (linearSweep ‖A - B‖ (clampResponse f))‖ ≤
        (modulusRobustnessFactor ‖A - B‖ - 2) * ω ‖A - B‖ := by
    refine hgap'.trans ?_
    have h1 : (modulusRobustnessFactor ‖A - B‖ - 2) * (ω ‖A - B‖ / ‖A - B‖) * ‖A - B‖ =
        (modulusRobustnessFactor ‖A - B‖ - 2) * ω ‖A - B‖ := by
      rw [mul_assoc, div_mul_cancel₀ _ hδne]
    exact le_of_eq h1
  have hmain := modulus_main_of_middle A B hA hB hA1 hB1 f ω hω hδpos
    ((modulusRobustnessFactor ‖A - B‖ - 2) * ω ‖A - B‖) hmid
  have hsum : 2 * ω ‖A - B‖ + (modulusRobustnessFactor ‖A - B‖ - 2) * ω ‖A - B‖ =
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by ring
  exact hmain.trans (le_of_eq hsum)

/-- The Lipschitz transport hypothesis gives the robustness bound, equality at zero separation,
and the universal rank logarithm bound. -/
theorem clause33_of_printed_lipschitz_transport (hgap : PrintedLipschitzTransport) :
    (∀ (H : Type) [Fintype H] [DecidableEq H] (A B : Matrix H H ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → 0 < ‖A - B‖ →
      ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
        modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖) ∧
  (∀ (H : Type) [Fintype H] [DecidableEq H] (A B : Matrix H H ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ),
    ‖A - B‖ = 0 → hermitianFunction A hA f = hermitianFunction B hB f) ∧
  (∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω →
        ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
          (2 + c₀ * hermitianRankLogWeight (min A.rank B.rank)) * ω ‖A - B‖) := by
  refine ⟨?_, ?_, ?_⟩
  · exact clause33_conj1_of_printed_lipschitz_transport hgap
  · exact clause33_conj2
  · exact clause33_conj3
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator Classical BigOperators
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Module Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib

/-- Eigenvector columns whose matrix satisfies `W * Wᴴ = 1` express Hermitian functional
calculus by conjugating the diagonal response values. -/
theorem hermitianFunction_eq_of_eigenColumns {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (M : Matrix I I ℂ) (hM : M.IsHermitian) (f : ℝ → ℂ)
    (W : Matrix I (Fin n) ℂ) (lam : Fin n → ℝ)
    (hW1 : W * Wᴴ = 1)
    (hW : ∀ j : Fin n, M *ᵥ (fun i => W i j) = (lam j : ℂ) • (fun i => W i j)) :
    W * diagonal (fun j => f (lam j)) * Wᴴ = hermitianFunction M hM f := by
  have key : hermitianFunction M hM f * W = W * diagonal (fun j => f (lam j)) := by
    ext i j
    have hv := hermitianFunction_eigenvector M hM f (lam j) (fun k => W k j) (hW j)
    have hi := congrArg (fun v : I → ℂ => v i) hv
    simp only [Pi.smul_apply] at hi
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    change (hermitianFunction M hM f *ᵥ (fun k => W k j)) i = _
    rw [hi]
    ring
  calc W * diagonal (fun j => f (lam j)) * Wᴴ
      = (hermitianFunction M hM f * W) * Wᴴ := by rw [key]
    _ = hermitianFunction M hM f * (W * Wᴴ) := by rw [← Matrix.mul_assoc]
    _ = hermitianFunction M hM f * 1 := by rw [hW1]
    _ = hermitianFunction M hM f := by rw [Matrix.mul_one]

/-- Hermitian functional calculus for a complex polynomial agrees with evaluating that
polynomial at the matrix. -/
theorem hermitianFunction_polynomial_complex {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (p : Polynomial ℂ) :
    hermitianFunction A hA (fun x => p.eval (x : ℂ)) = aeval A p := by
  rw [aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hA) A
    (fun j => (orderedHermitianValues hA j : ℂ)) (orderedHermitianBasis_action hA)]
  unfold hermitianFunction
  congr 1

/-- Responses agreeing on all ordered eigenvalues give equal Hermitian functional calculus
matrices. -/
theorem hermitianFunction_congr_on_values {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f g : ℝ → ℂ)
    (h : ∀ i : Fin (Fintype.card I), f (orderedHermitianValues hA i) = g (orderedHermitianValues hA i)) :
    hermitianFunction A hA f = hermitianFunction A hA g := by
  unfold hermitianFunction
  congr 1
  funext i
  exact h i

/-- The assertion that a matrix has a nonzero eigenvector with eigenvalue `μ`. -/
def HasVecEigen {X : Type} [Fintype X] (M : Matrix X X ℂ) (μ : ℂ) : Prop :=
  ∃ v : X → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v

/-- Every eigenvalue of a unitarily conjugated diagonal matrix is one of its diagonal values. -/
theorem hasVecEigen_of_unitary_diagonal {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (W : Matrix X Y ℂ) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1) (g : Y → ℂ) (μ : ℂ)
    (h : HasVecEigen (W * diagonal g * Wᴴ) μ) : ∃ j : Y, μ = g j := by
  obtain ⟨v, hv0, hv⟩ := h
  by_contra hc
  have hne : ∀ j : Y, g j ≠ μ := by
    intro j hj
    exact hc ⟨j, hj.symm⟩
  have hcomp : (W * diagonal g * Wᴴ) *ᵥ v = W *ᵥ (diagonal g *ᵥ (Wᴴ *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hmu : W *ᵥ (diagonal g *ᵥ (Wᴴ *ᵥ v)) = μ • v := by rw [← hcomp]; exact hv
  have hmu2 : Wᴴ *ᵥ (W *ᵥ (diagonal g *ᵥ (Wᴴ *ᵥ v))) = Wᴴ *ᵥ (μ • v) := by rw [hmu]
  have hmu3 : diagonal g *ᵥ (Wᴴ *ᵥ v) = μ • (Wᴴ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hW2, Matrix.one_mulVec, Matrix.mulVec_smul] at hmu2
    exact hmu2
  have hcoord : ∀ j : Y, g j * (Wᴴ *ᵥ v) j = μ * (Wᴴ *ᵥ v) j := by
    intro j
    have := congrArg (fun z : Y → ℂ => z j) hmu3
    simpa [Matrix.mulVec_diagonal] using! this
  have hzero : Wᴴ *ᵥ v = 0 := by
    ext j
    have := hcoord j
    have hsub : (g j - μ) * (Wᴴ *ᵥ v) j = 0 := by linear_combination this
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (hne j))
  have hv' : v = W *ᵥ (Wᴴ *ᵥ v) := by
    conv_rhs => rw [Matrix.mulVec_mulVec, hW1, Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at hv'
  exact hv0 hv'

/-- The right Gram matrix is diagonal in the right singular basis with squared singular values. -/
theorem rightGram_spectralDiagonal {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) :
    Aᴴ * A = spectralDiagonal (rightSingularBasis A)
      (fun i => (matrixSingularValues A i : ℂ) ^ 2) :=
  eq_spectralDiagonal_of_action _ _ _ (gram_apply_rightSingularBasis A)

/-- The left Gram matrix acts on a left singular basis vector by the corresponding squared
singular value. -/
theorem leftSingularBasis_gram_action {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (j : Fin (Fintype.card O)) :
    (A * Aᴴ).toEuclideanLin (leftSingularBasis A j) =
      ((matrixSingularValues A j : ℂ) ^ 2) • leftSingularBasis A j := by
  have hmul : (A * Aᴴ).toEuclideanLin =
      A.toEuclideanLin ∘ₗ (A.toEuclideanLin.adjoint) := by
    rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [hmul, LinearMap.comp_apply]
  by_cases hi : (j : ℕ) < finrank ℂ A.toEuclideanLin.range
  · have hI : (j : ℕ) < Fintype.card I :=
      lt_of_lt_of_le hi (by simpa using! A.toEuclideanLin.finrank_range_le)
    have hk : leftSingularBasis A j = leftSingularVector A ⟨j, hI⟩ :=
      leftSingularBasis_apply_of_lt A j hi
    rw [hk, adjoint_apply_leftSingularVector A ⟨j, hI⟩, map_smul,
      apply_rightSingularBasis_eq_smul_leftSingularVector A ⟨j, hI⟩, smul_smul]
    simp [pow_two]
  · have hz : matrixSingularValues A j = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr (le_of_not_gt hi)
    rw [adjoint_apply_leftSingularBasis_of_rank_le A j (le_of_not_gt hi),
      LinearMap.map_zero, hz]
    simp

/-- The left Gram matrix is diagonal in the left singular basis with squared singular values. -/
theorem leftGram_spectralDiagonal {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) :
    A * Aᴴ = spectralDiagonal (leftSingularBasis A)
      (fun j => (matrixSingularValues A j : ℂ) ^ 2) :=
  eq_spectralDiagonal_of_action _ _ _ (leftSingularBasis_gram_action A)

/-- Every eigenvalue of the right Gram matrix is a squared singular value indexed by the input
dimension. -/
theorem hasVecEigen_rightGram {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (μ : ℂ) (h : HasVecEigen (Aᴴ * A) μ) :
    ∃ i : Fin (Fintype.card I), μ = (matrixSingularValues A i : ℂ) ^ 2 := by
  rw [rightGram_spectralDiagonal A] at h
  simpa [spectralDiagonal] using!
    hasVecEigen_of_unitary_diagonal (basisColumns (rightSingularBasis A))
      (basisColumns_mul_adjoint _) (basisColumns_adjoint_mul _) _ μ h

/-- Every eigenvalue of the left Gram matrix is a squared singular value indexed by the output
dimension. -/
theorem hasVecEigen_leftGram {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (μ : ℂ) (h : HasVecEigen (A * Aᴴ) μ) :
    ∃ j : Fin (Fintype.card O), μ = (matrixSingularValues A j : ℂ) ^ 2 := by
  rw [leftGram_spectralDiagonal A] at h
  simpa [spectralDiagonal] using!
    hasVecEigen_of_unitary_diagonal (basisColumns (leftSingularBasis A))
      (basisColumns_mul_adjoint _) (basisColumns_adjoint_mul _) _ μ h

/-- Every ordered eigenvalue of the Hermitian dilation is a singular value of `A` or its
negative; see [HarrowHassidimLloyd2009]. -/
theorem dilation_orderedValue_signed_singular {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (j : Fin (Fintype.card (O ⊕ I))) :
    ∃ k : ℕ,
      orderedHermitianValues (hermitianDilation_adjoint A) j = matrixSingularValues A k ∨
      orderedHermitianValues (hermitianDilation_adjoint A) j = -matrixSingularValues A k := by
  set D : Matrix (O ⊕ I) (O ⊕ I) ℂ := hermitianDilation A with hDeq
  set hD : D.IsHermitian := hermitianDilation_adjoint A with hDeq2
  set lam : ℝ := orderedHermitianValues hD j with hlameq
  set wv := orderedHermitianBasis hD j with hwveq
  have hact : D.toEuclideanLin wv = (lam : ℂ) • wv := by
    rw [hwveq, hlameq]
    exact orderedHermitianBasis_action (hermitianDilation_adjoint A) j
  let w : (O ⊕ I) → ℂ := WithLp.ofLp wv
  have hconv : WithLp.ofLp (D.toEuclideanLin wv) = D *ᵥ w := by
    have h := Matrix.ofLp_toLpLin 2 2 D wv
    change WithLp.ofLp ((toLpLin 2 2 D) wv) = _
    rw [h]
    simp [Matrix.toLin'_apply, w]
  have hw : D *ᵥ w = (lam : ℂ) • w := by
    have h1 := congrArg WithLp.ofLp hact
    rw [hconv] at h1
    have h3 : WithLp.ofLp ((lam : ℂ) • wv) = (lam : ℂ) • w := by simp [w]
    rw [h3] at h1
    exact h1
  have hw0 : w ≠ 0 := by
    intro hz
    have hnorm : ‖wv‖ = 1 := by
      rw [hwveq]
      exact (orderedHermitianBasis (hermitianDilation_adjoint A)).norm_eq_one j
    have hz' : wv = 0 := (WithLp.ofLp_eq_zero (p := 2)).mp (by simpa [w] using! hz)
    rw [hz'] at hnorm
    simp at hnorm
  have hsq : (D * D) *ᵥ w = ((lam : ℂ) ^ 2) • w := by
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, hw, smul_smul]
    rw [pow_two]
  have hD2 : D * D = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
    rw [hDeq, ← pow_two, hermitianDilation_sq]
  have hfb : Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) *ᵥ w = ((lam : ℂ) ^ 2) • w := by
    rw [← hD2]
    exact hsq
  have hO : (A * Aᴴ) *ᵥ (fun o => w (Sum.inl o)) = ((lam : ℂ) ^ 2) • (fun o => w (Sum.inl o)) := by
    ext o
    have := congrArg (fun z : (O ⊕ I) → ℂ => z (Sum.inl o)) hfb
    simp [Matrix.fromBlocks_mulVec] at this
    simpa using! this
  have hI : (Aᴴ * A) *ᵥ (fun i => w (Sum.inr i)) = ((lam : ℂ) ^ 2) • (fun i => w (Sum.inr i)) := by
    ext i
    have := congrArg (fun z : (O ⊕ I) → ℂ => z (Sum.inr i)) hfb
    simp [Matrix.fromBlocks_mulVec] at this
    simpa using! this
  have hsplit : (fun o => w (Sum.inl o)) ≠ 0 ∨ (fun i => w (Sum.inr i)) ≠ 0 := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    apply hw0
    funext s
    cases s with
    | inl o => exact congrFun hc.1 o
    | inr i => exact congrFun hc.2 i
  have hkey {kk : ℕ} (hk : (lam : ℂ) ^ 2 = (matrixSingularValues A kk : ℂ) ^ 2) :
      lam = matrixSingularValues A kk ∨ lam = -matrixSingularValues A kk := by
    have hre : ((lam ^ 2 : ℝ) : ℂ) = ((matrixSingularValues A kk ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, Complex.ofReal_pow]
      exact hk
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (Complex.ofReal_injective hre)
  rcases hsplit with hO0 | hI0
  · obtain ⟨kk, hk⟩ := hasVecEigen_leftGram A ((lam : ℂ) ^ 2) ⟨_, hO0, hO⟩
    exact ⟨kk, hkey hk⟩
  · obtain ⟨kk, hk⟩ := hasVecEigen_rightGram A ((lam : ℂ) ^ 2) ⟨_, hI0, hI⟩
    exact ⟨kk, hkey hk⟩

/-- Consistent complex values at finitely many real nodes can be interpolated by a complex
polynomial. -/
theorem exists_poly_eval_nodes {ι : Type} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (r : ι → ℂ)
    (hcons : ∀ i j, i ∈ s → j ∈ s → v i = v j → r i = r j) :
    ∃ p : Polynomial ℂ, ∀ i ∈ s, p.eval ((v i : ℝ) : ℂ) = r i := by
  classical
  by_cases hs : s.Nonempty
  · let nodes : Finset ℝ := s.image v
    have hex : ∀ x ∈ nodes, ∃ i ∈ s, v i = x := fun x hx => Finset.mem_image.mp hx
    let rN : ℝ → ℂ := fun x => if h : x ∈ nodes then r (Classical.choose (hex x h)) else 0
    have hinj : Set.InjOn (fun x : ℝ => (x : ℂ)) nodes := by
      intro x _ y _ hxy
      exact Complex.ofReal_injective hxy
    refine ⟨Lagrange.interpolate nodes (fun x : ℝ => (x : ℂ)) rN, ?_⟩
    intro i hi
    have hmem : v i ∈ nodes := Finset.mem_image_of_mem v hi
    have hval : rN (v i) = r i := by
      dsimp [rN]
      rw [dif_pos hmem]
      have hch := Classical.choose_spec (hex (v i) hmem)
      exact hcons (Classical.choose (hex (v i) hmem)) i hch.1 hi hch.2
    have hinterp : (Lagrange.interpolate nodes (fun x : ℝ => (x : ℂ)) rN).eval ((v i : ℝ) : ℂ)
        = rN (v i) :=
      Lagrange.eval_interpolate_at_node rN hinj hmem
    rw [hval] at hinterp
    exact hinterp
  · refine ⟨0, ?_⟩
    intro i hi
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hi
    simp at hi

/-- An odd complex valued function on the reals vanishes at zero. -/
theorem IsOddFunction_eq_zero {f : ℝ → ℂ} (h : IsOddFunction f) : f 0 = 0 := by
  have h1 : f 0 = -f 0 := by
    rw [← h 0]
    simp
  have h2 : f 0 + f 0 = 0 := by linear_combination h1
  have h3 : (2 : ℂ) * f 0 = 0 := by simpa [two_mul] using! h2
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- An even singular polynomial can interpolate any prescribed response on all singular values
of a finite matrix. -/
theorem exists_even_singular_poly {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (f : ℝ → ℂ) :
    ∃ q : Polynomial ℂ, ∀ k : ℕ,
      (evenSingularPolynomial q).eval (matrixSingularValues A k : ℂ) = f (matrixSingularValues A k) := by
  have hcons : ∀ i j, i ∈ Finset.range (Fintype.card I + 1) →
      j ∈ Finset.range (Fintype.card I + 1) →
      (matrixSingularValues A i : ℝ) ^ 2 = (matrixSingularValues A j : ℝ) ^ 2 →
      f (matrixSingularValues A i) = f (matrixSingularValues A j) := by
    intro i j _ _ hsq
    have hσ : matrixSingularValues A i = matrixSingularValues A j :=
      (sq_eq_sq₀ (matrixSingularValues_nonneg A i) (matrixSingularValues_nonneg A j)).mp hsq
    rw [hσ]
  obtain ⟨q, hq⟩ := exists_poly_eval_nodes (Finset.range (Fintype.card I + 1))
    (fun k => (matrixSingularValues A k : ℝ) ^ 2) (fun k => f (matrixSingularValues A k)) hcons
  refine ⟨q, ?_⟩
  intro k
  simp only [evenSingularPolynomial, Polynomial.eval_comp, Polynomial.eval_pow,
    Polynomial.eval_X]
  by_cases hk : k < Fintype.card I + 1
  · have := hq k (Finset.mem_range.mpr hk)
    simpa [Complex.ofReal_pow] using! this
  · have hz : matrixSingularValues A k = 0 :=
      matrixSingularValues_of_card_le A (by omega)
    have hσI : matrixSingularValues A (Fintype.card I) = 0 :=
      matrixSingularValues_of_card_le A le_rfl
    have h0 := hq (Fintype.card I) (Finset.mem_range.mpr (by simp))
    rw [hσI] at h0
    rw [hz]
    simpa using! h0

/-- An odd singular polynomial can interpolate an odd response on all singular values of a
finite matrix. -/
theorem exists_odd_singular_poly {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (f : ℝ → ℂ) (hodd : IsOddFunction f) :
    ∃ q : Polynomial ℂ, ∀ k : ℕ,
      (oddSingularPolynomial q).eval (matrixSingularValues A k : ℂ) = f (matrixSingularValues A k) := by
  have hcons : ∀ i j, i ∈ Finset.range (Fintype.card I + 1) →
      j ∈ Finset.range (Fintype.card I + 1) →
      (matrixSingularValues A i : ℝ) ^ 2 = (matrixSingularValues A j : ℝ) ^ 2 →
      (if matrixSingularValues A i = 0 then 0 else f (matrixSingularValues A i) / matrixSingularValues A i)
        = (if matrixSingularValues A j = 0 then 0 else f (matrixSingularValues A j) / matrixSingularValues A j) := by
    intro i j _ _ hsq
    have hσ : matrixSingularValues A i = matrixSingularValues A j :=
      (sq_eq_sq₀ (matrixSingularValues_nonneg A i) (matrixSingularValues_nonneg A j)).mp hsq
    rw [hσ]
  obtain ⟨q, hq⟩ := exists_poly_eval_nodes (Finset.range (Fintype.card I + 1))
    (fun k => (matrixSingularValues A k : ℝ) ^ 2)
    (fun k => if matrixSingularValues A k = 0 then 0
      else f (matrixSingularValues A k) / matrixSingularValues A k) hcons
  refine ⟨q, ?_⟩
  intro k
  have hσ0 : matrixSingularValues A k = 0 → f (matrixSingularValues A k) = 0 := by
    intro h
    rw [h, IsOddFunction_eq_zero hodd]
  simp only [oddSingularPolynomial, evenSingularPolynomial, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_pow]
  by_cases hz : matrixSingularValues A k = 0
  · have hfeq : f (0 : ℝ) = 0 := by
      rw [← hz]
      exact hσ0 hz
    rw [hz, hfeq]
    simp
  · by_cases hk : k < Fintype.card I + 1
    · have hkq := hq k (Finset.mem_range.mpr hk)
      rw [if_neg hz] at hkq
      have hcast : (((matrixSingularValues A k : ℝ) ^ 2 : ℝ) : ℂ) =
          ((matrixSingularValues A k : ℝ) : ℂ) ^ 2 := Complex.ofReal_pow _ _
      rw [hcast] at hkq
      have hne : (matrixSingularValues A k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
      calc (matrixSingularValues A k : ℂ) * q.eval ((matrixSingularValues A k : ℂ) ^ 2)
          = (matrixSingularValues A k : ℂ) *
              (f (matrixSingularValues A k) / (matrixSingularValues A k : ℂ)) := by rw [hkq]
        _ = f (matrixSingularValues A k) := by field_simp
    · exact absurd (matrixSingularValues_of_card_le A (by omega)) hz

/-- Responses agreeing on the input indexed singular values have equal right singular
transforms. -/
theorem rightSingularTransform_congr {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    (h : ∀ i : Fin (Fintype.card I), f (matrixSingularValues A i) = g (matrixSingularValues A i)) :
    rightSingularTransform A f = rightSingularTransform A g := by
  unfold rightSingularTransform
  congr 1
  funext i
  exact h i

/-- Responses agreeing on the output indexed singular values have equal left singular
transforms. -/
theorem leftSingularTransform_congr {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    (h : ∀ j : Fin (Fintype.card O), f (matrixSingularValues A j) = g (matrixSingularValues A j)) :
    leftSingularTransform A f = leftSingularTransform A g := by
  unfold leftSingularTransform
  congr 1
  funext j
  exact h j

/-- Evaluating an even singular polynomial at `-x` gives its value at `x`. -/
theorem evenSingularPolynomial_eval_neg (q : Polynomial ℂ) (x : ℂ) :
    (evenSingularPolynomial q).eval (-x) = (evenSingularPolynomial q).eval x := by
  simp [evenSingularPolynomial, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

/-- The odd singular polynomial associated to `q` evaluates to `x * q.eval (x ^ 2)`. -/
theorem oddSingularPolynomial_eval (q : Polynomial ℂ) (x : ℂ) :
    (oddSingularPolynomial q).eval x = x * q.eval (x ^ 2) := by
  simp [oddSingularPolynomial, evenSingularPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_pow]

/-- One odd singular polynomial interpolates an odd response on the singular values of both `A`
and its adjoint. -/
theorem exists_odd_singular_poly_pair {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (A : Matrix O I ℂ) (f : ℝ → ℂ) (hodd : IsOddFunction f) :
    ∃ q : Polynomial ℂ,
      (∀ k : ℕ, (oddSingularPolynomial q).eval (matrixSingularValues A k : ℂ)
        = f (matrixSingularValues A k)) ∧
      (∀ k : ℕ, (oddSingularPolynomial q).eval (matrixSingularValues Aᴴ k : ℂ)
        = f (matrixSingularValues Aᴴ k)) := by
  classical
  let xi : ℕ → ℝ := fun k =>
    if k < Fintype.card I + 1 then matrixSingularValues A k
    else matrixSingularValues Aᴴ (k - (Fintype.card I + 1))
  have hxiA : ∀ k < Fintype.card I + 1, xi k = matrixSingularValues A k := by
    intro k hk
    unfold xi
    rw [if_pos hk]
  have hxi_nonneg : ∀ k, 0 ≤ xi k := by
    intro k
    unfold xi
    split_ifs <;> exact matrixSingularValues_nonneg _ _
  have hxiAH : ∀ j, xi (Fintype.card I + 1 + j) = matrixSingularValues Aᴴ j := by
    intro j
    have h : ¬(Fintype.card I + 1 + j < Fintype.card I + 1) := by omega
    unfold xi
    rw [if_neg h]
    exact congrArg _ (Nat.add_sub_cancel_left (Fintype.card I + 1) j)
  have hcons : ∀ i j, i ∈ Finset.range (Fintype.card I + Fintype.card O + 2) →
      j ∈ Finset.range (Fintype.card I + Fintype.card O + 2) →
      (xi i : ℝ) ^ 2 = (xi j : ℝ) ^ 2 →
      (if xi i = 0 then 0 else f (xi i) / xi i) = (if xi j = 0 then 0 else f (xi j) / xi j) := by
    intro i j _ _ hsq
    have hxi : xi i = xi j :=
      (sq_eq_sq₀ (hxi_nonneg i) (hxi_nonneg j)).mp hsq
    rw [hxi]
  obtain ⟨q, hq⟩ := exists_poly_eval_nodes (Finset.range (Fintype.card I + Fintype.card O + 2))
    (fun k => (xi k : ℝ) ^ 2) (fun k => if xi k = 0 then 0 else f (xi k) / xi k) hcons
  have hval : ∀ k < Fintype.card I + Fintype.card O + 2, xi k ≠ 0 →
      (xi k : ℂ) * q.eval ((xi k : ℂ) ^ 2) = f (xi k) := by
    intro k hk hnz
    have hkq := hq k (Finset.mem_range.mpr hk)
    rw [if_neg hnz] at hkq
    have hne : (xi k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnz
    rw [Complex.ofReal_pow] at hkq
    calc (xi k : ℂ) * q.eval ((xi k : ℂ) ^ 2)
        = (xi k : ℂ) * (f (xi k) / (xi k : ℂ)) := by rw [hkq]
      _ = f (xi k) := by field_simp
  refine ⟨q, ?_, ?_⟩
  · intro k
    simp only [oddSingularPolynomial_eval]
    by_cases hk : k < Fintype.card I + 1
    · have hne : xi k = matrixSingularValues A k := hxiA k hk
      by_cases hz : matrixSingularValues A k = 0
      · rw [hz]
        simp [IsOddFunction_eq_zero hodd]
      · have := hval k (by omega) (by rw [hne]; exact hz)
        rw [hne] at this
        exact this
    · have hz : matrixSingularValues A k = 0 :=
        matrixSingularValues_of_card_le A (by omega)
      rw [hz]
      simp [IsOddFunction_eq_zero hodd]
  · intro k
    simp only [oddSingularPolynomial_eval]
    by_cases hk : k < Fintype.card O + 1
    · have hne : xi (Fintype.card I + 1 + k) = matrixSingularValues Aᴴ k := hxiAH k
      by_cases hz : matrixSingularValues Aᴴ k = 0
      · rw [hz]
        simp [IsOddFunction_eq_zero hodd]
      · have := hval (Fintype.card I + 1 + k) (by omega) (by rw [hne]; exact hz)
        rw [hne] at this
        exact this
    · have hz : matrixSingularValues Aᴴ k = 0 :=
        matrixSingularValues_of_card_le Aᴴ (by omega)
      rw [hz]
      simp [IsOddFunction_eq_zero hodd]

/-- A polynomial matching the response at all positive and negative singular values evaluates on
the Hermitian dilation to its functional calculus. -/
theorem hermitianFunction_dilation_eq_aeval {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (f : ℝ → ℂ) (p : Polynomial ℂ)
    (hmatch : ∀ k : ℕ,
      p.eval (matrixSingularValues A k : ℂ) = f (matrixSingularValues A k) ∧
      p.eval ((-(matrixSingularValues A k) : ℝ) : ℂ) = f (-matrixSingularValues A k)) :
    hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f
      = aeval (hermitianDilation A) p := by
  have h := hermitianFunction_congr_on_values (hermitianDilation A)
      (hermitianDilation_adjoint A) f (fun x => p.eval (x : ℂ)) (by
    intro j
    obtain ⟨k, hk⟩ := dilation_orderedValue_signed_singular A j
    rcases hk with h | h
    · rw [h]
      exact (hmatch k).1.symm
    · rw [h]
      exact (hmatch k).2.symm)
  rw [h, hermitianFunction_polynomial_complex]

/-- An even response of the Hermitian dilation is block diagonal with the left and right
singular transforms as its diagonal blocks. -/
theorem hermitianDilation_even_fromBlocks {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (f : ℝ → ℂ) (heven : IsEvenFunction f) :
    hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f =
      Matrix.fromBlocks (leftSingularTransform A f) 0 0 (rightSingularTransform A f) := by
  obtain ⟨q, hq⟩ := exists_even_singular_poly A f
  have hmatch : ∀ k : ℕ,
      (evenSingularPolynomial q).eval (matrixSingularValues A k : ℂ) = f (matrixSingularValues A k) ∧
      (evenSingularPolynomial q).eval ((-(matrixSingularValues A k) : ℝ) : ℂ)
        = f (-matrixSingularValues A k) := by
    intro k
    constructor
    · exact hq k
    · simp only [Complex.ofReal_neg, evenSingularPolynomial_eval_neg, hq k]
      rw [heven]
  have hfeq := hermitianFunction_dilation_eq_aeval A f (evenSingularPolynomial q) hmatch
  rw [hfeq, aeval_evenSingularPolynomial,
    leftGram_aeval_eq_leftSingularTransform, gram_aeval_eq_rightSingularTransform]
  have hleft : ∀ j : Fin (Fintype.card O),
      q.eval ((matrixSingularValues A j : ℂ) ^ 2) = f (matrixSingularValues A j) := by
    intro j
    have := hq j
    simpa [evenSingularPolynomial, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X] using! this
  have hright : ∀ i : Fin (Fintype.card I),
      q.eval ((matrixSingularValues A i : ℂ) ^ 2) = f (matrixSingularValues A i) := by
    intro i
    have := hq i
    simpa [evenSingularPolynomial, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X] using! this
  rw [leftSingularTransform_congr A _ _ hleft, rightSingularTransform_congr A _ _ hright]

/-- Evaluating an odd singular polynomial at `-x` negates its value at `x`. -/
theorem oddSingularPolynomial_eval_neg (q : Polynomial ℂ) (x : ℂ) :
    (oddSingularPolynomial q).eval (-x) = - (oddSingularPolynomial q).eval x := by
  simp [oddSingularPolynomial, evenSingularPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_pow]

/-- An odd response of the Hermitian dilation has zero diagonal blocks and the singular
transforms of `A` and `Aᴴ` off the diagonal; see [HarrowHassidimLloyd2009]. -/
theorem hermitianDilation_odd_fromBlocks {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (f : ℝ → ℂ) (hodd : IsOddFunction f) :
    hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f =
      Matrix.fromBlocks 0 (oddSingularTransform A f) (oddSingularTransform Aᴴ f) 0 := by
  obtain ⟨q, hqA, hqAH⟩ := exists_odd_singular_poly_pair A f hodd
  have hmatch : ∀ k : ℕ,
      (oddSingularPolynomial q).eval (matrixSingularValues A k : ℂ) = f (matrixSingularValues A k) ∧
      (oddSingularPolynomial q).eval ((-(matrixSingularValues A k) : ℝ) : ℂ)
        = f (-matrixSingularValues A k) := by
    intro k
    constructor
    · exact hqA k
    · simp only [Complex.ofReal_neg, oddSingularPolynomial_eval_neg, hqA k]
      rw [hodd]
  have hfeq := hermitianFunction_dilation_eq_aeval A f (oddSingularPolynomial q) hmatch
  rw [hfeq, aeval_oddSingularPolynomial]
  have hA : A * aeval (Aᴴ * A) q = oddSingularTransform A f := by
    rw [mul_gram_aeval_eq_oddSingularTransform]
    refine oddSingularTransform_congr_positive A (fun x => (x : ℂ) * q.eval ((x : ℂ) ^ 2)) f
      (fun i _ => ?_)
    have := hqA i
    simpa [oddSingularPolynomial_eval] using! this
  have hAH : Aᴴ * aeval (A * Aᴴ) q = oddSingularTransform Aᴴ f := by
    have hgram : (Aᴴ)ᴴ * Aᴴ = A * Aᴴ := by simp
    rw [← hgram, mul_gram_aeval_eq_oddSingularTransform]
    refine oddSingularTransform_congr_positive Aᴴ (fun x => (x : ℂ) * q.eval ((x : ℂ) ^ 2)) f
      (fun j _ => ?_)
    have := hqAH j
    simpa [oddSingularPolynomial_eval] using! this
  rw [hA, hAH]

/-- The assertion of the modulus robustness bound for functional calculus on distinct finite
Hermitian contractions. -/
def Th20MainBound : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (A B : Matrix H H ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → 0 < ‖A - B‖ →
      ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
        modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖

/-- The Hermitian modulus bound implies the same robustness estimate for odd singular transforms
of distinct contractions. -/
theorem odd_singularTransform_bound_of_th20 (hTh20 : Th20MainBound)
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω)
    (hodd : IsOddFunction f) (hδ : 0 < ‖A - B‖) :
    ‖oddSingularTransform A f - oddSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have h12A : (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f).toBlocks₁₂
      = oddSingularTransform A f := by
    rw [hermitianDilation_odd_fromBlocks A f hodd]
    simp
  have h12B : (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f).toBlocks₁₂
      = oddSingularTransform B f := by
    rw [hermitianDilation_odd_fromBlocks B f hodd]
    simp
  rw [← h12A, ← h12B]
  have hle := dilation_block12_sub_norm_le
    (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f)
    (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f)
  have hnormA : ‖hermitianDilation A‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hA1
  have hnormB : ‖hermitianDilation B‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hB1
  have hδ' : 0 < ‖hermitianDilation A - hermitianDilation B‖ := by
    rw [hermitianDilation_sub_norm]; exact hδ
  have hth := hTh20 (O ⊕ I) (hermitianDilation A) (hermitianDilation B)
    (hermitianDilation_adjoint A) (hermitianDilation_adjoint B) f ω
    hnormA hnormB hω hδ'
  rw [hermitianDilation_sub_norm] at hth
  exact hle.trans hth

/-- The Hermitian modulus bound implies the same robustness estimate for right singular
transforms with an even response. -/
theorem rightEven_singularTransform_bound_of_th20 (hTh20 : Th20MainBound)
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (hω : ModulusOfContinuity f ω)
    (heven : IsEvenFunction f) (hδ : 0 < ‖A - B‖) :
    ‖rightSingularTransform A f - rightSingularTransform B f‖ ≤
      modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖ := by
  have h22A : (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f).toBlocks₂₂
      = rightSingularTransform A f := by
    rw [hermitianDilation_even_fromBlocks A f heven]
    simp
  have h22B : (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f).toBlocks₂₂
      = rightSingularTransform B f := by
    rw [hermitianDilation_even_fromBlocks B f heven]
    simp
  rw [← h22A, ← h22B]
  have hle := dilation_block22_sub_norm_le
    (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f)
    (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f)
  have hnormA : ‖hermitianDilation A‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hA1
  have hnormB : ‖hermitianDilation B‖ ≤ 1 := by
    rw [hermitianDilation_norm]; exact hB1
  have hδ' : 0 < ‖hermitianDilation A - hermitianDilation B‖ := by
    rw [hermitianDilation_sub_norm]; exact hδ
  have hth := hTh20 (O ⊕ I) (hermitianDilation A) (hermitianDilation B)
    (hermitianDilation_adjoint A) (hermitianDilation_adjoint B) f ω
    hnormA hnormB hω hδ'
  rw [hermitianDilation_sub_norm] at hth
  exact hle.trans hth

/-- The Hermitian modulus bound yields odd and even singular transform estimates, equality at
zero separation, and the corresponding dilation block identities. -/
theorem tunableGoal_of_th20 (hTh20 : Th20MainBound) :
  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → IsOddFunction f →
      0 < ‖A - B‖ →
        ‖oddSingularTransform A f - oddSingularTransform B f‖ ≤
          modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖) ∧
  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → IsEvenFunction f →
      0 < ‖A - B‖ →
        ‖rightSingularTransform A f - rightSingularTransform B f‖ ≤
          modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖) ∧
  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A B : Matrix O I ℂ) (f : ℝ → ℂ),
    ‖A - B‖ = 0 →
      oddSingularTransform A f = oddSingularTransform B f ∧
        rightSingularTransform A f = rightSingularTransform B f) ∧
  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (hD : (hermitianDilation A).IsHermitian)
      (f : ℝ → ℂ),
    IsOddFunction f →
      (Matrix.of fun (o : O) (i : I) =>
          hermitianFunction (hermitianDilation A) hD f (Sum.inl o) (Sum.inr i) :
        Matrix O I ℂ) = oddSingularTransform A f) ∧
  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (hD : (hermitianDilation A).IsHermitian)
      (f : ℝ → ℂ),
    IsEvenFunction f →
      (Matrix.of fun (i j : I) =>
          hermitianFunction (hermitianDilation A) hD f (Sum.inr i) (Sum.inr j) :
        Matrix I I ℂ) = rightSingularTransform A f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro O I _ _ _ _ A B f ω hA1 hB1 hω hodd hδ
    exact odd_singularTransform_bound_of_th20 hTh20 A B f ω hA1 hB1 hω hodd hδ
  · intro O I _ _ _ _ A B f ω hA1 hB1 hω heven hδ
    exact rightEven_singularTransform_bound_of_th20 hTh20 A B f ω hA1 hB1 hω heven hδ
  · intro O I _ _ _ _ A B f hδ
    exact singularTransforms_eq_of_norm_sub_zero A B f hδ
  · intro O I _ _ _ _ A hD f hodd
    have h := hermitianDilation_odd_fromBlocks A f hodd
    rw [h]
    ext o i
    simp [Matrix.fromBlocks]
  · intro O I _ _ _ _ A hD f heven
    have h := hermitianDilation_even_fromBlocks A f heven
    rw [h]
    ext i j
    simp [Matrix.fromBlocks]
end Qatlib.Concepts.QsvtCore.ApproxToolkit
