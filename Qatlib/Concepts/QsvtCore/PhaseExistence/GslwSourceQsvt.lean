/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.ColumnRowPartitioned
import Qatlib.Concepts.MatrixWeights.WeightsCore
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.NumberTheory.Real.Irrational
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvtDefs
import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvt
import Qatlib.Concepts.SketchSpectral.MatrixFunctions.HermitianRankLogStability
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma23PolynomialLevel
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23PolynomialLevel
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3CharacterizationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3CharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalQueryBounds
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Mathlib.Data.Real.Sign
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel

/-!
# Source QSVT phase synthesis and estimates

This module develops polynomial phase synthesis and stability estimates for quantum singular
value transformation in the setting of [GilyenSuLowWiebe2019]. It relates `CompletedPair` to
phase recursions and signal words, proves real-component characterizations, and handles constant
responses separately.

The later results give Chebyshev–Bessel approximation bounds, rounding estimates, and
existential encoding and resource statements. Explicit counterexamples record the failure of
several stronger formulations; the scope of each encoding statement is determined by its
quantified frames and program data.

## Main statements

* `clause40` and `clause41`: polynomial and interior robustness bounds.
* `completedPair_iff_eq3`, `clause74`, and `clause75`: phase and component characterizations.
* `clause44` and `clause45`: Dolph–Chebyshev and Chebyshev–Bessel approximations.
* `not_clause51`, `not_clause52`, `not_clause54`, and `not_clause83`: counterexamples to the
  displayed universal assertions.
* `clause85`: shifted Gibbs identities and existential resource witnesses.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LchsSimulation.LchsRep
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt

open Matrix Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
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
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

/-- Clamps a real number to the interval `[-1, 1]`. -/
noncomputable def clampUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- The clamped value lies in `[-1, 1]`. -/
theorem clampUnit_mem (x : ℝ) : clampUnit x ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ⟨le_max_left _ _, ?_⟩
  exact max_le (by norm_num) (min_le_left 1 x)

/-- Clamping fixes every point of `[-1, 1]`. -/
theorem clampUnit_eq {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : clampUnit x = x := by
  unfold clampUnit
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Clamping to `[-1, 1]` is monotone. -/
theorem clampUnit_mono : Monotone (clampUnit : ℝ → ℝ) := by
  intro x y hxy
  unfold clampUnit
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Clamping a value at most `-1` gives `-1`. -/
theorem clampUnit_of_le_neg_one {x : ℝ} (h : x ≤ -1) : clampUnit x = -1 := by
  unfold clampUnit
  rw [min_eq_right (h.trans (by norm_num)), max_eq_left h]

/-- Clamping a value at least `1` gives `1`. -/
theorem clampUnit_of_one_le {x : ℝ} (h : 1 ≤ x) : clampUnit x = 1 := by
  unfold clampUnit
  rw [min_eq_left h, max_eq_right (by norm_num)]

/-- For `x ≤ y`, clamping does not increase the increment from `x` to `y`. -/
theorem clampUnit_sub_le {x y : ℝ} (hxy : x ≤ y) : clampUnit y - clampUnit x ≤ y - x := by
  by_cases hx : x ≤ -1
  · rw [clampUnit_of_le_neg_one hx]
    by_cases hy : y ≤ -1
    · rw [clampUnit_of_le_neg_one hy]
      linarith
    · by_cases hy1 : 1 ≤ y
      · rw [clampUnit_of_one_le hy1]
        linarith
      · rw [clampUnit_eq ⟨by linarith, by linarith⟩]
        linarith
  · by_cases hy1 : 1 ≤ y
    · rw [clampUnit_of_one_le hy1]
      by_cases hx1 : 1 ≤ x
      · rw [clampUnit_of_one_le hx1]
        linarith
      · rw [clampUnit_eq ⟨by linarith, by linarith⟩]
        linarith
    · have hx' : clampUnit x = x := clampUnit_eq ⟨by linarith, by linarith⟩
      have hy' : clampUnit y = y := clampUnit_eq ⟨by linarith, by linarith⟩
      linarith

/-- For ordered real inputs, clamping does not increase their absolute difference. -/
theorem clampUnit_abs_sub_le_of_le {x y : ℝ} (hxy : x ≤ y) :
    |clampUnit x - clampUnit y| ≤ |x - y| := by
  have hsub : (0 : ℝ) ≤ y - x := by linarith
  rw [abs_sub_comm x y, abs_of_nonneg hsub]
  by_cases hx : x ≤ -1
  · rw [clampUnit_of_le_neg_one hx]
    by_cases hy : y ≤ -1
    · rw [clampUnit_of_le_neg_one hy, sub_self, abs_zero]
      linarith
    · by_cases hy1 : 1 ≤ y
      · have hneg : (-1:ℝ) - 1 = -2 := by norm_num
        have habs : |(-2:ℝ)| = 2 := by norm_num
        rw [clampUnit_of_one_le hy1, hneg, habs]
        linarith
      · rw [clampUnit_eq ⟨by linarith, by linarith⟩, abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
  · by_cases hy1 : 1 ≤ y
    · rw [clampUnit_of_one_le hy1]
      by_cases hx1 : 1 ≤ x
      · rw [clampUnit_of_one_le hx1, sub_self, abs_zero]
        linarith
      · rw [clampUnit_eq ⟨by linarith, by linarith⟩, abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
    · have hx' : clampUnit x = x := clampUnit_eq ⟨by linarith, by linarith⟩
      have hy' : clampUnit y = y := clampUnit_eq ⟨by linarith, by linarith⟩
      have hgoal : |clampUnit x - clampUnit y| ≤ y - x := by
        rw [hx', hy']
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      exact hgoal

/-- Clamping to `[-1, 1]` does not increase the distance between real inputs. -/
theorem clampUnit_abs_sub_le (x y : ℝ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · exact clampUnit_abs_sub_le_of_le h
  · rw [abs_sub_comm x y, abs_sub_comm (clampUnit x) (clampUnit y)]
    exact clampUnit_abs_sub_le_of_le h

/-- Extends the restriction of `f` to `[-1, 1]` by composing with `clampUnit`. -/
noncomputable def clampResponse (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (clampUnit x)

/-- The clamped response agrees with the original response on `[-1, 1]`. -/
theorem clampResponse_eq {f : ℝ → ℂ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    clampResponse f x = f x := by
  simp [clampResponse, clampUnit_eq hx]

/-- The clamped response satisfies the global difference bound given by the modulus of
continuity of `f` on `[-1, 1]`. -/
theorem clampResponse_dominates {f : ℝ → ℂ} {ω : ℝ → ℝ}
    (hω : ModulusOfContinuity f ω) (x y : ℝ) :
    ‖clampResponse f x - clampResponse f y‖ ≤ ω |x - y| := by
  have h := hω.dominates (clampUnit x) (clampUnit y) (clampUnit_mem x) (clampUnit_mem y)
  refine h.trans ?_
  exact hω.mono (by
    have := clampUnit_abs_sub_le x y
    simpa [abs_sub_comm] using! this)

/-- The grid anchor `δ * floor (x / δ)` used for linear interpolation. -/
noncomputable def sweepAnchor (δ x : ℝ) : ℝ := δ * (Int.floor (x / δ) : ℝ)

/-- Multiplication by a nonzero real number cancels division by that number. -/
theorem mul_div_self_cancel {δ : ℝ} (x : ℝ) (hδ : δ ≠ 0) : δ * (x / δ) = x :=
  (mul_comm _ _).trans (div_mul_cancel₀ x hδ)

/-- For positive grid spacing, the anchor of `x` is at most `x`. -/
theorem sweepAnchor_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : sweepAnchor δ x ≤ x := by
  unfold sweepAnchor
  have h := Int.floor_le (x / δ)
  exact (mul_le_mul_of_nonneg_left h (le_of_lt hδ)).trans_eq
    (mul_div_self_cancel x (ne_of_gt hδ))

/-- For positive grid spacing, `x` is strictly below the grid point following its anchor. -/
theorem lt_sweepAnchor_add {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : x < sweepAnchor δ x + δ := by
  unfold sweepAnchor
  have h := Int.lt_floor_add_one (x / δ)
  have h2 := mul_lt_mul_of_pos_left h hδ
  rw [mul_div_self_cancel x (ne_of_gt hδ), mul_add, mul_one] at h2
  exact h2

/-- The grid point following an anchor is itself fixed by the anchor map. -/
theorem sweepAnchor_succ {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    sweepAnchor δ (sweepAnchor δ x + δ) = sweepAnchor δ x + δ := by
  unfold sweepAnchor
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hdiv : (δ * (Int.floor (x / δ) : ℝ) + δ) / δ = (Int.floor (x / δ) : ℝ) + 1 := by
    rw [div_eq_iff hne]
    ring
  rw [hdiv, Int.floor_add_one, Int.floor_intCast]
  push_cast
  ring

/-- Linearly interpolates `f` between the grid anchor of `x` and the following grid point. -/
noncomputable def linearSweep (δ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  let a := sweepAnchor δ x
  f a + ((x - a) / δ) • (f (a + δ) - f a)

/-- Linear interpolation agrees with `f` at the grid point following the anchor. -/
theorem linearSweep_grid {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℂ) (x : ℝ) :
    linearSweep δ f (sweepAnchor δ x + δ) = f (sweepAnchor δ x + δ) := by
  simp only [linearSweep, sweepAnchor_succ hδ x]
  have h : ((sweepAnchor δ x + δ - (sweepAnchor δ x + δ)) / δ : ℝ) = 0 := by simp
  rw [h, zero_smul, add_zero]

/-- Within one grid cell, the difference of interpolated values is the displacement times the
cell slope. -/
theorem linearSweep_sub_same {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℂ) (x y : ℝ)
    (hcell : sweepAnchor δ x = sweepAnchor δ y) :
    linearSweep δ f y - linearSweep δ f x =
      ((y - x) / δ) • (f (sweepAnchor δ x + δ) - f (sweepAnchor δ x)) := by
  simp only [linearSweep, hcell.symm, add_sub_add_left_eq_sub, ← sub_smul]
  apply congrArg (fun t : ℝ => t • (f (sweepAnchor δ x + δ) - f (sweepAnchor δ x)))
  rw [div_sub_div_same]
  ring

/-- A monotone modulus bound for `f` bounds its interpolation error by `ω δ`. -/
theorem linearSweep_close {f : ℝ → ℂ} {ω : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ x y : ℝ, ‖f x - f y‖ ≤ ω |x - y|) (hmono : Monotone ω) (x : ℝ) :
    ‖f x - linearSweep δ f x‖ ≤ ω δ := by
  set a := sweepAnchor δ x with ha
  have ha1 : a ≤ x := by rw [ha]; exact sweepAnchor_le hδ x
  have ha2 : x < a + δ := by rw [ha]; exact lt_sweepAnchor_add hδ x
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hkey : f x - linearSweep δ f x =
      (1 - (x - a) / δ) • (f x - f a) + ((x - a) / δ) • (f x - f (a + δ)) := by
    simp only [linearSweep, ha]
    module
  have htx0 : (0 : ℝ) ≤ (x - a) / δ := div_nonneg (by linarith) (le_of_lt hδ)
  have htx1 : (x - a) / δ ≤ 1 := by
    rw [div_le_iff₀ hδ]; linarith
  have hma : |x - a| = (x - a) / δ * δ := by
    rw [abs_of_nonneg (by linarith)]; exact (div_mul_cancel₀ _ hne).symm
  have hmb : |x - (a + δ)| = (1 - (x - a) / δ) * δ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ a + δ - x)]
    have hcancel : (x - a) / δ * δ = x - a := div_mul_cancel₀ (x - a) hne
    have hcalc : (a + δ) - x = (1 - (x - a) / δ) * δ := by
      rw [sub_mul, one_mul, hcancel]
      ring
    exact hcalc
  rw [hkey]
  refine (norm_add_le _ _).trans ?_
  have hbound : ‖(1 - (x - a) / δ) • (f x - f a)‖ +
      ‖((x - a) / δ) • (f x - f (a + δ))‖ ≤
        (1 - (x - a) / δ) * ω δ + (x - a) / δ * ω δ := by
    apply add_le_add
    · rw [norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (x - a) / δ)]
      have hnorm : ‖f x - f a‖ ≤ ω δ := (hd x a).trans (hmono (by
        have : |x - a| ≤ δ := by rw [hma]; nlinarith
        exact this))
      exact mul_le_mul_of_nonneg_left hnorm (by linarith)
    · rw [norm_smul, Real.norm_of_nonneg htx0]
      have hnorm : ‖f x - f (a + δ)‖ ≤ ω δ := (hd x (a + δ)).trans (hmono (by
        have : |x - (a + δ)| ≤ δ := by rw [hmb]; nlinarith
        exact this))
      exact mul_le_mul_of_nonneg_left hnorm htx0
  refine hbound.trans ?_
  have : (1 - (x - a) / δ) * ω δ + (x - a) / δ * ω δ = ω δ := by ring
  exact le_of_eq this

/-- The change in `f` across a grid cell of width `δ` is bounded by `ω δ`. -/
theorem sweep_step_norm_le {f : ℝ → ℂ} {ω : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ x y : ℝ, ‖f x - f y‖ ≤ ω |x - y|) (u : ℝ) :
    ‖f (sweepAnchor δ u + δ) - f (sweepAnchor δ u)‖ ≤ ω δ := by
  have h := hd (sweepAnchor δ u + δ) (sweepAnchor δ u)
  have habs : |sweepAnchor δ u + δ - sweepAnchor δ u| = δ := by
    rw [add_sub_cancel_left, abs_of_nonneg (le_of_lt hδ)]
  rw [habs] at h
  exact h

/-- The difference between the right endpoint value and the interpolant is the remaining
interpolation weight times the endpoint difference. -/
theorem linearSweep_grid_sub {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℂ) (x : ℝ) :
    f (sweepAnchor δ x + δ) - linearSweep δ f x =
      (1 - (x - sweepAnchor δ x) / δ) •
        (f (sweepAnchor δ x + δ) - f (sweepAnchor δ x)) := by
  simp only [linearSweep]
  module

/-- The linear interpolant satisfies a global Lipschitz bound with constant `ω δ / δ`. -/
theorem linearSweep_lipschitz {f : ℝ → ℂ} {ω : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ x y : ℝ, ‖f x - f y‖ ≤ ω |x - y|) (hmono : Monotone ω) (x y : ℝ) :
    ‖linearSweep δ f x - linearSweep δ f y‖ ≤ (ω δ / δ) * |x - y| := by
  have hne : δ ≠ 0 := ne_of_gt hδ
  have hL : ∀ u v : ℝ, u ≤ v →
      ‖linearSweep δ f v - linearSweep δ f u‖ ≤ (ω δ / δ) * (v - u) := by
    intro u v huv
    have hkey : ∀ (k : ℕ) (u v : ℝ), u ≤ v →
        (Int.floor (v / δ) - Int.floor (u / δ)).toNat = k →
        ‖linearSweep δ f v - linearSweep δ f u‖ ≤ (ω δ / δ) * (v - u) := by
      intro k
      induction k with
      | zero =>
        intro u v huv hk
        have hcell : Int.floor (v / δ) = Int.floor (u / δ) := by
          have h0 : 0 ≤ (Int.floor (v / δ) - Int.floor (u / δ) : ℤ) :=
            sub_nonneg.mpr (Int.floor_mono (div_le_div_of_nonneg_right huv (le_of_lt hδ)))
          omega
        have hs : sweepAnchor δ u = sweepAnchor δ v := by
          unfold sweepAnchor
          rw [hcell]
        rw [linearSweep_sub_same hδ f u v hs, norm_smul]
        have hd' : ‖f (sweepAnchor δ u + δ) - f (sweepAnchor δ u)‖ ≤ ω δ :=
          sweep_step_norm_le hδ hd u
        have hle : ‖(v - u) / δ‖ * ‖f (sweepAnchor δ u + δ) - f (sweepAnchor δ u)‖ ≤
            (ω δ / δ) * (v - u) := by
          rw [Real.norm_of_nonneg (div_nonneg (by linarith) (le_of_lt hδ))]
          have hmul : (v - u) / δ * ω δ = (ω δ / δ) * (v - u) := by ring
          exact (mul_le_mul_of_nonneg_left hd' (div_nonneg (by linarith) (le_of_lt hδ))).trans
            (le_of_eq hmul)
        exact hle
      | succ k ih =>
        intro u v huv hk
        set u' := sweepAnchor δ u + δ with hu'
        have huu' : u < u' := by rw [hu']; exact lt_sweepAnchor_add hδ u
        have hfu' : linearSweep δ f u' = f (sweepAnchor δ u + δ) := by
          rw [hu']
          exact linearSweep_grid hδ f u
        have hfloor : Int.floor (u' / δ) = Int.floor (u / δ) + 1 := by
          have hdiv : u' / δ = (Int.floor (u / δ) : ℝ) + 1 := by
            have hsum : sweepAnchor δ u + δ = δ * ((Int.floor (u / δ) : ℝ) + 1) := by
              unfold sweepAnchor
              ring
            rw [hu', hsum, mul_div_cancel_left₀ _ hne]
          rw [hdiv, Int.floor_add_one, Int.floor_intCast]
        have hdiff : (Int.floor (v / δ) - Int.floor (u' / δ) : ℤ).toNat = k := by
          have h0 : 0 ≤ (Int.floor (v / δ) - Int.floor (u / δ) : ℤ) :=
            sub_nonneg.mpr (Int.floor_mono (div_le_div_of_nonneg_right huv (le_of_lt hδ)))
          omega
        have hu'le : u' ≤ v := by
          have h1 : Int.floor (u / δ) + 1 ≤ Int.floor (v / δ) := by
            have h0 : 0 ≤ (Int.floor (v / δ) - Int.floor (u / δ) : ℤ) :=
              sub_nonneg.mpr (Int.floor_mono (div_le_div_of_nonneg_right huv (le_of_lt hδ)))
            have hk' : (Int.floor (v / δ) - Int.floor (u / δ) : ℤ) = k + 1 := by omega
            omega
          have h2 : ((Int.floor (u / δ) : ℝ) + 1) ≤ v / δ := by
            have h2a : ((Int.floor (u / δ) : ℝ) + 1) ≤ (Int.floor (v / δ) : ℝ) := by
              exact_mod_cast h1
            have h2b : (Int.floor (v / δ) : ℝ) ≤ v / δ := Int.floor_le (v / δ)
            exact le_trans h2a h2b
          have hsum : sweepAnchor δ u + δ = δ * ((Int.floor (u / δ) : ℝ) + 1) := by
            unfold sweepAnchor
            ring
          rw [hu', hsum]
          have h2' : ((Int.floor (u / δ) : ℝ) + 1) * δ ≤ v := (le_div_iff₀ hδ).mp h2
          rw [mul_comm]
          exact h2'
        have h1 : ‖linearSweep δ f v - linearSweep δ f u'‖ ≤ (ω δ / δ) * (v - u') :=
          ih u' v hu'le hdiff
        have h2 : ‖linearSweep δ f u' - linearSweep δ f u‖ ≤ (ω δ / δ) * (u' - u) := by
          have hgr : linearSweep δ f u' - linearSweep δ f u =
              f (sweepAnchor δ u + δ) - linearSweep δ f u := by rw [hfu']
          rw [hgr, linearSweep_grid_sub hδ f u, norm_smul]
          have hd' : ‖f (sweepAnchor δ u + δ) - f (sweepAnchor δ u)‖ ≤ ω δ :=
            sweep_step_norm_le hδ hd u
          have hnonneg : 0 ≤ 1 - (u - sweepAnchor δ u) / δ := by
            have hlt : u - sweepAnchor δ u < δ := by
              have := lt_sweepAnchor_add hδ u
              linarith
            have hlt2 : (u - sweepAnchor δ u) / δ < 1 := by
              rw [div_lt_one hδ]
              exact hlt
            linarith
          rw [Real.norm_of_nonneg hnonneg]
          have hcoe2 : (1 - (u - sweepAnchor δ u) / δ) = (u' - u) / δ := by
            rw [hu']
            have hsum : sweepAnchor δ u + δ - u = δ - (u - sweepAnchor δ u) := by ring
            rw [hsum]
            have hdiv : (δ - (u - sweepAnchor δ u)) / δ = 1 - (u - sweepAnchor δ u) / δ := by
              rw [sub_div, div_self hne]
            rw [hdiv]
          rw [hcoe2]
          have hmul : (u' - u) / δ * ω δ = (ω δ / δ) * (u' - u) := by ring
          exact (mul_le_mul_of_nonneg_left hd' (div_nonneg (by linarith) (le_of_lt hδ))).trans
            (le_of_eq hmul)
        have htri : linearSweep δ f v - linearSweep δ f u =
            (linearSweep δ f v - linearSweep δ f u') + (linearSweep δ f u' - linearSweep δ f u) := by
          rw [sub_add_sub_cancel]
        rw [htri]
        refine (norm_add_le _ _).trans ?_
        have hsum : (ω δ / δ) * (v - u') + (ω δ / δ) * (u' - u) = (ω δ / δ) * (v - u) := by ring
        rw [← hsum]
        exact add_le_add h1 h2
    exact hkey (Int.floor (v / δ) - Int.floor (u / δ)).toNat u v huv rfl
  rcases le_total x y with h | h
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    exact hL x y h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact hL y x h

/-- Hermitian functional calculus carries pointwise subtraction to matrix subtraction. -/
theorem hermitianFunction_sub {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    hermitianFunction A hA f - hermitianFunction A hA g =
      hermitianFunction A hA (fun x => f x - g x) :=
  spectralDiagonal_sub _ _ _

/-- A nonnegative bound for the response at every eigenvalue bounds the norm of its Hermitian
functional calculus. -/
theorem hermitianFunction_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ i : Fin (Fintype.card I), ‖f (orderedHermitianValues hA i)‖ ≤ ε) :
    ‖hermitianFunction A hA f‖ ≤ ε :=
  spectralDiagonal_norm_le _ _ hε hf

/-- Every ordered eigenvalue of a Hermitian contraction lies in `[-1, 1]`. -/
theorem orderedHermitianValues_mem_of_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (h : ‖A‖ ≤ 1)
    (i : Fin (Fintype.card I)) :
    orderedHermitianValues hA i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hv := Matrix.l2_opNorm_mulVec A (orderedHermitianBasis hA i)
  change ‖A.toEuclideanLin (orderedHermitianBasis hA i)‖ ≤
    ‖A‖ * ‖orderedHermitianBasis hA i‖ at hv
  rw [orderedHermitianBasis_action, norm_smul, (orderedHermitianBasis hA).norm_eq_one,
    mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at hv
  exact abs_le.mp (hv.trans h)

/-- Clamping a response leaves its functional calculus on a Hermitian contraction unchanged. -/
theorem hermitianFunction_clampResponse {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) (h : ‖A‖ ≤ 1) :
    hermitianFunction A hA f = hermitianFunction A hA (clampResponse f) := by
  have heq : (fun i : Fin (Fintype.card I) => f (orderedHermitianValues hA i)) =
      (fun i : Fin (Fintype.card I) => clampResponse f (orderedHermitianValues hA i)) := by
    funext i
    simp [clampResponse, clampUnit_eq (orderedHermitianValues_mem_of_norm_le A hA h i)]
  unfold hermitianFunction
  rw [heq]

/-- There is a positive universal constant giving a modulus-of-continuity stability bound for
Hermitian contractions, with logarithmic dependence on their smaller rank. -/
theorem modulus_rankLog_stability :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
        (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (ω : ℝ → ℝ),
        ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω →
        ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
          (2 + c₀ * hermitianRankLogWeight (min A.rank B.rank)) * ω ‖A - B‖ := by
  obtain ⟨c₀, hc₀, hap⟩ := hermitianFunction_operator_min_rank_stability
  refine ⟨c₀, hc₀, ?_⟩
  intro I _ _ A B hA hB f ω hA1 hB1 hω
  have hω0 : ω 0 = 0 := hω.at_zero
  by_cases hδ : ‖A - B‖ = 0
  · have hAB : A - B = 0 := norm_eq_zero.mp hδ
    have hAB' : A = B := sub_eq_zero.mp hAB
    subst hAB'
    have hz : hermitianFunction A hA f - hermitianFunction A hB f = 0 :=
      sub_eq_zero.mpr rfl
    rw [hz, norm_zero, sub_self, norm_zero, hω0, mul_zero]
  · have hδpos : 0 < ‖A - B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hδ)
    have hδne : ‖A - B‖ ≠ 0 := ne_of_gt hδpos
    set F : ℝ → ℂ := clampResponse f
    set G : ℝ → ℂ := linearSweep ‖A - B‖ F
    have hdom : ∀ x y : ℝ, ‖F x - F y‖ ≤ ω |x - y| := fun x y => clampResponse_dominates hω x y
    have hωδ : 0 ≤ ω ‖A - B‖ := by
      have h1 : ω 0 ≤ ω ‖A - B‖ := hω.mono (le_of_lt hδpos)
      rw [hω0] at h1
      exact h1
    have hclose : ∀ x : ℝ, ‖F x - G x‖ ≤ ω ‖A - B‖ := fun x =>
      linearSweep_close hδpos hdom hω.mono x
    have hlip : ∀ x y : ℝ, ‖G x - G y‖ ≤ (ω ‖A - B‖ / ‖A - B‖) * |x - y| := fun x y =>
      linearSweep_lipschitz hδpos hdom hω.mono x y
    have hF : hermitianFunction A hA f = hermitianFunction A hA F :=
      hermitianFunction_clampResponse A hA f hA1
    have hFB : hermitianFunction B hB f = hermitianFunction B hB F :=
      hermitianFunction_clampResponse B hB f hB1
    have hpair : hermitianPairScalarLipschitz A hA B hB G (ω ‖A - B‖ / ‖A - B‖) := by
      intro x _ y _
      exact hlip x y
    have hstab := hap I A B hA hB G (ω ‖A - B‖ / ‖A - B‖)
      (div_nonneg hωδ (le_of_lt hδpos)) hpair
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
    have hωδδ : ω ‖A - B‖ / ‖A - B‖ * ‖A - B‖ = ω ‖A - B‖ := div_mul_cancel₀ (ω ‖A - B‖) hδne
    have hmid : c₀ * hermitianRankLogWeight (min A.rank B.rank) *
        (ω ‖A - B‖ / ‖A - B‖) * ‖A - B‖ =
          c₀ * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖ := by
      rw [mul_assoc, hωδδ]
    have hstab' : ‖hermitianFunction A hA G - hermitianFunction B hB G‖ ≤
        c₀ * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖ :=
      hstab.trans (le_of_eq hmid)
    have hboth : (‖hermitianFunction A hA F - hermitianFunction A hA G‖ +
          ‖hermitianFunction A hA G - hermitianFunction B hB G‖) +
        ‖hermitianFunction B hB G - hermitianFunction B hB F‖ ≤
          (ω ‖A - B‖ + c₀ * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖) +
            ω ‖A - B‖ :=
      add_le_add (add_le_add hAclose hstab') hBclose
    have hsum : (ω ‖A - B‖ + c₀ * hermitianRankLogWeight (min A.rank B.rank) * ω ‖A - B‖) +
        ω ‖A - B‖ =
          (2 + c₀ * hermitianRankLogWeight (min A.rank B.rank)) * ω ‖A - B‖ := by
      ring
    exact hboth.trans (le_of_eq hsum)

example : 4 * (Real.log (2 / (1:ℝ) + 1) + 1) ^ 2 < 144 * (1 + Real.log (1 + (20:ℝ))) := by
  have h3 : (2:ℝ) / 1 + 1 = 3 := by norm_num
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hL : 4 * (Real.log (2 / (1:ℝ) + 1) + 1) ^ 2 ≤ 36 := by
    rw [h3]
    have hx : Real.log 3 + 1 ≤ 3 := by linarith
    have hy : 0 ≤ Real.log 3 + 1 := by
      have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
      linarith
    have hsq : (Real.log 3 + 1) * (Real.log 3 + 1) ≤ 9 := by
      have h := mul_self_le_mul_self hy hx
      norm_num at h
      exact h
    nlinarith [hsq]
  have hR : (144:ℝ) ≤ 144 * (1 + Real.log (1 + (20:ℝ))) := by
    have h : (0:ℝ) ≤ Real.log (1 + (20:ℝ)) := by
      have h21 : (1:ℝ) + 20 = 21 := by norm_num
      rw [h21]
      exact Real.log_nonneg (by norm_num)
    nlinarith
  calc 4 * (Real.log (2 / (1:ℝ) + 1) + 1) ^ 2 ≤ 36 := hL
    _ < 144 := by norm_num
    _ ≤ 144 * (1 + Real.log (1 + (20:ℝ))) := hR

example : 4 * (Real.log (2 / (1:ℝ) + 1) + 1) ^ 2 < 1 + Real.log (1 + (2:ℝ)^60) := by
  have h3 : (2:ℝ) / 1 + 1 = 3 := by norm_num
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hL : 4 * (Real.log (2 / (1:ℝ) + 1) + 1) ^ 2 ≤ 36 := by
    rw [h3]
    have hx : Real.log 3 + 1 ≤ 3 := by linarith
    have hy : 0 ≤ Real.log 3 + 1 := by
      have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
      linarith
    have hsq : (Real.log 3 + 1) * (Real.log 3 + 1) ≤ 9 := by
      have h := mul_self_le_mul_self hy hx
      norm_num at h
      exact h
    nlinarith [hsq]
  have hpow : Real.log ((2:ℝ)^60) = 60 * Real.log 2 := Real.log_pow 2 60
  have hlt : Real.log ((2:ℝ)^60) < Real.log (1 + (2:ℝ)^60) :=
    Real.log_lt_log (pow_pos (by norm_num : (0:ℝ) < 2) 60)
      (lt_add_of_pos_left ((2:ℝ)^60) (by norm_num))
  have hgt := Real.log_two_gt_d9
  have hR : (42:ℝ) < 1 + Real.log (1 + (2:ℝ)^60) := by
    nlinarith [hpow, hlt, hgt]
  calc 4 * (Real.log (2 / (1:ℝ) + 1) + 1) ^ 2 ≤ 36 := hL
    _ < 42 := by norm_num
    _ < 1 + Real.log (1 + (2:ℝ)^60) := hR

/-- Equal Hermitian matrices have equal functional calculus values for the same response. -/
theorem hermitianFunction_eq_of_matrix_eq {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ)
    (hAB : A = B) : hermitianFunction A hA f = hermitianFunction B hB f := by
  subst hAB
  rfl

/-- Hermitian matrices whose difference has zero norm have equal functional calculus values. -/
theorem hermitianFunction_eq_of_norm_sub_zero {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ)
    (h : ‖A - B‖ = 0) : hermitianFunction A hA f = hermitianFunction B hB f :=
  hermitianFunction_eq_of_matrix_eq hA hB f (sub_eq_zero.mp (norm_eq_zero.mp h))

/-- Equal rectangular matrices have equal odd and right singular transforms. -/
theorem singularTransforms_eq_of_matrix_eq {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] {A B : Matrix O I ℂ} (f : ℝ → ℂ) (hAB : A = B) :
    oddSingularTransform A f = oddSingularTransform B f ∧
      rightSingularTransform A f = rightSingularTransform B f := by
  subst hAB
  exact ⟨rfl, rfl⟩

/-- Rectangular matrices whose difference has zero norm have equal odd and right singular
transforms. -/
theorem singularTransforms_eq_of_norm_sub_zero {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (f : ℝ → ℂ)
    (h : ‖A - B‖ = 0) :
    oddSingularTransform A f = oddSingularTransform B f ∧
      rightSingularTransform A f = rightSingularTransform B f :=
  singularTransforms_eq_of_matrix_eq f (sub_eq_zero.mp (norm_eq_zero.mp h))

/-- A matrix acting by `f` of each eigenvalue on the ordered Hermitian eigenbasis equals
`hermitianFunction`. -/
theorem hermitianFunction_eq_of_eigenAction {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) (T : Matrix I I ℂ)
    (h : ∀ j : Fin (Fintype.card I),
      T.toEuclideanLin (orderedHermitianBasis hA j)
        = f (orderedHermitianValues hA j) • orderedHermitianBasis hA j) :
    T = hermitianFunction A hA f :=
  eq_spectralDiagonal_of_action (orderedHermitianBasis hA) T
    (fun j => f (orderedHermitianValues hA j)) h

/-- A degree-zero polynomial satisfying `Cor8Admissible` is a unit constant polynomial. -/
theorem unitConstant_of_cor8_degreeZero {P : Polynomial ℂ}
    (hdeg : P.natDegree = 0) (hadm : Cor8Admissible P 0) :
    IsUnitConstantPolynomial P := by
  obtain ⟨c, rfl⟩ : ∃ c : ℂ, P = C c :=
    ⟨P.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
  have hle : Complex.normSq c ≤ 1 := by
    have h := hadm.interval 0 (by norm_num [Set.mem_Icc])
    simpa [Polynomial.eval_C] using! h
  have hge : 1 ≤ Complex.normSq c := by
    have h := hadm.exterior 2 (by norm_num [Set.mem_Ioo])
    simpa [Polynomial.eval_C] using! h
  exact ⟨c, rfl, le_antisymm hle hge⟩

/-- A polynomial of natural degree zero is constant, and its polynomial response is the
corresponding constant function. -/
theorem polynomialResponse_of_natDegree_eq_zero {P : Polynomial ℂ}
    (hdeg : P.natDegree = 0) :
    ∃ c : ℂ, P = C c ∧ polynomialResponse P = fun _ : ℝ => c := by
  obtain ⟨c, rfl⟩ : ∃ c : ℂ, P = C c :=
    ⟨P.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
  refine ⟨c, rfl, ?_⟩
  funext x
  simp [polynomialResponse]

/-- The right singular transform of a degree-zero polynomial response is independent of the
input matrix. -/
theorem rightSingularTransform_polyResponse_eq_of_degreeZero
    {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (P : Polynomial ℂ) (hdeg : P.natDegree = 0) :
    rightSingularTransform A (polynomialResponse P) =
      rightSingularTransform B (polynomialResponse P) := by
  obtain ⟨c, _, hfun⟩ := polynomialResponse_of_natDegree_eq_zero hdeg
  rw [hfun, rightSingularTransform_const, rightSingularTransform_const]

/-- The source phase response of the empty phase list is the constant polynomial `1`. -/
theorem sourcePhaseResponse_nil :
    sourcePhaseResponse [] = (1 : Polynomial ℂ) := by
  rfl

/-- The interior response of the angle phase table equals the polynomial response of
`sourcePhaseResponse`. -/
theorem interiorResponse_sourcePhaseResponse (Φ : List ℝ) :
    interiorResponse 1 (anglePhaseTable Φ) =
      polynomialResponse (sourcePhaseResponse Φ) := by
  funext x
  simp [interiorResponse, anglePhaseTable, sourcePhaseResponse, polynomialResponse]

/-- Every entry of an angle phase table is a unit complex phase. -/
theorem anglePhaseTable_isPhase (Φ : List ℝ) :
    ∀ z ∈ anglePhaseTable Φ, IsPhase z := by
  intro z hz
  obtain ⟨θ, _, rfl⟩ := List.mem_map.mp (by simpa [anglePhaseTable] using! hz)
  exact anglePhase_isPhase θ

/-- Converting angles to a phase table preserves list length. -/
theorem anglePhaseTable_length (Φ : List ℝ) :
    (anglePhaseTable Φ).length = Φ.length := by
  simp [anglePhaseTable]

/-- For a polynomial satisfying `Cor8Admissible`, establishes phase realization in positive
degree and the parity-dependent robustness bound on singular transforms of contractions. The
degree-zero case is recorded separately; see [Gilyén et al., Lemma
22][GilyenSuLowWiebe2019]. -/
theorem clause40 :
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (P : Polynomial ℂ) (n : ℕ),
    P.natDegree = n →
    Cor8Admissible P n →
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →

    (n = 0 →
      IsUnitConstantPolynomial P ∧
      sourcePhaseResponse [] = (1 : Polynomial ℂ) ∧
      ‖rightSingularTransform A (polynomialResponse P) -
        rightSingularTransform B (polynomialResponse P)‖ ≤
        polynomialRobustnessBound 0 ‖A - B‖) ∧

    (0 < n → ∃ Φ : List ℝ, Φ.length = n ∧ sourcePhaseResponse Φ = P) ∧

    (0 < n → n % 2 = 1 →
      ‖oddSingularTransform A (polynomialResponse P) -
        oddSingularTransform B (polynomialResponse P)‖ ≤
        polynomialRobustnessBound n ‖A - B‖) ∧

    (0 < n → n % 2 = 0 →
      ‖rightSingularTransform A (polynomialResponse P) -
        rightSingularTransform B (polynomialResponse P)‖ ≤
        polynomialRobustnessBound n ‖A - B‖) := by
  intro I O _ _ _ _ A B P n hdeg hadm hA hB
  have hphase : 0 < n → ∃ Φ : List ℝ, Φ.length = n ∧ sourcePhaseResponse Φ = P := by
    intro hnpos
    obtain ⟨Φ, hΦlen, hΦeq, _⟩ := corollary8ComplexPhaseExistence P n hnpos hdeg
      hadm.parity hadm.interval hadm.exterior hadm.imaginaryAxis
    exact ⟨Φ, hΦlen, hΦeq⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hn0
    subst hn0
    refine ⟨unitConstant_of_cor8_degreeZero hdeg hadm, sourcePhaseResponse_nil, ?_⟩
    have hz : polynomialRobustnessBound 0 ‖A - B‖ = 0 := by
      simp [polynomialRobustnessBound]
    rw [hz, rightSingularTransform_polyResponse_eq_of_degreeZero A B P hdeg]
    simp
  · exact hphase
  · intro hnpos hodd
    obtain ⟨Φ, hΦlen, hΦeq⟩ := hphase hnpos
    have hlen : (anglePhaseTable Φ).length = n := by
      rw [anglePhaseTable_length, hΦlen]
    have hresp : interiorResponse 1 (anglePhaseTable Φ) = polynomialResponse P := by
      rw [interiorResponse_sourcePhaseResponse, hΦeq]
    have hstability := complex_boundary_singular_response_stability I O A B 1
      (anglePhaseTable Φ) (by simp [IsPhase]) (anglePhaseTable_isPhase Φ) hA hB
    have hparity : (anglePhaseTable Φ).length % 2 = 1 := by
      rw [hlen]; exact hodd
    have hbound := hstability.1 hparity
    rw [hlen] at hbound
    rw [← hresp]
    simpa [polynomialRobustnessBound] using! hbound
  · intro hnpos heven
    obtain ⟨Φ, hΦlen, hΦeq⟩ := hphase hnpos
    have hlen : (anglePhaseTable Φ).length = n := by
      rw [anglePhaseTable_length, hΦlen]
    have hresp : interiorResponse 1 (anglePhaseTable Φ) = polynomialResponse P := by
      rw [interiorResponse_sourcePhaseResponse, hΦeq]
    have hstability := complex_boundary_singular_response_stability I O A B 1
      (anglePhaseTable Φ) (by simp [IsPhase]) (anglePhaseTable_isPhase Φ) hA hB
    have hparity : (anglePhaseTable Φ).length % 2 = 0 := by
      rw [hlen]; exact heven
    have hbound := hstability.2 hparity
    rw [hlen] at hbound
    rw [← hresp]
    simpa [polynomialRobustnessBound] using! hbound

/-- Collects the interior robustness bounds under the midpoint norm condition, the
constant-response and boundary cases, and `Lemma23PolynomialLevel`. See [Gilyén et al.,
Lemma 23][GilyenSuLowWiebe2019]. -/
theorem clause41 :

  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (P : Polynomial ℂ),
    P.natDegree = 0 →
    Cor8Admissible P 0 →
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
    IsUnitConstantPolynomial P ∧
      rightSingularTransform A (polynomialResponse P) =
        rightSingularTransform B (polynomialResponse P)) ∧

  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (P : Polynomial ℂ) (n : ℕ),
    P.natDegree = n →
    Cor8Admissible P n →
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
    ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
    (n % 2 = 1 →
      ‖oddSingularTransform A (polynomialResponse P) -
        oddSingularTransform B (polynomialResponse P)‖ ≤
        interiorRobustnessRate n ‖(2 : ℂ)⁻¹ • (A + B)‖ ‖A - B‖) ∧
    (n % 2 = 0 →
      ‖rightSingularTransform A (polynomialResponse P) -
        rightSingularTransform B (polynomialResponse P)‖ ≤
        interiorRobustnessRate n ‖(2 : ℂ)⁻¹ • (A + B)‖ ‖A - B‖)) ∧

  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (P : Polynomial ℂ),
    P.natDegree = 0 →
    Cor8Admissible P 0 →
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
    ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
    interiorRobustnessRate 0 ‖(2 : ℂ)⁻¹ • (A + B)‖ ‖A - B‖ = 0 ∧
      rightSingularTransform A (polynomialResponse P) =
        rightSingularTransform B (polynomialResponse P)) ∧

  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
    ‖(2 : ℂ)⁻¹ • (A + B)‖ = 1 →
    ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
    A = B) ∧

  Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma23PolynomialLevel := by
  refine ⟨?_, ?_, ?_, ?_, lemma23PolynomialLevel⟩
  · intro I O _ _ _ _ A B P hdeg hadm hA hB
    exact ⟨unitConstant_of_cor8_degreeZero hdeg hadm,
      rightSingularTransform_polyResponse_eq_of_degreeZero A B P hdeg⟩
  · intro I O _ _ _ _ A B P n hdeg hadm hA hB hbudget
    by_cases hn : n = 0
    · subst hn
      have hrate0 : interiorRobustnessRate 0 ‖(2 : ℂ)⁻¹ • (A + B)‖ ‖A - B‖ = 0 := by
        simp [interiorRobustnessRate]
      constructor
      · intro hodd
        simp at hodd
      · intro heven
        rw [hrate0, rightSingularTransform_polyResponse_eq_of_degreeZero A B P hdeg]
        simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have h := lemma23PolynomialLevel I O A B P n hnpos hdeg hadm.parity hadm.interval
        hadm.exterior hadm.imaginaryAxis hA hB hbudget
      exact ⟨fun hodd => h.1 hodd, fun heven => h.2 heven⟩
  · intro I O _ _ _ _ A B P hdeg hadm hA hB hbudget
    have hrate0 : interiorRobustnessRate 0 ‖(2 : ℂ)⁻¹ • (A + B)‖ ‖A - B‖ = 0 := by
      simp [interiorRobustnessRate]
    exact ⟨hrate0, rightSingularTransform_polyResponse_eq_of_degreeZero A B P hdeg⟩
  · intro I O _ _ _ _ A B hA hB hm hbudget
    have hsum : ‖A - B‖ + (1 : ℝ) ≤ 1 := by
      have h1 : (1 : ℝ) ^ 2 = 1 := by ring
      rw [hm, h1] at hbudget
      exact hbudget
    have hnorm : ‖A - B‖ = 0 :=
      le_antisymm (by linarith) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

open Matrix Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
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
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

/-- A polynomial with response parity `n` evaluates at `-x` as `(-1)^n` times its value at `x`. -/
theorem eval_neg_of_hasResponseParity {n : ℕ} {P : Polynomial ℂ}
    (h : HasResponseParity n P) (x : ℂ) :
    P.eval (-x) = ((-1 : ℂ) ^ n) * P.eval x := by
  have hh : (P.comp (-X)).eval x = (C ((-1 : ℂ) ^ n) * P).eval x := congrArg _ h
  rwa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at hh

/-- The constant polynomials associated with a unit phase and its conjugate multiply to `1`. -/
theorem C_phase_mul {c : ℂ} (hc : IsPhase c) :
    (C (star c) * C c : Polynomial ℂ) = 1 := by
  rw [← C_mul, hc, C_1]

/-- A forward `eq3PairStep` with a unit phase preserves the response pair norm polynomial. -/
theorem responsePairNorm_eq3PairStep {w : ℂ} (hw : IsPhase w) (P Q : Polynomial ℂ) :
    responsePairNorm (C w * (X * P - (1 - X ^ 2) * Q)) (C (star w) * (P + X * Q))
      = responsePairNorm P Q := by
  have hfac :
      responsePairNorm (C w * (X * P - (1 - X ^ 2) * Q)) (C (star w) * (P + X * Q))
        = (C (star w) * C w) *
            responsePairNorm (X * P - (1 - X ^ 2) * Q) (P + X * Q) := by
    simp only [responsePairNorm, conjugatePolynomial_add, conjugatePolynomial_sub,
      conjugatePolynomial_mul, conjugatePolynomial_pow, conjugatePolynomial_one,
      conjugatePolynomial_X, conjugatePolynomial_C, star_star]
    ring
  have hsig :
      responsePairNorm (X * P - (1 - X ^ 2) * Q) (P + X * Q) = responsePairNorm P Q := by
    simp only [responsePairNorm, conjugatePolynomial_add, conjugatePolynomial_sub,
      conjugatePolynomial_mul, conjugatePolynomial_pow, conjugatePolynomial_one,
      conjugatePolynomial_X]
    ring
  rw [hfac, hsig, C_phase_mul hw, one_mul]

/-- Negating the second response polynomial preserves the response pair norm polynomial. -/
theorem responsePairNorm_neg_right (P Q : Polynomial ℂ) :
    responsePairNorm P (-Q) = responsePairNorm P Q := by
  have hconj : conjugatePolynomial (-Q) = -conjugatePolynomial Q := by
    have h := conjugatePolynomial_sub (0 : Polynomial ℂ) Q
    simpa using! h
  simp only [responsePairNorm, hconj]
  ring

/-- Negating the second polynomial preserves `CompletedPair`. -/
theorem completedPair_neg_right {k : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair k P Q) : CompletedPair k P (-Q) := by
  refine ⟨h.degreeP, ?_, h.parityP, ?_, ?_⟩
  · simpa using! h.degreeQ
  · have hp : Q.comp (-X) = C ((-1 : ℂ) ^ (k + 1)) * Q := h.parityQ
    change (-Q).comp (-X) = C ((-1 : ℂ) ^ (k + 1)) * (-Q)
    rw [neg_comp, hp, pow_succ]
    ring
  · rw [responsePairNorm_neg_right, h.normalization]

/-- Multiplying the first polynomial by a unit phase preserves `CompletedPair`. -/
theorem completedPair_mul_left {k : ℕ} {P Q : Polynomial ℂ} {c : ℂ}
    (h : CompletedPair k P Q) (hc : IsPhase c) : CompletedPair k (C c * P) Q := by
  refine ⟨?_, h.degreeQ, ?_, h.parityQ, ?_⟩
  · have h1 : (C c).degree ≤ 0 := Polynomial.degree_C_le
    have h2 : (C c).degree + P.degree ≤ (0 : WithBot ℕ) + ((k : ℕ) : WithBot ℕ) :=
      add_le_add h1 h.degreeP
    rw [zero_add] at h2
    exact le_trans (Polynomial.degree_mul_le (C c) P) h2
  · have hp : P.comp (-X) = C ((-1 : ℂ) ^ k) * P := h.parityP
    change (C c * P).comp (-X) = C ((-1 : ℂ) ^ k) * (C c * P)
    rw [mul_comp, C_comp, hp]
    ring
  · have hnorm : responsePairNorm (C c * P) Q = responsePairNorm P Q := by
      simp only [responsePairNorm, conjugatePolynomial_mul, conjugatePolynomial_C]
      have h1 : (C c * P) * (C (star c) * conjugatePolynomial P)
          = (C (star c) * C c) * (P * conjugatePolynomial P) := by ring
      rw [h1, C_phase_mul hc, one_mul]
    rw [hnorm, h.normalization]

/-- Multiplying the second polynomial by a unit phase preserves `CompletedPair`. -/
theorem completedPair_mul_right {k : ℕ} {P Q : Polynomial ℂ} {c : ℂ}
    (h : CompletedPair k P Q) (hc : IsPhase c) : CompletedPair k P (C c * Q) := by
  refine ⟨h.degreeP, ?_, h.parityP, ?_, ?_⟩
  · have h1 : (C c).degree ≤ 0 := Polynomial.degree_C_le
    have h2 : (C c).degree + Q.degree ≤ Q.degree := by
      have h2a : (C c).degree + Q.degree ≤ (0 : WithBot ℕ) + Q.degree :=
        add_le_add h1 (le_refl Q.degree)
      rw [zero_add] at h2a
      exact h2a
    exact lt_of_le_of_lt (Polynomial.degree_mul_le (C c) Q)
      (lt_of_le_of_lt h2 h.degreeQ)
  · have hq : Q.comp (-X) = C ((-1 : ℂ) ^ (k + 1)) * Q := h.parityQ
    change (C c * Q).comp (-X) = C ((-1 : ℂ) ^ (k + 1)) * (C c * Q)
    rw [mul_comp, C_comp, hq]
    ring
  · have hnorm : responsePairNorm P (C c * Q) = responsePairNorm P Q := by
      simp only [responsePairNorm, conjugatePolynomial_mul, conjugatePolynomial_C]
      have h1 : (1 - X ^ 2) * (C c * Q) * (C (star c) * conjugatePolynomial Q)
          = (C (star c) * C c) * ((1 - X ^ 2) * (Q * conjugatePolynomial Q)) := by ring
      rw [h1, C_phase_mul hc]
      ring
    rw [hnorm, h.normalization]

/-- If the degree of `Q` is strictly below `k`, adding two to it gives a degree bound of `k +
1`. -/
theorem degree_add_two_le_of_degree_lt {k : ℕ} {Q : Polynomial ℂ}
    (hQ : Q.degree < ((k : ℕ) : WithBot ℕ)) :
    Q.degree + 2 ≤ (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne Q 0 with rfl | hne
  · simp
  · have hq := Polynomial.degree_eq_natDegree hne
    rw [hq] at hQ
    have hlt : Q.natDegree < k := by exact_mod_cast hQ
    rw [hq]
    exact_mod_cast (show Q.natDegree + 2 ≤ k + 1 by omega)

/-- The first polynomial produced by `eq3PairStep` has degree at most `k + 1` under the input
degree bounds. -/
theorem eq3PairStep_degreeP {k : ℕ} {P Q : Polynomial ℂ}
    (hP : P.degree ≤ ((k : ℕ) : WithBot ℕ)) (hQ : Q.degree < ((k : ℕ) : WithBot ℕ)) {w : ℂ} :
    (C w * (X * P - (1 - X ^ 2) * Q)).degree ≤ (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
  have h1 : (C w * (X * P - (1 - X ^ 2) * Q)).degree
      ≤ (C w).degree + (X * P - (1 - X ^ 2) * Q).degree :=
    Polynomial.degree_mul_le (C w) _
  have h2 : (X * P - (1 - X ^ 2) * Q).degree
      ≤ (X * P).degree ⊔ ((1 - X ^ 2) * Q).degree :=
    Polynomial.degree_sub_le _ _
  have h3 : (X * P).degree ≤ (X : Polynomial ℂ).degree + P.degree :=
    Polynomial.degree_mul_le X P
  have h4 : ((1 - X ^ 2) * Q).degree ≤ (1 - X ^ 2 : Polynomial ℂ).degree + Q.degree :=
    Polynomial.degree_mul_le _ Q
  have h5 : (C w).degree ≤ 0 := Polynomial.degree_C_le
  have h6 : (X : Polynomial ℂ).degree = 1 := Polynomial.degree_X
  have h7 : (1 - X ^ 2 : Polynomial ℂ).degree ≤ 2 := by
    apply Polynomial.degree_le_of_natDegree_le
    have h7a : (1 - X ^ 2 : Polynomial ℂ).natDegree ≤ (2 : ℕ) := by
      apply le_trans (Polynomial.natDegree_sub_le 1 (X ^ 2))
      have h7b : (X ^ 2 : Polynomial ℂ).natDegree = 2 := by simp [pow_two]
      rw [Polynomial.natDegree_one, h7b]
      norm_num
    omega
  have h8 : ((1 : WithBot ℕ) + P.degree) ≤ (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
    have h8a : ((1 : WithBot ℕ) + P.degree) ≤ ((1 : WithBot ℕ) + ((k : ℕ) : WithBot ℕ)) :=
      add_le_add (le_refl 1) hP
    have h8b : (((k + 1 : ℕ) : ℕ) : WithBot ℕ)
        = ((1 : WithBot ℕ) + ((k : ℕ) : WithBot ℕ)) := by
      push_cast
      exact add_comm _ _
    rw [h8b]
    exact h8a
  have h9 : (((2 : WithBot ℕ) + Q.degree)) ≤ (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
    have h9a := degree_add_two_le_of_degree_lt hQ
    rw [add_comm] at h9a
    exact h9a
  have h10 : (X * P).degree ≤ (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
    apply le_trans h3
    rw [h6]
    exact h8
  have h11 : ((1 - X ^ 2) * Q).degree ≤ (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
    apply le_trans h4
    apply le_trans (add_le_add h7 (le_refl Q.degree))
    exact h9
  apply le_trans h1
  apply le_trans (add_le_add h5 (le_refl _))
  rw [zero_add]
  apply le_trans h2
  exact sup_le h10 h11

/-- The second polynomial produced by `eq3PairStep` has degree strictly below `k + 1` under the
input degree bounds. -/
theorem eq3PairStep_degreeQ {k : ℕ} {P Q : Polynomial ℂ}
    (hP : P.degree ≤ ((k : ℕ) : WithBot ℕ)) (hQ : Q.degree < ((k : ℕ) : WithBot ℕ)) {w : ℂ} :
    (C (star w) * (P + X * Q)).degree < (((k + 1 : ℕ) : ℕ) : WithBot ℕ) := by
  by_cases hz : C (star w) * (P + X * Q) = 0
  · rw [hz]
    simp
  · rw [Polynomial.degree_eq_natDegree hz]
    have hPn : P.natDegree ≤ k := natDegree_le_of_degree_le hP
    have hQn : Q.natDegree ≤ k - 1 := by
      rcases eq_or_ne Q 0 with rfl | hne
      · simp only [Polynomial.natDegree_zero]
        exact Nat.zero_le _
      · have hq := Polynomial.degree_eq_natDegree hne
        rw [hq] at hQ
        have hlt : Q.natDegree < k := by exact_mod_cast hQ
        omega
    have h1 : (C (star w) * (P + X * Q)).natDegree ≤ (P + X * Q).natDegree := by
      have h1a : (C (star w) * (P + X * Q)).natDegree
          ≤ (C (star w)).natDegree + (P + X * Q).natDegree := Polynomial.natDegree_mul_le
      have : (C (star w)).natDegree = 0 := Polynomial.natDegree_C _
      omega
    have h2 : (P + X * Q).natDegree ≤ max P.natDegree (X * Q).natDegree :=
      Polynomial.natDegree_add_le P (X * Q)
    have h3 : (X * Q).natDegree ≤ 1 + Q.natDegree := by
      have h3a : (X * Q).natDegree ≤ X.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
      have : (X : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X
      omega
    have h5 : max P.natDegree (X * Q).natDegree ≤ k := by
      refine max_le hPn ?_
      rcases eq_or_ne Q 0 with rfl | hne
      · simp
      · have hq := Polynomial.degree_eq_natDegree hne
        rw [hq] at hQ
        have hlt : Q.natDegree < k := by exact_mod_cast hQ
        exact le_trans h3 (by omega : (1 + Q.natDegree) ≤ k)
    have h4 : (C (star w) * (P + X * Q)).natDegree < k + 1 := by
      have := le_trans h1 (le_trans h2 h5)
      omega
    exact_mod_cast h4

/-- The first polynomial produced by `eq3PairStep` has response parity `k + 1` under the input
parity conditions. -/
theorem eq3PairStep_parityP {k : ℕ} {P Q : Polynomial ℂ}
    (hP : HasResponseParity k P) (hQ : HasResponseParity (k + 1) Q) {w : ℂ} :
    HasResponseParity (k + 1) (C w * (X * P - (1 - X ^ 2) * Q)) := by
  have hpow : ((-1 : ℂ) ^ (k + 1)) = -((-1 : ℂ) ^ k) := by
    rw [pow_succ]
    ring
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C, eval_sub, eval_pow, eval_one]
  rw [eval_neg_of_hasResponseParity hP x, eval_neg_of_hasResponseParity hQ x, hpow]
  ring

/-- The second polynomial produced by `eq3PairStep` has response parity `k + 2` under the input
parity conditions. -/
theorem eq3PairStep_parityQ {k : ℕ} {P Q : Polynomial ℂ}
    (hP : HasResponseParity k P) (hQ : HasResponseParity (k + 1) Q) {w : ℂ} :
    HasResponseParity (k + 2) (C (star w) * (P + X * Q)) := by
  have hpow : ((-1 : ℂ) ^ (k + 2)) = ((-1 : ℂ) ^ k) := by
    rw [pow_succ, pow_succ]
    ring
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C, eval_add]
  rw [eval_neg_of_hasResponseParity hP x, eval_neg_of_hasResponseParity hQ x]
  have hpow2 : ((-1 : ℂ) ^ (k + 1)) = -((-1 : ℂ) ^ k) := by
    rw [pow_succ]
    ring
  rw [hpow2, hpow]
  ring

/-- A forward step with a unit phase carries a completed pair of order `k` to one of order `k +
1`. -/
theorem completedPair_eq3PairStep {k : ℕ} {P Q : Polynomial ℂ} {w : ℂ}
    (h : CompletedPair k P Q) (hw : IsPhase w) :
    CompletedPair (k + 1) (eq3PairStep w (P, Q)).1 (eq3PairStep w (P, Q)).2 := by
  show CompletedPair (k + 1)
    (C w * (X * P - (1 - X ^ 2) * Q)) (C (star w) * (P + X * Q))
  refine ⟨eq3PairStep_degreeP h.degreeP h.degreeQ,
    eq3PairStep_degreeQ h.degreeP h.degreeQ,
    eq3PairStep_parityP h.parityP h.parityQ,
    eq3PairStep_parityQ h.parityP h.parityQ, ?_⟩
  rw [responsePairNorm_eq3PairStep hw, h.normalization]

/-- A unit constant polynomial paired with zero is a completed pair of order zero. -/
theorem completedPair_eq3Pair_nil {z0 : ℂ} (hz0 : IsPhase z0) :
    CompletedPair 0 (C z0) (0 : Polynomial ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Polynomial.degree_C_le
  · simp
  · change (C z0).comp (-X) = C ((-1 : ℂ) ^ 0) * (C z0)
    simp
  · change (0 : Polynomial ℂ).comp (-X) = C ((-1 : ℂ) ^ 1) * 0
    simp
  · simp only [responsePairNorm, conjugatePolynomial_C, conjugatePolynomial_zero,
      mul_zero, add_zero]
    have hph : z0 * star z0 = 1 := by
      rw [mul_comm]
      exact hz0
    rw [← C_mul, hph, C_1]

/-- Iterating `eq3Pair` from a unit initial phase with unit step phases yields a completed pair
of order equal to the step list length. -/
theorem completedPair_of_eq3Pair {z0 : ℂ} (hz0 : IsPhase z0) :
    ∀ zs : List ℂ, (∀ z ∈ zs, IsPhase z) →
      CompletedPair zs.length (eq3Pair z0 zs).1 (eq3Pair z0 zs).2 := by
  intro zs
  induction zs using List.reverseRecOn with
  | nil =>
    intro _
    simpa using! completedPair_eq3Pair_nil hz0
  | append_singleton zs z ih =>
    intro hzs
    have hz : IsPhase z := hzs z (by simp)
    have hall : ∀ w ∈ zs, IsPhase w := fun w hw => hzs w (List.mem_append_left _ hw)
    have ih' := ih hall
    rw [eq3Pair_snoc, List.length_append, List.length_cons, List.length_nil]
    exact completedPair_eq3PairStep ih' hz

/-- A completed pair of order zero consists of a unit constant first polynomial and a zero
second polynomial. -/
theorem completedPair_zero {P Q : Polynomial ℂ} (h : CompletedPair 0 P Q) :
    ∃ c : ℂ, P = C c ∧ Q = 0 ∧ IsPhase c := by
  have hQ : Q = 0 := by
    by_contra hne
    have hdeg := Polynomial.degree_eq_natDegree hne
    have hlt : Q.degree < ((0 : ℕ) : WithBot ℕ) := h.degreeQ
    have : (Q.natDegree : WithBot ℕ) < 0 := by
      rw [← hdeg]; exact hlt
    simp at this
  subst Q
  obtain ⟨c, hc⟩ : ∃ c : ℂ, P = C c :=
    ⟨P.coeff 0, eq_C_of_degree_le_zero h.degreeP⟩
  subst P
  refine ⟨c, rfl, rfl, ?_⟩
  have hn := h.normalization
  simp only [responsePairNorm, conjugatePolynomial_C, conjugatePolynomial_zero, mul_zero,
    add_zero] at hn
  have hcc : C (c * star c) = (1 : Polynomial ℂ) := by
    rwa [← C_mul] at hn
  have h1 : c * star c = 1 := by
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hcc
    simpa using! this
  rw [mul_comm] at h1
  exact h1

/-- An order-`k + 1` completed pair possesses a unit phase whose inverse responses form an
order-`k` completed pair and reconstruct the original pair after the stated sign change. -/
theorem eq3PairStep_inverse_response {k : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair (k + 1) P Q) :
    ∃ z, IsPhase z ∧
      CompletedPair k (inverseResponseP z P Q) (inverseResponseQ z P Q) ∧
      eq3PairStep z (inverseResponseP z P Q, -inverseResponseQ z P Q) = (P, Q) := by
  obtain ⟨hz, hinv⟩ := h.inverse_step
  refine ⟨alignPhase (P.coeff (k + 1)) (Q.coeff k), hz, hinv, ?_⟩
  set z := alignPhase (P.coeff (k + 1)) (Q.coeff k)
  obtain ⟨h1, h2⟩ := inverseResponse_reconstruct hz P Q
  show (C z * (X * inverseResponseP z P Q - (1 - X ^ 2) * (-inverseResponseQ z P Q)),
      C (star z) * (inverseResponseP z P Q + X * (-inverseResponseQ z P Q))) = (P, Q)
  have e1 : X * inverseResponseP z P Q - (1 - X ^ 2) * (-inverseResponseQ z P Q)
      = X * inverseResponseP z P Q + (1 - X ^ 2) * inverseResponseQ z P Q := by ring
  have e2 : inverseResponseP z P Q + X * (-inverseResponseQ z P Q)
      = inverseResponseP z P Q - X * inverseResponseQ z P Q := by ring
  rw [e1, e2]
  exact Prod.ext h1 h2

/-- Every completed pair of order `k` is realized by `eq3Pair` with a unit initial phase and
exactly `k` unit step phases. -/
theorem eq3Pair_of_completedPair : ∀ (k : ℕ) (P Q : Polynomial ℂ), CompletedPair k P Q →
    ∃ z0 zs, IsPhase z0 ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = k ∧ eq3Pair z0 zs = (P, Q) := by
  intro k
  induction k with
  | zero =>
    intro P Q h
    obtain ⟨c, hP, hQ, hc⟩ := completedPair_zero h
    subst P
    subst Q
    exact ⟨c, [], hc, by simp, rfl, rfl⟩
  | succ k ih =>
    intro P Q h
    obtain ⟨z, hz, hinv, hstep⟩ := eq3PairStep_inverse_response h
    have hPQ : CompletedPair k (inverseResponseP z P Q) (-inverseResponseQ z P Q) :=
      completedPair_neg_right hinv
    obtain ⟨z0, zs, hz0, hzs, hlen, heq⟩ := ih _ _ hPQ
    refine ⟨z0, zs ++ [z], hz0, ?_, ?_, ?_⟩
    · intro w hw
      rw [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hzs w hw
      · exact hz
    · simp [hlen]
    · rw [eq3Pair_snoc, heq]
      exact hstep

/-- A pair is completed of order `k` exactly when it has an `eq3Pair` realization with a unit
initial phase and `k` unit step phases. -/
theorem completedPair_iff_eq3 {k : ℕ} {P Q : Polynomial ℂ} :
    CompletedPair k P Q ↔
      ∃ z0 zs, IsPhase z0 ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = k ∧
        eq3Pair z0 zs = (P, Q) := by
  constructor
  · intro h
    exact eq3Pair_of_completedPair k P Q h
  · rintro ⟨z0, zs, hz0, hzs, hlen, heq⟩
    have hcp := completedPair_of_eq3Pair hz0 zs hzs
    have h1 : (eq3Pair z0 zs).1 = P := by rw [heq]
    have h2 : (eq3Pair z0 zs).2 = Q := by rw [heq]
    rw [← hlen, ← h1, ← h2]
    exact hcp

/-- The two-dimensional response matrix with diagonal entries from `P` and its conjugate and
off-diagonal entries weighted by `i * sqrt (1 - x^2)` and `Q`. -/
noncomputable def responseMatrix (P Q : Polynomial ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![P.eval (x : ℂ),
     Complex.I * Real.sqrt (1 - x ^ 2) * Q.eval (x : ℂ);
     Complex.I * Real.sqrt (1 - x ^ 2) * (conjugatePolynomial Q).eval (x : ℂ),
     (conjugatePolynomial P).eval (x : ℂ)]

/-- Equality of response matrices throughout `[-1, 1]` determines both response polynomials. -/
theorem pair_eq_of_responseMatrix_eq {P Q P' Q' : Polynomial ℂ}
    (h : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → responseMatrix P Q x = responseMatrix P' Q' x) :
    P = P' ∧ Q = Q' := by
  have hP : P = P' := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hi : Set.Infinite (Set.Icc (-1 : ℝ) 1) := Set.Icc_infinite (by norm_num)
    apply (hi.image Complex.ofReal_injective.injOn).mono
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq]
    have hx' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (h x hx)
    simpa [responseMatrix] using! hx'
  subst P
  have hQ : Q = Q' := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hi : Set.Infinite (Set.Icc (-1 / 2 : ℝ) (1 / 2)) := Set.Icc_infinite (by norm_num)
    apply (hi.image Complex.ofReal_injective.injOn).mono
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq]
    have hx' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1)
      (h x ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩)
    have hsq : 0 < Real.sqrt (1 - x ^ 2) := by
      apply Real.sqrt_pos.mpr
      nlinarith [hx.1, hx.2]
    have hne : Complex.I * Real.sqrt (1 - x ^ 2) ≠ 0 := by
      apply mul_ne_zero Complex.I_ne_zero
      exact_mod_cast (ne_of_gt hsq)
    have hx'' : Complex.I * Real.sqrt (1 - x ^ 2) * Q.eval (x : ℂ)
        = Complex.I * Real.sqrt (1 - x ^ 2) * Q'.eval (x : ℂ) := by
      simpa [responseMatrix] using! hx'
    exact mul_left_cancel₀ hne hx''
  subst Q
  exact ⟨rfl, rfl⟩

/-- Collects equivalent polynomial-recursion and signal-word characterizations of completed
pairs, together with `Theorem3Characterization` and `SignalWordTransport`. See [Gilyén et
al., Theorem 3][GilyenSuLowWiebe2019]. -/
theorem clause74 :

  (∀ (k : ℕ) (P Q : Polynomial ℂ),
    (∃ z0 : ℂ, ∃ zs : List ℂ,
      IsPhase z0 ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = k ∧
        eq3Pair z0 zs = (P, Q)) ↔
    (∃ base : ℂ, ∃ zs : List ℂ,
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = k ∧
        responseP base zs = P ∧ responseQ base zs = Q)) ∧

  (∀ (k : ℕ) (P Q : Polynomial ℂ),
    CompletedPair k P Q ↔
      ∃ z0 : ℂ, ∃ zs : List ℂ,
        IsPhase z0 ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = k ∧
          eq3Pair z0 zs = (P, Q)) ∧

  (∀ (k : ℕ) (P Q : Polynomial ℂ),
    CompletedPair k P Q ↔
      ∃ z0 : ℂ, ∃ zs : List ℂ,
        IsPhase z0 ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = k ∧
          ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
            signalWord x z0 zs =
              !![P.eval (x : ℂ),
                 Complex.I * Real.sqrt (1 - x ^ 2) * Q.eval (x : ℂ);
                 Complex.I * Real.sqrt (1 - x ^ 2) *
                   (conjugatePolynomial Q).eval (x : ℂ),
                 (conjugatePolynomial P).eval (x : ℂ)]) ∧

  Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3Characterization ∧
  Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransport := by
  refine ⟨?_, ?_, ?_, theorem3Characterization, signalWordTransport⟩
  · intro k P Q
    exact (completedPair_iff_eq3 (k := k) (P := P) (Q := Q)).symm.trans
      (completedPair_iff_response (n := k) (P := P) (Q := Q))
  · intro k P Q
    exact completedPair_iff_eq3
  · intro k P Q
    rw [completedPair_iff_eq3]
    constructor
    · rintro ⟨z0, zs, hz0, hzs, hlen, heq⟩
      refine ⟨z0, zs, hz0, hzs, hlen, ?_⟩
      intro x hx
      have hswt : ∀ (u : ℂ) (ws : List ℂ) (y : ℝ), y ∈ Set.Icc (-1 : ℝ) 1 →
          signalWord y u ws = responseMatrix (eq3Pair u ws).1 (eq3Pair u ws).2 y :=
        signalWordTransport
      rw [hswt z0 zs x hx, heq]
      rfl
    · rintro ⟨z0, zs, hz0, hzs, hlen, hall⟩
      have hswt : ∀ (u : ℂ) (ws : List ℂ) (y : ℝ), y ∈ Set.Icc (-1 : ℝ) 1 →
          signalWord y u ws = responseMatrix (eq3Pair u ws).1 (eq3Pair u ws).2 y :=
        signalWordTransport
      have hpair : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
          responseMatrix (eq3Pair z0 zs).1 (eq3Pair z0 zs).2 x = responseMatrix P Q x := by
        intro x hx
        rw [← hswt z0 zs x hx, hall x hx]
        rfl
      obtain ⟨h1, h2⟩ := pair_eq_of_responseMatrix_eq hpair
      exact ⟨z0, zs, hz0, hzs, hlen, Prod.ext h1 h2⟩

/-- Collects exact source-word resource counts, parity formulas, controlled-family count
witnesses, and the clean projector-phase gadget identity. -/
theorem clause76 :

  (∀ (d : ℕ) (Φ : List ℝ), Φ.length = d →
    cppCounts (cppCompile (sourceRealFamily Φ)) = sourceCppQuadruple d ∧
    ∃ prog : QsvtProgram,
      prog.angles = Φ ∧
      prog.ledger.dataQueries + prog.ledger.adjointQueries = d ∧
      prog.ledger.projectorNots = 2 * (d / 2) + 2 * ((d + 1) / 2) ∧
      prog.ledger.phaseGates = d ∧
      prog.ledger.peakWorkspace = 1) ∧

  (∀ d : ℕ,
    sourceCppQuadruple d = (d, 2 * (d / 2), 2 * ((d + 1) / 2), d) ∧
    (d % 2 = 0 → 2 * (d / 2) = d ∧ 2 * ((d + 1) / 2) = d) ∧
    (d % 2 = 1 → 2 * (d / 2) = d - 1 ∧ 2 * ((d + 1) / 2) = d + 1) ∧
    2 * (d / 2) + 2 * ((d + 1) / 2) = 2 * d) ∧

  (∀ (d : ℕ) (Φ : List ℝ), Φ.length = d →
    ∃ (prog : QsvtProgram) (controlledDataUses controlledPhaseUses : ℕ),
      prog.angles = Φ ∧
      prog.ledger.dataQueries + prog.ledger.adjointQueries = d ∧
      prog.ledger.projectorNots = 2 * (d / 2) + 2 * ((d + 1) / 2) ∧
      prog.ledger.phaseGates = d ∧
      prog.ledger.peakWorkspace = 1 ∧
      controlledDataUses = d % 2 ∧
      controlledPhaseUses = d) ∧

  (∀ (d m : ℕ) (Φs : List (List ℝ)), Φs.length = 2 ^ m →
    (∀ Φ ∈ Φs, Φ.length = d) →
    ∃ (prog : QsvtProgram) (multiplyControlledPhaseGates : ℕ),
      prog.angles = Φs.headD [] ∧
      prog.ledger.dataQueries + prog.ledger.adjointQueries = d ∧
      prog.ledger.projectorNots = 2 * (d / 2) + 2 * ((d + 1) / 2) ∧
      prog.ledger.phaseGates = d ∧
      prog.ledger.peakWorkspace = 1 ∧
      multiplyControlledPhaseGates = d) ∧

  (∀ (H : Type) [Fintype H] [DecidableEq H] (P : Matrix H H ℂ) (φ : ℝ),
    IsOrthogonalProjector P →
      cppNot P ∈ unitaryGroup (Bool × H) ℂ ∧
      cppNot P * cppBitPhase (H := H) φ * cppNot P * cppCleanFrame (1 : Matrix H H ℂ) =
        cppCleanFrame (1 : Matrix H H ℂ) * phaseRotation P (anglePhase φ)) := by
  refine ⟨?_, ?_, ?_, ?_, cpp_not_clean_phase_gadget⟩
  · intro d Φ hlen
    have hlen2 : (sourceRealFamily Φ).length = d := by
      simpa [sourceRealFamily] using! hlen
    refine ⟨?_, ⟨⟨Φ, ⟨d, 0, 2 * (d / 2) + 2 * ((d + 1) / 2), d, 0, 0, 1⟩⟩,
      rfl, rfl, rfl, rfl, rfl⟩⟩
    rw [cppCompile_counts, hlen2]
    rfl
  · intro d
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro h; omega
    · intro h; omega
    · omega
  · intro d Φ hlen
    exact ⟨⟨Φ, ⟨d, 0, 2 * (d / 2) + 2 * ((d + 1) / 2), d, 0, 0, 1⟩⟩, d % 2, d,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro d m Φs hlen hall
    exact ⟨⟨Φs.headD [], ⟨d, 0, 2 * (d / 2) + 2 * ((d + 1) / 2), d, 0, 0, 1⟩⟩, d,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

open Qatlib
open Qatlib

/-- The coefficientwise identity saying that `r` is the real component of `R` when `b` is true,
or its imaginary component otherwise. -/
def componentEquiv (b : Bool) (R : Polynomial ℂ) (r : Polynomial ℝ) : Prop :=
  if b then
    R + conjugatePolynomial R = C (2 : ℂ) * r.map Complex.ofRealHom
  else
    R - conjugatePolynomial R = C (2 * Complex.I) * r.map Complex.ofRealHom

/-- The imaginary unit is a unit complex phase. -/
theorem isPhase_I : IsPhase Complex.I := by
  show star Complex.I * Complex.I = 1
  simp

/-- Coefficientwise conjugation of both polynomials preserves `CompletedPair`. -/
theorem completedPair_conjugate {k : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair k P Q) :
    CompletedPair k (conjugatePolynomial P) (conjugatePolynomial Q) := by
  obtain ⟨base, zs, hb, hzs, hlen, hp, hq⟩ := completedPair_iff_response.mp h
  apply completedPair_iff_response.mpr
  refine ⟨star base, zs.map star, isPhase_conjugate hb, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    exact isPhase_conjugate (hzs z hz)
  · simpa using! hlen
  · rw [(Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.response_conjugate base zs).1, hp]
  · rw [(Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.response_conjugate base zs).2, hq]

/-- A completed pair satisfies the weighted squared-norm identity at every real point of `[-1,
1]`. -/
theorem completedPair_normSq_eval {k : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair k P Q) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Complex.normSq (P.eval (x : ℂ)) + (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) = 1 := by
  have hn : (responsePairNorm P Q).eval (x : ℂ) = (1 : Polynomial ℂ).eval (x : ℂ) :=
    congrArg (fun p : Polynomial ℂ => p.eval (x : ℂ)) h.normalization
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.responsePairNorm_eval_real P Q x, eval_one] at hn
  rw [← Complex.ofReal_one] at hn
  exact Complex.ofReal_injective hn

/-- Evaluating a real polynomial after mapping its coefficients to `ℂ` gives the complex
embedding of its real evaluation. -/
theorem eval_map_ofReal (r : Polynomial ℝ) (x : ℝ) :
    (r.map Complex.ofRealHom).eval (x : ℂ) = ((r.eval x : ℝ) : ℂ) := by
  have hpt : ((x : ℝ) : ℂ) = Complex.ofRealHom x := (Complex.ofRealHom_eq_coe x).symm
  rw [hpt, Polynomial.eval_map_apply, Complex.ofRealHom_eq_coe]

/-- A real-component identity identifies the evaluation of `r` with the real part of the
evaluation of `R`. -/
theorem componentEquiv_eval_true {R : Polynomial ℂ} {r : Polynomial ℝ}
    (h : componentEquiv true R r) (x : ℝ) :
    r.eval x = (R.eval (x : ℂ)).re := by
  simp only [componentEquiv, if_true] at h
  have he : R.eval (x : ℂ) + star (R.eval (x : ℂ))
      = (2 : ℂ) * (((r.eval x : ℝ) : ℝ) : ℂ) := by
    have he0 := congrArg (fun p : Polynomial ℂ => p.eval (x : ℂ)) h
    simp only [eval_add, eval_mul, eval_C] at he0
    rw [conjugatePolynomial_eval_real, eval_map_ofReal] at he0
    exact he0
  rw [Complex.star_def] at he
  have hx := Complex.add_conj (R.eval (x : ℂ))
  rw [hx] at he
  push_cast at he
  have h2 := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he
  have h3 := Complex.ofReal_injective h2
  nlinarith

/-- An imaginary-component identity identifies the evaluation of `r` with the imaginary part of
the evaluation of `R`. -/
theorem componentEquiv_eval_false {R : Polynomial ℂ} {r : Polynomial ℝ}
    (h : componentEquiv false R r) (x : ℝ) :
    r.eval x = (R.eval (x : ℂ)).im := by
  simp only [componentEquiv] at h
  have he : R.eval (x : ℂ) - star (R.eval (x : ℂ))
      = ((2 : ℂ) * Complex.I) * (((r.eval x : ℝ) : ℝ) : ℂ) := by
    have he0 := congrArg (fun p : Polynomial ℂ => p.eval (x : ℂ)) h
    simp only [eval_sub, eval_mul, eval_C] at he0
    rw [conjugatePolynomial_eval_real, eval_map_ofReal] at he0
    exact he0
  rw [Complex.star_def] at he
  have hx := Complex.sub_conj (R.eval (x : ℂ))
  rw [hx] at he
  have hR : ((2 : ℂ) * Complex.I) * (((r.eval x : ℝ) : ℝ) : ℂ)
      = (((2 * r.eval x : ℝ) : ℝ) : ℂ) * Complex.I := by
    simp [Complex.ofReal_mul, mul_assoc, mul_comm]
  rw [hR] at he
  have h2 := mul_right_cancel₀ Complex.I_ne_zero he
  have h3 := Complex.ofReal_injective h2
  nlinarith

/-- A component identity identifies the evaluation of `r` with the selected real or imaginary
part of `R`. -/
theorem componentEquiv_eval {b : Bool} {R : Polynomial ℂ} {r : Polynomial ℝ}
    (h : componentEquiv b R r) (x : ℝ) :
    r.eval x = if b then (R.eval (x : ℂ)).re else (R.eval (x : ℂ)).im := by
  cases b with
  | true => exact componentEquiv_eval_true h x
  | false => exact componentEquiv_eval_false h x

/-- The square of a selected real component is bounded by the squared complex norm of the full
response. -/
theorem componentEquiv_normSq_le {b : Bool} {R : Polynomial ℂ} {r : Polynomial ℝ}
    (h : componentEquiv b R r) (x : ℝ) :
    r.eval x ^ 2 ≤ Complex.normSq (R.eval (x : ℂ)) := by
  cases b with
  | true =>
    rw [componentEquiv_eval_true h x]
    have hn := Complex.normSq_nonneg (R.eval (x : ℂ))
    simp only [Complex.normSq_apply] at hn ⊢
    nlinarith
  | false =>
    rw [componentEquiv_eval_false h x]
    have hn := Complex.normSq_nonneg (R.eval (x : ℂ))
    simp only [Complex.normSq_apply] at hn ⊢
    nlinarith

/-- A component identity transfers the common degree bound for `R` and its conjugate to `r`. -/
theorem componentEquiv_degree_le {b : Bool} {R : Polynomial ℂ} {r : Polynomial ℝ} {k : ℕ}
    (h : componentEquiv b R r) (hR : R.degree ≤ ((k : ℕ) : WithBot ℕ))
    (hC : (conjugatePolynomial R).degree ≤ ((k : ℕ) : WithBot ℕ)) :
    r.degree ≤ ((k : ℕ) : WithBot ℕ) := by
  cases b with
  | true =>
    simp only [componentEquiv, if_true] at h
    have h1 : (C (2 : ℂ) * r.map Complex.ofRealHom).degree
        = (r.map Complex.ofRealHom).degree :=
      Polynomial.degree_C_mul (by norm_num : (2 : ℂ) ≠ 0)
    have h2 : (r.map Complex.ofRealHom).degree = r.degree :=
      Polynomial.degree_map_eq_of_injective Complex.ofReal_injective r
    have h3 : (R + conjugatePolynomial R).degree
        ≤ R.degree ⊔ (conjugatePolynomial R).degree :=
      Polynomial.degree_add_le R (conjugatePolynomial R)
    rw [h, h1, h2] at h3
    exact le_trans h3 (sup_le hR hC)
  | false =>
    simp only [componentEquiv] at h
    have h1 : (C (2 * Complex.I) * r.map Complex.ofRealHom).degree
        = (r.map Complex.ofRealHom).degree :=
      Polynomial.degree_C_mul (by norm_num : (2 * Complex.I) ≠ 0)
    have h2 : (r.map Complex.ofRealHom).degree = r.degree :=
      Polynomial.degree_map_eq_of_injective Complex.ofReal_injective r
    have h3 : (R - conjugatePolynomial R).degree
        ≤ R.degree ⊔ (conjugatePolynomial R).degree :=
      Polynomial.degree_sub_le R (conjugatePolynomial R)
    rw [h, h1, h2] at h3
    exact le_trans h3 (sup_le hR hC)

/-- A component identity transfers the common strict degree bound for `R` and its conjugate to
`r`. -/
theorem componentEquiv_degree_lt {b : Bool} {R : Polynomial ℂ} {r : Polynomial ℝ} {k : ℕ}
    (h : componentEquiv b R r) (hR : R.degree < ((k : ℕ) : WithBot ℕ))
    (hC : (conjugatePolynomial R).degree < ((k : ℕ) : WithBot ℕ)) :
    r.degree < ((k : ℕ) : WithBot ℕ) := by
  cases b with
  | true =>
    simp only [componentEquiv, if_true] at h
    have h1 : (C (2 : ℂ) * r.map Complex.ofRealHom).degree
        = (r.map Complex.ofRealHom).degree :=
      Polynomial.degree_C_mul (by norm_num : (2 : ℂ) ≠ 0)
    have h2 : (r.map Complex.ofRealHom).degree = r.degree :=
      Polynomial.degree_map_eq_of_injective Complex.ofReal_injective r
    have h3 : (R + conjugatePolynomial R).degree
        ≤ R.degree ⊔ (conjugatePolynomial R).degree :=
      Polynomial.degree_add_le R (conjugatePolynomial R)
    rw [h, h1, h2] at h3
    exact lt_of_le_of_lt h3 (max_lt hR hC)
  | false =>
    simp only [componentEquiv] at h
    have h1 : (C (2 * Complex.I) * r.map Complex.ofRealHom).degree
        = (r.map Complex.ofRealHom).degree :=
      Polynomial.degree_C_mul (by norm_num : (2 * Complex.I) ≠ 0)
    have h2 : (r.map Complex.ofRealHom).degree = r.degree :=
      Polynomial.degree_map_eq_of_injective Complex.ofReal_injective r
    have h3 : (R - conjugatePolynomial R).degree
        ≤ R.degree ⊔ (conjugatePolynomial R).degree :=
      Polynomial.degree_sub_le R (conjugatePolynomial R)
    rw [h, h1, h2] at h3
    exact lt_of_le_of_lt h3 (max_lt hR hC)

/-- A component identity transfers response parity of `R` and its conjugate to real parity of
`r`. -/
theorem componentEquiv_parity {b : Bool} {R : Polynomial ℂ} {r : Polynomial ℝ} {n : ℕ}
    (h : componentEquiv b R r) (hR : HasResponseParity n R)
    (hC : HasResponseParity n (conjugatePolynomial R)) :
    HasRealParity n r := by
  have hpow : (((-1 : ℝ) ^ n : ℝ) : ℂ) = (-1 : ℂ) ^ n := by simp
  have hinj := Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  cases b with
  | true =>
    have hE : R + conjugatePolynomial R = C (2 : ℂ) * r.map Complex.ofRealHom := h
    have hcomp : (R + conjugatePolynomial R).comp (-X)
        = C ((-1 : ℂ) ^ n) * (R + conjugatePolynomial R) := by
      rw [add_comp, hR, hC]
      ring
    rw [hE] at hcomp
    rw [mul_comp, Polynomial.C_comp] at hcomp
    rw [← mul_assoc, mul_comm (C ((-1 : ℂ) ^ n)) (C (2 : ℂ)), mul_assoc] at hcomp
    have hc : C (2 : ℂ) ≠ 0 := by norm_num
    have hcancel : (r.map Complex.ofRealHom).comp (-X)
        = C ((-1 : ℂ) ^ n) * r.map Complex.ofRealHom :=
      mul_left_cancel₀ hc hcomp
    show r.comp (-X) = C ((-1 : ℝ) ^ n) * r
    apply hinj
    rw [Polynomial.map_mul, Polynomial.map_C, Complex.ofRealHom_eq_coe, hpow]
    rw [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]
    exact hcancel
  | false =>
    have hE : R - conjugatePolynomial R = C (2 * Complex.I) * r.map Complex.ofRealHom := h
    have hcomp : (R - conjugatePolynomial R).comp (-X)
        = C ((-1 : ℂ) ^ n) * (R - conjugatePolynomial R) := by
      rw [sub_comp, hR, hC]
      ring
    rw [hE] at hcomp
    rw [mul_comp, Polynomial.C_comp] at hcomp
    rw [← mul_assoc, mul_comm (C ((-1 : ℂ) ^ n)) (C (2 * Complex.I)), mul_assoc] at hcomp
    have hc : C (2 * Complex.I) ≠ 0 := by norm_num
    have hcancel : (r.map Complex.ofRealHom).comp (-X)
        = C ((-1 : ℂ) ^ n) * r.map Complex.ofRealHom :=
      mul_left_cancel₀ hc hcomp
    show r.comp (-X) = C ((-1 : ℝ) ^ n) * r
    apply hinj
    rw [Polynomial.map_mul, Polynomial.map_C, Complex.ofRealHom_eq_coe, hpow]
    rw [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]
    exact hcancel

/-- The displayed coefficientwise real-part identity gives `componentEquiv true`. -/
theorem componentEquiv_true_of_real {P : Polynomial ℂ} {r : Polynomial ℝ}
    (h : P + conjugatePolynomial P = C (2 : ℂ) * r.map Complex.ofRealHom) :
    componentEquiv true P r := by
  simpa [componentEquiv] using! h

/-- Multiplication by `i` turns the displayed real-part identity for `P` into an
imaginary-component identity. -/
theorem componentEquiv_false_smul_I {P : Polynomial ℂ} {r : Polynomial ℝ}
    (h : P + conjugatePolynomial P = C (2 : ℂ) * r.map Complex.ofRealHom) :
    componentEquiv false (C Complex.I * P) r := by
  have h1 : conjugatePolynomial (C Complex.I * P)
      = C (-Complex.I) * conjugatePolynomial P := by
    rw [conjugatePolynomial_mul, conjugatePolynomial_C]
    simp
  have h2 : C Complex.I * P - C (-Complex.I) * conjugatePolynomial P
      = C Complex.I * (P + conjugatePolynomial P) := by
    rw [C_neg]
    ring
  have h3 : C Complex.I * P - conjugatePolynomial (C Complex.I * P)
      = C (2 * Complex.I) * r.map Complex.ofRealHom := by
    rw [h1, h2, h]
    rw [← mul_assoc, ← C_mul, mul_comm Complex.I (2 : ℂ)]
  exact h3

/-- Selected real or imaginary components of a completed pair satisfy the degree, parity, and
weighted norm inequality on `[-1, 1]`. -/
theorem conditions_of_components {k : ℕ} {Pt Qt : Polynomial ℝ} {bP bQ : Bool}
    {P Q : Polynomial ℂ}
    (h : CompletedPair k P Q) (hP : componentEquiv bP P Pt)
    (hQ : componentEquiv bQ Q Qt) :
    Pt.degree ≤ (k : WithBot ℕ) ∧ Qt.degree < (k : WithBot ℕ) ∧
      HasRealParity k Pt ∧ HasRealParity (k + 1) Qt ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1 := by
  have hconj := completedPair_conjugate h
  refine ⟨componentEquiv_degree_le hP h.degreeP hconj.degreeP,
    componentEquiv_degree_lt hQ h.degreeQ hconj.degreeQ,
    componentEquiv_parity hP h.parityP hconj.parityP,
    componentEquiv_parity hQ h.parityQ hconj.parityQ, ?_⟩
  intro x hx
  have h1 := componentEquiv_normSq_le hP x
  have h2 := componentEquiv_normSq_le hQ x
  have h3 := completedPair_normSq_eval h x hx
  have h4 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  nlinarith

/-- Real polynomials satisfying the degree, parity, and weighted norm conditions extend to a
completed pair with the requested real or imaginary components. -/
theorem components_of_conditions {k : ℕ} {Pt Qt : Polynomial ℝ} {bP bQ : Bool}
    (h : Pt.degree ≤ (k : WithBot ℕ) ∧ Qt.degree < (k : WithBot ℕ) ∧
      HasRealParity k Pt ∧ HasRealParity (k + 1) Qt ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1) :
    ∃ P Q : Polynomial ℂ,
      CompletedPair k P Q ∧ componentEquiv bP P Pt ∧ componentEquiv bQ Q Qt := by
  obtain ⟨hdegP, hdegQ, hparP, hparQ, hineq⟩ := h
  obtain ⟨P0, Q0, hCP, hreP, hreQ⟩ :=
    Iff.mp (theorem5RealCharacterization k Pt Qt) ⟨hdegP, hdegQ, hparP, hparQ, hineq⟩
  have hI : IsPhase Complex.I := isPhase_I
  cases bP with
  | false =>
    cases bQ with
    | false =>
      exact ⟨C Complex.I * P0, C Complex.I * Q0,
        completedPair_mul_left (completedPair_mul_right hCP hI) hI,
        componentEquiv_false_smul_I hreP, componentEquiv_false_smul_I hreQ⟩
    | true =>
      exact ⟨C Complex.I * P0, Q0, completedPair_mul_left hCP hI,
        componentEquiv_false_smul_I hreP, componentEquiv_true_of_real hreQ⟩
  | true =>
    cases bQ with
    | false =>
      exact ⟨P0, C Complex.I * Q0, completedPair_mul_right hCP hI,
        componentEquiv_true_of_real hreP, componentEquiv_false_smul_I hreQ⟩
    | true =>
      exact ⟨P0, Q0, hCP, componentEquiv_true_of_real hreP, componentEquiv_true_of_real hreQ⟩

/-- Characterizes real polynomial component pairs by degree, parity, and the weighted norm
inequality, and records phase and conjugation closure. See [Gilyén et al., Theorem
5][GilyenSuLowWiebe2019]. -/
theorem clause75 :

  (∀ (k : ℕ) (Pt Qt : Polynomial ℝ) (bP bQ : Bool),
    (Pt.degree ≤ (k : WithBot ℕ) ∧ Qt.degree < (k : WithBot ℕ) ∧
      HasRealParity k Pt ∧ HasRealParity (k + 1) Qt ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1) ↔
    (∃ P Q : Polynomial ℂ,
      CompletedPair k P Q ∧
      (if bP then
        P + conjugatePolynomial P = C (2 : ℂ) * Pt.map Complex.ofRealHom
      else
        P - conjugatePolynomial P = C (2 * Complex.I) * Pt.map Complex.ofRealHom) ∧
      (if bQ then
        Q + conjugatePolynomial Q = C (2 : ℂ) * Qt.map Complex.ofRealHom
      else
        Q - conjugatePolynomial Q = C (2 * Complex.I) * Qt.map Complex.ofRealHom))) ∧

  (∀ (k : ℕ) (P Q : Polynomial ℂ) (c : ℂ),
    CompletedPair k P Q → IsPhase c →
      CompletedPair k (C c * P) (C (star c) * Q) ∧
      CompletedPair k (conjugatePolynomial P) (conjugatePolynomial Q)) ∧

  Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterization := by
  refine ⟨?_, ?_, theorem5RealCharacterization⟩
  · intro k Pt Qt bP bQ
    constructor
    · intro h
      obtain ⟨P, Q, hCP, hP, hQ⟩ := components_of_conditions (bP := bP) (bQ := bQ) h
      exact ⟨P, Q, hCP, hP, hQ⟩
    · rintro ⟨P, Q, hCP, hP, hQ⟩
      exact conditions_of_components hCP hP hQ
  · intro k P Q c hCP hc
    refine ⟨?_, completedPair_conjugate hCP⟩
    exact completedPair_mul_right (completedPair_mul_left hCP hc) (isPhase_conjugate hc)

open Matrix Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
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
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator Classical BigOperators

/-- Gives two-point query lower bounds for well-formed adjoint circuits compressed by
isometries, including the scalar-response and complementary-square-root bounds under their
stated hypotheses. -/
theorem clause46 :

  (∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
      [Nonempty I] (L R : Matrix (Bool×W) I ℂ)
      (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool×W)))
      (f : ℝ → ℝ) (x y : ℝ) (ε : ℝ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R →
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit word →
    x ∈ Set.Icc (-1 : ℝ) 1 → y ∈ Set.Icc (-1 : ℝ) 1 → x ≠ y →
    |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → 0 ≤ ε →
    ‖((f x : ℂ)) • (1 : Matrix I I ℂ) -
      Qatlib.Concepts.Execution.WorkspaceCP.compress L (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.QsvtCore.QueryLowerBound.scalarSignalLift W x) word) R‖ ≤ ε →
    ‖((f y : ℂ)) • (1 : Matrix I I ℂ) -
      Qatlib.Concepts.Execution.WorkspaceCP.compress L (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.QsvtCore.QueryLowerBound.scalarSignalLift W y) word) R‖ ≤ ε →
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount word : ℝ) ≥
      max 0 (|f x - f y| - 2 * ε) / (2 * |x - y|)) ∧

  (∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
      [Nonempty I] (L R : Matrix (Bool×W) I ℂ)
      (word : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Bool×W)))
      (x y a b eps : ℝ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R →
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit word →
    x ∈ Set.Icc (-1 : ℝ) 1 → y ∈ Set.Icc (-1 : ℝ) 1 → x ≠ y → 0 ≤ eps →
    eps ≤ a → a ≤ 1 → 0 ≤ b → b + eps ≤ 1 →
    ‖((a : ℂ)) • (1 : Matrix I I ℂ) -
      Qatlib.Concepts.Execution.WorkspaceCP.compress L (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.QsvtCore.QueryLowerBound.scalarSignalLift W x) word) R‖ ≤ eps →
    ‖((b : ℂ)) • (1 : Matrix I I ℂ) -
      Qatlib.Concepts.Execution.WorkspaceCP.compress L (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.QsvtCore.QueryLowerBound.scalarSignalLift W y) word) R‖ ≤ eps →
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount word : ℝ) ≥
      max (max 0 (|a - b| - 2 * eps))
        (Real.sqrt (1 - (b + eps) ^ 2) - Real.sqrt (1 - (a - eps) ^ 2)) /
          Qatlib.Concepts.QsvtCore.QueryLowerBound.scalarSignalDistance x y) := by
  refine ⟨?_, ?_⟩
  · intro W I _ _ _ _ _ L R word f x y ε hL hR hw hx hy hxy hxhalf hyhalf hε hfx hfy
    exact (Qatlib.Concepts.QsvtCore.QueryLowerBound.scalar_signal_actual_response_query_lower_bound W I L R word
      x y (f x) (f y) ε hL hR hw hx hy hxy hε hfx hfy).2 hxhalf hyhalf
  · intro W I _ _ _ _ _ L R word x y a b eps hL hR hw hx hy hxy heps haeps ha1 hb0 hbeps ha hb
    exact Qatlib.Concepts.QsvtCore.QueryLowerBound.scalar_signal_safe_leakage_query_lower_bound_corrected W I L R word
      x y a b eps hL hR hw hx hy hxy heps haeps ha1 hb0 hbeps ha hb

/-- A complex number with squared norm one is a unit phase. -/
theorem isPhase_of_normSq {c : ℂ} (h : Complex.normSq c = 1) : IsPhase c := by
  unfold IsPhase
  rw [Complex.star_def, mul_comm, Complex.mul_conj, h, Complex.ofReal_one]

/-- The angle phase at zero is `1`. -/
theorem anglePhase_zero : anglePhase 0 = 1 := by
  apply Complex.ext <;> simp [anglePhase]

/-- A unit complex constant is realized by the two-angle list `[Complex.arg c, 0]`. -/
theorem sourcePhaseResponse_arg_pair (c : ℂ) (hc : Complex.normSq c = 1) :
    sourcePhaseResponse [Complex.arg c, 0] = Polynomial.C c := by
  have hph : IsPhase c := isPhase_of_normSq hc
  have harg : anglePhase (Complex.arg c) = c := anglePhase_arg_of_isPhase hph
  have hmap : ([Complex.arg c, 0] : List ℝ).map anglePhase = [c, 1] := by
    simp only [List.map_cons, List.map_nil, harg, anglePhase_zero]
  unfold sourcePhaseResponse
  rw [hmap]
  simp only [responseP_cons, responseQ_cons, responseP_nil, responseQ_nil,
    Polynomial.C_1, star_one, one_mul, mul_one, mul_zero, sub_zero]
  ring

/-- The source phase response has evaluation parity equal to the phase list length. -/
theorem sourcePhaseResponse_eval_parity (Ψ : List ℝ) (x : ℂ) :
    (sourcePhaseResponse Ψ).eval (-x) =
      (-1 : ℂ) ^ Ψ.length * (sourcePhaseResponse Ψ).eval x := by
  unfold sourcePhaseResponse
  have hlen : (Ψ.map anglePhase).length = Ψ.length := by simp
  have h := (response_parity 1 (Ψ.map anglePhase) x).1
  rw [hlen] at h
  exact h

/-- A phase list realizing a unit constant polynomial has even length. -/
theorem length_even_of_sourcePhaseResponse_const {Ψ : List ℝ} {c : ℂ}
    (h : sourcePhaseResponse Ψ = Polynomial.C c) (hc : Complex.normSq c = 1) :
    Ψ.length % 2 = 0 := by
  by_contra hne
  have hmod : Ψ.length % 2 = 1 := by omega
  have hpow : (-1 : ℂ) ^ Ψ.length = -1 := by
    have h2 : Ψ.length = 2 * (Ψ.length / 2) + 1 := by omega
    rw [h2, pow_add, pow_mul]
    simp
  have hpar := sourcePhaseResponse_eval_parity Ψ 0
  rw [h, Polynomial.eval_C, Polynomial.eval_C, hpow] at hpar
  rw [neg_one_mul] at hpar
  have hcc : c + c = 0 := (add_eq_zero_iff_eq_neg (a := c) (b := c)).mpr hpar
  have h2c : (2 : ℂ) * c = 0 := by rwa [two_mul]
  cases mul_eq_zero.mp h2c with
  | inl habs => exact absurd habs (by norm_num)
  | inr hz =>
    rw [hz] at hc
    simp at hc

/-- A phase list realizing a unit constant other than `1` has length at least two. -/
theorem length_two_le_of_sourcePhaseResponse_const {Ψ : List ℝ} {c : ℂ}
    (h : sourcePhaseResponse Ψ = Polynomial.C c) (hc : Complex.normSq c = 1)
    (hc1 : c ≠ 1) : 2 ≤ Ψ.length := by
  have heven : Ψ.length % 2 = 0 := length_even_of_sourcePhaseResponse_const h hc
  by_contra hlt
  have hlen0 : Ψ.length = 0 := by omega
  have hnil : Ψ = [] := List.eq_nil_of_length_eq_zero hlen0
  rw [hnil] at h
  have hs : sourcePhaseResponse ([] : List ℝ) = (1 : Polynomial ℂ) := rfl
  have h1 : (1 : Polynomial ℂ) = Polynomial.C c := by rw [← h, hs]
  have hceq : c = 1 := by
    have h0 := congrArg (fun p : Polynomial ℂ => p.eval 0) h1
    simp only [Polynomial.eval_one, Polynomial.eval_C] at h0
    exact h0.symm
  exact hc1 hceq

/-- Records the empty-list response, two-angle realizations and minimal lengths for unit
constants, and `Corollary8ComplexPhaseExistence`. See [Gilyén et al., Corollary
8][GilyenSuLowWiebe2019]. -/
theorem clause47 :

  sourcePhaseResponse [] = (1 : Polynomial ℂ) ∧

  (sourcePhaseResponse [] = Polynomial.C (1 : ℂ)) ∧

  (∀ c : ℂ, Complex.normSq c = 1 →
    (c = 1 ∨ sourcePhaseResponse [Complex.arg c, 0] = Polynomial.C c) ∧
    (c ≠ 1 →
      sourcePhaseResponse [Complex.arg c, 0] = Polynomial.C c ∧
      (∀ Ψ : List ℝ, sourcePhaseResponse Ψ = Polynomial.C c → 2 ≤ Ψ.length)) ∧
    (∀ Ψ : List ℝ, sourcePhaseResponse Ψ = Polynomial.C c → Ψ.length % 2 = 0)) ∧

  Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistence := by
  refine ⟨?_, ?_, ?_, corollary8ComplexPhaseExistence⟩
  · rfl
  · rfl
  · intro c hc
    refine ⟨Or.inr (sourcePhaseResponse_arg_pair c hc), ?_, ?_⟩
    · intro hc1
      exact ⟨sourcePhaseResponse_arg_pair c hc,
        fun Ψ hΨ => length_two_le_of_sourcePhaseResponse_const hΨ hc hc1⟩
    · intro Ψ hΨ
      exact length_even_of_sourcePhaseResponse_const hΨ hc

/-- The real part of a finite complex sum is the sum of the real parts. -/
theorem re_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    Complex.re (∑ i ∈ s, f i) = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s _ ih => simp

/-- The imaginary part of a finite complex sum is the sum of the imaginary parts. -/
theorem im_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    Complex.im (∑ i ∈ s, f i) = ∑ i ∈ s, (f i).im := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s _ ih => simp

/-- Polynomial evaluation commutes with a finite sum. -/
theorem eval_finset_sum_poly {R : Type} [Semiring R] {ι : Type}
    (s : Finset ι) (f : ι → Polynomial R) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Polynomial.eval_add, ih]

/-- A complex polynomial equals the sum of its coefficient monomials over its support. -/
theorem coeff_sum_eq (P : Polynomial ℂ) :
    (∑ i ∈ P.support,
      (Polynomial.C (P.coeff i) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ)) = P := by
  have h := Polynomial.sum_C_mul_X_pow_eq P
  rw [Polynomial.sum_def] at h
  simpa using! h

/-- Evaluation at a real input equals the finite sum of the coefficient monomial evaluations. -/
theorem polynomial_eval_eq_coeff_sum (P : Polynomial ℂ) (x : ℝ) :
    P.eval (x : ℂ) = ∑ i ∈ P.support,
      (P.coeff i : ℂ) * ((x : ℂ) ^ (i : ℕ)) := by
  have heq : (∑ i ∈ P.support,
      (Polynomial.C (P.coeff i) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ)).eval (x : ℂ)
      = P.eval (x : ℂ) :=
    congrArg (fun q : Polynomial ℂ => q.eval (x : ℂ)) (coeff_sum_eq P)
  have h2 : (∑ i ∈ P.support,
      (Polynomial.C (P.coeff i) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ)).eval (x : ℂ)
      = ∑ i ∈ P.support, (P.coeff i : ℂ) * ((x : ℂ) ^ (i : ℕ)) := by
    rw [eval_finset_sum_poly]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact heq.symm.trans h2

/-- The polynomial formed from real coefficient parts evaluates to the real part of the original
polynomial at a real input. -/
theorem polynomial_eval_re_eq (P : Polynomial ℂ) (x : ℝ) :
    (∑ i ∈ P.support, Polynomial.C (P.coeff i).re * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x
      = (P.eval (x : ℂ)).re := by
  have hxr (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).re = x ^ (i : ℕ) := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have hxi (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have hre : (P.eval (x : ℂ)).re = ∑ i ∈ P.support, ((P.coeff i).re * x ^ (i : ℕ)) := by
    rw [polynomial_eval_eq_coeff_sum, re_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.mul_re, hxr, hxi]
    ring
  rw [hre, eval_finset_sum_poly]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The polynomial formed from imaginary coefficient parts evaluates to the imaginary part of
the original polynomial at a real input. -/
theorem polynomial_eval_im_eq (P : Polynomial ℂ) (x : ℝ) :
    (∑ i ∈ P.support, Polynomial.C (P.coeff i).im * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x
      = (P.eval (x : ℂ)).im := by
  have hxr (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).re = x ^ (i : ℕ) := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have hxi (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have him : (P.eval (x : ℂ)).im = ∑ i ∈ P.support, ((P.coeff i).im * x ^ (i : ℕ)) := by
    rw [polynomial_eval_eq_coeff_sum, im_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.mul_im, hxr, hxi]
    ring
  rw [him, eval_finset_sum_poly]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- A complex polynomial evaluation at a real input decomposes into the evaluations of its real
and imaginary coefficient polynomials. -/
theorem polynomial_eval_eq_re_add_im (P : Polynomial ℂ) (x : ℝ) :
    P.eval (x : ℂ) =
      Complex.ofReal ((∑ i ∈ P.support,
        Polynomial.C (P.coeff i).re * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x) +
        Complex.I * Complex.ofReal ((∑ i ∈ P.support,
          Polynomial.C (P.coeff i).im * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x) := by
  rw [polynomial_eval_re_eq, polynomial_eval_im_eq, mul_comm]
  exact (Complex.re_add_im (P.eval (x : ℂ))).symm

/-- Hermitian functional calculus preserves pointwise addition of responses. -/
theorem hermitianFunction_add {I : Type} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) (f g : ℝ → ℂ) :
    hermitianFunction H hH (fun x => f x + g x) =
      hermitianFunction H hH f + hermitianFunction H hH g := by
  unfold hermitianFunction spectralDiagonal
  rw [← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]

/-- Multiplying a response by a complex constant multiplies its Hermitian functional calculus by
the same scalar. -/
theorem hermitianFunction_mul {I : Type} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) (c : ℂ) (f : ℝ → ℂ) :
    hermitianFunction H hH (fun x => c * f x) = c • hermitianFunction H hH f := by
  unfold hermitianFunction spectralDiagonal
  have hdi : (fun i => c * f (orderedHermitianValues hH i))
      = c • (fun i => f (orderedHermitianValues hH i)) := by
    funext i; rfl
  rw [hdi, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- Pointwise equal responses have equal Hermitian functional calculus values. -/
theorem hermitianFunction_congr {I : Type} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) (f g : ℝ → ℂ) (h : ∀ x, f x = g x) :
    hermitianFunction H hH f = hermitianFunction H hH g := by
  have hfun : f = g := funext h
  rw [hfun]

/-- Splits a complex polynomial bounded by `1/4` on `[-1, 1]` into bounded even and odd real and
imaginary components, realizes their real responses by phase lists with a cost ledger, and
gives the corresponding Hermitian functional calculus decomposition. -/
theorem clause48 :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (P : Polynomial ℂ)
    (hH : H.IsHermitian),
    ‖H‖ ≤ 1 →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Complex.normSq (P.eval (Complex.ofReal x)) ≤ (1 / 4) ^ 2) →
    (let reP : Polynomial ℝ :=
      ∑ i ∈ P.support, Polynomial.C (P.coeff i).re * Polynomial.X ^ (i : ℕ)
     let imP : Polynomial ℝ :=
      ∑ i ∈ P.support, Polynomial.C (P.coeff i).im * Polynomial.X ^ (i : ℕ)
     let reE : Polynomial ℝ :=
      (reP + reP.comp (-Polynomial.X)) * Polynomial.C (1 / 2)
     let reO : Polynomial ℝ :=
      (reP - reP.comp (-Polynomial.X)) * Polynomial.C (1 / 2)
     let imE : Polynomial ℝ :=
      (imP + imP.comp (-Polynomial.X)) * Polynomial.C (1 / 2)
     let imO : Polynomial ℝ :=
      (imP - imP.comp (-Polynomial.X)) * Polynomial.C (1 / 2)

     reP = reE + reO ∧ imP = imE + imO ∧
       reE.comp (-Polynomial.X) = reE ∧ reO.comp (-Polynomial.X) = -reO ∧
       imE.comp (-Polynomial.X) = imE ∧ imO.comp (-Polynomial.X) = -imO ∧
       (∀ x ∈ Set.Icc (-1 : ℝ) 1,
         |reE.eval x| ≤ 1 / 4 ∧ |reO.eval x| ≤ 1 / 4 ∧
         |imE.eval x| ≤ 1 / 4 ∧ |imO.eval x| ≤ 1 / 4) ∧

     (∃ (Φre Φro Φim Φio : List ℝ) (led : QsvtCostLedger),
       (∀ x : ℝ, ((sourcePhaseResponse Φre).eval (x : ℂ)).re = reE.eval x) ∧
       (∀ x : ℝ, ((sourcePhaseResponse Φro).eval (x : ℂ)).re = reO.eval x) ∧
       (∀ x : ℝ, ((sourcePhaseResponse Φim).eval (x : ℂ)).re = imE.eval x) ∧
       (∀ x : ℝ, ((sourcePhaseResponse Φio).eval (x : ℂ)).re = imO.eval x) ∧
       led.dataQueries =
         Φre.length + Φro.length + Φim.length + Φio.length ∧
       led.adjointQueries = led.dataQueries ∧
       led.phaseGates = led.dataQueries ∧
       1 ≤ led.peakWorkspace) ∧

     hermitianFunction H hH (polynomialResponse P) =
       hermitianFunction H hH (fun x => ((reE.eval x : ℝ) : ℂ)) +
       hermitianFunction H hH (fun x => ((reO.eval x : ℝ) : ℂ)) +
       Complex.I •
         (hermitianFunction H hH (fun x => ((imE.eval x : ℝ) : ℂ)) +
           hermitianFunction H hH (fun x => ((imO.eval x : ℝ) : ℂ)))) := by
  intro I _ _ H P hH hHnorm hbound reP imP reE reO imE imO
  have hreP : ∀ y : ℝ, reP.eval y = (P.eval (y : ℂ)).re :=
    fun y => polynomial_eval_re_eq P y
  have himP : ∀ y : ℝ, imP.eval y = (P.eval (y : ℂ)).im :=
    fun y => polynomial_eval_im_eq P y
  have hC2 : (2 : Polynomial ℝ) * Polynomial.C (1 / 2 : ℝ) = 1 := by
    conv_lhs => rw [show (2 : Polynomial ℝ) = Polynomial.C (2 : ℝ) from
      (Polynomial.C_eq_natCast 2).symm, ← Polynomial.C_mul]
    rw [show (2 : ℝ) * (1 / 2) = 1 from by ring, Polynomial.C_1]
  have hreE_eq : reE = (reP + reP.comp (-Polynomial.X)) * Polynomial.C (1 / 2) := rfl
  have hreO_eq : reO = (reP - reP.comp (-Polynomial.X)) * Polynomial.C (1 / 2) := rfl
  have himE_eq : imE = (imP + imP.comp (-Polynomial.X)) * Polynomial.C (1 / 2) := rfl
  have himO_eq : imO = (imP - imP.comp (-Polynomial.X)) * Polynomial.C (1 / 2) := rfl
  have hsplit_re : reP = reE + reO := by
    rw [hreE_eq, hreO_eq, ← add_mul]
    have hsum : (reP + reP.comp (-Polynomial.X)) + (reP - reP.comp (-Polynomial.X))
        = 2 * reP := by ring
    rw [hsum, show (2 * reP : Polynomial ℝ) * Polynomial.C (1 / 2 : ℝ)
      = reP * ((2 : Polynomial ℝ) * Polynomial.C (1 / 2 : ℝ)) from by ring, hC2, mul_one]
  have hsplit_im : imP = imE + imO := by
    rw [himE_eq, himO_eq, ← add_mul]
    have hsum : (imP + imP.comp (-Polynomial.X)) + (imP - imP.comp (-Polynomial.X))
        = 2 * imP := by ring
    rw [hsum, show (2 * imP : Polynomial ℝ) * Polynomial.C (1 / 2 : ℝ)
      = imP * ((2 : Polynomial ℝ) * Polynomial.C (1 / 2 : ℝ)) from by ring, hC2, mul_one]
  have hpar_reE : reE.comp (-Polynomial.X) = reE := by
    rw [hreE_eq, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.comp_assoc,
      Polynomial.neg_comp, Polynomial.X_comp, neg_neg, Polynomial.comp_X,
      Polynomial.C_comp, add_comm]
  have hpar_reO : reO.comp (-Polynomial.X) = -reO := by
    rw [hreO_eq, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.comp_assoc,
      Polynomial.neg_comp, Polynomial.X_comp, neg_neg, Polynomial.comp_X,
      Polynomial.C_comp]
    ring
  have hpar_imE : imE.comp (-Polynomial.X) = imE := by
    rw [himE_eq, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.comp_assoc,
      Polynomial.neg_comp, Polynomial.X_comp, neg_neg, Polynomial.comp_X,
      Polynomial.C_comp, add_comm]
  have hpar_imO : imO.comp (-Polynomial.X) = -imO := by
    rw [himO_eq, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.comp_assoc,
      Polynomial.neg_comp, Polynomial.X_comp, neg_neg, Polynomial.comp_X,
      Polynomial.C_comp]
    ring
  have hquarter : ∀ y : ℝ, y ∈ Set.Icc (-1 : ℝ) 1 →
      |reP.eval y| ≤ 1 / 4 ∧ |imP.eval y| ≤ 1 / 4 := by
    intro y hy
    have hy1 : (y : ℂ) = Complex.ofReal y := rfl
    have hnorm : Complex.normSq (P.eval (Complex.ofReal y)) ≤ (1 / 4) ^ 2 :=
      hbound y hy
    have habs : ‖P.eval (Complex.ofReal y)‖ ≤ 1 / 4 := by
      have hnorm := hbound y hy
      have hsqn : (‖P.eval (Complex.ofReal y)‖) ^ 2 = Complex.normSq (P.eval (Complex.ofReal y)) :=
        (Complex.normSq_eq_norm_sq _).symm
      have hnn : 0 ≤ ‖P.eval (Complex.ofReal y)‖ := norm_nonneg _
      have h2 : ‖P.eval (Complex.ofReal y)‖ ^ 2 ≤ ((1 / 4 : ℝ) ^ 2) := by rwa [hsqn]
      exact (sq_le_sq₀ hnn (show (0:ℝ) ≤ 1 / 4 by norm_num)).mp h2
    have hre : |reP.eval y| ≤ 1 / 4 := by
      rw [hreP y, show (P.eval (y : ℂ)) = P.eval (Complex.ofReal y) from rfl]
      exact le_trans (Complex.abs_re_le_norm _) habs
    have him : |imP.eval y| ≤ 1 / 4 := by
      rw [himP y, show (P.eval (y : ℂ)) = P.eval (Complex.ofReal y) from rfl]
      have himle : |Complex.im (P.eval (Complex.ofReal y))| ≤ ‖P.eval (Complex.ofReal y)‖ := by
        have h1 := Complex.abs_re_le_norm (Complex.I * P.eval (Complex.ofReal y))
        have h2 : Complex.re (Complex.I * P.eval (Complex.ofReal y))
            = -Complex.im (P.eval (Complex.ofReal y)) := by
          simp [Complex.mul_re]
        rw [h2] at h1
        simpa using! h1
      exact le_trans himle habs
    exact ⟨hre, him⟩
  have henv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |reE.eval x| ≤ 1 / 4 ∧ |reO.eval x| ≤ 1 / 4 ∧
      |imE.eval x| ≤ 1 / 4 ∧ |imO.eval x| ≤ 1 / 4 := by
    intro x hx
    have hx' : -x ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc] at hx ⊢; constructor <;> linarith
    have hre : (1 / 4 : ℝ) + 1 / 4 = 2 * (1 / 4) := by ring
    have hhalf : ∀ a b : ℝ, |(a + b) * (1 / 2 : ℝ)| ≤ (|a| + |b|) * (1 / 2) := by
      intro a b
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_right (abs_add_le a b) (by norm_num)
    have hbound4 : ∀ {a b : ℝ}, |a| ≤ 1 / 4 → |b| ≤ 1 / 4 → |(a + b) * (1 / 2 : ℝ)| ≤ 1 / 4 := by
      intro a b ha hb
      have := hhalf a b
      have hsum : (|a| + |b|) * (1 / 2 : ℝ) ≤ 1 / 4 := by nlinarith [abs_nonneg a, abs_nonneg b]
      exact le_trans this hsum
    have hbound4' : ∀ {a b : ℝ}, |a| ≤ 1 / 4 → |b| ≤ 1 / 4 → |(a - b) * (1 / 2 : ℝ)| ≤ 1 / 4 := by
      intro a b ha hb
      have h1 : a - b = a + (-b) := by ring
      rw [h1]
      exact hbound4 ha (by simpa using! hb)
    obtain ⟨hreP1, himP1⟩ := hquarter x hx
    obtain ⟨hreP2, himP2⟩ := hquarter (-x) hx'
    have hreE : |reE.eval x| ≤ 1 / 4 := by
      rw [hreE_eq, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
      exact hbound4 hreP1 hreP2
    have hreO : |reO.eval x| ≤ 1 / 4 := by
      rw [hreO_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_comp,
        Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
      exact hbound4' hreP1 hreP2
    have himE : |imE.eval x| ≤ 1 / 4 := by
      rw [himE_eq, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
      exact hbound4 himP1 himP2
    have himO : |imO.eval x| ≤ 1 / 4 := by
      rw [himO_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_comp,
        Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
      exact hbound4' himP1 himP2
    exact ⟨hreE, hreO, himE, himO⟩
  have heven_pow : ∀ d : ℕ, d % 2 = 0 → (-1 : ℝ) ^ d = 1 := by
    intro d hd
    have h2 : d = 2 * (d / 2) := by omega
    rw [h2, pow_mul]
    norm_num
  have hodd_pow : ∀ d : ℕ, d % 2 = 1 → (-1 : ℝ) ^ d = -1 := by
    intro d hd
    have h2 : d = 2 * (d / 2) + 1 := by omega
    rw [h2, pow_add, pow_mul]
    norm_num
  have hreal_even : ∀ {p : Polynomial ℝ} {d : ℕ}, d % 2 = 0 →
      p.comp (-Polynomial.X) = p → Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d p := by
    intro p d hd hp
    show p.comp (-Polynomial.X) = Polynomial.C ((-1 : ℝ) ^ d) * p
    rw [heven_pow d hd, Polynomial.C_1, one_mul]
    exact hp
  have hreal_odd : ∀ {p : Polynomial ℝ} {d : ℕ}, d % 2 = 1 →
      p.comp (-Polynomial.X) = -p → Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d p := by
    intro p d hd hp
    show p.comp (-Polynomial.X) = Polynomial.C ((-1 : ℝ) ^ d) * p
    rw [hodd_pow d hd, Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
    exact hp
  set dE : ℕ := 2 * (reE.natDegree + 1) with hdE
  set dO : ℕ := 2 * (reO.natDegree + 1) + 1 with hdO
  set dIE : ℕ := 2 * (imE.natDegree + 1) with hdIE
  set dIO : ℕ := 2 * (imO.natDegree + 1) + 1 with hdIO
  have hdE_pos : 0 < dE := by rw [hdE]; positivity
  have hdO_pos : 0 < dO := by rw [hdO]; positivity
  have hdIE_pos : 0 < dIE := by rw [hdIE]; positivity
  have hdIO_pos : 0 < dIO := by rw [hdIO]; positivity
  have hdE_par : dE % 2 = 0 := by rw [hdE]; omega
  have hdO_par : dO % 2 = 1 := by rw [hdO]; omega
  have hdIE_par : dIE % 2 = 0 := by rw [hdIE]; omega
  have hdIO_par : dIO % 2 = 1 := by rw [hdIO]; omega
  have hdegE : reE.degree ≤ (dE : WithBot ℕ) := by
    apply le_trans Polynomial.degree_le_natDegree
    have h : reE.natDegree ≤ dE := by rw [hdE]; omega
    exact_mod_cast h
  have hdegO : reO.degree ≤ (dO : WithBot ℕ) := by
    apply le_trans Polynomial.degree_le_natDegree
    have h : reO.natDegree ≤ dO := by rw [hdO]; omega
    exact_mod_cast h
  have hdegIE : imE.degree ≤ (dIE : WithBot ℕ) := by
    apply le_trans Polynomial.degree_le_natDegree
    have h : imE.natDegree ≤ dIE := by rw [hdIE]; omega
    exact_mod_cast h
  have hdegIO : imO.degree ≤ (dIO : WithBot ℕ) := by
    apply le_trans Polynomial.degree_le_natDegree
    have h : imO.natDegree ≤ dIO := by rw [hdIO]; omega
    exact_mod_cast h
  have hparE : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity dE reE :=
      hreal_even hdE_par hpar_reE
  have hparO : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity dO reO :=
      hreal_odd hdO_par hpar_reO
  have hparIE : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity dIE imE :=
      hreal_even hdIE_par hpar_imE
  have hparIO : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity dIO imO :=
      hreal_odd hdIO_par hpar_imO
  have hbE : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |reE.eval x| ≤ 1 := by
    intro x hx
    have := (henv x hx).1
    linarith
  have hbO : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |reO.eval x| ≤ 1 := by
    intro x hx
    have := (henv x hx).2.1
    linarith
  have hbIE : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |imE.eval x| ≤ 1 := by
    intro x hx
    have := (henv x hx).2.2.1
    linarith
  have hbIO : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |imO.eval x| ≤ 1 := by
    intro x hx
    have := (henv x hx).2.2.2
    linarith
  obtain ⟨Φre, hΦre, hΦre_eval⟩ :=
    source_length_real_phase_existence reE dE hdE_pos hdegE hparE hbE
  obtain ⟨Φro, hΦro, hΦro_eval⟩ :=
    source_length_real_phase_existence reO dO hdO_pos hdegO hparO hbO
  obtain ⟨Φim, hΦim, hΦim_eval⟩ :=
    source_length_real_phase_existence imE dIE hdIE_pos hdegIE hparIE hbIE
  obtain ⟨Φio, hΦio, hΦio_eval⟩ :=
    source_length_real_phase_existence imO dIO hdIO_pos hdegIO hparIO hbIO
  have hwords : ∃ (Φre Φro Φim Φio : List ℝ) (led : QsvtCostLedger),
      (∀ x : ℝ, ((sourcePhaseResponse Φre).eval (x : ℂ)).re = reE.eval x) ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φro).eval (x : ℂ)).re = reO.eval x) ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φim).eval (x : ℂ)).re = imE.eval x) ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φio).eval (x : ℂ)).re = imO.eval x) ∧
      led.dataQueries = Φre.length + Φro.length + Φim.length + Φio.length ∧
      led.adjointQueries = led.dataQueries ∧
      led.phaseGates = led.dataQueries ∧
      1 ≤ led.peakWorkspace := by
    set s : ℕ := Φre.length + Φro.length + Φim.length + Φio.length
    refine ⟨Φre, Φro, Φim, Φio, ⟨s, s, 0, s, 0, 0, 1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hΦre_eval
    · exact hΦro_eval
    · exact hΦim_eval
    · exact hΦio_eval
    · rfl
    · rfl
    · rfl
    · norm_num
  have hfun_eq : (polynomialResponse P) =
      (fun x : ℝ => (((reE.eval x : ℝ) : ℂ) + ((reO.eval x : ℝ) : ℂ) +
        Complex.I * (((imE.eval x : ℝ) : ℂ) + ((imO.eval x : ℝ) : ℂ)))) := by
    funext x
    have hp := polynomial_eval_eq_re_add_im P x
    have hreS : ((∑ i ∈ P.support,
        Polynomial.C (P.coeff i).re * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x)
        = reP.eval x := rfl
    have himS : ((∑ i ∈ P.support,
        Polynomial.C (P.coeff i).im * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x)
        = imP.eval x := rfl
    rw [hreS, himS] at hp
    have hre : Complex.ofReal (reP.eval x) = (((reE.eval x : ℝ) : ℂ) + ((reO.eval x : ℝ) : ℂ)) := by
      rw [hsplit_re, Polynomial.eval_add, Complex.ofReal_add]
    have him : Complex.ofReal (imP.eval x) = (((imE.eval x : ℝ) : ℂ) + ((imO.eval x : ℝ) : ℂ)) := by
      rw [hsplit_im, Polynomial.eval_add, Complex.ofReal_add]
    rw [hre, him] at hp
    exact hp
  refine ⟨hsplit_re, hsplit_im, hpar_reE, hpar_reO, hpar_imE, hpar_imO, henv, hwords, ?_⟩
  rw [hfun_eq]
  rw [hermitianFunction_add (hH := hH)
      (f := fun x : ℝ => (((reE.eval x : ℝ) : ℂ) + ((reO.eval x : ℝ) : ℂ)))
      (g := fun x : ℝ => Complex.I * (((imE.eval x : ℝ) : ℂ) + ((imO.eval x : ℝ) : ℂ)))]
  rw [hermitianFunction_add (hH := hH) (f := fun x : ℝ => ((reE.eval x : ℝ) : ℂ))
      (g := fun x : ℝ => ((reO.eval x : ℝ) : ℂ))]
  rw [hermitianFunction_mul (hH := hH) (c := Complex.I)
      (f := fun x : ℝ => (((imE.eval x : ℝ) : ℂ) + ((imO.eval x : ℝ) : ℂ)))]
  rw [hermitianFunction_add (hH := hH) (f := fun x : ℝ => ((imE.eval x : ℝ) : ℂ))
      (g := fun x : ℝ => ((imO.eval x : ℝ) : ℂ))]

open Matrix Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
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
open scoped Matrix.Norms.L2Operator BigOperators Classical

/-- A standard coordinate vector with complex entry `1` has Euclidean norm one. -/
theorem euclidean_single_norm_one {n : Type} [Fintype n] [DecidableEq n] (j : n) :
    ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ = 1 := by
  have h := EuclideanSpace.norm_sq_eq (EuclideanSpace.single j (1 : ℂ))
  have happly : ∀ i : n, (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n) i
      = if i = j then (1 : ℂ) else 0 := by
    intro i
    simp only [EuclideanSpace.single, PiLp.single_apply]
  have hs : (∑ i : n, ‖EuclideanSpace.single j (1 : ℂ) i‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h2 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ ^ 2 = 1 := by
    rw [h, hs]
  have h3 : 0 ≤ ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ := norm_nonneg _
  calc
    ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖
        = Real.sqrt (‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ ^ 2) :=
      (Real.sqrt_sq h3).symm
    _ = Real.sqrt 1 := by rw [h2]
    _ = 1 := Real.sqrt_one

/-- Every entry of a matrix with operator norm at most one has complex norm at most one. -/
theorem entry_norm_le_l2_opNorm {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) (h : ‖A‖ ≤ 1) : ‖A i j‖ ≤ 1 := by
  set e : EuclideanSpace ℂ n := EuclideanSpace.single j (1 : ℂ) with he
  have hnorm : ‖e‖ = 1 := by
    rw [he]
    exact euclidean_single_norm_one j
  have hvec : ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ e)‖ ≤ ‖A‖ * ‖e‖ :=
    Matrix.l2_opNorm_mulVec A e
  rw [hnorm, mul_one] at hvec
  have hentry : (A *ᵥ e) i = A i j := by
    rw [he]
    change (A *ᵥ (Pi.single j (1 : ℂ) : n → ℂ)) i = A i j
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  have hcomp : ‖A i j‖ ≤ ‖(EuclideanSpace.equiv n ℂ).symm (A *ᵥ e)‖ := by
    have hthis := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ e)) i
    have hof : ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ e)).ofLp = (A *ᵥ e) := rfl
    rw [hof, hentry] at hthis
    exact hthis
  exact hcomp.trans (hvec.trans h)

/-- Every real number has an integer multiple of `2^(-t)` within distance `2^(-t) / 2`. -/
theorem dyadic_round_near (x t : ℝ) :
    ∃ k : ℤ, |x - (k : ℝ) / (2 : ℝ) ^ t| ≤ ((2 : ℝ) ^ t)⁻¹ / 2 := by
  have h2t : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos two_pos t
  have hex : ∃ k : ℤ, |x * (2 : ℝ) ^ t - k| ≤ (1 : ℝ) / 2 := by
    refine ⟨Int.floor (x * (2 : ℝ) ^ t + 1 / 2), ?_⟩
    have h1 : (Int.floor (x * (2 : ℝ) ^ t + 1 / 2) : ℝ) ≤ x * (2 : ℝ) ^ t + 1 / 2 :=
      Int.floor_le _
    have h2 : x * (2 : ℝ) ^ t + 1 / 2 < (Int.floor (x * (2 : ℝ) ^ t + 1 / 2) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_⟩
  have hsplit : x - (k : ℝ) / (2 : ℝ) ^ t = (x * (2 : ℝ) ^ t - k) / (2 : ℝ) ^ t := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos h2t]
  have h3 : |x * (2 : ℝ) ^ t - k| / (2 : ℝ) ^ t ≤ ((2 : ℝ) ^ t)⁻¹ / 2 := by
    have h4 : (1 : ℝ) / 2 / (2 : ℝ) ^ t = ((2 : ℝ) ^ t)⁻¹ / 2 := by field_simp
    calc
      |x * (2 : ℝ) ^ t - k| / (2 : ℝ) ^ t ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ t := by gcongr
      _ = ((2 : ℝ) ^ t)⁻¹ / 2 := h4
  exact h3

/-- The stated precision exponent bounds the total squared rounding budget by `ε^2` for positive
dimension and `0 < ε ≤ 1`. -/
theorem clause59_rounding_budget (d B : ℕ) (ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((d : ℝ) / 2) *
      (((2 : ℝ) ^ ((4 : ℝ) * ((B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε)) : ℕ) : ℝ)))⁻¹ ^ 2) ≤
      ε ^ 2 := by
  set s : ℕ := B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε)) with hs
  set t : ℝ := (4 : ℝ) * (s : ℝ) with ht
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hlog2 : (2 : ℝ) ≤ 8 * Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    nlinarith

  have hinv : (((2 : ℝ) ^ t)⁻¹ ^ 2) = (2 : ℝ) ^ (-2 * t) := by
    have hneg : (2 : ℝ) ^ (-t) = ((2 : ℝ) ^ t)⁻¹ := Real.rpow_neg h2pos.le t
    calc
      (((2 : ℝ) ^ t)⁻¹ ^ 2) = ((2 : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ t)⁻¹ := by ring
      _ = (2 : ℝ) ^ (-t) * (2 : ℝ) ^ (-t) := by rw [← hneg]
      _ = (2 : ℝ) ^ (-t + -t) := (Real.rpow_add h2pos _ _).symm
      _ = (2 : ℝ) ^ (-2 * t) := by rw [show -t + -t = -2 * t by ring]
  rw [hinv]

  have hsplit : (2 : ℝ) ^ (-2 * t) =
      (2 : ℝ) ^ (-8 * (B : ℝ)) *
        ((2 : ℝ) ^ (-8 * (Nat.clog 2 d : ℝ)) * (2 : ℝ) ^ (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ))) := by
    have hcast : (s : ℝ) = (B : ℝ) + (Nat.clog 2 d : ℝ) + (Nat.ceil (Real.log (1 / ε)) : ℝ) := by
      rw [hs]
      simp
    rw [ht, hcast]
    have h1 : -2 * ((4 : ℝ) * ((B : ℝ) + (Nat.clog 2 d : ℝ) + (Nat.ceil (Real.log (1 / ε)) : ℝ))) =
        -8 * (B : ℝ) + (-8 * (Nat.clog 2 d : ℝ)) + (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ)) := by
      ring
    rw [h1, Real.rpow_add h2pos, Real.rpow_add h2pos]
    ring
  rw [hsplit]

  have hB : (2 : ℝ) ^ (-8 * (B : ℝ)) ≤ 1 := by
    have hexp : -8 * (B : ℝ) ≤ (0 : ℝ) := by
      have : (0 : ℝ) ≤ B := by exact_mod_cast Nat.zero_le B
      nlinarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    simpa [Real.rpow_zero] using! h
  have hclog : (2 : ℝ) ^ (-8 * (Nat.clog 2 d : ℝ)) ≤ (d : ℝ)⁻¹ := by
    have hclog0 : (0 : ℝ) ≤ Nat.clog 2 d := by exact_mod_cast Nat.zero_le _
    have hexp : -8 * (Nat.clog 2 d : ℝ) ≤ -(Nat.clog 2 d : ℝ) := by nlinarith
    have hmono : (2 : ℝ) ^ (-8 * (Nat.clog 2 d : ℝ)) ≤ (2 : ℝ) ^ (-(Nat.clog 2 d : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hpow : (2 : ℝ) ^ (-(Nat.clog 2 d : ℝ)) = ((2 : ℝ) ^ (Nat.clog 2 d : ℝ))⁻¹ :=
      Real.rpow_neg h2pos.le _
    have hle : (d : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 d : ℝ) := by
      have h := Nat.le_pow_clog (show (1 : ℕ) < 2 by norm_num) d
      rw [Real.rpow_natCast]
      exact_mod_cast h
    have hle' : ((2 : ℝ) ^ (Nat.clog 2 d : ℝ))⁻¹ ≤ (d : ℝ)⁻¹ := by
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have hpow0 : 0 < (2 : ℝ) ^ (Nat.clog 2 d : ℝ) := Real.rpow_pos_of_pos h2pos _
      exact (inv_le_inv₀ hpow0 hdpos).mpr hle
    exact (hmono.trans hpow.le).trans hle'
  have hL : (2 : ℝ) ^ (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ)) ≤ ε ^ (8 * Real.log 2) := by
    have hlog : Real.log (1 / ε) ≤ (Nat.ceil (Real.log (1 / ε)) : ℝ) := Nat.le_ceil _
    have hlog1 : Real.log (1 / ε) = -Real.log ε := by
      rw [Real.log_div (by norm_num) (ne_of_gt hε), Real.log_one, zero_sub]
    have hexp : -8 * (Nat.ceil (Real.log (1 / ε)) : ℝ) ≤ -8 * Real.log (1 / ε) := by
      nlinarith
    have hmono : (2 : ℝ) ^ (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ)) ≤
        (2 : ℝ) ^ (-8 * Real.log (1 / ε)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hcore : (2 : ℝ) ^ (-8 * Real.log (1 / ε)) = ε ^ (8 * Real.log 2) := by
      rw [hlog1]
      have hexp' : -8 * -Real.log ε = 8 * Real.log ε := by ring
      rw [hexp']
      have ha : (2 : ℝ) ^ (8 * Real.log ε) = Real.exp (Real.log 2 * (8 * Real.log ε)) :=
        Real.rpow_def_of_pos h2pos _
      have hb : ε ^ (8 * Real.log 2) = Real.exp (Real.log ε * (8 * Real.log 2)) :=
        Real.rpow_def_of_pos hε _
      rw [ha, hb]
      congr 1
      ring
    exact hmono.trans (le_of_eq hcore)

  have hmul : (2 : ℝ) ^ (-8 * (B : ℝ)) *
      ((2 : ℝ) ^ (-8 * (Nat.clog 2 d : ℝ)) * (2 : ℝ) ^ (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ))) ≤
      1 * ((d : ℝ)⁻¹ * ε ^ (8 * Real.log 2)) := by
    have hinner : (2 : ℝ) ^ (-8 * (Nat.clog 2 d : ℝ)) *
        (2 : ℝ) ^ (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ)) ≤
        (d : ℝ)⁻¹ * ε ^ (8 * Real.log 2) :=
      mul_le_mul hclog hL (Real.rpow_nonneg (by norm_num) _)
        (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le d))
    have houter : (2 : ℝ) ^ (-8 * (B : ℝ)) *
        ((2 : ℝ) ^ (-8 * (Nat.clog 2 d : ℝ)) * (2 : ℝ) ^ (-8 * (Nat.ceil (Real.log (1 / ε)) : ℝ))) ≤
        1 * ((d : ℝ)⁻¹ * ε ^ (8 * Real.log 2)) :=
      mul_le_mul hB hinner
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))
        (by norm_num)
    exact houter
  have hle2 : ((d : ℝ) / 2) * (1 * ((d : ℝ)⁻¹ * ε ^ (8 * Real.log 2))) ≤ ε ^ 2 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hrew : (d : ℝ) / 2 * (1 * ((d : ℝ)⁻¹ * ε ^ (8 * Real.log 2))) =
        (1 / 2 : ℝ) * ε ^ (8 * Real.log 2) := by
      field_simp
    rw [hrew]
    have hpow : ε ^ (8 * Real.log 2) ≤ ε ^ 2 := by
      rw [← Real.rpow_natCast ε 2]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hlog2
    have hstep : (1 / 2 : ℝ) * ε ^ (8 * Real.log 2) ≤ (1 / 2 : ℝ) * ε ^ 2 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hstep2 : (1 / 2 : ℝ) * ε ^ 2 ≤ ε ^ 2 := by
      have : (0 : ℝ) ≤ ε ^ 2 := by positivity
      nlinarith
    exact hstep.trans hstep2
  have hhalf : (0 : ℝ) ≤ (d : ℝ) / 2 := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast Nat.zero_le d
    positivity
  exact (mul_le_mul_of_nonneg_left hmul hhalf).trans hle2

/-- Constructs a dyadic approximation to a unit vector with squared error at most `ε^2`, norm
error at most `ε`, and witnesses for the stated resource bounds and ledger composition. -/
theorem clause50 :
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (d B : ℕ) (v : Fin d → ℂ) (ε : ℝ),
      0 < d →
      (∑ i : Fin d, Complex.normSq (v i) = 1) →
      (∀ i : Fin d,
        ∃ q : Fin 2 → ℚ,
          |(q 0 : ℝ) - (v i).re| ≤ (2 : ℝ) ^ (-((B : ℝ))) ∧
          |(q 1 : ℝ) - (v i).im| ≤ (2 : ℝ) ^ (-((B : ℝ)))) →
      0 < ε → ε ≤ 1 →
      ∃ (vhat : Fin d → ℂ) (led : QsvtCostLedger),
        (∀ i : Fin d,
          ∃ p : Fin 2 → ℤ,
            (vhat i).re = (p 0 : ℝ) / (2 : ℝ) ^ (C * (B + Nat.clog 2 d +
              Nat.ceil (Real.log (1 / ε)))) ∧
            (vhat i).im = (p 1 : ℝ) / (2 : ℝ) ^ (C * (B + Nat.clog 2 d +
              Nat.ceil (Real.log (1 / ε))))) ∧
        (∑ i : Fin d, Complex.normSq (vhat i - v i)) ≤ ε ^ 2 ∧
        abs (Real.sqrt (∑ i : Fin d, Complex.normSq (vhat i)) - 1) ≤ ε ∧
        led.elementaryGates ≤
          C * d * (B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε))) ^ 2 ∧
        led.integerBitTime ≤
          C * d * (B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε))) ^ 3 ∧
        led.peakWorkspace ≤ C * (Nat.clog 2 d + B) ∧
        (∀ (m : ℕ) (ledWord : QsvtCostLedger),
          ∃ ledTot : QsvtCostLedger,
            ledTot.dataQueries = led.dataQueries + m ∧
            ledTot.adjointQueries = led.adjointQueries + m ∧
            ledTot.elementaryGates =
              led.elementaryGates + ledWord.elementaryGates ∧
            ledTot.integerBitTime = led.integerBitTime + ledWord.integerBitTime ∧
            ledTot.peakWorkspace = max led.peakWorkspace ledWord.peakWorkspace) := by
  refine ⟨4, by norm_num, ?_⟩
  intro d B v ε hd hsum happrox hε0 hε1
  set s : ℕ := B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε)) with hs
  set t : ℝ := (4 : ℝ) * (s : ℝ) with ht
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2t : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos h2pos t
  have hround : ∀ x : ℝ, ∃ k : ℤ, |x - (k : ℝ) / (2 : ℝ) ^ t| ≤ ((2 : ℝ) ^ t)⁻¹ / 2 :=
    fun x => dyadic_round_near x t
  have hkr : ∀ i : Fin d, ∃ k : ℤ, |(v i).re - (k : ℝ) / (2 : ℝ) ^ t| ≤ ((2 : ℝ) ^ t)⁻¹ / 2 :=
    fun i => hround _
  have hki : ∀ i : Fin d, ∃ k : ℤ, |(v i).im - (k : ℝ) / (2 : ℝ) ^ t| ≤ ((2 : ℝ) ^ t)⁻¹ / 2 :=
    fun i => hround _
  choose kr hk2 using hkr
  choose ki hki2 using hki
  set vhat : Fin d → ℂ := (fun i => Complex.mk ((kr i : ℝ) / (2 : ℝ) ^ t)
    ((ki i : ℝ) / (2 : ℝ) ^ t)) with hvhat
  have hre : ∀ i : Fin d, |(vhat i - v i).re| ≤ ((2 : ℝ) ^ t)⁻¹ / 2 := by
    intro i
    have h1 : (vhat i).re = (kr i : ℝ) / (2 : ℝ) ^ t := by rw [hvhat]
    rw [Complex.sub_re, h1, abs_sub_comm]
    exact hk2 i
  have him : ∀ i : Fin d, |(vhat i - v i).im| ≤ ((2 : ℝ) ^ t)⁻¹ / 2 := by
    intro i
    have h1 : (vhat i).im = (ki i : ℝ) / (2 : ℝ) ^ t := by rw [hvhat]
    rw [Complex.sub_im, h1, abs_sub_comm]
    exact hki2 i
  have herr : ∀ i : Fin d,
      Complex.normSq (vhat i - v i) ≤ (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 + (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 := by
    intro i
    have hre2 : ((vhat i - v i).re) ^ 2 ≤ (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 := by
      have hnn : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹ / 2 := by positivity
      exact (sq_le_sq).mpr (by simpa [abs_of_nonneg hnn] using! hre i)
    have him2 : ((vhat i - v i).im) ^ 2 ≤ (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 := by
      have hnn : (0 : ℝ) ≤ ((2 : ℝ) ^ t)⁻¹ / 2 := by positivity
      exact (sq_le_sq).mpr (by simpa [abs_of_nonneg hnn] using! him i)
    rw [Complex.normSq_apply]
    nlinarith
  have hsum2 : (∑ i : Fin d, Complex.normSq (vhat i - v i)) ≤ ε ^ 2 := by
    have hle2c : ∀ i : Fin d, Complex.normSq (vhat i - v i) ≤ 2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 := by
      intro i
      have h := herr i
      have heq : (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 + (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 =
          2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 := by ring
      exact heq ▸ h
    have hsumle : (∑ i : Fin d, Complex.normSq (vhat i - v i))
        ≤ ∑ _i : Fin d, 2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2 :=
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d => Complex.normSq (vhat i - v i))
        (g := fun _ : Fin d => 2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2) (fun i _ => hle2c i)
    have hsumg : (∑ _i : Fin d, 2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2) =
        (d : ℝ) * (2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hrew : (d : ℝ) * (2 * (((2 : ℝ) ^ t)⁻¹ / 2) ^ 2) = (d / 2 : ℝ) * (((2 : ℝ) ^ t)⁻¹ ^ 2) := by
      field_simp
    have hstep : (∑ i : Fin d, Complex.normSq (vhat i - v i))
        ≤ (d / 2 : ℝ) * (((2 : ℝ) ^ t)⁻¹ ^ 2) := by
      rw [← hrew, ← hsumg]
      exact hsumle
    have hte : t = (4 : ℝ) * ((B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε)) : ℕ) : ℝ) := by
      rw [ht, hs]
    calc
      (∑ i : Fin d, Complex.normSq (vhat i - v i)) ≤ (d / 2 : ℝ) * (((2 : ℝ) ^ t)⁻¹ ^ 2) := hstep
      _ = (d / 2 : ℝ) *
          (((2 : ℝ) ^ ((4 : ℝ) * ((B + Nat.clog 2 d + Nat.ceil (Real.log (1 / ε)) : ℕ) : ℝ)))⁻¹ ^ 2) := by
        rw [hte]
      _ ≤ ε ^ 2 := clause59_rounding_budget d B ε hd hε0 hε1
  have hnorm : abs (Real.sqrt (∑ i : Fin d, Complex.normSq (vhat i)) - 1) ≤ ε := by
    set x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 vhat
    set y : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v
    have hx : ‖x‖ = Real.sqrt (∑ i : Fin d, Complex.normSq (vhat i)) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_norm_sq]
    have hy : ‖y‖ = Real.sqrt (∑ i : Fin d, Complex.normSq (v i)) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_norm_sq]
    have hy1 : ‖y‖ = 1 := by
      rw [hy, hsum, Real.sqrt_one]
    have hxy : ‖x - y‖ = Real.sqrt (∑ i : Fin d, Complex.normSq (vhat i - v i)) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [Complex.normSq_eq_norm_sq, WithLp.ofLp_sub]; rfl
    have htri : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
    have hsqrt : Real.sqrt (∑ i : Fin d, Complex.normSq (vhat i - v i)) ≤ ε := by
      have h := Real.sqrt_le_sqrt hsum2
      rwa [Real.sqrt_sq (le_of_lt hε0)] at h
    have hfinal : |‖x‖ - ‖y‖| ≤ ε := htri.trans (hxy.le.trans hsqrt)
    rw [← hx, ← hy1]
    exact hfinal
  refine ⟨vhat, ⟨0, 0, 0, 0, 0, 0, 0⟩, ?_, hsum2, hnorm, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨![kr i, ki i], ?_, ?_⟩
    · have h1 : (vhat i).re = (kr i : ℝ) / (2 : ℝ) ^ t := by rw [hvhat]
      have h2 : (![kr i, ki i] 0 : ℤ) = kr i := by simp
      rw [h1, h2, ht, hs]
      simp
    · have h1 : (vhat i).im = (ki i : ℝ) / (2 : ℝ) ^ t := by rw [hvhat]
      have h2 : (![kr i, ki i] 1 : ℤ) = ki i := by simp
      rw [h1, h2, ht, hs]
      simp
  · simp; positivity
  · simp; positivity
  · simp; positivity
  · intro m ledWord
    refine ⟨⟨m, m, 0, 0, ledWord.elementaryGates, ledWord.integerBitTime,
      ledWord.peakWorkspace⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp

/-- The sum of entry norms in a row is at most its sparsity bound when every entry has norm at
most one. -/
theorem sparse_row_norm_sum_le {d s : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hs : 0 < s) (hrow : ∀ i : Fin d,
      (Finset.univ.filter (fun j : Fin d => A i j ≠ 0)).card ≤ s)
    (hentry : ∀ i j : Fin d, ‖A i j‖ ≤ 1) (i : Fin d) :
    (∑ j : Fin d, ‖A i j‖) ≤ (s : ℝ) := by
  let t := Finset.univ.filter (fun j : Fin d => A i j ≠ 0)
  have hsplit : (∑ j : Fin d, ‖A i j‖) = ∑ j ∈ t, ‖A i j‖ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro j _ hj
    have hz : A i j = 0 := by simpa [t] using! hj
    simp [hz]
  rw [hsplit]
  calc
    (∑ j ∈ t, ‖A i j‖) ≤ ∑ _j ∈ t, (1 : ℝ) :=
      Finset.sum_le_sum fun j _ => hentry i j
    _ = (t.card : ℝ) := by simp
    _ ≤ (s : ℝ) := by exact_mod_cast hrow i

/-- The sum of entry norms in a column is at most its sparsity bound when every entry has norm
at most one. -/
theorem sparse_col_norm_sum_le {d s : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hs : 0 < s) (hcol : ∀ j : Fin d,
      (Finset.univ.filter (fun i : Fin d => A i j ≠ 0)).card ≤ s)
    (hentry : ∀ i j : Fin d, ‖A i j‖ ≤ 1) (j : Fin d) :
    (∑ i : Fin d, ‖A i j‖) ≤ (s : ℝ) := by
  let t := Finset.univ.filter (fun i : Fin d => A i j ≠ 0)
  have hsplit : (∑ i : Fin d, ‖A i j‖) = ∑ i ∈ t, ‖A i j‖ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hj
    have hz : A i j = 0 := by simpa [t] using! hj
    simp [hz]
  rw [hsplit]
  calc
    (∑ i ∈ t, ‖A i j‖) ≤ ∑ _i ∈ t, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hentry i j
    _ = (t.card : ℝ) := by simp
    _ ≤ (s : ℝ) := by exact_mod_cast hcol j

/-- For a sparse contraction satisfying the stated coefficient approximation assumptions,
constructs isometries whose overlap is `A / s` and a cost ledger satisfying the stated
bounds. -/
theorem clause53 :
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (d s b : ℕ) (A : Matrix (Fin d) (Fin d) ℂ),
      0 < d → 0 < s → 0 < b →
      (∀ i : Fin d,
        (Finset.univ.filter (fun j : Fin d => A i j ≠ 0)).card ≤ s) ∧
      (∀ j : Fin d,
        (Finset.univ.filter (fun i : Fin d => A i j ≠ 0)).card ≤ s) ∧
      (∀ i j : Fin d,
        ∃ q : Fin 2 → ℚ,
          |(q 0 : ℝ) - (A i j).re| ≤ (2 : ℝ) ^ (-((b : ℝ))) ∧
          |(q 1 : ℝ) - (A i j).im| ≤ (2 : ℝ) ^ (-((b : ℝ)))) ∧
      ‖A‖ ≤ 1 →
      (∃ (H : Type) (_ : Fintype H) (L R : Matrix H (Fin d) ℂ),
        Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L ∧ Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R ∧
          Lᴴ * R = ((s : ℂ)⁻¹ • A)) ∧
      (∃ led : QsvtCostLedger,
        led.dataQueries ≤ C * s ∧
        led.adjointQueries ≤ C * s ∧
        led.projectorNots ≤ C * s ∧
        led.phaseGates ≤ C * s * (b + Nat.clog 2 (d + 2)) ∧
        led.elementaryGates ≤ C * s * (b + Nat.clog 2 (d + 2)) ^ 2 ∧
        led.integerBitTime ≤ C * s * (b + Nat.clog 2 (d + 2)) ^ 3 ∧
        led.peakWorkspace ≤ C * (Nat.clog 2 (d + 2) + b)) := by
  refine ⟨1, le_refl _, ?_⟩
  intro d s b A hd hs hb hhyp
  obtain ⟨hrow, hcol, _happrox, hnorm⟩ := hhyp
  have hentry : ∀ i j : Fin d, ‖A i j‖ ≤ 1 := fun i j =>
    entry_norm_le_l2_opNorm A i j hnorm
  have hrowsum : ∀ o : Fin d, (∑ i : Fin d, ‖A o i‖) ≤ (s : ℝ) :=
    fun o => sparse_row_norm_sum_le A hs hrow hentry o
  have hcolsum : ∀ i : Fin d, (∑ o : Fin d, ‖A o i‖) ≤ (s : ℝ) :=
    fun i => sparse_col_norm_sum_le A hs hcol hentry i
  have hreals : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨hL, hR, hcorner⟩ :=
    sparse_overlap_actual_frames_and_corner (Fin d) (Fin d) A (s : ℝ) hreals hrowsum hcolsum
  have hcorner' : (sparseOverlapLeft A (s : ℝ))ᴴ * sparseOverlapRight A (s : ℝ) =
      ((s : ℂ)⁻¹ • A) := by
    have hsC : (((s : ℕ) : ℝ) : ℂ) = ((s : ℕ) : ℂ) := by simp
    rw [hcorner, hsC]
  refine ⟨⟨_, _, _, _, hL, hR, hcorner'⟩, ?_⟩
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (simp; try positivity)

/-- Outside the unit interval on the positive side, a Chebyshev polynomial evaluates as `cosh (n
* arcosh x)`. -/
theorem eval_T_real_eq_cosh {n : ℤ} {x : ℝ} (hx : 1 ≤ x) :
    (Polynomial.Chebyshev.T ℝ n).eval x = Real.cosh ((n : ℝ) * Real.arcosh x) := by
  have h := Polynomial.Chebyshev.T_real_cosh (Real.arcosh x) n
  rw [Real.cosh_arcosh hx] at h
  exact h

/-- The real absolute value of the integer sign power is one. -/
theorem abs_negOnePow_natCast (n : ℕ) : |(((n : ℤ).negOnePow : ℝ))| = 1 := by
  rw [Int.cast_negOnePow_natCast ℝ n]
  simp

/-- For `|z| ≥ 1`, the absolute value of a Chebyshev evaluation at `z` equals its evaluation at
`|z|`. -/
theorem abs_eval_T_real_eq_eval_abs {n : ℕ} {z : ℝ} (hz : 1 ≤ |z|) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z| =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |z| := by
  rcases le_or_gt 0 z with h | h
  · rw [abs_of_nonneg h] at hz
    rw [abs_of_nonneg h]
    exact abs_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1)
      (Polynomial.Chebyshev.one_le_eval_T_real (n : ℤ) hz))
  · rw [abs_of_neg h] at hz
    have hz' : z = -(-z : ℝ) := (neg_neg z).symm
    conv_lhs => rw [hz']
    rw [Polynomial.Chebyshev.T_eval_neg, abs_mul, abs_negOnePow_natCast, one_mul,
      abs_of_neg h]
    exact abs_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1)
      (Polynomial.Chebyshev.one_le_eval_T_real (n : ℤ) hz))

/-- A real polynomial of degree at most `n` bounded by one on `[-1, 1]` is bounded outside that
interval by the degree-`n` Chebyshev polynomial. -/
theorem abs_eval_T_real_le_eval_of_one_le {n : ℕ} {P : Polynomial ℝ}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    |P.eval y| ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval y := by
  have h1 : (Polynomial.derivative^[0] P).eval y ≤
      (Polynomial.derivative^[0] (Polynomial.Chebyshev.T ℝ (n : ℤ))).eval y :=
    Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) hy
      hPdeg hPbnd
  have hneg : (-P).degree ≤ n := by rwa [Polynomial.degree_neg]
  have hnb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(-P).eval x| ≤ 1 := by
    intro x hx
    rw [Polynomial.eval_neg]
    simpa using! hPbnd x hx
  have h2 : (Polynomial.derivative^[0] (-P)).eval y ≤
      (Polynomial.derivative^[0] (Polynomial.Chebyshev.T ℝ (n : ℤ))).eval y :=
    Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) hy
      hneg hnb
  simp only [Function.iterate_zero_apply] at h1 h2
  rw [abs_le]
  constructor
  · rw [Polynomial.eval_neg] at h2
    linarith
  · exact h1

/-- A Chebyshev polynomial of natural order is monotone on `[1, ∞)`. -/
theorem eval_T_real_mono {n : ℕ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x ≤
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval y := by
  rw [eval_T_real_eq_cosh hx, eval_T_real_eq_cosh (le_trans hx hxy)]
  have hnn : (0:ℝ) ≤ (n : ℝ) * Real.arcosh x := by
    exact mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg (by linarith))
  have hcmp : (n : ℝ) * Real.arcosh x ≤ (n : ℝ) * Real.arcosh y := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact (Real.arcosh_le_arcosh (by linarith : (0:ℝ) < x) (by linarith)).2 hxy
  have hxy' : |(n : ℝ) * Real.arcosh x| ≤ |(n : ℝ) * Real.arcosh y| := by
    rw [abs_of_nonneg hnn, abs_of_nonneg (le_trans hnn hcmp)]
    exact hcmp
  exact Real.cosh_le_cosh.2 hxy'

/-- For `0 ≤ x < 1`, the exponential is bounded by `1 / (1 - x)`. -/
theorem exp_le_one_div_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 0 < (1 - x : ℝ) := by linarith
  have h2 := Real.one_sub_le_exp_neg x
  have h3 : Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos x))
  have h4 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; simp
  rw [le_div_iff₀ h1]
  linarith

/-- For `0 < δ < 1`, `sqrt δ` is bounded by `arcosh (1 / (1 - δ))`. -/
theorem dolph_cosh_sqrt_le (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Real.sqrt δ ≤ Real.arcosh (1 / (1 - δ)) := by
  have h1 : 0 < (1 - δ : ℝ) := by linarith
  have h2 : 0 ≤ δ := le_of_lt hδ0
  have h3 : Real.cosh (Real.sqrt δ) ≤ Real.exp ((Real.sqrt δ) ^ 2 / 2) :=
    Real.cosh_le_exp_half_sq _
  have h4 : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt h2
  rw [h4] at h3
  have h5 : Real.exp (δ / 2) ≤ 1 / (1 - δ / 2) :=
    exp_le_one_div_one_sub (by linarith) (by linarith)
  have h7 : 1 / (1 - δ / 2 : ℝ) ≤ 1 / (1 - δ) := by
    refine one_div_le_one_div_of_le ?_ ?_
    · linarith
    · linarith
  have h8 : Real.cosh (Real.sqrt δ) ≤ 1 / (1 - δ) :=
    le_trans (le_trans h3 h5) h7
  have h9 : Real.arcosh (Real.cosh (Real.sqrt δ)) = Real.sqrt δ :=
    Real.arcosh_cosh (Real.sqrt_nonneg δ)
  have h10 : Real.arcosh (Real.cosh (Real.sqrt δ)) ≤ Real.arcosh (1 / (1 - δ)) := by
    refine (Real.arcosh_le_arcosh ?_ ?_).2 h8
    · exact Real.cosh_pos _
    · exact one_div_pos.mpr h1
  rw [← h9]
  exact h10

/-- For `0 < ε < 1`, `arcosh (1 / ε)` is bounded by `log (2 / ε)`. -/
theorem arcosh_inv_le_log_two_div {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Real.arcosh (1 / ε) ≤ Real.log (2 / ε) := by
  have h1 : 0 < (1 / ε : ℝ) := one_div_pos.mpr hε0
  have h2 : Real.sqrt ((1 / ε) ^ 2 - 1) ≤ 1 / ε := by
    have h2a : 0 ≤ ((1 / ε : ℝ) ^ 2 - 1) := by
      have : (1:ℝ) ≤ 1 / ε := (one_le_div₀ hε0).mpr (le_of_lt hε1)
      nlinarith
    have h2b : ((1 / ε : ℝ) ^ 2 - 1) ≤ (1 / ε) ^ 2 := by nlinarith
    calc Real.sqrt ((1 / ε) ^ 2 - 1) ≤ Real.sqrt ((1 / ε) ^ 2) := Real.sqrt_le_sqrt h2b
      _ = 1 / ε := Real.sqrt_sq (le_of_lt h1)
  have h2c : (2 : ℝ) / ε = 1 / ε + 1 / ε := by ring
  have h4 : 0 < (1 / ε : ℝ) + Real.sqrt ((1 / ε) ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg h1 (Real.sqrt_nonneg _)
  have h5 : (1 / ε : ℝ) + Real.sqrt ((1 / ε) ^ 2 - 1) ≤ 2 / ε := by
    rw [h2c]; linarith
  show Real.log (1 / ε + Real.sqrt ((1 / ε) ^ 2 - 1)) ≤ Real.log (2 / ε)
  exact Real.log_le_log h4 h5

/-- The scaled Dolph–Chebyshev polynomial is bounded by `ε` on `[-1 + δ, 1 - δ]` when its degree
meets the logarithmic width bound. -/
theorem dolph_flat_of_le_half_width {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) (hn : 0 < n)
    (hlog : Real.log (2 / ε) / Real.sqrt δ ≤ (n : ℝ)) :
    let c := Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε))
    let Pε : Polynomial ℝ :=
      Polynomial.C ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
        (Polynomial.C c * Polynomial.X)
    ∀ x ∈ Set.Icc (-1 + δ : ℝ) (1 - δ), |Pε.eval x| ≤ ε := by
  intro c Pε x hx
  have hnpos : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have h1ε : (1:ℝ) ≤ 1 / ε := (one_le_div₀ hε0).mpr (le_of_lt hε1)
  have harc : Real.arcosh (1 / ε) ≤ Real.log (2 / ε) :=
    arcosh_inv_le_log_two_div hε0 hε1
  have hhalf : Real.sqrt δ ≤ Real.arcosh (1 / (1 - δ)) :=
    dolph_cosh_sqrt_le δ hδ0 hδ1
  have hchain : Real.arcosh (1 / ε) ≤ (n : ℝ) * Real.sqrt δ := by
    have h1 : Real.log (2 / ε) ≤ (n : ℝ) * Real.sqrt δ := by
      have := (div_le_iff₀ hsq).mp hlog
      linarith
    linarith
  have hmul : (n : ℝ) * Real.sqrt δ ≤ (n : ℝ) * Real.arcosh (1 / (1 - δ)) :=
    mul_le_mul_of_nonneg_left hhalf (le_of_lt hnpos)
  have hle : Real.arcosh (1 / ε) ≤ (n : ℝ) * Real.arcosh (1 / (1 - δ)) := by
    linarith
  have harg0 : 0 ≤ (1 / (n : ℝ)) * Real.arcosh (1 / ε) :=
    mul_nonneg (one_div_nonneg.mpr (le_of_lt hnpos)) (Real.arcosh_nonneg h1ε)
  have harcc : Real.arcosh c = (1 / (n : ℝ)) * Real.arcosh (1 / ε) := by
    show Real.arcosh (Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε))) = _
    exact Real.arcosh_cosh harg0
  have hcle : c ≤ 1 / (1 - δ) := by
    have h1 : Real.arcosh c ≤ Real.arcosh (1 / (1 - δ)) := by
      rw [harcc]
      have h2 : (1 / (n : ℝ)) * Real.arcosh (1 / ε) = Real.arcosh (1 / ε) / (n : ℝ) := by ring
      rw [h2]
      have h3 : Real.arcosh (1 / ε) / (n : ℝ) ≤ Real.arcosh (1 / (1 - δ)) := by
        rw [div_le_iff₀ hnpos, mul_comm]
        exact hle
      exact h3
    have h2 : 0 < 1 / (1 - δ) := one_div_pos.mpr (by linarith)
    have h3 : 0 < c := Real.cosh_pos _
    exact (Real.arcosh_le_arcosh h3 h2).1 h1
  have hPε : Pε.eval x = ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c * x) := by
    show (Polynomial.C ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
        (Polynomial.C c * Polynomial.X)).eval x = _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
  have hcx : |c * x| ≤ 1 := by
    have hcpos : 0 < c := Real.cosh_pos _
    rw [abs_mul, abs_of_nonneg (le_of_lt hcpos)]
    have hxb : |x| ≤ 1 - δ := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have h1 : c * |x| ≤ c * (1 - δ) := mul_le_mul_of_nonneg_left hxb (le_of_lt hcpos)
    have h2 : c * (1 - δ) ≤ 1 / (1 - δ) * (1 - δ) :=
      mul_le_mul_of_nonneg_right hcle (by linarith)
    have h3 : 1 / (1 - δ) * (1 - δ) = 1 := by
      rw [one_div_mul_cancel (by linarith : (1 - δ : ℝ) ≠ 0)]
    linarith
  have hT : |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c * x)| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hcx
  rw [hPε, abs_mul, abs_of_nonneg (le_of_lt hε0)]
  nlinarith

/-- Constructs normalized Dolph–Chebyshev polynomials with the stated flatness bound, proves the
corresponding optimal interval-width bound, and gives a logarithmic degree cutoff. -/
theorem clause44 :

  (∀ (ε : ℝ) (n : ℕ), 0 < ε → ε < 1 → 0 < n →
    let c := Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε))
    let Pε : Polynomial ℝ :=
      Polynomial.C ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
        (Polynomial.C c * Polynomial.X)
    Pε.natDegree = n ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pε.eval x| ≤ 1) ∧
      Pε.eval 1 = 1 ∧ Pε.eval (-1) = (-1 : ℝ) ^ n ∧
      (∀ x : ℝ, |x| ≤ 1 / c → |Pε.eval x| ≤ ε)) ∧

  (∀ (ε : ℝ) (n : ℕ) (Q : Polynomial ℝ) (lam : ℝ),
    0 < ε → ε < 1 → 0 < n →
    Q.natDegree ≤ n →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Q.eval x| ≤ 1) →
    Q.eval 1 = 1 → Q.eval (-1) = (-1 : ℝ) ^ n →
    (∀ x : ℝ, |x| ≤ lam → |Q.eval x| ≤ ε) →
    lam ≤ 1 / Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε))) ∧

  (∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∃ n : ℕ, 0 < n ∧
      n ≤ Nat.ceil (Real.log (2 / ε) / Real.sqrt δ) ∧
      (let c := Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε))
       let Pε : Polynomial ℝ :=
         Polynomial.C ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
           (Polynomial.C c * Polynomial.X)
       ∀ x ∈ Set.Icc (-1 + δ : ℝ) (1 - δ), |Pε.eval x| ≤ ε)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ε n hε hε1 hn c Pε
    have hc : c = Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) := rfl
    have hnpos : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hεne : ε ≠ 0 := ne_of_gt hε
    have h1ε : (1:ℝ) ≤ 1 / ε := (one_le_div₀ hε).mpr (le_of_lt hε1)
    have harcpos : 0 < Real.arcosh (1 / ε) :=
      Real.arcosh_pos (by
        have : (1:ℝ) < 1 / ε := (one_lt_div₀ hε).mpr (by linarith)
        exact this)
    have hargpos : (0:ℝ) < (1 / (n : ℝ)) * Real.arcosh (1 / ε) :=
      mul_pos (one_div_pos.mpr hnpos) harcpos
    have hc1 : 1 < c := by
      rw [hc]
      exact Real.one_lt_cosh.mpr (ne_of_gt hargpos)
    have hcpos : 0 < c := by linarith
    have hcnz : c ≠ 0 := ne_of_gt hcpos
    have harcc : Real.arcosh c = (1 / (n : ℝ)) * Real.arcosh (1 / ε) := by
      rw [hc]
      exact Real.arcosh_cosh (le_of_lt hargpos)
    have hTc : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval c = 1 / ε := by
      rw [eval_T_real_eq_cosh (le_of_lt hc1)]
      rw [harcc]
      have hnn : ((n : ℤ) : ℝ) * ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) = Real.arcosh (1 / ε) := by
        rw [Int.cast_natCast, ← mul_assoc, mul_one_div_cancel (ne_of_gt hnpos), one_mul]
      rw [hnn, Real.cosh_arcosh h1ε]
    have hPeval : ∀ x : ℝ, Pε.eval x = ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c * x) := by
      intro x
      show (Polynomial.C ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
          (Polynomial.C c * Polynomial.X)).eval x = _
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (Polynomial.C ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
        (Polynomial.C c * Polynomial.X)).natDegree = n
      rw [Polynomial.natDegree_C_mul hεne, Polynomial.natDegree_comp,
        Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast,
        Polynomial.natDegree_C_mul hcnz, Polynomial.natDegree_X, mul_one]
    · intro x hx
      rw [hPeval x, abs_mul, abs_of_nonneg (le_of_lt hε)]
      have hcx : |c * x| ≤ c := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hcpos)]
        have : |x| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hx.1, hx.2]
        nlinarith
      by_cases hsmall : |c * x| ≤ 1
      · have hT : |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c * x)| ≤ 1 :=
          Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hsmall
        nlinarith
      · push Not at hsmall
        have hT : |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c * x)| =
            (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |c * x| :=
          abs_eval_T_real_eq_eval_abs (le_of_lt hsmall)
        have hmono : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |c * x| ≤
            (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval c :=
          eval_T_real_mono (le_of_lt hsmall) hcx
        rw [hT]
        have h1 : ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |c * x| ≤
            ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval c :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hε)
        rw [hTc, mul_one_div_cancel hεne] at h1
        exact h1
    · rw [hPeval 1, mul_one, hTc]
      field_simp
    · have hneg : c * (-1 : ℝ) = -c := mul_neg_one c
      rw [hPeval (-1), hneg, Polynomial.Chebyshev.T_eval_neg, hTc]
      have hnp : (((n : ℤ).negOnePow : ℝ)) = (-1 : ℝ) ^ n :=
        Int.cast_negOnePow_natCast ℝ n
      rw [hnp]
      have h1 : ε * (((-1 : ℝ) ^ n) * (1 / ε)) = (-1 : ℝ) ^ n := by
        rw [mul_left_comm, mul_one_div_cancel hεne, mul_one]
      exact h1
    · intro x hx
      rw [hPeval x, abs_mul, abs_of_nonneg (le_of_lt hε)]
      have hcx : |c * x| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hcpos)]
        have hxb : |x| ≤ 1 / c := hx
        have h1 : c * |x| ≤ c * (1 / c) := mul_le_mul_of_nonneg_left hxb (le_of_lt hcpos)
        rw [mul_one_div_cancel hcnz] at h1
        exact h1
      have hT : |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c * x)| ≤ 1 :=
        Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hcx
      nlinarith
  · intro ε n Q lam hε hε1 hn hQdeg hQbnd hQ1 hQm1 hQflat
    have hnpos : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hεne : ε ≠ 0 := ne_of_gt hε
    have h1ε : (1:ℝ) ≤ 1 / ε := (one_le_div₀ hε).mpr (le_of_lt hε1)
    have hcpos : 0 < Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) := Real.cosh_pos _
    by_cases hlam0 : lam ≤ 0
    · have : (0:ℝ) < 1 / Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) :=
        one_div_pos.mpr hcpos
      linarith
    · push Not at hlam0
      by_cases hlam1 : 1 ≤ lam
      · have h := hQflat 1 (by rw [abs_one]; exact hlam1)
        rw [hQ1] at h
        simp at h
        linarith
      · push Not at hlam1
        have hlam1' : (1:ℝ) ≤ 1 / lam := (one_le_div₀ hlam0).mpr (le_of_lt hlam1)
        set R : Polynomial ℝ := Q.comp (Polynomial.C lam * Polynomial.X) with hRdef
        have hRdeg : R.degree ≤ n := by
          apply le_trans Polynomial.degree_le_natDegree
          have h1 : (Q.comp (Polynomial.C lam * Polynomial.X)).natDegree
              = Q.natDegree * (Polynomial.C lam * Polynomial.X).natDegree :=
            Polynomial.natDegree_comp
          rw [hRdef, h1, Polynomial.natDegree_C_mul (ne_of_gt hlam0),
            Polynomial.natDegree_X, mul_one]
          exact_mod_cast hQdeg
        have hRbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |R.eval x| ≤ ε := by
          intro x hx
          rw [hRdef, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          have h2 : |lam * x| ≤ lam := by
            rw [abs_mul, abs_of_nonneg (le_of_lt hlam0)]
            have : |x| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith [hx.1, hx.2]
            nlinarith
          exact hQflat (lam * x) h2
        set S : Polynomial ℝ := Polynomial.C (1 / ε) * R with hSdef
        have hSdeg : S.degree ≤ n := by
          rw [hSdef, Polynomial.degree_C_mul (one_div_ne_zero hεne)]
          exact hRdeg
        have hSbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |S.eval x| ≤ 1 := by
          intro x hx
          rw [hSdef, Polynomial.eval_mul, Polynomial.eval_C, abs_mul,
            abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hε))]
          have hR := hRbnd x hx
          have h1 : (1 / ε) * |R.eval x| ≤ (1 / ε) * ε :=
            mul_le_mul_of_nonneg_left hR (one_div_nonneg.mpr (le_of_lt hε))
          rw [one_div_mul_cancel hεne] at h1
          exact h1
        have hSval : S.eval (1 / lam) = 1 / ε := by
          rw [hSdef, Polynomial.eval_mul, Polynomial.eval_C]
          have h2 : R.eval (1 / lam) = Q.eval 1 := by
            rw [hRdef, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X]
            congr 1
            exact mul_one_div_cancel (ne_of_gt hlam0)
          rw [h2, hQ1]
          ring
        have hgrow : |S.eval (1 / lam)| ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (1 / lam) :=
          abs_eval_T_real_le_eval_of_one_le hSdeg hSbnd hlam1'
        rw [hSval, abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hε))] at hgrow
        have hTlam : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (1 / lam)
            = Real.cosh ((n : ℝ) * Real.arcosh (1 / lam)) :=
          eval_T_real_eq_cosh hlam1'
        rw [hTlam, ← Real.cosh_arcosh h1ε] at hgrow
        have hnn : 0 ≤ Real.arcosh (1 / ε) := Real.arcosh_nonneg h1ε
        have hnn2 : 0 ≤ (n : ℝ) * Real.arcosh (1 / lam) :=
          mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg hlam1')
        have hargs : Real.arcosh (1 / ε) ≤ (n : ℝ) * Real.arcosh (1 / lam) := by
          have := Real.cosh_le_cosh.1 hgrow
          rwa [abs_of_nonneg hnn, abs_of_nonneg hnn2] at this
        have hdiv : Real.arcosh (1 / ε) / (n : ℝ) ≤ Real.arcosh (1 / lam) := by
          rw [div_le_iff₀ hnpos, mul_comm]
          exact hargs
        have harg0 : 0 ≤ (1 / (n : ℝ)) * Real.arcosh (1 / ε) :=
          mul_nonneg (one_div_nonneg.mpr (le_of_lt hnpos)) hnn
        have harcc : Real.arcosh (Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)))
            = (1 / (n : ℝ)) * Real.arcosh (1 / ε) :=
          Real.arcosh_cosh harg0
        have hcle : Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) ≤ 1 / lam := by
          have h1 : Real.arcosh (Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)))
              ≤ Real.arcosh (1 / lam) := by
            rw [harcc]
            have h2 : (1 / (n : ℝ)) * Real.arcosh (1 / ε)
                = Real.arcosh (1 / ε) / (n : ℝ) := by ring
            rw [h2]
            exact hdiv
          have h2 : 0 < 1 / lam := one_div_pos.mpr hlam0
          exact (Real.arcosh_le_arcosh hcpos h2).1 h1
        have hgoal : lam ≤ 1 / Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) := by
          rw [le_div_iff₀ hcpos]
          have h1 : lam * Real.cosh ((1 / (n : ℝ)) * Real.arcosh (1 / ε)) ≤ lam * (1 / lam) :=
            mul_le_mul_of_nonneg_left hcle (le_of_lt hlam0)
          rw [mul_one_div_cancel (ne_of_gt hlam0)] at h1
          exact h1
        exact hgoal
  · intro ε δ hε hε1 hδ hδ1
    have hlog : 0 < Real.log (2 / ε) := by
      apply Real.log_pos
      have : (1:ℝ) < 2 / ε := by
        rw [lt_div_iff₀ hε]
        linarith
      exact this
    have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    have hdiv : 0 < Real.log (2 / ε) / Real.sqrt δ := div_pos hlog hsq
    refine ⟨Nat.ceil (Real.log (2 / ε) / Real.sqrt δ), ?_, ?_, ?_⟩
    · exact Nat.ceil_pos.mpr hdiv
    · exact le_rfl
    · exact dolph_flat_of_le_half_width hε hε1 hδ hδ1
        (Nat.ceil (Real.log (2 / ε) / Real.sqrt δ)) (Nat.ceil_pos.mpr hdiv)
        (Nat.le_ceil _)

/-- An angle phase equals the complex exponential `exp (θ * i)`. -/
theorem anglePhase_eq_exp (θ : ℝ) : anglePhase θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  have h2 : (Complex.cos θ + Complex.sin θ * Complex.I : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im]
      ring
    · rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im]
      ring
  rw [← Complex.cos_add_sin_I θ, h2]
  rfl

/-- The distance between two angle phases is bounded by the absolute difference of their angles. -/
theorem anglePhase_sub_le (φ ψ : ℝ) : ‖anglePhase φ - anglePhase ψ‖ ≤ |φ - ψ| := by
  rw [anglePhase_eq_exp φ, anglePhase_eq_exp ψ]
  exact norm_exp_mul_I_sub_le φ ψ

/-- Rounds a real angle down to the grid of integer multiples of `2^(-b)`. -/
noncomputable def dyadicRound (b : ℕ) (ψ : ℝ) : ℝ :=
  (Int.floor (ψ * (2 : ℝ) ^ b) : ℝ) / (2 : ℝ) ^ b

/-- The dyadically rounded angle is an integer multiple of `2^(-b)`. -/
theorem dyadicRound_int (b : ℕ) (ψ : ℝ) :
    ∃ k : ℤ, dyadicRound b ψ = (k : ℝ) / (2 : ℝ) ^ b :=
  ⟨Int.floor (ψ * (2 : ℝ) ^ b), rfl⟩

/-- Dyadic rounding fixes zero. -/
theorem dyadicRound_zero (b : ℕ) : dyadicRound b 0 = 0 := by
  simp [dyadicRound]

/-- Dyadic rounding changes an angle by at most `2^(-b)`. -/
theorem dyadicRound_near (b : ℕ) (ψ : ℝ) :
    |dyadicRound b ψ - ψ| ≤ (2 : ℝ) ^ (-((b : ℝ))) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hk1 : (Int.floor (ψ * (2 : ℝ) ^ b) : ℝ) ≤ ψ * (2 : ℝ) ^ b := Int.floor_le _
  have hk2 : ψ * (2 : ℝ) ^ b < (Int.floor (ψ * (2 : ℝ) ^ b) : ℝ) + 1 := Int.lt_floor_add_one _
  have habs : |(Int.floor (ψ * (2 : ℝ) ^ b) : ℝ) - ψ * (2 : ℝ) ^ b| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hdiv : dyadicRound b ψ - ψ =
      ((Int.floor (ψ * (2 : ℝ) ^ b) : ℝ) - ψ * (2 : ℝ) ^ b) / (2 : ℝ) ^ b := by
    unfold dyadicRound
    field_simp
  have hstep : |dyadicRound b ψ - ψ| ≤ 1 / (2 : ℝ) ^ b := by
    rw [hdiv, abs_div, abs_of_pos hpow]
    have := div_le_div_of_nonneg_right habs (le_of_lt hpow)
    simpa using! this
  have hconv : (1 : ℝ) / (2 : ℝ) ^ b = (2 : ℝ) ^ (-((b : ℝ))) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div]
  rw [hconv] at hstep
  exact hstep

/-- For positive `n`, `(n + 1) * 3^n` is bounded by `16^n`. -/
theorem mul_tri_pow_le_pow16 : ∀ n : ℕ, 1 ≤ n → (n + 1) * 3 ^ n ≤ 16 ^ n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
    intro h
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      norm_num
    · have ih' := ih (by omega)
      have h3 : (n + 1 + 1) * 3 ^ (n + 1) = 3 * (n + 2) * 3 ^ n := by
        rw [pow_succ]
        ring
      have h16 : 16 ^ (n + 1) = 16 * 16 ^ n := by
        rw [pow_succ]
        ring
      rw [show n + 1 + 1 = n + 2 by omega, h3, h16]
      have hlin : 3 * (n + 2) ≤ 16 * (n + 1) := by omega
      have h3n : (0 : ℕ) ≤ 3 ^ n := Nat.zero_le _
      calc
        3 * (n + 2) * 3 ^ n ≤ 16 * (n + 1) * 3 ^ n := Nat.mul_le_mul_right _ hlin
        _ = 16 * ((n + 1) * 3 ^ n) := by ring
        _ ≤ 16 * 16 ^ n := Nat.mul_le_mul_left _ ih'

/-- On the complex unit disk, a polynomial evaluation is bounded in norm by its coefficient
mass. -/
theorem coeffMass_eval_le (p : Polynomial ℂ) (x : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖p.eval x‖ ≤ Qatlib.Concepts.NativeNumerics.PhaseSynthesis.coeffMass p := by
  have hsum := Polynomial.eval_eq_sum_range' (n := p.natDegree + 1)
    (p.natDegree.lt_succ_self) x
  have hm :=
      Qatlib.Concepts.NativeNumerics.PhaseSynthesis.coeffMass_range p (p.natDegree + 1)
      (p.natDegree.lt_succ_self)
  rw [hsum, hm]
  calc
    ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i‖
        ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * x ^ i‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖x‖ ^ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg x) hx) (norm_nonneg _)
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ := by simp

/-- The specified bit precision makes the coefficient stability budget at most `ε`. -/
theorem clause49_stability_budget (n B : ℕ) (ε : ℝ) (b : ℕ) (hn : 0 < n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : b = 4 * (n + B + Nat.ceil (Real.log (1 / ε)))) :
    (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) * (2 : ℝ) ^ (-((b : ℝ))) ≤ ε := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hlog2 : (4 : ℝ) * Real.log 2 ≥ 1 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    nlinarith
  have hbc : (b : ℝ) = 4 * ((n : ℝ) + B + Nat.ceil (Real.log (1 / ε))) := by
    simp [hb]
  rw [hbc]
  have hsplit : (2 : ℝ) ^ (-(4 * ((n : ℝ) + B + Nat.ceil (Real.log (1 / ε))))) =
      (2 : ℝ) ^ (-(4 * (n : ℝ))) *
        ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) := by
    have h1 : -(4 * ((n : ℝ) + B + Nat.ceil (Real.log (1 / ε)))) =
        -(4 * (n : ℝ)) + -(4 * (B : ℝ)) + -(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)) := by
      ring
    rw [h1, Real.rpow_add h2pos, Real.rpow_add h2pos]
    ring
  rw [hsplit]
  have hB : (2 : ℝ) ^ (-(4 * (B : ℝ))) ≤ 1 := by
    have hexp : -(4 * (B : ℝ)) ≤ (0 : ℝ) := by
      have : (0 : ℝ) ≤ B := by exact_mod_cast Nat.zero_le B
      nlinarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    simpa [Real.rpow_zero] using! h
  have hn2 : (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) * (2 : ℝ) ^ (-(4 * (n : ℝ))) ≤ 1 := by
    have hcore : (2 : ℝ) ^ ((4 : ℝ) * (n : ℝ)) = (16 ^ n : ℝ) := by
      have ha : (2 : ℝ) ^ ((4 : ℝ) * (n : ℝ)) = ((2 : ℝ) ^ (4 : ℝ)) ^ (n : ℝ) :=
        Real.rpow_mul h2pos.le _ _
      have hc : (((2 : ℝ) ^ (4 : ℝ)) ^ (n : ℝ)) = (((2 : ℝ) ^ 4) ^ n : ℝ) := by
        have h : ((2 : ℝ) ^ (4 : ℝ)) = ((2 : ℝ) ^ 4) := Real.rpow_natCast 2 4
        rw [h, Real.rpow_natCast]
      rw [ha, hc]
      norm_num
    have hneg : (2 : ℝ) ^ (-(4 * (n : ℝ))) = ((16 ^ n : ℝ))⁻¹ := by
      rw [Real.rpow_neg h2pos.le, hcore]
    rw [hneg]
    have hcast : (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) = ((n + 1) * 3 ^ n : ℕ) := rfl
    have htri := mul_tri_pow_le_pow16 n hn
    have hpos : (0 : ℝ) < 16 ^ n := by positivity
    have hdiv : (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) / (16 ^ n : ℝ) ≤ 1 := by
      rw [div_le_one hpos]
      exact_mod_cast htri
    have hmul : (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) * ((16 ^ n : ℝ))⁻¹
        = (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) / (16 ^ n : ℝ) := by
      rw [div_eq_mul_inv]
    rw [hmul]
    exact hdiv
  have hL : (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ))) ≤ ε := by
    have hlog : Real.log (1 / ε) ≤ (Nat.ceil (Real.log (1 / ε)) : ℝ) := Nat.le_ceil _
    have hlog1 : Real.log (1 / ε) = -Real.log ε := by
      rw [Real.log_div (by norm_num) (ne_of_gt hε), Real.log_one, zero_sub]
    have hexp : -(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)) ≤ -(4 * Real.log (1 / ε)) := by
      nlinarith
    have hmono : (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ))) ≤
        (2 : ℝ) ^ (-(4 * Real.log (1 / ε))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hcore : (2 : ℝ) ^ (-(4 * Real.log (1 / ε))) = ε ^ (4 * Real.log 2) := by
      rw [hlog1]
      have hexp' : -(4 * -Real.log ε) = 4 * Real.log ε := by ring
      rw [hexp']
      have ha : (2 : ℝ) ^ (4 * Real.log ε) = Real.exp (Real.log 2 * (4 * Real.log ε)) :=
        Real.rpow_def_of_pos h2pos _
      have hb' : ε ^ (4 * Real.log 2) = Real.exp (Real.log ε * (4 * Real.log 2)) :=
        Real.rpow_def_of_pos hε _
      rw [ha, hb']
      congr 1
      ring
    have hpow : ε ^ (4 * Real.log 2) ≤ ε ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 hlog2
    have h1 : ε ^ (1 : ℝ) = ε := Real.rpow_one _
    calc
      (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))
          ≤ (2 : ℝ) ^ (-(4 * Real.log (1 / ε))) := hmono
      _ = ε ^ (4 * Real.log 2) := hcore
      _ ≤ ε ^ (1 : ℝ) := hpow
      _ = ε := h1
  have hprod : (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) *
      ((2 : ℝ) ^ (-(4 * (n : ℝ))) *
        ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ))))) ≤ ε := by
    have hrearr : (((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) *
        ((2 : ℝ) ^ (-(4 * (n : ℝ))) *
          ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ))))) =
        ((((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) * (2 : ℝ) ^ (-(4 * (n : ℝ)))) *
          ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) := by
      ring
    rw [hrearr]
    have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ))) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    have hle1 : ((((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) * (2 : ℝ) ^ (-(4 * (n : ℝ)))) *
        ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) ≤
        1 * ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hn2 hnn
    have hle2 : (1 : ℝ) *
        ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) ≤
        1 * (1 * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (by norm_num) _))
        (by norm_num)
    have hle3 : (1 : ℝ) * (1 * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) ≤ ε := by
      simp only [one_mul]
      exact hL
    calc
      ((((n + 1 : ℕ) * 3 ^ n : ℕ) : ℝ) * (2 : ℝ) ^ (-(4 * (n : ℝ)))) *
          ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) ≤
        (1 : ℝ) * ((2 : ℝ) ^ (-(4 * (B : ℝ))) * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) :=
        hle1
      _ ≤ (1 : ℝ) * (1 * (2 : ℝ) ^ (-(4 * (Nat.ceil (Real.log (1 / ε)) : ℝ)))) := hle2
      _ ≤ ε := hle3
  exact hprod

/-- For a positive-degree polynomial satisfying `Cor8Admissible` and the rational coefficient
size bound, constructs exact and dyadically rounded phase lists whose response polynomials
differ by at most `ε` on `[-1, 1]`. -/
theorem clause49 :
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : Polynomial ℂ) (n B : ℕ) (ε : ℝ),
      0 < n → P.natDegree = n → Cor8Admissible P n →
      (∀ i ≤ n,
        ∃ qre qim : ℚ,
          (qre : ℝ) = (P.coeff i).re ∧ (qim : ℝ) = (P.coeff i).im ∧
          qre.num.natAbs.size + qre.den.size +
            qim.num.natAbs.size + qim.den.size ≤ B) →
      0 < ε → ε ≤ 1 →
      ∃ (b : ℕ) (Φ Φ₀ : List ℝ) (cert : Polynomial ℂ),
        b ≤ C * (n + B + Nat.ceil (Real.log (1 / ε))) ∧
        Φ.length = n ∧ Φ₀.length = n ∧
        sourcePhaseResponse Φ₀ = P ∧
        (∀ φ ∈ Φ, ∃ k : ℤ, φ = (k : ℝ) / (2 : ℝ) ^ b) ∧
        (∀ φ ∈ Φ, ∃ ψ ∈ Φ₀, |φ - ψ| ≤ (2 : ℝ) ^ (-((b : ℝ)))) ∧
        sourcePhaseResponse Φ = cert ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          ‖cert.eval (x : ℂ) - P.eval (x : ℂ)‖ ≤ ε) := by
  refine ⟨4, by norm_num, ?_⟩
  intro P n B ε hn hdeg hadm happrox hε0 hε1
  obtain ⟨Φ₀, hΦ₀len, hΦ₀eq, _⟩ :=
    Qatlib.Concepts.QsvtCore.PhaseExistence.corollary8ComplexPhaseExistence
      P n hn hdeg hadm.parity hadm.interval hadm.exterior hadm.imaginaryAxis
  set b : ℕ := 4 * (n + B + Nat.ceil (Real.log (1 / ε))) with hb
  set Φ : List ℝ := Φ₀.map (dyadicRound b) with hΦ
  set cert : Polynomial ℂ := sourcePhaseResponse Φ with hcert
  have hΦlen : Φ.length = n := by rw [hΦ, List.length_map]; exact hΦ₀len
  refine ⟨b, Φ, Φ₀, cert, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hb, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  · exact hΦlen
  · exact hΦ₀len
  · exact hΦ₀eq
  · intro φ hφ
    rw [hΦ] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
    exact dyadicRound_int b ψ
  · intro φ hφ
    rw [hΦ] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
    exact ⟨ψ, hψ, dyadicRound_near b ψ⟩
  · exact hcert.symm
  · intro x hx
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    have hxnorm : ‖(x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hx1
    have heval : cert.eval (x : ℂ) - P.eval (x : ℂ) = (cert - P).eval (x : ℂ) :=
      (Polynomial.eval_sub cert P (x : ℂ)).symm
    have hcertdeg : cert.natDegree ≤ n := by
      have h := (response_degree 1 (Φ.map anglePhase)).1
      have hl : (Φ.map anglePhase).length = n := by
        rw [List.length_map]
        exact hΦlen
      have hceq : cert.natDegree = (responseP 1 (Φ.map anglePhase)).natDegree := rfl
      rw [hceq]
      exact h.trans hl.le
    have hsubdeg : (cert - P).natDegree < n + 1 := by
      have h1 : (cert - P).natDegree ≤ max cert.natDegree P.natDegree :=
        Polynomial.natDegree_sub_le cert P
      omega
    have hmass : Qatlib.Concepts.NativeNumerics.PhaseSynthesis.coeffMass (cert - P) =
        ∑ i ∈ Finset.range (n + 1), ‖cert.coeff i - P.coeff i‖ := by
      rw [Qatlib.Concepts.NativeNumerics.PhaseSynthesis.coeffMass_range (cert - P) (n + 1) hsubdeg]
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.coeff_sub]
    have hdelta : (0 : ℝ) ≤ (2 : ℝ) ^ (-((b : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hbase : ‖((1 : ℂ) : ℂ) - 1‖ ≤ (2 : ℝ) ^ (-((b : ℝ))) := by
      simp only [sub_self, norm_zero]
      exact Real.rpow_nonneg (by norm_num) _
    have h10 : anglePhase 0 = 1 := by
      rw [anglePhase_eq_exp]
      simp
    have hentry : ∀ i < n,
        ‖(Φ.map anglePhase).getD i 1 - (Φ₀.map anglePhase).getD i 1‖ ≤
          (2 : ℝ) ^ (-((b : ℝ))) := by
      intro i hi
      have hzs : (Φ.map anglePhase).getD i 1 = anglePhase (Φ.getD i 0) := by
        have h : (Φ.map anglePhase).getD i 1 =
            (Φ.map anglePhase).getD i (anglePhase 0) := by rw [h10]
        exact h.trans (List.getD_map Φ 0 (f := anglePhase) (n := i))
      have hws : (Φ₀.map anglePhase).getD i 1 = anglePhase (Φ₀.getD i 0) := by
        have h : (Φ₀.map anglePhase).getD i 1 =
            (Φ₀.map anglePhase).getD i (anglePhase 0) := by rw [h10]
        exact h.trans (List.getD_map Φ₀ 0 (f := anglePhase) (n := i))
      rw [hzs, hws]
      have hΦget : Φ.getD i 0 = dyadicRound b (Φ₀.getD i 0) := by
        have h : (Φ₀.map (dyadicRound b)).getD i 0 =
            (Φ₀.map (dyadicRound b)).getD i (dyadicRound b 0) := by
          rw [dyadicRound_zero]
        rw [hΦ]
        exact h.trans (List.getD_map Φ₀ 0 (f := dyadicRound b) (n := i))
      have habs : |Φ.getD i 0 - Φ₀.getD i 0| ≤ (2 : ℝ) ^ (-((b : ℝ))) := by
        rw [hΦget]
        exact dyadicRound_near b (Φ₀.getD i 0)
      exact (anglePhase_sub_le (Φ.getD i 0) (Φ₀.getD i 0)).trans habs
    have hlip0 :=
      Qatlib.Concepts.NativeNumerics.PhaseSynthesis.response_coefficients_derived_lipschitz n (1 : ℂ) (1 : ℂ)
        (Φ.map anglePhase) (Φ₀.map anglePhase) ((2 : ℝ) ^ (-((b : ℝ))))
        (by rw [List.length_map]; exact hΦlen)
        (by rw [List.length_map]; exact hΦ₀len)
        (by simp [IsPhase]) (by simp [IsPhase])
        (by intro z hz; obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hz; exact anglePhase_isPhase φ)
        (by intro w hw; obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hw; exact anglePhase_isPhase φ)
        hdelta hbase hentry
    have hbridge1 : (responseP 1 (Φ.map anglePhase)) = cert := rfl
    have hbridge2 : (responseP 1 (Φ₀.map anglePhase)) = P := by
      have : (responseP 1 (Φ₀.map anglePhase)) = sourcePhaseResponse Φ₀ := rfl
      rw [this, hΦ₀eq]
    have hlip : (∑ i ∈ Finset.range (n + 1), ‖cert.coeff i - P.coeff i‖) ≤
        (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseConstant n : ℝ) * (2 : ℝ) ^ (-((b : ℝ))) := by
      rw [← hbridge1, ← hbridge2]
      exact hlip0
    have hpc :
        (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseConstant n : ℝ) =
        (((n + 1) * 3 ^ n : ℕ) : ℝ) := rfl
    have hst : (Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseConstant n : ℝ) * (2 : ℝ) ^ (-((b : ℝ))) ≤ ε := by
      rw [hpc]
      exact clause49_stability_budget n B ε b hn hε0 hε1 hb
    calc
      ‖cert.eval (x : ℂ) - P.eval (x : ℂ)‖ = ‖(cert - P).eval (x : ℂ)‖ := by rw [heval]
      _ ≤ Qatlib.Concepts.NativeNumerics.PhaseSynthesis.coeffMass (cert - P) := coeffMass_eval_le (cert - P) (x : ℂ) hxnorm
      _ = ∑ i ∈ Finset.range (n + 1), ‖cert.coeff i - P.coeff i‖ := hmass
      _ ≤ ε := hlip.trans hst

end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt

namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel

/-- The integral Bessel coefficient `(1 / π) * ∫₀^π cos (mθ - u sin θ) dθ`. -/
noncomputable def besselInt (m : ℕ) (u : ℝ) : ℝ :=
  (1 / Real.pi) * intervalIntegral
    (fun θ => Real.cos ((m : ℝ) * θ - u * Real.sin θ)) 0 Real.pi MeasureTheory.volume

/-- The cosine kernel defining `besselInt` is even in its integration variable. -/
theorem besselInt_kernel_even (m : ℕ) (u : ℝ) (θ : ℝ) :
    Real.cos ((m : ℝ) * (-θ) - u * Real.sin (-θ))
      = Real.cos ((m : ℝ) * θ - u * Real.sin θ) := by
  have h : (m : ℝ) * (-θ) - u * Real.sin (-θ) = -((m : ℝ) * θ - u * Real.sin θ) := by
    rw [Real.sin_neg]
    ring
  rw [h, Real.cos_neg]

/-- The integral Bessel coefficient equals the symmetrized cosine integral over `[-π, π]`
divided by `2π`. -/
theorem besselInt_eq_symm (m : ℕ) (u : ℝ) :
    besselInt m u = (1 / (2 * Real.pi)) * intervalIntegral
      (fun θ => Real.cos ((m : ℝ) * θ - u * Real.sin θ)) (-Real.pi) Real.pi
      MeasureTheory.volume := by
  set f : ℝ → ℝ := fun θ => Real.cos ((m : ℝ) * θ - u * Real.sin θ) with hf
  have heven : ∀ θ : ℝ, f (-θ) = f θ := fun θ => besselInt_kernel_even m u θ
  have hcomp' : ∫ x in -Real.pi..0, f ((-1 : ℝ) * x)
      = ((-1 : ℝ)⁻¹) • ∫ x in Real.pi..0, f x := by
    have h := intervalIntegral.integral_comp_mul_left (f := f) (c := (-1 : ℝ))
      (a := -Real.pi) (b := 0) (by norm_num : (-1 : ℝ) ≠ 0)
    have hb1 : (-1 : ℝ) * (-Real.pi) = Real.pi := by ring
    have hb2 : (-1 : ℝ) * 0 = 0 := by ring
    rw [hb1, hb2] at h
    exact h
  have hL : ∫ x in -Real.pi..0, f ((-1 : ℝ) * x) = ∫ x in -Real.pi..0, f x := by
    apply intervalIntegral.integral_congr
    intro x _
    show f ((-1 : ℝ) * x) = f x
    rw [show (-1 : ℝ) * x = -x from by ring, heven]
  have hR : ((-1 : ℝ)⁻¹ : ℝ) • ∫ x in Real.pi..0, f x = ∫ x in 0..Real.pi, f x := by
    rw [show ((-1 : ℝ)⁻¹) = (-1 : ℝ) from by ring, neg_one_smul,
      intervalIntegral.integral_symm, neg_neg]
  have hneg : ∫ θ in (-Real.pi)..0, f θ = ∫ θ in 0..Real.pi, f θ := by
    rw [← hL, hcomp', hR]
  have hcont : Continuous f := by
    unfold f
    fun_prop
  have hII : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hsum : ∫ θ in (-Real.pi)..Real.pi, f θ
      = (∫ θ in (-Real.pi)..0, f θ) + ∫ θ in 0..Real.pi, f θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := f) (a := -Real.pi) (b := 0) (c := Real.pi)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hshow : ∫ θ in (-Real.pi)..Real.pi, f θ
      = 2 * ∫ θ in 0..Real.pi, f θ := by
    rw [hsum, hneg]
    ring
  unfold besselInt
  rw [hf, hshow]
  ring

/-- The integral of the integer Fourier exponential over `[-π, π]` is `2π` in mode zero and zero
otherwise. -/
theorem integral_exp_int_mul (n : ℤ) :
    intervalIntegral (fun θ : ℝ =>
        Complex.exp (Complex.I * ((((n : ℝ) * θ : ℝ)) : ℂ)))
      (-Real.pi) Real.pi MeasureTheory.volume
      = if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    have h0 : (fun θ : ℝ => Complex.exp (Complex.I * ((((((0 : ℤ) : ℝ) * θ : ℝ)) : ℂ))))
        = fun _ => (1 : ℂ) := by
      funext θ
      simp
    rw [h0, intervalIntegral.integral_const, sub_neg_eq_add,
      Complex.real_smul, mul_one]
    push_cast
    ring
  · simp only [if_neg hn]
    have hc : Complex.I * ((n : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
    have hform : ∀ θ : ℝ, Complex.exp (Complex.I * ((((n : ℝ) * θ : ℝ) : ℂ)))
        = Complex.exp ((Complex.I * ((n : ℝ) : ℂ)) * θ) := by
      intro θ
      congr 1
      push_cast
      ring
    have hcongr : intervalIntegral
        (fun θ : ℝ => Complex.exp (Complex.I * ((((n : ℝ) * θ : ℝ) : ℂ))))
        (-Real.pi) Real.pi MeasureTheory.volume
        = intervalIntegral
          (fun x : ℝ => Complex.exp ((Complex.I * ((n : ℝ) : ℂ)) * x))
          (-Real.pi) Real.pi MeasureTheory.volume :=
      intervalIntegral.integral_congr (fun x _ => hform x)
    rw [hcongr]
    have h := integral_exp_mul_complex (c := Complex.I * ((n : ℝ) : ℂ))
      (a := -Real.pi) (b := Real.pi) hc
    rw [h]
    have he1 : Complex.exp ((Complex.I * ((n : ℝ) : ℂ)) * Real.pi)
        = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
      have hE : (Complex.I * ((n : ℝ) : ℂ)) * Real.pi
          = ((((n : ℝ) * Real.pi : ℝ) : ℂ)) * Complex.I := by
        push_cast
        ring
      rw [hE, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hcos : Real.cos ((n : ℝ) * Real.pi) = (-1 : ℝ) ^ n :=
        Real.cos_int_mul_pi n
      have hsin : Real.sin ((n : ℝ) * Real.pi) = 0 :=
        Real.sin_int_mul_pi n
      rw [hcos, hsin]
      push_cast
      ring
    have he2 : Complex.exp ((Complex.I * ((n : ℝ) : ℂ)) * (((-Real.pi : ℝ) : ℂ)))
        = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
      have hE : (Complex.I * ((n : ℝ) : ℂ)) * (((-Real.pi : ℝ) : ℂ))
          = (((-(n : ℝ) * Real.pi : ℝ) : ℂ)) * Complex.I := by
        push_cast
        ring
      rw [hE, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hcos : Real.cos (-(n : ℝ) * Real.pi) = (-1 : ℝ) ^ n := by
        rw [neg_mul, Real.cos_neg]
        exact Real.cos_int_mul_pi n
      have hsin : Real.sin (-(n : ℝ) * Real.pi) = 0 := by
        rw [neg_mul, Real.sin_neg]
        have h := Real.sin_int_mul_pi n
        linarith
      rw [hcos, hsin]
      push_cast
      ring
    rw [he1, he2, sub_self, zero_div]

/-- Expresses the real sine as a difference of two complex exponentials. -/
theorem sin_eq_exp_sub (θ : ℝ) :
    ((Real.sin θ : ℝ) : ℂ)
      = (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))
          - Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))) / (2 * Complex.I) := by
  rw [Complex.ofReal_sin]
  have h1 : Complex.exp (Complex.I * ((θ : ℝ) : ℂ))
      = Complex.cos ((θ : ℝ) : ℂ) + Complex.sin ((θ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
  have h2 : Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))
      = Complex.cos ((θ : ℝ) : ℂ) - Complex.sin ((θ : ℝ) : ℂ) * Complex.I := by
    have hh : -(Complex.I * ((θ : ℝ) : ℂ)) = ((-(θ : ℝ) : ℂ)) * Complex.I := by
      ring
    rw [hh, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]
  field_simp
  ring

/-- The complex exponential has its usual factorial power series. -/
private theorem cexp_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (((n.factorial : ℕ) : ℂ))) (Complex.exp z) := by
  have hsum : Summable (fun n : ℕ => z ^ n / (((n.factorial : ℕ) : ℂ))) :=
    NormedSpace.expSeries_div_summable z (𝔸 := ℂ)
  have h1 : Filter.Tendsto
      (fun n : ℕ => ∑ m ∈ Finset.range n, z ^ m / (((m.factorial : ℕ) : ℂ)))
      Filter.atTop (nhds ((Complex.exp' z).lim)) :=
    (Complex.exp' z).tendsto_limit
  rw [Complex.exp_def]
  have h2 := hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique h1 h2 ▸ hsum.hasSum

/-- The product of opposite Fourier exponentials with the indicated powers is the Fourier mode
`2m - k`. -/
private theorem exp_pow_mul_exp_pow (θ : ℝ) (k m : ℕ) (hm : m ≤ k) :
    Complex.exp (Complex.I * ((θ : ℝ) : ℂ)) ^ m
      * Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ))) ^ (k - m)
      = Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ)))) := by
  have h1 : Complex.exp (Complex.I * ((θ : ℝ) : ℂ)) ^ m
      = Complex.exp (((m : ℂ)) * (Complex.I * ((θ : ℝ) : ℂ))) := by
    rw [← Complex.exp_nat_mul]
  have h2 : Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ))) ^ (k - m)
      = Complex.exp (((((k - m : ℕ) : ℂ)) * (-(Complex.I * ((θ : ℝ) : ℂ))))) := by
    rw [← Complex.exp_nat_mul]
  rw [h1, h2, ← Complex.exp_add]
  congr 1
  have hkm : (((k - m : ℕ) : ℤ)) = ((k : ℤ) - (m : ℤ)) := by
    omega
  have hcast1 : ((m : ℂ)) = ((((m : ℤ) : ℝ) : ℂ)) := by
    rfl
  have hcast2 : (((((k - m : ℕ) : ℂ))) = ((((((k - m : ℕ) : ℤ) : ℝ) : ℂ)))) := by
    rfl
  rw [hcast1, hcast2, hkm]
  push_cast
  ring

/-- Expands a natural power of sine as a finite binomial sum of complex Fourier exponentials. -/
theorem sin_pow_eq_exp_sum (θ : ℝ) (k : ℕ) :
    (((Real.sin θ : ℝ) : ℂ)) ^ k
      = (((2 * Complex.I) : ℂ)⁻¹) ^ k *
        ∑ m ∈ Finset.range (k + 1),
          ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
            * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ))))) := by
  have hsin := sin_eq_exp_sub θ
  rw [hsin, div_pow]
  have hconv : (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))
        - Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))) ^ k / (2 * Complex.I) ^ k
      = (((2 * Complex.I) : ℂ)⁻¹) ^ k *
        (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))
          - Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))) ^ k := by
    rw [div_eq_mul_inv, inv_pow, mul_comm]
  rw [hconv]
  congr 1
  rw [sub_pow]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ k := by
    have := Finset.mem_range.mp hm
    omega
  have hexp := exp_pow_mul_exp_pow θ k m hm'
  calc (-1 : ℂ) ^ (m + k) * Complex.exp (Complex.I * ((θ : ℝ) : ℂ)) ^ m
        * Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ))) ^ (k - m) * ((k.choose m : ℕ) : ℂ)
      = (-1 : ℂ) ^ (m + k) *
          (Complex.exp (Complex.I * ((θ : ℝ) : ℂ)) ^ m
            * Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ))) ^ (k - m))
          * ((k.choose m : ℕ) : ℂ) := by
        ring
    _ = (-1 : ℂ) ^ (m + k)
          * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ))))
          * ((k.choose m : ℕ) : ℂ) := by
        rw [hexp]
    _ = (-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
          * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ)))) := by
        ring

/-- The integral of a continuous odd complex function over `[-π, π]` is zero. -/
theorem intervalIntegral_odd_zero (f : ℝ → ℂ) (hcont : Continuous f)
    (hodd : ∀ θ : ℝ, f (-θ) = -f θ) :
    intervalIntegral f (-Real.pi) Real.pi MeasureTheory.volume = 0 := by
  have hcomp : ∫ x in -Real.pi..0, f ((-1 : ℝ) * x)
      = ((-1 : ℝ)⁻¹ : ℝ) • ∫ x in Real.pi..0, f x := by
    have h := intervalIntegral.integral_comp_mul_left (f := f) (c := (-1 : ℝ))
      (a := -Real.pi) (b := 0) (by norm_num : (-1 : ℝ) ≠ 0)
    have hb1 : (-1 : ℝ) * (-Real.pi) = Real.pi := by ring
    have hb2 : (-1 : ℝ) * 0 = 0 := by ring
    rw [hb1, hb2] at h
    exact h
  have hL : ∫ x in -Real.pi..0, f ((-1 : ℝ) * x) = -∫ x in -Real.pi..0, f x := by
    have hEq : ∫ x in -Real.pi..0, f ((-1 : ℝ) * x) = ∫ x in -Real.pi..0, -f x := by
      apply intervalIntegral.integral_congr
      intro x _
      show f ((-1 : ℝ) * x) = -f x
      rw [show (-1 : ℝ) * x = -x from by ring, hodd]
    rw [hEq, intervalIntegral.integral_neg]
  have hneg : ∫ θ in (-Real.pi)..0, f θ = -∫ θ in 0..Real.pi, f θ := by
    have h1 : ∫ x in -Real.pi..0, f x = -∫ x in -Real.pi..0, f ((-1 : ℝ) * x) := by
      rw [hL, neg_neg]
    rw [h1, hcomp, show ((-1 : ℝ)⁻¹) = (-1 : ℝ) from by ring, neg_one_smul,
      intervalIntegral.integral_symm]
    ring
  have hsum : ∫ θ in (-Real.pi)..Real.pi, f θ
      = (∫ θ in (-Real.pi)..0, f θ) + ∫ θ in 0..Real.pi, f θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := f) (a := -Real.pi) (b := 0) (c := Real.pi)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  rw [hsum, hneg]
  abel

/-- Evaluates the integral of a Fourier exponential times a sine power as a finite binomial sum,
retaining only the zero Fourier mode. -/
theorem integral_exp_sin_pow (r k : ℕ) :
    intervalIntegral (fun θ : ℝ =>
        Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
          * (((Real.sin θ : ℝ) : ℂ)) ^ k)
      (-Real.pi) Real.pi MeasureTheory.volume
      = (((2 * Complex.I) : ℂ)⁻¹) ^ k *
        ∑ m ∈ Finset.range (k + 1),
          ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
            * (if (r + 2 * m : ℤ) = (k : ℤ) then (2 * Real.pi : ℂ) else 0)) := by
  have hdist : ∀ θ : ℝ,
      Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
        * (((Real.sin θ : ℝ) : ℂ)) ^ k
      = (((2 * Complex.I) : ℂ)⁻¹) ^ k *
        ∑ m ∈ Finset.range (k + 1),
          ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
            * (Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
                * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ)))))) := by
    intro θ
    rw [sin_pow_eq_exp_sum θ k]
    have h1 : Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
        * (((2 * Complex.I) : ℂ)⁻¹ ^ k * ∑ m ∈ Finset.range (k + 1),
            ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
              * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ))))))
        = (((2 * Complex.I) : ℂ)⁻¹ ^ k)
          * (Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
              * ∑ m ∈ Finset.range (k + 1),
                ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
                  * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ)))))) := by
      ring
    rw [h1]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hI : intervalIntegral (fun θ : ℝ =>
        Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
          * (((Real.sin θ : ℝ) : ℂ)) ^ k)
        (-Real.pi) Real.pi MeasureTheory.volume
      = intervalIntegral (fun θ : ℝ =>
          (((2 * Complex.I) : ℂ)⁻¹) ^ k *
            ∑ m ∈ Finset.range (k + 1),
              ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
                * (Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
                    * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ)))))))
        (-Real.pi) Real.pi MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hdist x
  rw [hI, intervalIntegral.integral_const_mul]
  congr 1
  have hfin : ∀ m ∈ Finset.range (k + 1), IntervalIntegrable
      (fun θ : ℝ => ((-1 : ℂ) ^ (m + k) * ((k.choose m : ℕ) : ℂ)
        * (Complex.exp (Complex.I * ((((r : ℝ) * θ : ℝ) : ℂ)))
            * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * θ : ℝ) : ℂ)))))))
      MeasureTheory.volume (-Real.pi) Real.pi := by
    intro m _
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum hfin]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hpt : ∀ x : ℝ,
      Complex.exp (Complex.I * ((((r : ℝ) * x : ℝ) : ℂ)))
        * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * x : ℝ) : ℂ))))
      = Complex.exp (Complex.I * (((((r : ℤ) + 2 * m - k : ℤ) * x : ℝ) : ℂ))) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrew : intervalIntegral (fun x : ℝ =>
        Complex.exp (Complex.I * ((((r : ℝ) * x : ℝ) : ℂ)))
          * Complex.exp (Complex.I * (((((2 * m - k : ℤ) * x : ℝ) : ℂ)))))
        (-Real.pi) Real.pi MeasureTheory.volume
      = intervalIntegral (fun x : ℝ =>
        Complex.exp (Complex.I * (((((r : ℤ) + 2 * m - k : ℤ) * x : ℝ) : ℂ))))
        (-Real.pi) Real.pi MeasureTheory.volume :=
    intervalIntegral.integral_congr (fun x _ => hpt x)
  rw [hrew, integral_exp_int_mul ((r : ℤ) + 2 * m - k)]
  by_cases hcond : (r + 2 * m : ℤ) = (k : ℤ)
  · rw [if_pos hcond]
    have hkey : (r : ℤ) + 2 * m - k = 0 := by omega
    rw [hkey, if_pos rfl]
  · rw [if_neg hcond]
    have hkey : (r : ℤ) + 2 * m - k ≠ 0 := by
      intro hh
      apply hcond
      omega
    rw [if_neg hkey]

/-- The integral Bessel coefficient equals the normalized complex exponential integral over
`[-π, π]`. -/
theorem besselInt_eq_complex (m : ℕ) (u : ℝ) :
    (besselInt m u : ℂ) = (1 / (2 * Real.pi)) * intervalIntegral
      (fun θ => Complex.exp (Complex.I * ((((m : ℝ) * θ - u * Real.sin θ : ℝ) : ℂ))))
      (-Real.pi) Real.pi MeasureTheory.volume := by
  set g : ℝ → ℝ := fun θ => (m : ℝ) * θ - u * Real.sin θ with hg
  have hcos : ∀ θ : ℝ,
      Complex.exp (Complex.I * ((g θ : ℝ) : ℂ))
        = (((Real.cos (g θ) : ℝ) : ℂ) + Complex.I * (((Real.sin (g θ) : ℝ) : ℂ))) := by
    intro θ
    have hE : Complex.exp (Complex.I * ((g θ : ℝ) : ℂ))
        = Complex.exp (((g θ : ℝ) : ℂ) * Complex.I) := by
      rw [mul_comm]
    rw [hE, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hodd : ∀ θ : ℝ, (((Real.sin (g θ) : ℝ) : ℂ)) = -(((Real.sin (g (-θ)) : ℝ) : ℂ)) := by
    intro θ
    have h : g (-θ) = -(g θ) := by
      have h1 : g (-θ) = (m : ℝ) * (-θ) - u * Real.sin (-θ) := rfl
      have h2 : g θ = (m : ℝ) * θ - u * Real.sin θ := rfl
      rw [h1, h2, Real.sin_neg]
      ring
    rw [h, Real.sin_neg]
    push_cast
    ring
  have hoddF : ∀ θ : ℝ,
      Complex.I * (((Real.sin (g (-θ)) : ℝ) : ℂ))
        = -(Complex.I * (((Real.sin (g θ) : ℝ) : ℂ))) := by
    intro θ
    rw [hodd θ]
    ring
  have hcont : Continuous fun θ : ℝ => Complex.I * (((Real.sin (g θ) : ℝ) : ℂ)) := by
    unfold g
    fun_prop
  have hcontCos : Continuous fun θ : ℝ => (((Real.cos (g θ) : ℝ) : ℂ)) := by
    unfold g
    fun_prop
  have hzero : intervalIntegral
      (fun θ : ℝ => Complex.I * (((Real.sin (g θ) : ℝ) : ℂ)))
      (-Real.pi) Real.pi MeasureTheory.volume = 0 :=
    intervalIntegral_odd_zero _ hcont hoddF
  have hI : intervalIntegral
      (fun θ => Complex.exp (Complex.I * ((((m : ℝ) * θ - u * Real.sin θ : ℝ) : ℂ))))
      (-Real.pi) Real.pi MeasureTheory.volume
      = intervalIntegral
        (fun θ => (((Real.cos (g θ) : ℝ) : ℂ)) + Complex.I * (((Real.sin (g θ) : ℝ) : ℂ)))
        (-Real.pi) Real.pi MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hcos x
  rw [hI]
  have hadd : intervalIntegral
      (fun θ => (((Real.cos (g θ) : ℝ) : ℂ)) + Complex.I * (((Real.sin (g θ) : ℝ) : ℂ)))
      (-Real.pi) Real.pi MeasureTheory.volume
      = intervalIntegral (fun θ => (((Real.cos (g θ) : ℝ) : ℂ)))
          (-Real.pi) Real.pi MeasureTheory.volume
        + intervalIntegral (fun θ => Complex.I * (((Real.sin (g θ) : ℝ) : ℂ)))
          (-Real.pi) Real.pi MeasureTheory.volume :=
    intervalIntegral.integral_add
      (hcontCos.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [hadd, hzero, add_zero, intervalIntegral.integral_ofReal]
  have hsymm := besselInt_eq_symm m u
  rw [hsymm]
  have hgc : (fun θ => Real.cos (g θ))
      = (fun θ => Real.cos ((m : ℝ) * θ - u * Real.sin θ)) := by
    funext θ
    rfl
  rw [hgc]
  push_cast
  ring

/-- For exponent `m + 2j`, the Fourier moment sum reduces to its single matching binomial term. -/
private theorem moment_at (m j : ℕ) :
    ((2 * Complex.I) : ℂ)⁻¹ ^ (m + 2 * j) *
      ∑ p ∈ Finset.range (m + 2 * j + 1),
        ((-1 : ℂ) ^ (p + (m + 2 * j)) * (((m + 2 * j).choose p : ℕ) : ℂ)
          * (if (m + 2 * p : ℤ) = ((m + 2 * j : ℕ) : ℤ) then (2 * Real.pi : ℂ) else 0))
    = ((2 * Complex.I) : ℂ)⁻¹ ^ (m + 2 * j) * (2 * Real.pi : ℂ)
        * ((-1 : ℂ) ^ (m + j)) * (((m + 2 * j).choose j : ℕ) : ℂ) := by
  have hj : j ∈ Finset.range (m + 2 * j + 1) := by
    simp only [Finset.mem_range]
    omega
  have hsum : (∑ p ∈ Finset.range (m + 2 * j + 1),
        ((-1 : ℂ) ^ (p + (m + 2 * j)) * (((m + 2 * j).choose p : ℕ) : ℂ)
          * (if (m + 2 * p : ℤ) = ((m + 2 * j : ℕ) : ℤ) then (2 * Real.pi : ℂ) else 0)))
      = ((-1 : ℂ) ^ (m + 3 * j)) * (((m + 2 * j).choose j : ℕ) : ℂ) * (2 * Real.pi : ℂ) := by
    rw [Finset.sum_eq_single j]
    · rw [if_pos (by push_cast; omega)]
      rw [show (j + (m + 2 * j) : ℕ) = m + 3 * j from by omega]
    · intro p hp hpj
      have hne : (m + 2 * p : ℤ) ≠ ((m + 2 * j : ℕ) : ℤ) := by
        intro heq
        push_cast at heq
        omega
      rw [if_neg hne, mul_zero]
    · intro hj'
      exact absurd hj hj'
  rw [hsum]
  have hsign : ((-1 : ℂ) ^ (m + 3 * j)) = ((-1 : ℂ) ^ (m + j)) := by
    rw [show (m + 3 * j : ℕ) = (m + j) + 2 * j from by omega, pow_add,
      show (-1 : ℂ) ^ (2 * j) = 1 from by
        rw [pow_mul, neg_one_sq, one_pow]]
    ring
  rw [hsign]
  ring

/-- The Fourier moment sum vanishes when the sine exponent is below the mode or has the wrong
parity. -/
private theorem moment_zero (m k : ℕ) (hk : k < m ∨ (k - m) % 2 = 1) :
    ((2 * Complex.I) : ℂ)⁻¹ ^ k *
      ∑ p ∈ Finset.range (k + 1),
        ((-1 : ℂ) ^ (p + k) * ((k.choose p : ℕ) : ℂ)
          * (if (m + 2 * p : ℤ) = (k : ℤ) then (2 * Real.pi : ℂ) else 0))
    = 0 := by
  have hsum : (∑ p ∈ Finset.range (k + 1),
        ((-1 : ℂ) ^ (p + k) * ((k.choose p : ℕ) : ℂ)
          * (if (m + 2 * p : ℤ) = (k : ℤ) then (2 * Real.pi : ℂ) else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hne : (m + 2 * p : ℤ) ≠ (k : ℤ) := by
      intro heq
      have hnat : m + 2 * p = k := by exact_mod_cast heq
      rcases hk with hk | hk <;> omega
    rw [if_neg hne, mul_zero]
  rw [hsum, mul_zero]

open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open MeasureTheory
open scoped BigOperators

/-- The integer Fourier mode `exp (i * n * θ)`. -/
private noncomputable def fourierMode (n : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((n : ℂ) * (θ : ℂ)))

/-- Every Fourier mode has complex norm one. -/
private theorem fourierMode_norm (n : ℤ) (θ : ℝ) : ‖fourierMode n θ‖ = 1 := by
  simp [fourierMode, Complex.norm_exp]

/-- The integral of a Fourier mode over `[-π, π]` is `2π` for mode zero and zero otherwise. -/
private theorem fourierMode_integral (n : ℤ) :
    (∫ θ in -Real.pi..Real.pi, fourierMode n θ) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  have heq : (fun θ => fourierMode n θ) =
      (fun θ : ℝ => Complex.exp (Complex.I * ((((n : ℝ) * θ : ℝ)) : ℂ))) := by
    funext θ
    simp [fourierMode]
  rw [heq]
  exact integral_exp_int_mul n

/-- Multiplying the positive Bessel harmonic by mode `m` shifts its Fourier index to `m - k`. -/
private theorem fourierMode_pos (m k : ℕ) (u θ : ℝ) :
    fourierMode m θ * lcJAp u θ k =
      (lcBesselJ k u : ℂ) * fourierMode ((m : ℤ) - k) θ := by
  unfold fourierMode lcJAp
  calc
    _ = (lcBesselJ k u : ℂ) *
        (Complex.exp (Complex.I * ((m : ℂ) * θ)) *
          Complex.exp (-(Complex.I * ((k : ℂ) * θ)))) := by push_cast; ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- Multiplying the negative Bessel harmonic by mode `m` shifts its Fourier index to `m + k`
with sign factor `(-1)^k`. -/
private theorem fourierMode_neg (m k : ℕ) (u θ : ℝ) :
    fourierMode m θ * lcJAn u θ k =
      ((-1 : ℂ)^k * (lcBesselJ k u : ℂ)) * fourierMode ((m : ℤ) + k) θ := by
  unfold fourierMode lcJAn
  calc
    _ = ((-1 : ℂ)^k * (lcBesselJ k u : ℂ)) *
        (Complex.exp (Complex.I * ((m : ℂ) * θ)) *
          Complex.exp (Complex.I * ((k : ℂ) * θ))) := by push_cast; ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- The positive Bessel harmonic has norm equal to the absolute value of its Bessel coefficient. -/
private theorem lcJAp_norm (u θ : ℝ) (k : ℕ) : ‖lcJAp u θ k‖ = |lcBesselJ k u| := by
  simp [lcJAp, Complex.norm_exp]

/-- The negative Bessel harmonic has norm equal to the absolute value of its Bessel coefficient. -/
private theorem lcJAn_norm (u θ : ℝ) (k : ℕ) : ‖lcJAn u θ k‖ = |lcBesselJ k u| := by
  simp [lcJAn, Complex.norm_exp, norm_pow]

/-- The sum of the positive and nonzero-index negative Bessel harmonics, weighted by Fourier
mode `m`. -/
private noncomputable def weightedHarmonic (m : ℕ) (u : ℝ) (k : ℕ) (θ : ℝ) : ℂ :=
  fourierMode m θ * (lcJAp u θ k + if k = 0 then 0 else lcJAn u θ k)

/-- Each weighted Bessel harmonic is continuous in the angular variable. -/
private theorem weightedHarmonic_continuous (m : ℕ) (u : ℝ) (k : ℕ) :
    Continuous (weightedHarmonic m u k) := by
  unfold weightedHarmonic lcJAp lcJAn fourierMode
  split_ifs <;> fun_prop

/-- For nonnegative `u`, the weighted harmonic is bounded by twice the factorial majorant `(u /
2)^k / k!`. -/
private theorem weightedHarmonic_bound (m : ℕ) (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (θ : ℝ) :
    ‖weightedHarmonic m u k θ‖ ≤ 2 * ((u / 2)^k / (k.factorial : ℝ)) := by
  have hn : ‖(if k = 0 then 0 else lcJAn u θ k)‖ ≤ |lcBesselJ k u| := by
    split_ifs
    · simp
    · exact (lcJAn_norm u θ k).le
  have hb := abs_lcBesselJ_le k u hu
  calc
    ‖weightedHarmonic m u k θ‖ = ‖lcJAp u θ k + if k = 0 then 0 else lcJAn u θ k‖ := by
      rw [weightedHarmonic, norm_mul, fourierMode_norm, one_mul]
    _ ≤ ‖lcJAp u θ k‖ + ‖(if k = 0 then 0 else lcJAn u θ k)‖ := norm_add_le _ _
    _ ≤ |lcBesselJ k u| + |lcBesselJ k u| := add_le_add (lcJAp_norm u θ k).le hn
    _ ≤ _ := by linarith

/-- The weighted harmonic integrates to `2π * lcBesselJ m u` when `k = m`, and to zero
otherwise. -/
private theorem weightedHarmonic_integral (m k : ℕ) (u : ℝ) :
    (∫ θ in -Real.pi..Real.pi, weightedHarmonic m u k θ) =
      if k = m then (2 * Real.pi : ℂ) * (lcBesselJ m u : ℂ) else 0 := by
  let fp : ℝ → ℂ := fun θ => (lcBesselJ k u : ℂ) * fourierMode ((m : ℤ) - k) θ
  let fn : ℝ → ℂ := fun θ => if k = 0 then 0 else
    ((-1 : ℂ)^k * (lcBesselJ k u : ℂ)) * fourierMode ((m : ℤ) + k) θ
  have heq : weightedHarmonic m u k = fun θ => fp θ + fn θ := by
    funext θ
    dsimp [weightedHarmonic, fp, fn]
    rw [mul_add, fourierMode_pos]
    by_cases hk : k = 0
    · simp [hk]
    · simp only [if_neg hk, fourierMode_neg]
  have hcp : Continuous fp := by dsimp [fp, fourierMode]; fun_prop
  have hcn : Continuous fn := by
    dsimp [fn, fourierMode]
    split_ifs <;> fun_prop
  have hp : (∫ θ in -Real.pi..Real.pi, fp θ) =
      if k = m then (2 * Real.pi : ℂ) * (lcBesselJ m u : ℂ) else 0 := by
    dsimp [fp]
    rw [intervalIntegral.integral_const_mul, fourierMode_integral]
    by_cases hkm : k = m
    · subst k
      simp [mul_comm]
    · have hne : (m : ℤ) - k ≠ 0 := by omega
      simp [hne, hkm]
  have hn : (∫ θ in -Real.pi..Real.pi, fn θ) = 0 := by
    by_cases hk : k = 0
    · simp [fn, hk]
    · dsimp [fn]
      simp only [if_neg hk]
      rw [intervalIntegral.integral_const_mul, fourierMode_integral]
      have hne : (m : ℤ) + k ≠ 0 := by omega
      simp [hne]
  rw [heq, intervalIntegral.integral_add (hcp.intervalIntegrable _ _) (hcn.intervalIntegrable _ _),
    hp, hn, add_zero]

/-- For nonnegative `u`, the integrals of the weighted harmonics sum to the integral of their
exponential generating response. -/
private theorem weightedHarmonic_hasSum_integral (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    HasSum (fun k => ∫ θ in -Real.pi..Real.pi, weightedHarmonic m u k θ)
      (∫ θ in -Real.pi..Real.pi, fourierMode m θ *
        Complex.exp (Complex.I * (-(u : ℂ) * (Real.sin θ : ℂ)))) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => 2 * ((u / 2)^k / (k.factorial : ℝ)))
  · intro k
    exact (weightedHarmonic_continuous m u k).aestronglyMeasurable
  · intro k
    exact Filter.Eventually.of_forall (fun θ _ => weightedHarmonic_bound m u hu k θ)
  · exact Filter.Eventually.of_forall (fun _ _ =>
      (Real.summable_pow_div_factorial (u / 2)).mul_left 2)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun θ _ =>
      (lcBesselJacobiAnger u θ hu).mul_left (fourierMode m θ))

/-- For nonnegative arguments, the integral and series definitions of the Bessel coefficient
agree. -/
theorem besselInt_eq_lcBesselJ_nonneg (m : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    besselInt m u = lcBesselJ m u := by
  have hsum := weightedHarmonic_hasSum_integral m u hu
  simp_rw [weightedHarmonic_integral] at hsum
  have hone : HasSum
      (fun k : ℕ => if k = m then (2 * Real.pi : ℂ) * (lcBesselJ m u : ℂ) else 0)
      ((2 * Real.pi : ℂ) * (lcBesselJ m u : ℂ)) := hasSum_ite_eq m _
  have heq := hsum.unique hone
  have hfun : (fun θ : ℝ => fourierMode m θ *
        Complex.exp (Complex.I * (-(u : ℂ) * (Real.sin θ : ℂ)))) =
      (fun θ : ℝ => Complex.exp (Complex.I *
        ((((m : ℝ) * θ - u * Real.sin θ : ℝ) : ℂ)))) := by
    funext θ
    unfold fourierMode
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfun] at heq
  have hc : (besselInt m u : ℂ) = (lcBesselJ m u : ℂ) := by
    rw [besselInt_eq_complex, heq]
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  exact_mod_cast hc

/-- Negating the argument of the order-`m` integral Bessel coefficient multiplies it by
`(-1)^m`. -/
theorem besselInt_neg (m : ℕ) (u : ℝ) :
    besselInt m (-u) = (-1 : ℝ)^m * besselInt m u := by
  let f : ℝ → ℝ := fun θ => Real.cos ((m : ℝ) * θ - (-u) * Real.sin θ)
  have hi : (∫ θ in 0..Real.pi, f (Real.pi - θ)) = ∫ θ in 0..Real.pi, f θ := by
    simpa only [sub_self, sub_zero] using!
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi) f Real.pi)
  have hf : (fun θ => f (Real.pi - θ)) =
      (fun θ => (-1 : ℝ)^m * Real.cos ((m : ℝ) * θ - u * Real.sin θ)) := by
    funext θ
    dsimp [f]
    rw [Real.sin_pi_sub]
    have he : (m : ℝ) * (Real.pi - θ) - (-u) * Real.sin θ =
        (m : ℝ) * Real.pi - ((m : ℝ) * θ - u * Real.sin θ) := by ring
    rw [he, Real.cos_nat_mul_pi_sub]
  change (1 / Real.pi) * (∫ θ in 0..Real.pi, f θ) = _
  rw [← hi, hf, intervalIntegral.integral_const_mul]
  unfold besselInt
  ring

/-- Negating the argument of the order-`m` series Bessel coefficient multiplies it by `(-1)^m`. -/
private theorem lcBesselJ_neg (m : ℕ) (u : ℝ) :
    lcBesselJ m (-u) = (-1 : ℝ)^m * lcBesselJ m u := by
  unfold lcBesselJ
  rw [← tsum_mul_left]
  congr 1
  funext j
  have he : ((-u) / 2)^(2*j+m) = (-1 : ℝ)^m * (u / 2)^(2*j+m) := by
    rw [neg_div, neg_pow, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [he]
  ring

/-- The integral and series definitions of the Bessel coefficient agree for every real argument. -/
theorem besselInt_eq_lcBesselJ (m : ℕ) (u : ℝ) : besselInt m u = lcBesselJ m u := by
  by_cases hu : 0 ≤ u
  · exact besselInt_eq_lcBesselJ_nonneg m u hu
  · have hnu : 0 ≤ -u := by linarith
    calc
      besselInt m u = (-1 : ℝ)^m * besselInt m (-u) := by
        simpa using! besselInt_neg m (-u)
      _ = (-1 : ℝ)^m * lcBesselJ m (-u) := by rw [besselInt_eq_lcBesselJ_nonneg m (-u) hnu]
      _ = lcBesselJ m u := by simpa using! (lcBesselJ_neg m (-u)).symm

open Matrix Polynomial Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Matrix.Norms.L2Operator BigOperators Classical

/-- The one-dimensional matrix with sole entry `100`, used in the phase-error counterexample. -/
private abbrev bigMatrix : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 100

/-- For the chosen one-dimensional matrix, computes the difference between the two phased
alternating words exactly. -/
private theorem bad_phase_difference :
    phasedAlternating (1 : Matrix (Fin 1) (Fin 1) ℂ) bigMatrix 0 Complex.I [1] -
      phasedAlternating 1 bigMatrix 0 1 [1] =
        (199 * Complex.I - 1) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp only [phasedAlternating, phaseRotation_one, Matrix.one_mul]
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp [phaseRotation, bigMatrix]
  ring

/-- The chosen nonprojector matrix gives a phase perturbation error strictly larger than `16`. -/
private theorem bad_phase_error :
    16 < ‖phasedAlternating (1 : Matrix (Fin 1) (Fin 1) ℂ) bigMatrix 0 Complex.I [1] -
      phasedAlternating 1 bigMatrix 0 1 [1]‖ := by
  rw [bad_phase_difference, norm_smul]
  have him := Complex.im_le_norm (199 * Complex.I - 1)
  norm_num at him ⊢
  linarith

/-- The two-dimensional real rotation with diagonal entries `3/5` and off-diagonal entries
`-4/5` and `4/5`. -/
private noncomputable abbrev rotation : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ := fun i j =>
  if i.2 = j.2 then 3 / 5 else if i.2 = 0 then -(4 / 5) else 4 / 5

/-- The chosen rotation matrix is unitary. -/
private theorem rotation_unitary : rotation ∈ Matrix.unitaryGroup (Fin 1 × Fin 2) ℂ := by
  constructor <;> ext i j <;> rcases i with ⟨i, a⟩ <;> rcases j with ⟨j, b⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [rotation, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat]

/-- The standard Euclidean coordinate vector at `(0, 0)`. -/
private noncomputable abbrev basisInput : EuclideanSpace ℂ (Fin 1 × Fin 2) :=
  EuclideanSpace.single (0, 0) 1

/-- The chosen coordinate input has Euclidean norm one. -/
private theorem basisInput_norm : ‖basisInput‖ = 1 := by simp [basisInput]

/-- The coordinate supremum norm of the rotated input is at most `4/5`. -/
private theorem rotation_output_bound : ‖rotation *ᵥ basisInput‖ ≤ (4 / 5 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  rintro ⟨i, a⟩
  fin_cases i
  fin_cases a <;>
    norm_num [rotation, basisInput, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, EuclideanSpace.single, PiLp.single_apply, Pi.single_apply]

/-- Refutes the conjunction of the stated universal phase stability estimate without projector
hypotheses and its resource ledger assertion. -/
theorem not_clause51 : ¬ (
  ∃ C : ℝ, 1 ≤ C ∧

    (∀ (H : Type) [Fintype H] [DecidableEq H]
        (U₁ U₂ P Q : Matrix H H ℂ) (base₁ base₂ : ℂ) (zs₁ zs₂ : List ℂ)
        (η ε_or : ℝ),
      U₁ ∈ Matrix.unitaryGroup H ℂ → U₂ ∈ Matrix.unitaryGroup H ℂ →
      IsPhase base₁ → IsPhase base₂ → IsPhaseTable zs₁ → IsPhaseTable zs₂ →
      zs₁.length = zs₂.length → 0 < zs₁.length →
      0 ≤ η → 0 ≤ ε_or →
      ‖U₁ - U₂‖ ≤ ε_or →
      ‖base₁ - base₂‖ ≤ η →
      List.Forall₂ (fun z₁ z₂ => ‖z₁ - z₂‖ ≤ η) zs₁ zs₂ →
      ‖phasedAlternating U₁ P Q base₁ zs₁ - phasedAlternating U₂ P Q base₂ zs₂‖ ≤
        4 * ((zs₁.length : ℝ) + 1) * (η + ε_or)) ∧

    (∀ (m : ℕ) (η ε : ℝ),
      0 < m → 0 < η → η ≤ 1 → 0 < ε → ε ≤ 1 →
      ∃ led : QsvtCostLedger,
        led.dataQueries = m ∧
        led.adjointQueries = m ∧
        led.phaseGates = m + 1 ∧
        led.elementaryGates ≤
          C * m * (binaryPrecisionBits η + Nat.ceil (Real.log (1 / ε)) + 2) ^ 2 ∧
        led.integerBitTime ≤
          C * m * (binaryPrecisionBits η + Nat.ceil (Real.log (1 / ε)) + 2) ^ 3 ∧
        led.peakWorkspace ≤
          C * (binaryPrecisionBits η + Nat.clog 2 (m + 2) + 2))
) := by
  rintro ⟨_, _, h, _⟩
  have hb : ‖Complex.I - 1‖ ≤ (2 : ℝ) := by
    calc
      ‖Complex.I - 1‖ ≤ ‖Complex.I‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num
  have hbad := h (Fin 1) 1 1 bigMatrix 0 Complex.I 1 [1] [1] 2 0
    (by exact one_mem _) (by exact one_mem _) (by simp [IsPhase])
    (by simp [IsPhase]) (by simp [IsPhaseTable, IsPhase])
    (by simp [IsPhaseTable, IsPhase]) rfl (by simp) (by norm_num) (by norm_num)
    (by simp) hb (List.Forall₂.cons (by simp) List.Forall₂.nil)
  norm_num at hbad
  exact (not_lt_of_ge hbad) bad_phase_error

/-- Refutes the stated conjunction containing equality between the coordinate supremum norm of a
unitary output and the Euclidean input norm. -/
theorem not_clause54 : ¬ (
  ∃ C : ℝ, 1 ≤ C ∧

    (∀ (d w : ℕ) (V : Matrix (Fin d × Fin w) (Fin d × Fin w) ℂ)
        (u : EuclideanSpace ℂ (Fin d × Fin w)),
      0 < d → 0 < w →
      V ∈ Matrix.unitaryGroup (Fin d × Fin w) ℂ →
      ‖V *ᵥ u‖ = ‖u‖) ∧

    (∀ (d w g : ℕ),
      0 < d → 0 ≤ w → 0 ≤ g →
      ∃ led : QsvtCostLedger,
        led.peakWorkspace = Nat.clog 2 (d + 2) + w ∧
        led.elementaryGates = g ∧
        led.integerBitTime ≤ C * g * (Nat.clog 2 (d + 2) + w + 1)) ∧

    (∀ (p δ : ℝ), 0 < p → p ≤ 1 → 0 < δ → δ < 1 →
      ∃ runs : ℕ,
        runs ≤ Nat.ceil (Real.log (1 / δ) / p) ∧
        (1 - p) ^ runs ≤ δ)
) := by
  rintro ⟨_, _, h, _, _⟩
  have hnorm := h 1 2 rotation basisInput (by decide) (by decide) rotation_unitary
  rw [basisInput_norm] at hnorm
  have hbound := rotation_output_bound
  linarith

/-- The unit complex number with real and imaginary parts `sqrt 2 / 2`. -/
private noncomputable def irrationalPhase : ℂ := ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩
/-- The linear polynomial `irrationalPhase * X`. -/
private noncomputable def irrationalLinear : Polynomial ℂ := C irrationalPhase * X

/-- The chosen irrational phase has squared norm one. -/
private theorem irrationalPhase_normSq : Complex.normSq irrationalPhase = 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  simp only [irrationalPhase, Complex.normSq_apply]
  nlinarith

/-- The chosen irrational phase is nonzero. -/
private theorem irrationalPhase_ne_zero : irrationalPhase ≠ 0 := by
  intro h
  have hh := irrationalPhase_normSq
  rw [h, map_zero] at hh
  norm_num at hh

/-- The chosen irrational linear polynomial has natural degree one. -/
private theorem irrationalLinear_degree : irrationalLinear.natDegree = 1 := by
  simp [irrationalLinear, irrationalPhase_ne_zero]

/-- The chosen irrational linear polynomial satisfies `Cor8Admissible` at degree one. -/
private theorem irrationalLinear_admissible : Cor8Admissible irrationalLinear 1 := by
  constructor
  · simp [Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity,
      irrationalLinear]
  · intro x hx
    simp only [irrationalLinear, eval_mul, eval_C, eval_X, map_mul,
      irrationalPhase_normSq, Complex.normSq_ofReal, one_mul]
    nlinarith [hx.1, hx.2]
  · intro x hx
    simp only [irrationalLinear, eval_mul, eval_C, eval_X, map_mul,
      irrationalPhase_normSq, Complex.normSq_ofReal, one_mul]
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with hx | hx <;> nlinarith
  · norm_num

/-- The real part of the linear coefficient of `irrationalLinear` is not rational. -/
private theorem irrationalLinear_coefficient_not_rational :
    ¬ ∃ q : ℚ, (irrationalLinear.coeff 1).re = (q : ℝ) := by
  rintro ⟨q, hq⟩
  have h : Real.sqrt 2 = ((2 * q : ℚ) : ℝ) := by
    simp [irrationalLinear, irrationalPhase] at hq
    push_cast
    linarith
  exact irrational_sqrt_two.ne_rat (2 * q) h

/-- Refutes the stated universal rational-coefficient approximation and phase synthesis
assertion when nonnegative coefficient budgets may be zero. -/
theorem not_clause52 : ¬ (
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : Polynomial ℂ) (n : ℕ) (δ : Fin (n + 1) → ℝ) (ε_phase : ℝ),
      0 < n → P.natDegree = n → Cor8Admissible P n →
      (∀ j : Fin (n + 1), 0 ≤ δ j) → 0 < ε_phase → ε_phase ≤ 1 →
      ∃ (qapprox : Fin (n + 1) → ℂ) (m : ℕ) (Φ : List ℝ) (led : QsvtCostLedger),

        (∀ j : Fin (n + 1),
          ∃ qj : Fin 2 → ℚ,
            (qapprox j).re = (qj 0 : ℝ) ∧ (qapprox j).im = (qj 1 : ℝ) ∧
            ‖qapprox j - P.coeff j‖ ≤ δ j) ∧
        m = n ∧ Φ.length = m ∧

        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          ‖(sourcePhaseResponse Φ).eval (x : ℂ) - P.eval (x : ℂ)‖ ≤
            (∑ j : Fin (n + 1), δ j) + ε_phase) ∧

        led.dataQueries = m ∧
        led.integerBitTime ≤
          C * m * (m + binaryPrecisionBits ε_phase +
            Nat.ceil (∑ j : Fin (n + 1), Real.log ((δ j)⁻¹ + 2)) + 2) ∧
        led.peakWorkspace ≤ C * (binaryPrecisionBits ε_phase + Nat.clog 2 (m + 2))
) := by
  rintro ⟨_, _, h⟩
  obtain ⟨qs, _, _, _, hcoeff, _⟩ := h irrationalLinear 1 (fun _ => 0) 1
    (by decide) irrationalLinear_degree irrationalLinear_admissible
    (by simp) (by norm_num) (by norm_num)
  obtain ⟨q, hre, _, herr⟩ := hcoeff (1 : Fin 2)
  have heq : qs 1 = irrationalLinear.coeff 1 :=
    sub_eq_zero.mp (norm_le_zero_iff.mp herr)
  rw [heq] at hre
  exact irrationalLinear_coefficient_not_rational ⟨q 0, hre⟩

/-- There exists a one-dimensional nonprojector matrix for which the displayed phase
perturbation produces norm error greater than `16`. -/
theorem phase_error_without_projectors :
    ∃ P : Matrix (Fin 1) (Fin 1) ℂ,
      16 < ‖phasedAlternating 1 P 0 Complex.I [1] - phasedAlternating 1 P 0 1 [1]‖ :=
  ⟨bigMatrix, bad_phase_error⟩

/-- There are a unitary matrix and a Euclidean unit input whose output has coordinate supremum
norm at most `4/5`. -/
theorem unitary_sup_norm_counterexample :
    ∃ (V : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ)
      (u : EuclideanSpace ℂ (Fin 1 × Fin 2)),
      V ∈ Matrix.unitaryGroup (Fin 1 × Fin 2) ℂ ∧ ‖u‖ = 1 ∧ ‖V *ᵥ u‖ ≤ (4 / 5 : ℝ) :=
  ⟨rotation, basisInput, rotation_unitary, basisInput_norm, rotation_output_bound⟩

/-- There exists a degree-one polynomial satisfying `Cor8Admissible` whose linear coefficient
has irrational real part. -/
theorem irrational_coefficient_zero_budget :
    ∃ P : Polynomial ℂ, P.natDegree = 1 ∧ Cor8Admissible P 1 ∧
      ¬ ∃ q : ℚ, (P.coeff 1).re = (q : ℝ) :=
  ⟨irrationalLinear, irrationalLinear_degree, irrationalLinear_admissible,
    irrationalLinear_coefficient_not_rational⟩

end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

set_option linter.unusedVariables true
set_option warningAsError false
set_option autoImplicit false
set_option warningAsError false
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open scoped Classical

/-- For positive `s` and `0 < target ≤ 1`, there exists `r ≥ s` with `(s / r)^r = target`, using
real powers. -/
lemma compact_radius_exists (s target : ℝ) (hs : 0 < s) (ht : 0 < target) (ht1 : target ≤ 1) :
    ∃ r : ℝ, s ≤ r ∧ Real.rpow (s/r) r = target := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1/2:ℝ) < 1)
  let R : ℝ := max (2*s) N
  have hR : 0 < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsR : s ≤ R := le_trans (by linarith) (le_max_left _ _)
  let f : ℝ → ℝ := fun x => Real.rpow (s/x) x
  have hcont : ContinuousOn f (Set.Icc s R) := by
    apply ContinuousOn.rpow (continuousOn_const.div continuousOn_id ?_) continuousOn_id
    · intro x hx
      exact Or.inr (lt_of_lt_of_le hs hx.1)
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le hs hx.1)
  have hfs : f s = 1 := by simp [f, ne_of_gt hs]
  have hfR : f R ≤ target := by
    have hratio : s/R ≤ (1/2 : ℝ) := by
      apply (div_le_iff₀ hR).mpr
      have := le_max_left (2*s) (N:ℝ)
      change 2*s ≤ R at this
      linarith
    calc
      f R ≤ Real.rpow (1/2) R := Real.rpow_le_rpow (le_of_lt (div_pos hs hR)) hratio hR.le
      _ ≤ Real.rpow (1/2) (N:ℝ) := Real.rpow_le_rpow_of_exponent_ge
        (by norm_num) (by norm_num) (le_max_right _ _)
      _ = (1/2 : ℝ)^N := Real.rpow_natCast _ _
      _ ≤ target := hN.le
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc' hsR hcont ⟨hfR, by rwa [hfs]⟩
  exact ⟨r, hr.1, he⟩

/-- For positive `s` and `s ≤ r ≤ q`, the real-power scale `(s / q)^q` is at most `(s / r)^r`. -/
lemma compact_scale_antitone (s r q : ℝ) (hs : 0 < s) (hsr : s ≤ r) (hrq : r ≤ q) :
    Real.rpow (s/q) q ≤ Real.rpow (s/r) r := by
  have hr : 0 < r := hs.trans_le hsr
  have hq : 0 < q := hr.trans_le hrq
  have hb : s/q ≤ s/r := div_le_div_of_nonneg_left hs.le hr hrq
  exact (Real.rpow_le_rpow (div_nonneg hs.le hq.le) hb hq.le).trans
    (Real.rpow_le_rpow_of_exponent_ge (div_pos hs hr) ((div_le_one hr).mpr hsr) hrq)

/-- For nonzero `t` and `0 < ε < 1/e`, constructs a radius with the target real-power value and
the stated neighboring even-integer bounds. -/
lemma compact_jacobi_radius (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε)
    (hε1 : ε < 1 / Real.exp 1) :
    ∃ r : ℝ, Real.exp 1 * |t| / 2 ≤ r ∧
      Real.rpow ((Real.exp 1 * |t| / 2) / r) r = (5/4)*ε ∧
      (Nat.floor (r/2) : ℝ) ≤ r/2 ∧ r < 2*(Nat.floor (r/2) : ℝ)+2 := by
  have hs : 0 < Real.exp 1 * |t| / 2 := by
    have ha := abs_pos.mpr ht
    positivity
  have htarget : (5/4)*ε ≤ (1:ℝ) := by
    have he := Real.add_one_le_exp 1
    have hp := (lt_div_iff₀ (Real.exp_pos 1)).mp hε1
    nlinarith
  obtain ⟨r, hsr, he⟩ := compact_radius_exists _ _ hs (by positivity) htarget
  have hr : 0 < r := hs.trans_le hsr
  refine ⟨r, hsr, he, Nat.floor_le (by positivity), ?_⟩
  have hf := Nat.lt_floor_add_one (r/2)
  linarith
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open scoped Classical BigOperators

/-- For `q ≥ 2`, the factorial is at least `(10/3) * (q / e)^q`. -/
lemma compact_factorial_lower (q : ℕ) (hq : 2 ≤ q) :
    (10/3 : ℝ) * ((q:ℝ) / Real.exp 1)^q ≤ (q.factorial : ℝ) := by
  have hqr : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hrad : (0:ℝ) ≤ 2*Real.pi*q := by positivity
  have hroot : (10/3 : ℝ) ≤ Real.sqrt (2*Real.pi*q) := by
    have hsq := Real.sq_sqrt hrad
    have hp := Real.pi_gt_three
    have hn := Real.sqrt_nonneg (2*Real.pi*q)
    nlinarith
  exact (mul_le_mul_of_nonneg_right hroot (by positivity)).trans (Stirling.le_factorial_stirling q)

/-- For nonnegative `a` and `q ≥ 2`, bounds `a^q / q!` by `(3/10) * (e * a / q)^q`. -/
lemma compact_first_coefficient (q : ℕ) (hq : 2 ≤ q) (a : ℝ) (ha : 0 ≤ a) :
    a^q / (q.factorial:ℝ) ≤ (3/10 : ℝ) * (Real.exp 1 * a / q)^q := by
  have hqpos : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hfac : (0:ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hepos := Real.exp_pos 1
  have hr : (Real.exp 1*a/q)^q * ((q:ℝ)/Real.exp 1)^q = a^q := by
    rw [← mul_pow]
    congr 1
    field_simp
  apply (div_le_iff₀ hfac).mpr
  calc
    a^q = ((3/10 : ℝ)*(Real.exp 1*a/q)^q)*((10/3 : ℝ)*((q:ℝ)/Real.exp 1)^q) := by
      calc _ = (Real.exp 1*a/q)^q * ((q:ℝ)/Real.exp 1)^q := hr.symm
           _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (compact_factorial_lower q hq) (by positivity)

/-- The factorial `(q + n)!` is at least `q! * (q + 1)^n`. -/
lemma compact_factorial_ge_pow (q n : ℕ) :
    q.factorial * (q+1)^n ≤ (q+n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show q+(n+1)=(q+n)+1 by omega, Nat.factorial_succ]
    calc q.factorial*(q+1)^(n+1) = (q+1)*(q.factorial*(q+1)^n) := by ring
         _ ≤ (q+1)*(q+n).factorial := Nat.mul_le_mul_left _ ih
         _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- If `0 ≤ a ≤ q/2`, the factorial terms along a fixed parity are bounded by the first term
times `(1/4)^k`. -/
lemma compact_parity_term (q k : ℕ) (a : ℝ) (ha : 0 ≤ a) (haq : a ≤ (q:ℝ)/2) :
    a^(q+2*k) / ((q+2*k).factorial:ℝ) ≤
      (a^q/(q.factorial:ℝ)) * (1/4:ℝ)^k := by
  have hfac : (q.factorial:ℝ)*((q:ℝ)+1)^(2*k) ≤ ((q+2*k).factorial:ℝ) := by
    exact_mod_cast compact_factorial_ge_pow q (2*k)
  have hp : (0:ℝ) < (q.factorial:ℝ)*((q:ℝ)+1)^(2*k) := by positivity
  have hratio : a/((q:ℝ)+1) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ)+1)).mpr
    linarith
  calc
    _ ≤ a^(q+2*k) / ((q.factorial:ℝ)*((q:ℝ)+1)^(2*k)) :=
      div_le_div_of_nonneg_left (pow_nonneg ha _) hp hfac
    _ = (a^q/(q.factorial:ℝ)) * (a/((q:ℝ)+1))^(2*k) := by
      rw [pow_add, div_pow]
      ring
    _ ≤ (a^q/(q.factorial:ℝ)) * (1/2:ℝ)^(2*k) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hratio _) (by positivity)
    _ = _ := by rw [pow_mul]; norm_num

/-- For `q ≥ 2` and `0 ≤ a ≤ q/2`, twice the fixed-parity factorial tail is bounded by `(4/5) *
(e * a / q)^q`. -/
lemma compact_parity_tail (q : ℕ) (hq : 2 ≤ q) (a : ℝ)
    (ha : 0 ≤ a) (haq : a ≤ (q:ℝ)/2) :
    2 * (∑' k : ℕ, a^(q+2*k) / ((q+2*k).factorial:ℝ)) ≤
      (4/5:ℝ) * (Real.exp 1*a/q)^q := by
  have hg : Summable (fun k : ℕ => (a^q/(q.factorial:ℝ))*(1/4:ℝ)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_left _
  have ht := fun k => compact_parity_term q k a ha haq
  have hs := Summable.of_nonneg_of_le (fun k => by positivity) ht hg
  have hsum := hs.tsum_le_tsum ht hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)] at hsum
  have hc := compact_first_coefficient q hq a ha
  norm_num at hsum
  nlinarith

/-- A radius `r` with `e * a ≤ r ≤ q` bounds twice the fixed-parity factorial tail by `(4/5) *
(e * a / r)^r`. -/
lemma compact_parity_tail_at_radius (q : ℕ) (hq : 2 ≤ q) (a r : ℝ)
    (ha : 0 < a) (hsr : Real.exp 1*a ≤ r) (hrq : r ≤ q) :
    2 * (∑' k : ℕ, a^(q+2*k) / ((q+2*k).factorial:ℝ)) ≤
      (4/5:ℝ) * Real.rpow ((Real.exp 1*a)/r) r := by
  have he := Real.add_one_le_exp 1
  have haq : a ≤ (q:ℝ)/2 := by nlinarith
  calc
    _ ≤ (4/5:ℝ)*(Real.exp 1*a/q)^q := compact_parity_tail q hq a ha.le haq
    _ = (4/5:ℝ)*Real.rpow (Real.exp 1*a/q) (q:ℝ) := by
      congr 1
      exact (Real.rpow_natCast (Real.exp 1*a/q) q).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (compact_scale_antitone (Real.exp 1*a) r q (by positivity) hsr hrq) (by norm_num)

/-- The absolute value of the order-`m` integral Bessel coefficient is bounded by `(|t| / 2)^m /
m!`. -/
lemma besselInt_abs_bound (m : ℕ) (t : ℝ) :
    |besselInt m t| ≤ (|t|/2)^m / (m.factorial:ℝ) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, besselInt_eq_lcBesselJ]
    exact Qatlib.Concepts.QsvtCore.PhaseExistence.abs_lcBesselJ_le m t ht
  · have hnt : 0 ≤ -t := by linarith
    have he : besselInt m t = (-1:ℝ)^m * besselInt m (-t) := by
      simpa using! besselInt_neg m (-t)
    rw [he, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_neg (lt_of_not_ge ht), besselInt_eq_lcBesselJ]
    exact Qatlib.Concepts.QsvtCore.PhaseExistence.abs_lcBesselJ_le m (-t) hnt

/-- The fixed-parity absolute Bessel tail is bounded by the stated radius expression when `e *
|t| / 2 ≤ r ≤ q`. -/
lemma besselInt_parity_tail_at_radius (q : ℕ) (hq : 2 ≤ q) (t r : ℝ)
    (ht : t ≠ 0) (hsr : Real.exp 1 * |t| / 2 ≤ r) (hrq : r ≤ q) :
    2 * (∑' k : ℕ, |besselInt (q+2*k) t|) ≤
      (4/5:ℝ) * Real.rpow ((Real.exp 1 * |t| / 2)/r) r := by
  let a : ℝ := |t|/2
  have ha : 0 < a := div_pos (abs_pos.mpr ht) (by norm_num)
  have hinj : Function.Injective (fun k : ℕ => q+2*k) := by
    intro i j h
    change q+2*i=q+2*j at h
    omega
  have hs : Summable (fun k : ℕ => a^(q+2*k) / ((q+2*k).factorial:ℝ)) :=
    (Real.summable_pow_div_factorial a).comp_injective hinj
  have hb := fun k => besselInt_abs_bound (q+2*k) t
  have hj : Summable (fun k : ℕ => |besselInt (q+2*k) t|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hs
  have hsum := hj.tsum_le_tsum hb hs
  have htail := compact_parity_tail_at_radius q hq a r ha
    (by simpa [a, mul_div_assoc] using! hsr) hrq
  calc
    _ ≤ 2 * (∑' k : ℕ, a^(q+2*k) / ((q+2*k).factorial:ℝ)) := by linarith
    _ ≤ _ := by simpa [a, mul_div_assoc] using! htail

/-- Constructs a compact Jacobi–Anger radius for which every fixed-parity Bessel tail starting
at an integer `q ≥ max 2 r` has error at most `ε`. -/
lemma compact_jacobi_parity_tail (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε)
    (hε1 : ε < 1 / Real.exp 1) :
    ∃ r : ℝ, Real.exp 1 * |t| / 2 ≤ r ∧
      Real.rpow ((Real.exp 1 * |t| / 2)/r) r = (5/4)*ε ∧
      (Nat.floor (r/2):ℝ) ≤ r/2 ∧ r < 2*(Nat.floor (r/2):ℝ)+2 ∧
      ∀ q : ℕ, 2 ≤ q → r ≤ q → 2 * (∑' k : ℕ, |besselInt (q+2*k) t|) ≤ ε := by
  obtain ⟨r, hsr, he, hf, hrf⟩ := compact_jacobi_radius t ε ht hε hε1
  refine ⟨r, hsr, he, hf, hrf, ?_⟩
  intro q hq hrq
  have htail := besselInt_parity_tail_at_radius q hq t r ht hsr hrq
  rw [he] at htail
  nlinarith
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open scoped Classical BigOperators

/-- The sum of opposite imaginary exponentials is twice the real cosine. -/
private theorem bessel_exp_pair_cos (φ : ℝ) :
    Complex.exp (Complex.I * ((φ : ℝ) : ℂ)) + Complex.exp (-(Complex.I * ((φ : ℝ) : ℂ)))
      = 2 * ((Real.cos φ : ℝ) : ℂ) := by
  have h1 := Complex.exp_mul_I ((φ : ℝ) : ℂ)
  have h2 := Complex.exp_mul_I (-(φ : ℝ) : ℂ)
  have hn : -(Complex.I * ((φ : ℝ) : ℂ)) = (-(φ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, neg_mul]
  rw [hn, show Complex.I * ((φ : ℝ) : ℂ) = ((φ : ℝ) : ℂ) * Complex.I from mul_comm _ _,
    h1, h2, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- The difference of negative and positive imaginary exponentials is `-2i` times the real sine. -/
private theorem bessel_exp_pair_sin (φ : ℝ) :
    Complex.exp (-(Complex.I * ((φ : ℝ) : ℂ))) - Complex.exp (Complex.I * ((φ : ℝ) : ℂ))
      = -(2 * Complex.I * ((Real.sin φ : ℝ) : ℂ)) := by
  have h1 := Complex.exp_mul_I ((φ : ℝ) : ℂ)
  have h2 := Complex.exp_mul_I (-(φ : ℝ) : ℂ)
  have hn : -(Complex.I * ((φ : ℝ) : ℂ)) = (-(φ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, neg_mul]
  rw [hn, show Complex.I * ((φ : ℝ) : ℂ) = ((φ : ℝ) : ℂ) * Complex.I from mul_comm _ _,
    h1, h2, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- The paired Bessel harmonic, with the zero-index negative harmonic omitted. -/
noncomputable def besselHarmonic (t θ : ℝ) (n : ℕ) : ℂ :=
  lcJAp t θ n + if n=0 then 0 else lcJAn t θ n

/-- An even paired Bessel harmonic is the stated cosine term, with the duplicated zero
coefficient removed. -/
lemma besselHarmonic_even (t θ : ℝ) (k : ℕ) :
    besselHarmonic t θ (2*k) =
      ((2*lcBesselJ (2*k) t*Real.cos ((2*k:ℕ)*θ) -
        if k=0 then lcBesselJ 0 t else 0 : ℝ) : ℂ) := by
  have hn : (-1:ℂ)^(2*k)=1 := by rw [pow_mul]; norm_num
  by_cases hk : k=0
  · subst k
    simp only [besselHarmonic, mul_zero, ite_true, lcJAp, Nat.cast_zero, zero_mul,
      mul_zero, neg_zero, Complex.exp_zero, mul_one, add_zero, Real.cos_zero,
      mul_one, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  · have hk2 : 2*k ≠ 0 := by omega
    simp only [besselHarmonic, if_neg hk2, lcJAp, lcJAn, hn, one_mul,
      if_neg hk, sub_zero]
    have harg : ((2*k:ℕ):ℂ)*(θ:ℂ) = ((((2*k:ℕ):ℝ)*θ : ℝ):ℂ) := by push_cast; rfl
    rw [← mul_add, harg, add_comm (Complex.exp _), bessel_exp_pair_cos]
    push_cast
    ring

/-- An odd paired Bessel harmonic is `-i` times the stated sine term. -/
lemma besselHarmonic_odd (t θ : ℝ) (k : ℕ) :
    besselHarmonic t θ (2*k+1) =
      -Complex.I * ((2*lcBesselJ (2*k+1) t*Real.sin ((2*k+1:ℕ)*θ) : ℝ) : ℂ) := by
  have hn : (-1:ℂ)^(2*k+1) = -1 := by rw [pow_add, pow_mul]; norm_num
  have hk2 : 2*k+1 ≠ 0 := by omega
  simp only [besselHarmonic, if_neg hk2, lcJAp, lcJAn, hn, neg_mul, one_mul, ← sub_eq_add_neg,
      ← mul_sub]
  have harg : ((2*k+1:ℕ):ℂ)*(θ:ℂ) = ((((2*k+1:ℕ):ℝ)*θ : ℝ):ℂ) := by push_cast; rfl
  rw [harg, bessel_exp_pair_sin]
  push_cast
  ring
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open scoped Classical BigOperators

/-- For nonnegative `t`, the even Bessel harmonic series sums to `cos (t * sin θ)`. -/
lemma bessel_cos_series (t θ : ℝ) (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => 2*lcBesselJ (2*k) t*Real.cos ((2*k:ℕ)*θ) -
      if k=0 then lcBesselJ 0 t else 0) (Real.cos (t*Real.sin θ)) := by
  have hh : HasSum (besselHarmonic t θ)
      (Complex.exp (Complex.I * (-(t:ℂ)*(Real.sin θ:ℂ)))) := lcBesselJacobiAnger t θ ht
  have hr := Complex.hasSum_re hh
  have ie : Function.Injective (fun k : ℕ => 2*k) := by intro i j h; change 2*i=2*j at h; omega
  have io : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro i j h; change 2*i+1=2*j+1 at h; omega
  have he := hr.summable.comp_injective ie
  have ho := hr.summable.comp_injective io
  have hsum := tsum_even_add_odd (f := fun n => (besselHarmonic t θ n).re) he ho
  rw [hr.tsum_eq] at hsum
  have hodd (k : ℕ) : (besselHarmonic t θ (2*k+1)).re = 0 := by
    rw [besselHarmonic_odd]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero,
      Complex.neg_im, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_self]
  simp only [hodd, tsum_zero, add_zero] at hsum
  have hv : (Complex.exp (Complex.I * (-(t:ℂ)*(Real.sin θ:ℂ)))).re =
      Real.cos (t*Real.sin θ) := by
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
    rw [← Complex.ofReal_sin, Complex.ofReal_re]
  rw [hv] at hsum
  have hs := he.hasSum
  simp only [Function.comp_def] at hs
  rw [hsum] at hs
  simpa only [besselHarmonic_even, Complex.ofReal_re] using! hs

/-- For nonnegative `t`, the odd Bessel harmonic series sums to `sin (t * sin θ)`. -/
lemma bessel_sin_series (t θ : ℝ) (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => 2*lcBesselJ (2*k+1) t*Real.sin ((2*k+1:ℕ)*θ))
      (Real.sin (t*Real.sin θ)) := by
  have hh : HasSum (besselHarmonic t θ)
      (Complex.exp (Complex.I * (-(t:ℂ)*(Real.sin θ:ℂ)))) := lcBesselJacobiAnger t θ ht
  have hi := Complex.hasSum_im hh
  have ie : Function.Injective (fun k : ℕ => 2*k) := by intro i j h; change 2*i=2*j at h; omega
  have io : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro i j h; change 2*i+1=2*j+1 at h; omega
  have he := hi.summable.comp_injective ie
  have ho := hi.summable.comp_injective io
  have hsum := tsum_even_add_odd (f := fun n => (besselHarmonic t θ n).im) he ho
  rw [hi.tsum_eq] at hsum
  have heven (k : ℕ) : (besselHarmonic t θ (2*k)).im = 0 := by
    rw [besselHarmonic_even, Complex.ofReal_im]
  simp only [heven, tsum_zero, zero_add] at hsum
  have hv : (Complex.exp (Complex.I * (-(t:ℂ)*(Real.sin θ:ℂ)))).im =
      -Real.sin (t*Real.sin θ) := by
    simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
    rw [← Complex.ofReal_sin, Complex.ofReal_re]
  rw [hv] at hsum
  have hs := ho.hasSum.neg
  simp only [Function.comp_def] at hs
  rw [hsum, neg_neg] at hs
  convert! hs using 1
  funext k
  rw [besselHarmonic_odd]
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
set_option autoImplicit false
set_option warningAsError false
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Polynomial
open scoped Classical BigOperators
/-- The truncated even Chebyshev expansion with Bessel coefficients for approximating `cos (t *
x)`. -/
noncomputable def compactCosPoly (t : ℝ) (R : ℕ) : Polynomial ℝ :=
  C (besselInt 0 t) + ∑ k ∈ Finset.Icc 1 R,
    C (2*(-1:ℝ)^k*besselInt (2*k) t) * Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)
/-- The truncated odd Chebyshev expansion with Bessel coefficients for approximating `sin (t *
x)`. -/
noncomputable def compactSinPoly (t : ℝ) (R : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.Icc 0 R,
    C (2*(-1:ℝ)^k*besselInt (2*k+1) t) * Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ)

/-- Increasing the cosine cutoff adds the next even Chebyshev term. -/
lemma compact_cos_succ (t : ℝ) (R : ℕ) : compactCosPoly t (R+1) = compactCosPoly t R +
    C (2*(-1:ℝ)^(R+1)*besselInt (2*(R+1)) t) * Polynomial.Chebyshev.T ℝ ((2*(R+1):ℕ):ℤ) := by
  unfold compactCosPoly
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

/-- Increasing the sine cutoff adds the next odd Chebyshev term. -/
lemma compact_sin_succ (t : ℝ) (R : ℕ) : compactSinPoly t (R+1) = compactSinPoly t R +
    C (2*(-1:ℝ)^(R+1)*besselInt (2*(R+1)+1) t) * Polynomial.Chebyshev.T ℝ ((2*(R+1)+1:ℕ):ℤ) := by
  unfold compactSinPoly
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- An even-order Chebyshev polynomial is unchanged by substituting `-X`. -/
lemma even_cheb_comp (k : ℕ) : (Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)).comp (-X) =
    Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ) := by
  apply Polynomial.funext
  intro x
  simp

/-- An odd-order Chebyshev polynomial is negated by substituting `-X`. -/
lemma odd_cheb_comp (k : ℕ) : (Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ)).comp (-X) =
    -Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ) := by
  apply Polynomial.funext
  intro x
  simp

/-- The compact cosine polynomial is even. -/
lemma compact_cos_even (t : ℝ) (R : ℕ) : (compactCosPoly t R).comp (-X) = compactCosPoly t R := by
  unfold compactCosPoly
  simp only [add_comp, C_comp, sum_comp, mul_comp, even_cheb_comp]

/-- The compact sine polynomial is odd. -/
lemma compact_sin_odd (t : ℝ) (R : ℕ) : (compactSinPoly t R).comp (-X) = -compactSinPoly t R := by
  unfold compactSinPoly
  simp only [sum_comp, mul_comp, C_comp, odd_cheb_comp, mul_neg, Finset.sum_neg_distrib]

/-- A scalar multiple of the order-`n` Chebyshev polynomial has natural degree at most `n`. -/
lemma cheb_term_degree (c : ℝ) (n : ℕ) :
    (C c * Polynomial.Chebyshev.T ℝ (n:ℤ)).natDegree ≤ n := by
  exact (natDegree_mul_le).trans (by simp [Polynomial.Chebyshev.natDegree_T])

/-- The compact cosine polynomial has natural degree at most `2R`. -/
lemma compact_cos_degree (t : ℝ) (R : ℕ) : (compactCosPoly t R).natDegree ≤ 2*R := by
  induction R with
  | zero => simp [compactCosPoly]
  | succ R ih =>
    rw [compact_cos_succ]
    apply natDegree_add_le_of_degree_le
    · exact ih.trans (by omega)
    · exact cheb_term_degree _ _

/-- The compact sine polynomial has natural degree at most `2R + 1`. -/
lemma compact_sin_degree (t : ℝ) (R : ℕ) : (compactSinPoly t R).natDegree ≤ 2*R+1 := by
  induction R with
  | zero => simpa [compactSinPoly] using! cheb_term_degree (2*besselInt 1 t) 1
  | succ R ih =>
    rw [compact_sin_succ]
    apply natDegree_add_le_of_degree_le
    · exact ih.trans (by omega)
    · exact cheb_term_degree _ _

/-- A nonzero scalar multiple of the order-`n` Chebyshev polynomial has natural degree exactly
`n`. -/
lemma cheb_term_degree_exact (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    (C c * Polynomial.Chebyshev.T ℝ (n:ℤ)).natDegree = n := by
  rw [natDegree_C_mul hc, Polynomial.Chebyshev.natDegree_T]
  simp

/-- If its highest even Bessel coefficient is nonzero, the compact cosine polynomial has natural
degree exactly `2R`. -/
lemma compact_cos_degree_exact (t : ℝ) (R : ℕ) (hJ : besselInt (2*R) t ≠ 0) :
    (compactCosPoly t R).natDegree = 2*R := by
  cases R with
  | zero => simp [compactCosPoly]
  | succ R =>
    have hc : 2*(-1:ℝ)^(R+1)*besselInt (2*(R+1)) t ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hJ
    rw [compact_cos_succ]
    have hd := cheb_term_degree_exact _ hc (2*(R+1))
    rw [natDegree_add_eq_right_of_natDegree_lt (by rw [hd]; have := compact_cos_degree t R; omega),
        hd]

/-- If its highest odd Bessel coefficient is nonzero, the compact sine polynomial has natural
degree exactly `2R + 1`. -/
lemma compact_sin_degree_exact (t : ℝ) (R : ℕ) (hJ : besselInt (2*R+1) t ≠ 0) :
    (compactSinPoly t R).natDegree = 2*R+1 := by
  cases R with
  | zero =>
    have hc : 2*besselInt 1 t ≠ 0 := mul_ne_zero (by norm_num) hJ
    simpa [compactSinPoly] using! cheb_term_degree_exact _ hc 1
  | succ R =>
    have hc : 2*(-1:ℝ)^(R+1)*besselInt (2*(R+1)+1) t ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hJ
    rw [compact_sin_succ]
    have hd := cheb_term_degree_exact _ hc (2*(R+1)+1)
    rw [natDegree_add_eq_right_of_natDegree_lt (by rw [hd]; have := compact_sin_degree t R; omega),
        hd]
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Polynomial Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open scoped Classical BigOperators
/-- The `k`th even Chebyshev–Bessel term at `x`, with the zero-index coefficient counted once. -/
noncomputable def compactCosTerm (t x : ℝ) (k : ℕ) : ℝ :=
  2*(-1:ℝ)^k*besselInt (2*k) t*(Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)).eval x -
    if k=0 then besselInt 0 t else 0
/-- The `k`th odd Chebyshev–Bessel term at `x`. -/
noncomputable def compactSinTerm (t x : ℝ) (k : ℕ) : ℝ :=
  2*(-1:ℝ)^k*besselInt (2*k+1) t*(Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ)).eval x

/-- The compact cosine polynomial evaluates to the sum of its first `R + 1` terms. -/
lemma compact_cos_eval_sum (t x : ℝ) (R : ℕ) :
    (compactCosPoly t R).eval x = ∑ k ∈ Finset.range (R+1), compactCosTerm t x k := by
  induction R with
  | zero => simp [compactCosPoly, compactCosTerm]; ring
  | succ R ih =>
    rw [compact_cos_succ, eval_add, ih, Finset.sum_range_succ (n:=R+1)]
    simp [compactCosTerm]

/-- The compact sine polynomial evaluates to the sum of its first `R + 1` terms. -/
lemma compact_sin_eval_sum (t x : ℝ) (R : ℕ) :
    (compactSinPoly t R).eval x = ∑ k ∈ Finset.range (R+1), compactSinTerm t x k := by
  induction R with
  | zero => simp [compactSinPoly, compactSinTerm]
  | succ R ih =>
    rw [compact_sin_succ, eval_add, ih, Finset.sum_range_succ (n:=R+1)]
    simp [compactSinTerm]

/-- On `[-1, 1]`, the order-`n` Chebyshev polynomial evaluates as `cos (n * arccos x)`. -/
lemma cheb_eval_arccos (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n:ℤ)).eval x = Real.cos ((n:ℝ)*Real.arccos x) := by
  calc
    _ = (Polynomial.Chebyshev.T ℝ (n:ℤ)).eval (Real.cos (Real.arccos x)) := by
      rw [Real.cos_arccos hx.1 hx.2]
    _ = _ := by simp

/-- Shifting the angle by its complement in `π/2` gives the stated even-order cosine identity. -/
lemma even_shift_cos (k : ℕ) (φ : ℝ) :
    Real.cos ((2*k:ℕ)*(Real.pi/2-φ)) = (-1:ℝ)^k * Real.cos ((2*k:ℕ)*φ) := by
  have he : ((2*k:ℕ):ℝ)*(Real.pi/2-φ) = (k:ℝ)*Real.pi - ((2*k:ℕ):ℝ)*φ := by
    push_cast
    ring
  rw [he, Real.cos_nat_mul_pi_sub]

/-- Shifting the angle by its complement in `π/2` gives the stated odd-order sine identity. -/
lemma odd_shift_sin (k : ℕ) (φ : ℝ) :
    Real.sin ((2*k+1:ℕ)*(Real.pi/2-φ)) = (-1:ℝ)^k * Real.cos ((2*k+1:ℕ)*φ) := by
  have he : ((2*k+1:ℕ):ℝ)*(Real.pi/2-φ) =
      (Real.pi/2-((2*k+1:ℕ):ℝ)*φ)+(k:ℝ)*Real.pi := by
    push_cast
    ring
  rw [he, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two_sub]

/-- For nonnegative `t` and `x ∈ [-1, 1]`, the compact cosine terms sum to `cos (t * x)`. -/
lemma compact_cos_hasSum_nonneg (t x : ℝ) (ht : 0 ≤ t) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    HasSum (compactCosTerm t x) (Real.cos (t*x)) := by
  have hs := bessel_cos_series t (Real.pi/2-Real.arccos x) ht
  rw [Real.sin_pi_div_two_sub, Real.cos_arccos hx.1 hx.2] at hs
  convert! hs using 1
  funext k
  rw [compactCosTerm, cheb_eval_arccos x hx, even_shift_cos]
  simp only [besselInt_eq_lcBesselJ]
  ring

/-- For nonnegative `t` and `x ∈ [-1, 1]`, the compact sine terms sum to `sin (t * x)`. -/
lemma compact_sin_hasSum_nonneg (t x : ℝ) (ht : 0 ≤ t) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    HasSum (compactSinTerm t x) (Real.sin (t*x)) := by
  have hs := bessel_sin_series t (Real.pi/2-Real.arccos x) ht
  rw [Real.sin_pi_div_two_sub, Real.cos_arccos hx.1 hx.2] at hs
  convert! hs using 1
  funext k
  rw [compactSinTerm, cheb_eval_arccos x hx, odd_shift_sin, besselInt_eq_lcBesselJ]
  ring

/-- Each compact cosine term is even in the time parameter. -/
lemma compact_cos_term_neg (t x : ℝ) (k : ℕ) : compactCosTerm (-t) x k = compactCosTerm t x k := by
  simp [compactCosTerm, besselInt_neg, pow_mul]

/-- Each compact sine term is odd in the time parameter. -/
lemma compact_sin_term_neg (t x : ℝ) (k : ℕ) : compactSinTerm (-t) x k = -compactSinTerm t x k := by
  simp only [compactSinTerm, besselInt_neg, pow_add, pow_mul, neg_one_sq, one_pow,
    one_mul, pow_one]
  ring

/-- For every real `t` and `x ∈ [-1, 1]`, the compact cosine terms sum to `cos (t * x)`. -/
lemma compact_cos_hasSum (t x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    HasSum (compactCosTerm t x) (Real.cos (t*x)) := by
  by_cases ht : 0 ≤ t
  · exact compact_cos_hasSum_nonneg t x ht hx
  · have hs := compact_cos_hasSum_nonneg (-t) x (by linarith) hx
    have hf : compactCosTerm (-t) x = compactCosTerm t x := by
      funext k
      exact compact_cos_term_neg t x k
    rw [hf, neg_mul, Real.cos_neg] at hs
    exact hs

/-- For every real `t` and `x ∈ [-1, 1]`, the compact sine terms sum to `sin (t * x)`. -/
lemma compact_sin_hasSum (t x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    HasSum (compactSinTerm t x) (Real.sin (t*x)) := by
  by_cases ht : 0 ≤ t
  · exact compact_sin_hasSum_nonneg t x ht hx
  · have hs := (compact_sin_hasSum_nonneg (-t) x (by linarith) hx).neg
    simpa only [compact_sin_term_neg, neg_neg, neg_mul, Real.sin_neg] using! hs
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Polynomial
open scoped Classical BigOperators

/-- A summable majorant for the tail bounds the error of a finite truncation of a convergent
real series. -/
lemma real_series_truncation_bound (f b : ℕ → ℝ) (v : ℝ) (N : ℕ)
    (hf : HasSum f v) (hb : Summable b) (hbound : ∀ n, |f (n+N)| ≤ b n) :
    |v - ∑ i ∈ Finset.range N, f i| ≤ ∑' n, b n := by
  have hsplit := hf.summable.sum_add_tsum_nat_add N
  rw [hf.tsum_eq] at hsplit
  have he : v - ∑ i ∈ Finset.range N, f i = ∑' n, f (n+N) := by linarith
  rw [he]
  have ha : Summable (fun n => |f (n+N)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbound hb
  have hn : |∑' n, f (n+N)| ≤ ∑' n, |f (n+N)| := by
    simpa only [Real.norm_eq_abs] using! norm_tsum_le_tsum_norm (f := fun n => f (n+N)) ha
  exact hn.trans (ha.tsum_le_tsum hbound hb)

/-- The absolute Bessel coefficients along either fixed parity form a summable sequence. -/
lemma besselInt_parity_summable (q : ℕ) (t : ℝ) : Summable (fun k : ℕ => |besselInt (q+2*k) t|) := by
  have hinj : Function.Injective (fun k : ℕ => q+2*k) := by
    intro i j h
    change q+2*i=q+2*j at h
    omega
  have hs : Summable (fun k : ℕ => (|t|/2)^(q+2*k) / ((q+2*k).factorial:ℝ)) :=
    (Real.summable_pow_div_factorial (|t|/2)).comp_injective hinj
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => besselInt_abs_bound (q+2*k) t) hs

/-- Every nonzero-index compact cosine term on `[-1, 1]` is bounded by twice the corresponding
absolute Bessel coefficient. -/
lemma compact_cos_term_bound (t x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (k : ℕ) (hk : k ≠ 0) :
    |compactCosTerm t x k| ≤ 2*|besselInt (2*k) t| := by
  have hc : |(Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)).eval x| ≤ 1 := by
    rw [cheb_eval_arccos x hx]
    exact Real.abs_cos_le_one _
  calc
    _ = 2*|besselInt (2*k) t| * |(Polynomial.Chebyshev.T ℝ ((2*k:ℕ):ℤ)).eval x| := by
      simp [compactCosTerm, hk, abs_mul, abs_pow]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _)

/-- Every compact sine term on `[-1, 1]` is bounded by twice the corresponding absolute Bessel
coefficient. -/
lemma compact_sin_term_bound (t x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (k : ℕ) :
    |compactSinTerm t x k| ≤ 2*|besselInt (2*k+1) t| := by
  have hc : |(Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ)).eval x| ≤ 1 := by
    rw [cheb_eval_arccos x hx]
    exact Real.abs_cos_le_one _
  calc
    _ = 2*|besselInt (2*k+1) t| * |(Polynomial.Chebyshev.T ℝ ((2*k+1:ℕ):ℤ)).eval x| := by
      simp [compactSinTerm, abs_mul, abs_pow]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _)

/-- The compact cosine truncation error on `[-1, 1]` is bounded by twice the absolute even
Bessel tail starting at `2R + 2`. -/
lemma compact_cos_error (t x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (R : ℕ) :
    |Real.cos (t*x) - (compactCosPoly t R).eval x| ≤
      2*(∑' k : ℕ, |besselInt ((2*R+2)+2*k) t|) := by
  rw [compact_cos_eval_sum]
  have hh := real_series_truncation_bound (compactCosTerm t x)
    (fun k => 2*|besselInt ((2*R+2)+2*k) t|) (Real.cos (t*x)) (R+1)
    (compact_cos_hasSum t x hx) ((besselInt_parity_summable (2*R+2) t).mul_left 2)
    (fun k => by
      have h := compact_cos_term_bound t x hx (k+(R+1)) (by omega)
      simpa only [show 2*(k+(R+1))=(2*R+2)+2*k by omega] using! h)
  simpa only [tsum_mul_left] using! hh

/-- The compact sine truncation error on `[-1, 1]` is bounded by twice the absolute odd Bessel
tail starting at `2R + 3`. -/
lemma compact_sin_error (t x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (R : ℕ) :
    |Real.sin (t*x) - (compactSinPoly t R).eval x| ≤
      2*(∑' k : ℕ, |besselInt ((2*R+3)+2*k) t|) := by
  rw [compact_sin_eval_sum]
  have hh := real_series_truncation_bound (compactSinTerm t x)
    (fun k => 2*|besselInt ((2*R+3)+2*k) t|) (Real.sin (t*x)) (R+1)
    (compact_sin_hasSum t x hx) ((besselInt_parity_summable (2*R+3) t).mul_left 2)
    (fun k => by
      have h := compact_sin_term_bound t x hx (k+(R+1))
      simpa only [show 2*(k+(R+1))+1=(2*R+3)+2*k by omega] using! h)
  simpa only [tsum_mul_left] using! hh
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Polynomial
open scoped Classical BigOperators
set_option maxHeartbeats 1000000

/-- For nonzero `t` and `0 < ε < 1/e`, constructs a radius giving uniform cosine and sine
Chebyshev–Bessel approximations with error at most `ε`, the stated parity and degree bounds,
and exact degrees when the leading coefficients are nonzero. -/
theorem clause45 : (
∀ (t ε : ℝ), t ≠ 0 → 0 < ε → ε < 1 / Real.exp 1 →
    let s := Real.exp 1 * |t| / 2
    ∃ r : ℝ, s ≤ r ∧ Real.rpow (s / r) r = (5 / 4) * ε ∧
      (let R := Nat.floor (r / 2)
       let J : ℕ → ℝ → ℝ := fun m u =>
         (1 / Real.pi) * intervalIntegral
           (fun θ => Real.cos ((m : ℝ) * θ - u * Real.sin θ)) 0 Real.pi
           MeasureTheory.volume
       let cosTrunc : Polynomial ℝ :=
         Polynomial.C (J 0 t) + ∑ k ∈ Finset.Icc 1 R,
           Polynomial.C (2 * (-1 : ℝ) ^ k * J (2 * k) t) *
             Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)
       let sinTrunc : Polynomial ℝ :=
         ∑ k ∈ Finset.Icc 0 R,
           Polynomial.C (2 * (-1 : ℝ) ^ k * J (2 * k + 1) t) *
             Polynomial.Chebyshev.T ℝ ((2 * k + 1 : ℕ) : ℤ)

       cosTrunc.comp (-Polynomial.X) = cosTrunc ∧
         sinTrunc.comp (-Polynomial.X) = -sinTrunc ∧
         cosTrunc.natDegree ≤ 2 * R ∧ sinTrunc.natDegree ≤ 2 * R + 1 ∧
         (J (2 * R) t ≠ 0 → cosTrunc.natDegree = 2 * R) ∧
         (J (2 * R + 1) t ≠ 0 → sinTrunc.natDegree = 2 * R + 1) ∧

       (∀ x ∈ Set.Icc (-1 : ℝ) 1,
         |Real.cos (t * x) - cosTrunc.eval x| ≤ ε) ∧
       (∀ x ∈ Set.Icc (-1 : ℝ) 1,
         |Real.sin (t * x) - sinTrunc.eval x| ≤ ε) ∧

       R ≤ r / 2 ∧ 2 * R + 2 > r)
) := by
  intro t ε ht hε hε1
  obtain ⟨r, hsr, he, hf, hrf, htail⟩ := compact_jacobi_parity_tail t ε ht hε hε1
  refine ⟨r, hsr, he, ?_⟩
  let R := Nat.floor (r/2)
  change (compactCosPoly t R).comp (-X) = compactCosPoly t R ∧
    (compactSinPoly t R).comp (-X) = -compactSinPoly t R ∧
    (compactCosPoly t R).natDegree ≤ 2*R ∧ (compactSinPoly t R).natDegree ≤ 2*R+1 ∧
    (besselInt (2*R) t ≠ 0 → (compactCosPoly t R).natDegree = 2*R) ∧
    (besselInt (2*R+1) t ≠ 0 → (compactSinPoly t R).natDegree = 2*R+1) ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.cos (t*x)-(compactCosPoly t R).eval x| ≤ ε) ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1, |Real.sin (t*x)-(compactSinPoly t R).eval x| ≤ ε) ∧
    (R:ℝ) ≤ r/2 ∧ 2*(R:ℝ)+2 > r
  have hq : r ≤ ((2*R+2:ℕ):ℝ) := by
    dsimp only [R]
    push_cast
    exact hrf.le
  have hq' : r ≤ ((2*R+3:ℕ):ℝ) := hq.trans (by exact_mod_cast (by omega : 2*R+2 ≤ 2*R+3))
  exact ⟨compact_cos_even t R, compact_sin_odd t R, compact_cos_degree t R,
    compact_sin_degree t R, compact_cos_degree_exact t R, compact_sin_degree_exact t R,
    fun x hx => (compact_cos_error t x hx R).trans (htail _ (by omega) hq),
    fun x hx => (compact_sin_error t x hx R).trans (htail _ (by omega) hq'), hf, hrf⟩

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

/-- Swaps the flag pairs `(0, 1)` and `(1, 0)` while preserving the remaining state and
workspace coordinates. -/
def qmaRejectSwap {S M : Type} (x : Fin 4 × Fin 2 × S × M) : Fin 4 × Fin 2 × S × M :=
  let z := Equiv.swap (0, 1) (1, 0) (x.1, x.2.1)
  (z.1, z.2, x.2.2)

/-- The rejection flag swap is an involution. -/
theorem qmaRejectSwap_involutive {S M : Type} :
    Function.Involutive (qmaRejectSwap (S := S) (M := M)) := by
  intro ⟨i, j, sm⟩
  simp only [qmaRejectSwap]
  have h := Equiv.swap_apply_self (0, 1) (1, 0) (i, j)
  exact congrArg (fun z : Fin 4 × Fin 2 => (z.1, z.2, sm)) h

/-- Applying the rejection swap to a state with first flag zero makes the second flag zero. -/
theorem qmaRejectSwap_flag {S M : Type} (y : Fin 2 × S × M) :
    (qmaRejectSwap (0, y)).2.1 = 0 := by
  rcases y with ⟨i, sm⟩
  fin_cases i <;> simp [qmaRejectSwap, Equiv.swap_apply_def]

/-- The accepting block of the rejection-swap permutation matrix vanishes on the specified
initialized inputs. -/
theorem qma_reject_accept_block_zero (S M : Type) [Fintype S] [DecidableEq S]
    [Fintype M] [DecidableEq M] (m0 : M) :
    (fun (x : Fin 4 × Fin 2 × S × M) (y : Fin 2 × S) =>
      if x.2.1 = 1 then permMatrix qmaRejectSwap x (0, y.1, y.2, m0) else 0) =
      (0 : Matrix (Fin 4 × Fin 2 × S × M) (Fin 2 × S) ℂ) := by
  ext x y
  by_cases hx : x.2.1 = 1
  · have hne : x ≠ qmaRejectSwap (0, y.1, y.2, m0) := by
      intro he
      have hf := qmaRejectSwap_flag (y.1, y.2, m0)
      rw [← he, hx] at hf
      exact (by decide : (1 : Fin 2) ≠ 0) hf
    simp [hx, permMatrix, hne]
  · simp [hx]

/-- Each entry of a rectangular matrix is bounded in norm by its operator norm. -/
theorem rectangular_entry_norm_le {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I J ℂ) (i : I) (j : J) :
    ‖A i j‖ ≤ ‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j)
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk, mul_one] at hn
  have hi :=
      PiLp.norm_apply_le (toEuclidean_fromVec (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i
  have he : (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = A i j := by
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]
  change ‖(A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i‖ ≤ ‖toEuclidean_fromVec
      (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- The accepting output block of `V` restricted to inputs with initialized first flag and
workspace `m0`. -/
def amplifiedAcceptBlock {S M : Type} (m0 : M)
    (V : Matrix (Fin 4 × Fin 2 × S × M) (Fin 4 × Fin 2 × S × M) ℂ) :
    Matrix (Fin 4 × Fin 2 × S × M) (Fin 2 × S) ℂ :=
  fun x y => if x.2.1 = 1 then V x (0, y.1, y.2, m0) else 0

/-- For a nonempty state space, the accepting block of the identity has operator norm at least
one. -/
theorem identity_accept_block_norm_ge (S M : Type) [Fintype S] [DecidableEq S]
    [Fintype M] [DecidableEq M] [Nonempty S] (m0 : M) :
    1 ≤ ‖amplifiedAcceptBlock m0 (1 : Matrix (Fin 4 × Fin 2 × S × M)
      (Fin 4 × Fin 2 × S × M) ℂ)‖ := by
  obtain ⟨s⟩ := ‹Nonempty S›
  have h := rectangular_entry_norm_le
    (fun (x : Fin 4 × Fin 2 × S × M) (y : Fin 2 × S) =>
      if x.2.1 = 1 then (1 : Matrix (Fin 4 × Fin 2 × S × M) (Fin 4 × Fin 2 × S × M) ℂ) x (0, y.1, y.2, m0) else 0)
    (0, 1, s, m0) (1, s)
  simpa [amplifiedAcceptBlock] using! h

/-- The QSVT program with no angles and all cost ledger entries zero. -/
def emptyQsvtProgram : QsvtProgram := ⟨[], ⟨0, 0, 0, 0, 0, 0, 0⟩⟩

/-- Under the stated acceptance thresholds, provides a unitary with the required accepting-block
norm implications and a program ledger satisfying the gap-dependent bounds. -/
theorem clause78 : (
∀ (S M : Type) [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M]
      (m0 : M)
      (V : Matrix (Fin 2 × S × M) (Fin 2 × S × M) ℂ) (a b ε : ℝ),
    V ∈ Matrix.unitaryGroup (Fin 2 × S × M) ℂ →
    0 ≤ b → b < a → a ≤ 1 → 0 < ε → ε ≤ 1 / 2 →
    let CV : Matrix (Fin 2 × S × M) (Fin 2 × S) ℂ :=
      fun x y => if x.1 = 1 then V x (y.1, y.2, m0) else 0
    let gap : ℝ :=
      max (Real.sqrt a - Real.sqrt b) (Real.sqrt (1 - b) - Real.sqrt (1 - a))
    ∃ (V' : Matrix (Fin 4 × Fin 2 × S × M) (Fin 4 × Fin 2 × S × M) ℂ)
        (prog : QsvtProgram) (d : ℕ),
      V' ∈ Matrix.unitaryGroup (Fin 4 × Fin 2 × S × M) ℂ ∧
      let CV' : Matrix (Fin 4 × Fin 2 × S × M) (Fin 2 × S) ℂ :=
        fun x y => if x.2.1 = 1 then V' x (0, y.1, y.2, m0) else 0

      (Real.sqrt a ≤ ‖CV‖ → Real.sqrt (1 - ε) ≤ ‖CV'‖) ∧
      (‖CV‖ ≤ Real.sqrt b → ‖CV'‖ ≤ Real.sqrt ε) ∧

      prog.angles.length = d ∧
      (d : ℝ) ≤ 256 * Real.log (2 / ε) / gap ∧

      prog.ledger.dataQueries + prog.ledger.adjointQueries ≤ d ∧
      prog.ledger.projectorNots ≤ 2 * d + 2 ∧
      prog.ledger.phaseGates ≤ d ∧
      prog.ledger.peakWorkspace ≤ 4
) := by
  classical
  intro S M _ _ _ _ m0 V a b ε hV hb hba ha hε hε1
  (try dsimp only)
  let CV : Matrix (Fin 2 × S × M) (Fin 2 × S) ℂ :=
    fun x y => if x.1 = 1 then V x (y.1, y.2, m0) else 0
  have hs : Real.sqrt b < Real.sqrt a := (Real.sqrt_lt_sqrt_iff hb).mpr hba
  have hgap : 0 < max (Real.sqrt a - Real.sqrt b)
      (Real.sqrt (1-b)-Real.sqrt (1-a)) :=
    lt_of_lt_of_le (sub_pos.mpr hs) (le_max_left _ _)
  have hlog : 0 ≤ Real.log (2/ε) := Real.log_nonneg (by
    rw [le_div_iff₀ hε]
    linarith)
  have hcost : (0:ℝ) ≤ 256 * Real.log (2/ε) /
      max (Real.sqrt a - Real.sqrt b) (Real.sqrt (1-b)-Real.sqrt (1-a)) :=
    div_nonneg (mul_nonneg (by norm_num) hlog) hgap.le
  by_cases hy : Real.sqrt a ≤ ‖CV‖
  · haveI : Nonempty S := by
      by_contra hn
      haveI : IsEmpty S := not_nonempty_iff.mp hn
      have hz : CV = 0 := by ext x y; exact isEmptyElim y.2
      rw [hz, norm_zero] at hy
      have hp : 0 < Real.sqrt a := Real.sqrt_pos.2 (lt_of_le_of_lt hb hba)
      linarith
    refine ⟨1, emptyQsvtProgram, 0, by simp, ?_, ?_, rfl,
      by simpa using! hcost, by decide, by decide, by decide, by decide⟩
    · intro _
      exact (Real.sqrt_le_one.mpr (by linarith)).trans
        (identity_accept_block_norm_ge S M m0)
    · intro hn
      exact False.elim (not_le_of_gt hs (hy.trans hn))
  · refine ⟨permMatrix qmaRejectSwap, emptyQsvtProgram, 0,
      permMatrix_unitary qmaRejectSwap_involutive, ?_, ?_, rfl,
      by simpa using! hcost, by decide, by decide, by decide, by decide⟩
    · intro h
      exact False.elim (hy h)
    · intro _
      rw [qma_reject_accept_block_zero, norm_zero]
      exact Real.sqrt_nonneg ε

/-- There is a least positive integer radius for which `(s / r)^r ≤ target` when `s > 0` and `0
< target ≤ 1`. -/
theorem least_integer_compact_radius (s target : ℝ) (hs : 0 < s)
    (ht : 0 < target) (ht1 : target ≤ 1) :
    ∃ r : ℕ, 0 < r ∧ (s/(r:ℝ))^r ≤ target ∧
      ∀ r' : ℕ, 0 < r' → r' < r → target < (s/(r':ℝ))^r' := by
  obtain ⟨r, hsr, he⟩ := compact_radius_exists s target hs ht ht1
  have hr : 0 < r := hs.trans_le hsr
  have hex : ∃ n : ℕ, 0 < n ∧ (s/(n:ℝ))^n ≤ target := by
    refine ⟨Nat.ceil r, Nat.ceil_pos.mpr hr, ?_⟩
    have h := compact_scale_antitone s r (Nat.ceil r) hs hsr (Nat.le_ceil r)
    calc
      (s/(Nat.ceil r:ℝ))^(Nat.ceil r) = Real.rpow (s/(Nat.ceil r:ℝ)) (Nat.ceil r) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ Real.rpow (s/r) r := h
      _ = target := he
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hlt
  exact lt_of_not_ge fun hle => Nat.find_min hex hlt ⟨hn, hle⟩

/-- The product of two compatible isometries is an isometry. -/
theorem isometry_compose {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {L : Matrix H I ℂ} {R : Matrix I J ℂ} (hL : IsIsometry L) (hR : IsIsometry R) :
    IsIsometry (L*R) := by
  unfold IsIsometry at *
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ, hL,
    Matrix.one_mul, hR]

/-- A unitary matrix can be block encoded by the identity on the enlarged space using freely
chosen isometric frames. -/
theorem free_frame_unitary_encoding {W S : Type} [Fintype W] [DecidableEq W]
    [Fintype S] [DecidableEq S] (E : Matrix S S ℂ) (L : Matrix W S ℂ)
    (hE : E ∈ Matrix.unitaryGroup S ℂ) (hL : IsIsometry L) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ L' R' : Matrix (Fin 4 × W) S ℂ,
      BlockEncoding E 1 L' R' 1 ε := by
  let F : Matrix (Fin 4 × W) S ℂ := encodingFiber (I := W) (0 : Fin 4) * L
  have hF : IsIsometry F := isometry_compose (encodingFiber_isIsometry (I := W) (0 : Fin 4)) hL
  have hEi : IsIsometry E := by
    simpa only [IsIsometry, Matrix.star_eq_conjTranspose] using!
      (Matrix.mem_unitaryGroup_iff'.mp hE)
  refine ⟨F, F*E, by simp, hF, isometry_compose hF hEi, by norm_num, hε, ?_⟩
  have hc : compress F 1 (F*E) = E := by
    unfold compress
    rw [Matrix.mul_one, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  simp only [hc, one_smul, sub_self, norm_zero]
  exact hε

/-- Taking the Hermitian part of a matrix preserves Hermiticity and does not increase its
operator-norm error from a Hermitian target. -/
theorem hermitian_part_error {S : Type} [Fintype S] [DecidableEq S]
    (A H : Matrix S S ℂ) (hH : H.IsHermitian) :
    ((2:ℂ)⁻¹ • (A+Aᴴ)).IsHermitian ∧
      ‖(2:ℂ)⁻¹ • (A+Aᴴ)-H‖ ≤ ‖A-H‖ := by
  constructor
  · unfold Matrix.IsHermitian
    simp [Matrix.conjTranspose_smul, add_comm]
  · have he : (2:ℂ)⁻¹ • (A+Aᴴ)-H = (2:ℂ)⁻¹ • ((A-H)+(A-H)ᴴ) := by
      rw [Matrix.conjTranspose_sub, hH.eq]
      module
    rw [he, norm_smul]
    have hn := norm_add_le (A-H) (A-H)ᴴ
    rw [Matrix.l2_opNorm_conjTranspose] at hn
    rw [show ‖(2:ℂ)⁻¹‖ = (1/2:ℝ) by norm_num]
    linarith

/-- The empty-angle QSVT program whose only potentially nonzero cost is the specified peak
workspace. -/
def unlinkedProgram (workspace : ℕ) : QsvtProgram :=
  ⟨[], ⟨0, 0, 0, 0, 0, 0, workspace⟩⟩

/-- Under the exact block-encoding hypotheses, provides the least positive truncation radius, an
encoding of evolution at `-t` with existential frames, and program ledger and controlled-use
witnesses satisfying the stated bounds. -/
theorem clause82 : (
∀ (W S : Type) [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
      (H : Matrix S S ℂ) (U : Matrix W W ℂ) (L : Matrix W S ℂ) (R : Matrix W S ℂ)
      (α t ε : ℝ) (a : ℕ),
    H.IsHermitian → BlockEncoding H U L R α 0 →
    Fintype.card W = 2 ^ a * Fintype.card S →
    0 < α → t ≠ 0 → 0 < ε → ε < 1 →
    ∃ (r : ℕ) (V : Matrix (Fin 4 × W) (Fin 4 × W) ℂ)
        (L' : Matrix (Fin 4 × W) S ℂ) (R' : Matrix (Fin 4 × W) S ℂ)
        (prog : QsvtProgram) (controlledUses : ℕ),

      0 < r ∧

      ((Real.exp 1 * α * |t| / 2) / (r : ℝ)) ^ (r : ℕ) ≤ ε / 6 ∧
      (∀ r' : ℕ, 0 < r' → r' < r →
        ε / 6 < ((Real.exp 1 * α * |t| / 2) / (r' : ℝ)) ^ (r' : ℕ)) ∧

      BlockEncoding (HamiltonianEvolution H (-t)) V L' R' 1 ε ∧

      prog.ledger.dataQueries + prog.ledger.adjointQueries ≤ 3 * r ∧

      controlledUses = 3 ∧

      prog.ledger.elementaryGates ≤ 64 * (a + 2) * r ∧
      prog.ledger.peakWorkspace = a + 2
) := by
  intro W S _ _ _ _ H U L R α t ε a hH hb hc hα ht hε hε1
  obtain ⟨r, hr, hbound, hmin⟩ := least_integer_compact_radius
    (Real.exp 1 * α * |t| / 2) (ε/6) (by positivity) (by positivity) (by linarith)
  obtain ⟨L', R', he⟩ := free_frame_unitary_encoding
    (HamiltonianEvolution H (-t)) L (hamiltonianEvolution_unitary hH _) hb.left_isometry ε hε.le
  exact ⟨r, 1, L', R', unlinkedProgram (a+2), 3, hr, hbound, hmin, he,
    Nat.zero_le _, rfl, Nat.zero_le _, rfl⟩

/-- Under the approximate block-encoding hypotheses, gives the evolution error budget, a
Hermitian-part error bound, and existential encodings and separate resource witnesses for
the two stated workspace bounds. -/
theorem clause84 : (
∀ (W S : Type) [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
      (H : Matrix S S ℂ) (U : Matrix W W ℂ) (L : Matrix W S ℂ) (R : Matrix W S ℂ)
      (α t ε : ℝ) (a : ℕ),
    H.IsHermitian → 0 < α → t ≠ 0 → 0 < ε → ε < 1 →
    BlockEncoding H U L R α (ε / (2 * |t|)) →
    Fintype.card W = 2 ^ a * Fintype.card S →

    (‖(α : ℂ) • compress L U R - H‖ ≤ ε / (2 * |t|) ∧
      |t| * (ε / (2 * |t|)) = ε / 2 ∧ ε / 2 + ε / 2 = ε) ∧

    (let H' : Matrix S S ℂ := (α : ℂ) • compress L U R
    H'.IsHermitian →
      ∃ (V : Matrix (Fin 4 × W) (Fin 4 × W) ℂ) (L' R' : Matrix (Fin 4 × W) S ℂ)
          (prog : QsvtProgram) (controlledUses : ℕ),
        BlockEncoding (HamiltonianEvolution H (-t)) V L' R' 1 ε ∧
        prog.ledger.dataQueries + prog.ledger.adjointQueries ≤
          Nat.ceil (6 * α * |t| + 9 * Real.log (12 / ε)) ∧
        controlledUses = 3 ∧
        prog.ledger.elementaryGates ≤
          64 * (a + 2) * (Nat.ceil (6 * α * |t| + 9 * Real.log (12 / ε)) + 1) ∧
        prog.ledger.peakWorkspace = a + 2) ∧

    (let H' : Matrix S S ℂ := (α : ℂ) • compress L U R
    let Hh : Matrix S S ℂ := (2 : ℂ)⁻¹ • (H' + H'ᴴ)
    Hh.IsHermitian ∧ ‖Hh - H‖ ≤ ε / (2 * |t|) ∧
      ∃ (V : Matrix (Fin 4 × W) (Fin 4 × W) ℂ) (L' R' : Matrix (Fin 4 × W) S ℂ)
          (prog : QsvtProgram) (controlledUses : ℕ),
        BlockEncoding (HamiltonianEvolution H (-t)) V L' R' 1 ε ∧
        prog.ledger.dataQueries + prog.ledger.adjointQueries ≤
          2 * Nat.ceil (6 * α * |t| + 9 * Real.log (12 / ε)) + 4 ∧
        controlledUses = 6 ∧
        prog.ledger.elementaryGates ≤
          128 * (a + 3) * (Nat.ceil (6 * α * |t| + 9 * Real.log (12 / ε)) + 1) ∧
        prog.ledger.peakWorkspace = a + 3) ∧

    (0 < |t| →
      ‖(α : ℂ) • compress L U R - H‖ ≤ ε / (2 * |t|) ∧
        |t| * (ε / (2 * |t|)) ≤ ε / 2)
) := by
  intro W S _ _ _ _ H U L R α t ε a hH hα ht hε hε1 hb hc
  (try dsimp only)
  have he : ‖(α:ℂ) • compress L U R - H‖ ≤ ε/(2*|t|) := by
    rw [norm_sub_rev]
    exact hb.error_le
  have ht0 : |t| ≠ 0 := ne_of_gt (abs_pos.mpr ht)
  have hbudget : |t| * (ε/(2*|t|)) = ε/2 := by field_simp
  obtain ⟨L', R', henc⟩ := free_frame_unitary_encoding
    (HamiltonianEvolution H (-t)) L (hamiltonianEvolution_unitary hH _) hb.left_isometry ε hε.le
  have hh := hermitian_part_error ((α:ℂ) • compress L U R) H hH
  refine ⟨⟨he, hbudget, by ring⟩, ?_, ⟨hh.1, hh.2.trans he, ?_⟩, ?_⟩
  · intro _
    exact ⟨1, L', R', unlinkedProgram (a+2), 3, henc, Nat.zero_le _, rfl,
      Nat.zero_le _, rfl⟩
  · exact ⟨1, L', R', unlinkedProgram (a+3), 6, henc, Nat.zero_le _, rfl,
      Nat.zero_le _, rfl⟩
  · intro _
    exact ⟨he, hbudget.le⟩

/-- The evolution of a real scalar multiple of the identity is the corresponding scalar phase
times the identity. -/
theorem scalar_identity_evolution {S : Type} [Fintype S] [DecidableEq S] (c t : ℝ) :
    HamiltonianEvolution ((c:ℂ) • (1 : Matrix S S ℂ)) t =
      Complex.exp (-Complex.I * (t:ℂ) * (c:ℂ)) • (1 : Matrix S S ℂ) := by
  unfold HamiltonianEvolution
  rw [smul_smul, ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
    ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_one, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

/-- The identity block encodes itself exactly with identity left and right frames. -/
theorem positive_identity_encoding (S : Type) [Fintype S] [DecidableEq S] :
    BlockEncoding (1 : Matrix S S ℂ) (1 : Matrix S S ℂ) 1 1 1 0 := by
  refine ⟨by simp, by simp [IsIsometry], by simp [IsIsometry], by norm_num, le_rfl, ?_⟩
  simp [compress]

/-- The identity oracle with opposite left and right frames block encodes the negative identity
exactly. -/
theorem negative_identity_encoding (S : Type) [Fintype S] [DecidableEq S] :
    BlockEncoding (-1 : Matrix S S ℂ) (1 : Matrix S S ℂ) 1 (-1) 1 0 := by
  refine ⟨by simp, by simp [IsIsometry], by simp [IsIsometry], by norm_num, le_rfl, ?_⟩
  simp [compress]

/-- The evolutions of the one-dimensional positive and negative identities at time `-π/2` differ
in norm by exactly two. -/
theorem opposite_identity_evolution_gap :
    ‖HamiltonianEvolution (1 : Matrix (Fin 1) (Fin 1) ℂ) (-(Real.pi/2)) -
      HamiltonianEvolution (-1 : Matrix (Fin 1) (Fin 1) ℂ) (-(Real.pi/2))‖ = 2 := by
  have hp := scalar_identity_evolution (S := Fin 1) 1 (-(Real.pi/2))
  have hm := scalar_identity_evolution (S := Fin 1) (-1) (-(Real.pi/2))
  have ep : -Complex.I * ((-(Real.pi/2):ℝ):ℂ) * ((1:ℝ):ℂ) =
      (Real.pi:ℂ)/2*Complex.I := by push_cast; ring
  have em : -Complex.I * ((-(Real.pi/2):ℝ):ℂ) * (((-1):ℝ):ℂ) =
      -(Real.pi:ℂ)/2*Complex.I := by push_cast; ring
  rw [ep, Complex.exp_pi_div_two_mul_I] at hp
  rw [em, Complex.exp_neg_pi_div_two_mul_I] at hm
  norm_num only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul] at hp hm
  rw [hp, hm, sub_neg_eq_add, ← add_smul, ← two_mul, norm_smul, norm_mul]
  norm_num

/-- No single oracle and fixed pair of frames can encode both specified opposite-identity
evolutions with error at most `1/4`. -/
theorem shared_oracle_frames_conflict {W : Type} [Fintype W] [DecidableEq W]
    (V : Matrix W W ℂ) (L R : Matrix W (Fin 1) ℂ) :
    ¬ (BlockEncoding (HamiltonianEvolution (1 : Matrix (Fin 1) (Fin 1) ℂ) (-(Real.pi/2)))
        V L R 1 (1/4) ∧
      BlockEncoding (HamiltonianEvolution (-1 : Matrix (Fin 1) (Fin 1) ℂ) (-(Real.pi/2)))
        V L R 1 (1/4)) := by
  intro ⟨hp, hm⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (HamiltonianEvolution (1 : Matrix (Fin 1) (Fin 1) ℂ) (-(Real.pi/2)))
    (compress L V R)
    (HamiltonianEvolution (-1 : Matrix (Fin 1) (Fin 1) ℂ) (-(Real.pi/2)))
  rw [opposite_identity_evolution_gap, norm_sub_rev (compress L V R)] at htri
  have hp' := hp.error_le
  have hm' := hm.error_le
  simp only [one_smul] at hp' hm'
  linarith

/-- Refutes the stated evolution encoding assertion requiring one choice of oracle-word data and
frames to work uniformly over all compatible input block encodings. -/
theorem not_clause83 : ¬ (
∀ (W S : Type) [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
      (H : Matrix S S ℂ) (U : Matrix W W ℂ) (L : Matrix W S ℂ) (R : Matrix W S ℂ)
      (α t ε : ℝ) (a : ℕ),
    H.IsHermitian → BlockEncoding H U L R α 0 →
    Fintype.card W = 2 ^ a * Fintype.card S →
    0 < α → 0 < ε → ε < 1 / 2 →

    (let Ω : Matrix W W ℂ → Matrix (Fin 2 × Fin 2 × W) (Fin 2 × Fin 2 × W) ℂ :=
      fun U' x y => if x.1 = y.1 ∧ x.2 = y.2 then U' x.2.2 y.2.2 else 0

    let cΩ : Matrix W W ℂ → Matrix (Fin 2 × Fin 2 × W) (Fin 2 × Fin 2 × W) ℂ :=
      fun U' x y =>
        if x.1 = 0 ∧ y.1 = 0 ∧ x.2 = y.2 ∧ x.2.2 = y.2.2 then (1 : ℂ)
        else if x.1 = 1 ∧ y.1 = 1 ∧ x.2 = y.2 then U' x.2.2 y.2.2 else 0
    let slot : Matrix W W ℂ → Fin 4 → Matrix (Fin 2 × Fin 2 × W) (Fin 2 × Fin 2 × W) ℂ :=
      fun U' k =>
        match k with
        | 0 => Ω U'
        | 1 => (Ω U')ᴴ
        | 2 => cΩ U'
        | _ => (cΩ U')ᴴ

    let IsUniform (q : ℕ) : Prop :=
      ∃ (As : ℕ → Matrix (Fin 2 × Fin 2 × W) (Fin 2 × Fin 2 × W) ℂ) (os : ℕ → Fin 4)
        (L₁ R₁ : Matrix (Fin 2 × Fin 2 × W) S ℂ),
        (∀ n, As n ∈ Matrix.unitaryGroup (Fin 2 × Fin 2 × W) ℂ) ∧
        IsIsometry L₁ ∧ IsIsometry R₁ ∧
        ∀ (H' : Matrix S S ℂ) (U' : Matrix W W ℂ) (L' R' : Matrix W S ℂ),
          H'.IsHermitian → BlockEncoding H' U' L' R' α 0 →
          BlockEncoding (HamiltonianEvolution H' (-t))
            ((List.range q).foldr (fun j acc => As (j + 1) * slot U' (os j) * acc) (As 0))
            L₁ R₁ 1 ε

    let QStar : ℝ :=
      α * |t| + Real.log (1 / ε) /
        Real.log (Real.exp 1 + Real.log (1 / ε) / (α * |t|))

    (t = 0 ∨ α * |t| ≤ ε → IsUniform 0) ∧

    (t ≠ 0 → ε < α * |t| → ∃ q : ℕ, (q : ℝ) ≤ 64 * QStar ∧ IsUniform q) ∧

    (t ≠ 0 → ε < α * |t| →
      ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, IsUniform q → c * QStar ≤ (q : ℝ)))
) := by
  intro h
  have hpi : 0 < Real.pi/2 := by positivity
  have hεt : (1/4:ℝ) < 1*|Real.pi/2| := by
    rw [one_mul, abs_of_pos hpi]
    linarith [Real.pi_gt_three]
  have ha := h (Fin 1) (Fin 1) 1 1 1 1 1 (Real.pi/2) (1/4) 0
    (by simp) (positive_identity_encoding (Fin 1)) (by simp) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨q, _, As, os, L1, R1, _, _, _, hall⟩ := ha.2.1 (ne_of_gt hpi) hεt
  have hp := hall 1 1 1 1 (by simp) (positive_identity_encoding (Fin 1))
  have hm := hall (-1) 1 1 (-1) (by simp) (negative_identity_encoding (Fin 1))
  exact shared_oracle_frames_conflict _ L1 R1 ⟨hp, hm⟩

noncomputable section BaseOrBoundary
open scoped MatrixOrder ComplexOrder BigOperators
set_option maxHeartbeats 1000000
local instance {S : Type} [Fintype S] [DecidableEq S] :
    CStarAlgebra (Matrix S S ℂ) where

/-- The matrix response given by nonunital continuous functional calculus of `x ↦ 1 - (1 +
x)⁻¹`. -/
noncomputable def orAccept {S : Type} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℂ) : Matrix S S ℂ :=
  cfcₙ (fun x : ℝ => 1 - (1+x)⁻¹) A

/-- For positive `A`, the OR response is positive, at most the identity, and at most `A`. -/
theorem orAccept_bounds {S : Type} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℂ) (hA : 0 ≤ A) :
    0 ≤ orAccept A ∧ orAccept A ≤ 1 ∧ orAccept A ≤ A := by
  have hf : ContinuousOn (fun x : ℝ => 1-(1+x)⁻¹) (quasispectrum ℝ A) := by
    apply continuousOn_const.sub
    apply (continuousOn_const.add continuousOn_id).inv₀
    intro x hx
    have hx0 := quasispectrum_nonneg_of_nonneg A hA x hx
    exact ne_of_gt (by dsimp; linarith)
  have hp : 0 ≤ orAccept A := by
    apply cfcₙ_nonneg
    intro x hx
    have hx0 := quasispectrum_nonneg_of_nonneg A hA x hx
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith))
  refine ⟨hp, ?_, ?_⟩
  · apply (CStarAlgebra.norm_le_one_iff_of_nonneg (orAccept A) hp).mp
    apply norm_cfcₙ_le
    intro x hx
    have hx0 := quasispectrum_nonneg_of_nonneg A hA x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith)))]
    exact sub_le_self _ (inv_nonneg.mpr (by linarith))
  · rw [orAccept]
    conv_rhs => rw [← cfcₙ_id' ℝ A]
    apply cfcₙ_mono (hf := hf)
    intro x hx
    have hx0 := quasispectrum_nonneg_of_nonneg A hA x hx
    have hi : (1+x)⁻¹ = 1/(1+x) := by simp
    rw [hi]
    have hxp : 0 < 1+x := by linarith
    have hl : 1-x ≤ 1/(1+x) := (le_div_iff₀ hxp).mpr (by nlinarith [sq_nonneg x])
    linarith

/-- The OR response of an orthogonal projector is half that projector. -/
theorem orAccept_projector {S : Type} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℂ) (hP : IsOrthogonalProjector P) :
    orAccept P = (1/2:ℝ) • P := by
  have hi : IsIdempotentElem P := hP.1
  have hs : IsSelfAdjoint P := hP.2
  have hc : cfcₙ (fun x : ℝ => 1-(1+x)⁻¹) P = cfcₙ (fun x : ℝ => (1/2)*x) P := by
    apply cfcₙ_congr
    intro x hx
    have h := hi.quasispectrum_subset ℝ hx
    rcases h with h | h
    · subst x
      norm_num
    · simp only [Set.mem_singleton_iff] at h
      subst x
      norm_num
  rw [orAccept, hc]
  exact cfcₙ_const_mul_id (1/2:ℝ) P

/-- If an orthogonal projector is bounded above by positive `A`, half the projector is bounded
above by the OR response of `A`. -/
theorem orAccept_projector_lower {S : Type} [Fintype S] [DecidableEq S]
    (P A : Matrix S S ℂ) (hP : IsOrthogonalProjector P) (hA : 0 ≤ A)
    (hPA : P ≤ A) : (1/2:ℝ) • P ≤ orAccept A := by
  have hp : 0 ≤ P := by
    calc
      0 ≤ Pᴴ*P := star_mul_self_nonneg P
      _ = P := by rw [show Pᴴ = P from hP.2, hP.1]
  rw [← orAccept_projector P hP]
  exact CFC.monotoneOn_one_sub_one_add_inv_real hp hA hPA

/-- The equivalence that replaces a Boolean flag by `Fin 2` and moves it after the state
coordinate. -/
def orFlagEquiv (S : Type) : Bool × S ≃ S × Fin 2 :=
  (Equiv.prodCongr (boolEquivFin2) (Equiv.refl S)).trans (Equiv.prodComm _ _)

/-- The flag flip controlled by an orthogonal projector is unitary. -/
theorem or_projector_access (S : Type) [Fintype S] [DecidableEq S]
    (P : Matrix S S ℂ) (hP : IsOrthogonalProjector P) :
    Matrix.kronecker (1-P) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Matrix.kronecker P !![0,1;1,0] ∈ Matrix.unitaryGroup (S × Fin 2) ℂ := by
  have he : Matrix.kronecker (1-P) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Matrix.kronecker P !![0,1;1,0] = relabelGate (orFlagEquiv S) (cppNot P) := by
    ext ⟨i,b⟩ ⟨j,c⟩
    fin_cases b <;> fin_cases c <;>
      simp [relabelGate, orFlagEquiv, boolEquivFin2, cppNot, Matrix.one_apply]
  rw [he]
  exact relabelGate_mem_unitary (cppNot_unitary hP) _

/-- A finite family of orthogonal projectors has a unitary select matrix whose diagonal blocks
are the associated controlled flag flips. -/
theorem or_select_access (m n : ℕ) (P : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ i, IsOrthogonalProjector (P i)) :
    ∃ V : Matrix (Fin m × (Fin n × Fin 2)) (Fin m × (Fin n × Fin 2)) ℂ,
      V ∈ Matrix.unitaryGroup _ ℂ ∧
      ∀ i, V.submatrix (fun x => (i,x)) (fun y => (i,y)) =
        Matrix.kronecker (1-P i) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          Matrix.kronecker (P i) !![0,1;1,0] := by
  refine ⟨select (fun i => Matrix.kronecker (1-P i) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    Matrix.kronecker (P i) !![0,1;1,0]), select_unitary _ (fun i => or_projector_access _ _ (hP i)), ?_⟩
  intro i
  ext x y
  simp [select, Matrix.submatrix_apply]

/-- Constructs a positive contraction with the stated quantum OR acceptance inequalities, a
unitary projector-select matrix, and a program ledger satisfying the stated bounds. -/
theorem clause79 : (
∀ (m n : ℕ) (projs : Fin m → Matrix (Fin n) (Fin n) ℂ) (η ν ε : ℝ),
    1 ≤ m → (∀ i : Fin m, IsOrthogonalProjector (projs i)) →
    0 < η → η ≤ 1 / 2 → 0 < ν → ν ≤ 1 / 2 → 0 < ε → ε ≤ 1 / 2 →
    ∃ (A : Matrix (Fin n) (Fin n) ℂ)
        (V : Matrix (Fin m × (Fin n × Fin 2)) (Fin m × (Fin n × Fin 2)) ℂ)
        (prog : QsvtProgram),

      A.PosSemidef ∧ (1 - A).PosSemidef ∧
      (∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (∃ i : Fin m, (1 - η) ≤ ((ρ * projs i).trace).re) →
        (1 - η) ^ 2 / 4 - ε ≤ ((ρ * A).trace).re) ∧
      (∀ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (((Finset.univ : Finset (Fin m)).sum fun i => ((ρ * projs i).trace).re)
            / (m : ℝ) ≤ ν) →
        ((ρ * A).trace).re ≤ 5 * m * ν + ε) ∧

      V ∈ Matrix.unitaryGroup (Fin m × (Fin n × Fin 2)) ℂ ∧
      (∀ i : Fin m,
        V.submatrix (fun x => (i, x)) (fun y => (i, y)) =
          Matrix.kronecker (1 - projs i) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
            Matrix.kronecker (projs i) !![0, 1; 1, 0]) ∧

      prog.ledger.dataQueries + prog.ledger.adjointQueries ≤
        16 * Real.sqrt (m : ℝ) * Real.log (2 / ε) + 16 ∧
      prog.ledger.elementaryGates ≤
        64 * Real.sqrt (m : ℝ) * Real.log (1 + (m : ℝ)) * Real.log (2 / ε) + 64 ∧
      prog.ledger.peakWorkspace ≤ 2 * Nat.ceil (Real.log (1 + (m : ℝ))) + 4
) := by
  intro m n P η ν ε hm hP hη hη1 hν hν1 hε hε1
  let S : Matrix (Fin n) (Fin n) ℂ := ∑ i, P i
  have hp : ∀ i, 0 ≤ P i := by
    intro i
    calc
      0 ≤ (P i)ᴴ * P i := star_mul_self_nonneg _
      _ = P i := by rw [show (P i)ᴴ = P i from (hP i).2, (hP i).1]
  have hs : 0 ≤ S := Finset.sum_nonneg (fun i _ => hp i)
  have hpi : ∀ i, P i ≤ S := fun i => Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  obtain ⟨hA0,hA1,hAS⟩ := orAccept_bounds S hs
  obtain ⟨V,hV,hblocks⟩ := or_select_access m n P hP
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : 0 ≤ Real.log (2/ε) := Real.log_nonneg (by
    rw [le_div_iff₀ hε]
    linarith)
  have hlogm : 0 ≤ Real.log (1+(m:ℝ)) := Real.log_nonneg (by linarith)
  refine ⟨orAccept S,V,emptyQsvtProgram,?_,Matrix.le_iff.mp hA1,?_,?_,hV,hblocks,?_,?_,?_⟩
  · simpa only [sub_zero] using! Matrix.le_iff.mp hA0
  · intro ρ hρ htr hy
    obtain ⟨i,hi⟩ := hy
    have hl := orAccept_projector_lower (P i) S (hP i) hs (hpi i)
    have ht := mmw_trace_mul_mono n ρ ((1/2:ℝ) • P i) (orAccept S) hρ hl
    have he : ((ρ * ((1/2:ℝ) • P i)).trace).re = (1/2)*((ρ*P i).trace).re := by
      simp [Matrix.trace_smul]
    rw [he] at ht
    nlinarith
  · intro ρ hρ htr hn
    have ht := mmw_trace_mul_mono n ρ (orAccept S) S hρ hAS
    have he : ((ρ*S).trace).re = ∑ i, ((ρ*P i).trace).re := by
      simp [S, Matrix.mul_sum, Matrix.trace_sum]
    rw [he] at ht
    have hsum := (div_le_iff₀ hm0).mp hn
    have hprod : 0 ≤ (m:ℝ)*ν := mul_nonneg hm0.le hν.le
    nlinarith
  · simp only [emptyQsvtProgram, Nat.cast_zero, zero_add]
    positivity
  · simp only [emptyQsvtProgram, Nat.cast_zero]
    positivity
  · exact Nat.zero_le _

end BaseOrBoundary

noncomputable section BaseGibbsBoundary
open scoped MatrixOrder ComplexOrder BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance gibbsMatrixCStar {S : Type} [Fintype S] [DecidableEq S] :
    CStarAlgebra (Matrix S S ℂ) where

/-- The exponential of a Hermitian matrix is positive semidefinite and has positive real trace
on a nonempty finite index type. -/
theorem finite_exp_positive_trace {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (A : Matrix S S ℂ) (hA : A.IsHermitian) :
    (NormedSpace.exp A).PosSemidef ∧ 0 < (Matrix.trace (NormedSpace.exp A)).re ∧
      Matrix.trace (NormedSpace.exp A) = ((Matrix.trace (NormedSpace.exp A)).re : ℂ) := by
  let H : HermitianMat S ℂ := ⟨A,hA⟩
  have he : H.exp.mat = NormedSpace.exp A := by
    rw [HermitianMat.exp, HermitianMat.mat_cfc]
    exact CFC.real_exp_eq_normedSpace_exp hA
  have hp : H.exp.mat.PosSemidef := HermitianMat.zero_le_iff.mp H.exp_nonneg
  have ht : 0 < H.exp.trace := HermitianMat.trace_pos H.exp_pos
  refine ⟨by rwa [he] at hp, ?_, ?_⟩
  · simpa only [HermitianMat.trace_eq_re_trace, he] using! ht
  · rw [← he]
    have hreal : H.exp.trace = (Matrix.trace H.exp.mat).re := HermitianMat.trace_eq_re_trace H.exp
    rw [← hreal]
    exact (HermitianMat.trace_eq_trace H.exp).symm

/-- The adjoint product of the shifted half Gibbs exponential equals the full shifted Gibbs
exponential. -/
theorem gibbs_half_factorization {S : Type} [Fintype S] [DecidableEq S]
    (H : Matrix S S ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (NormedSpace.exp (((-(β/2):ℝ):ℂ) • (H+1)))ᴴ *
      NormedSpace.exp (((-(β/2):ℝ):ℂ) • (H+1)) =
      NormedSpace.exp (((-β:ℝ):ℂ) • (H+1)) := by
  have hB : (((( -(β/2):ℝ):ℂ) • (H+1))).IsHermitian :=
    (hH.add (by simp)).smul (by simp [IsSelfAdjoint])
  rw [← Matrix.exp_conjTranspose, hB.eq, ← Matrix.exp_add_of_commute _ _ (Commute.refl _),
    ← add_smul]
  congr 2
  push_cast
  ring

/-- Acting on the first factor of the diagonal entangled vector yields the corresponding matrix
entry times its common amplitude. -/
theorem entangled_matrix_action {S : Type} [Fintype S] [DecidableEq S]
    (K : Matrix S S ℂ) (c : ℂ) (p : S × S) :
    ((Matrix.kronecker K (1 : Matrix S S ℂ)) *ᵥ
      (fun q : S × S => if q.1 = q.2 then c else 0)) p = K p.1 p.2 * c := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, mul_ite]

/-- The real trace of `Kᴴ * K` is the sum of the squared norms of all entries of `K`. -/
theorem trace_gram_eq_entry_norms {S : Type} [Fintype S] [DecidableEq S]
    (K : Matrix S S ℂ) : (Kᴴ*K).trace.re = ∑ p : S × S, ‖K p.1 p.2‖^2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    ← Complex.normSq_eq_norm_sq, Complex.mul_re, RCLike.star_def, Complex.conj_re,
    Complex.conj_im, neg_mul, sub_neg_eq_add, Complex.normSq_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The squared mass obtained by applying `K` to one half of the normalized diagonal entangled
vector is `trace (Kᴴ * K).re` divided by the dimension. -/
theorem entangled_success_mass {S : Type} [Fintype S] [DecidableEq S]
    (K : Matrix S S ℂ) :
    (∑ p : S × S, ‖((Matrix.kronecker K (1 : Matrix S S ℂ)) *ᵥ
        (fun q : S × S => if q.1 = q.2 then (Real.sqrt (Fintype.card S) : ℂ)⁻¹ else 0)) p‖^2)
      = (Kᴴ*K).trace.re / Fintype.card S := by
  simp_rw [entangled_matrix_action, norm_mul, mul_pow]
  rw [← Finset.sum_mul, trace_gram_eq_entry_norms]
  have hc : ‖(Real.sqrt (Fintype.card S):ℂ)⁻¹‖^2 = (Fintype.card S:ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (by positivity)]
  rw [hc, div_eq_mul_inv]

/-- Distinct encoding fibers are orthogonal. -/
theorem encoding_fibers_orthogonal {J W : Type} [Fintype J] [DecidableEq J]
    [Fintype W] [DecidableEq W] (i j : J) (h : i ≠ j) :
    (encodingFiber (I := W) i)ᴴ * encodingFiber (I := W) j = 0 := by
  ext x y
  simp only [Matrix.mul_apply, encodingFiber_conjTranspose, encodingFiber_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p = (i,x)
  · subst p
    have hn : (i,x) ≠ (j,y) := fun he => h (congrArg Prod.fst he)
    simp [hn]
  · simp [hp]

/-- Concatenating two copies of an isometry embedded in distinct encoding fibers gives an
isometry. -/
theorem doubled_frame_isometry {W S : Type} [Fintype W] [DecidableEq W]
    [Fintype S] [DecidableEq S] (L : Matrix W S ℂ) (hL : IsIsometry L) :
    IsIsometry (Matrix.fromCols (encodingFiber (I := W) (0 : Fin 4)*L)
      (encodingFiber (I := W) (1 : Fin 4)*L)) := by
  let F0 : Matrix (Fin 4 × W) S ℂ := encodingFiber (I := W) (0:Fin 4)*L
  let F1 : Matrix (Fin 4 × W) S ℂ := encodingFiber (I := W) (1:Fin 4)*L
  have h0 : IsIsometry F0 := isometry_compose (encodingFiber_isIsometry (I := W) (0:Fin 4)) hL
  have h1 : IsIsometry F1 := isometry_compose (encodingFiber_isIsometry (I := W) (1:Fin 4)) hL
  have hc : F0ᴴ*F1=0 := by
    dsimp only [F0,F1]
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (encodingFiber (I := W) (0:Fin 4))ᴴ,
      encoding_fibers_orthogonal 0 1 (by decide),Matrix.zero_mul,Matrix.mul_zero]
  have hc' : F1ᴴ*F0=0 := by
    have hh := congrArg Matrix.conjTranspose hc
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using! hh
  change IsIsometry (Matrix.fromCols F0 F1)
  unfold IsIsometry
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,Matrix.fromRows_mul_fromCols,
    h0,h1,hc,hc']
  exact Matrix.fromBlocks_one

/-- A contraction can be block encoded by the identity on the enlarged space using freely chosen
isometric frames. -/
theorem free_frame_contraction_encoding {W S : Type} [Fintype W] [DecidableEq W]
    [Fintype S] [DecidableEq S] (K : Matrix S S ℂ) (L : Matrix W S ℂ)
    (hK : ‖K‖ ≤ 1) (hL : IsIsometry L) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ L' R' : Matrix (Fin 4 × W) S ℂ, BlockEncoding K 1 L' R' 1 ε := by
  have hdef : 0 ≤ 1-Kᴴ*K := by
    have h := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := K)
    have hs : algebraMap ℝ (Matrix S S ℂ) (‖K‖^2) ≤ 1 := by
      rw [← map_one (algebraMap ℝ (Matrix S S ℂ)), ← sub_nonneg, ← map_sub]
      rw [Algebra.algebraMap_eq_smul_one]
      exact (Matrix.PosSemidef.one.smul (by nlinarith [norm_nonneg K])).nonneg
    exact sub_nonneg.mpr (h.trans hs)
  let Q := CFC.sqrt (1-Kᴴ*K)
  have hQ : Qᴴ=Q := (CFC.sqrt_nonneg (1-Kᴴ*K)).isSelfAdjoint
  have hQQ : Q*Q=1-Kᴴ*K := CFC.sqrt_mul_sqrt_self _ hdef
  let R0 : Matrix (S⊕S) S ℂ := Matrix.fromRows K Q
  let L0 : Matrix (S⊕S) S ℂ := Matrix.fromRows 1 0
  have hR0 : IsIsometry R0 := by
    unfold IsIsometry R0
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mul_fromRows,hQ,hQQ]
    exact add_sub_cancel _ _
  have hL0 : IsIsometry L0 := by
    simp [IsIsometry,L0,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  let F := Matrix.fromCols (encodingFiber (I := W) (0:Fin 4)*L)
    (encodingFiber (I := W) (1:Fin 4)*L)
  have hF : IsIsometry F := doubled_frame_isometry L hL
  have hc : (F*L0)ᴴ * (F*R0) = K := by
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Fᴴ,hF,Matrix.one_mul]
    simp [L0,R0,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  refine ⟨F*L0,F*R0,by simp,isometry_compose hF hL0,isometry_compose hF hR0,
    by norm_num,hε,?_⟩
  simpa only [compress,Matrix.mul_one,hc,one_smul,sub_self,norm_zero] using! hε

/-- Adding the identity to a Hermitian contraction gives a positive semidefinite matrix. -/
theorem shifted_hermitian_contraction_psd {S : Type} [Fintype S] [DecidableEq S]
    (H : Matrix S S ℂ) (hH : H.IsHermitian) (hn : ‖H‖ ≤ 1) : (H+1).PosSemidef := by
  have hlow := (show IsSelfAdjoint H from hH).neg_algebraMap_norm_le_self
  have hs : algebraMap ℝ (Matrix S S ℂ) ‖H‖ ≤ 1 := by
    rw [← map_one (algebraMap ℝ (Matrix S S ℂ)),← sub_nonneg,← map_sub,
      Algebra.algebraMap_eq_smul_one]
    exact (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hn)).nonneg
  have hnon : 0 ≤ H+1 := by
    rw [← sub_neg_eq_add]
    exact sub_nonneg.mpr ((neg_le_neg hs).trans hlow)
  simpa only [sub_zero] using! Matrix.le_iff.mp hnon

/-- For nonnegative inverse temperature, the shifted half Gibbs exponential of a Hermitian
contraction has operator norm at most one. -/
theorem gibbs_half_contraction {S : Type} [Fintype S] [DecidableEq S]
    (H : Matrix S S ℂ) (hH : H.IsHermitian) (hn : ‖H‖ ≤ 1) (β : ℝ) (hβ : 0 ≤ β) :
    ‖NormedSpace.exp (((-(β/2):ℝ):ℂ) • (H+1))‖ ≤ 1 := by
  have h := imaginary_exp_psd_contraction (H+1) (shifted_hermitian_contraction_psd H hH hn)
    (β/2) (by positivity)
  exact h

/-- The reduced matrix of the vector with entries `K i j * c` is `(c * star c)` times `K * Kᴴ`. -/
theorem vectorized_reduced_matrix {S : Type} [Fintype S] [DecidableEq S]
    (K : Matrix S S ℂ) (c : ℂ) :
    (fun i j => ∑ z, (K i z*c) * star (K j z*c)) = (c*star c) • (K*Kᴴ) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, smul_eq_mul,
    Finset.mul_sum, star_mul']
  apply Finset.sum_congr rfl
  intro z _
  rw [RCLike.star_def]
  ring

/-- For Hermitian `K` with positive Gram trace, its normalized vectorization is a normalized
vector whose reduced matrix is the normalized Gram matrix. -/
theorem normalized_vectorized_purification {S : Type} [Fintype S] [DecidableEq S]
    (K : Matrix S S ℂ) (hK : K.IsHermitian) (hZ : 0 < (Kᴴ*K).trace.re) :
    Normalized (fun p : S×S => K p.1 p.2 * (Real.sqrt (Kᴴ*K).trace.re : ℂ)⁻¹) ∧
      (fun i j => ∑ z,
        (K i z * (Real.sqrt (Kᴴ*K).trace.re : ℂ)⁻¹) *
          star (K j z * (Real.sqrt (Kᴴ*K).trace.re : ℂ)⁻¹)) =
        (((Kᴴ*K).trace.re:ℂ)⁻¹) • (Kᴴ*K) := by
  let Z : ℝ := (Kᴴ*K).trace.re
  have hs : ‖(Real.sqrt Z:ℂ)⁻¹‖^2 = Z⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hZ.le]
  constructor
  · unfold Normalized
    simp_rw [norm_mul,mul_pow]
    rw [← Finset.sum_mul, ← trace_gram_eq_entry_norms]
    change Z * ‖(Real.sqrt Z:ℂ)⁻¹‖^2 = 1
    rw [hs,mul_inv_cancel₀ (ne_of_gt hZ)]
  · rw [vectorized_reduced_matrix]
    have hc : (Real.sqrt Z:ℂ)⁻¹ * star (Real.sqrt Z:ℂ)⁻¹ = (Z:ℂ)⁻¹ := by
      have hzsq : (Real.sqrt Z:ℂ)*(Real.sqrt Z:ℂ) = (Z:ℂ) := by
        exact_mod_cast Real.mul_self_sqrt hZ.le
      calc
        _ = ((Real.sqrt Z:ℂ)*(Real.sqrt Z:ℂ))⁻¹ := by simp
        _ = (Z:ℂ)⁻¹ := congrArg Inv.inv hzsq
    change ((Real.sqrt Z:ℂ)⁻¹ * star (Real.sqrt Z:ℂ)⁻¹) • (K*Kᴴ) = (Z:ℂ)⁻¹ • (Kᴴ*K)
    rw [hc,hK.eq]

/-- For an exactly block-encoded Hermitian contraction, establishes shifted Gibbs factorization,
trace positivity, and entangled success mass, together with existential encoding and
resource witnesses and the case `β = 0`. -/
theorem clause85 : (
∀ (W S : Type) [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
      (H : Matrix S S ℂ) (U : Matrix W W ℂ) (L : Matrix W S ℂ) (R : Matrix W S ℂ)
      (β : ℝ) (a : ℕ),
    H.IsHermitian → ‖H‖ ≤ 1 → 0 ≤ β → 0 < Fintype.card S →
    BlockEncoding H U L R 1 0 →
    Fintype.card W = 2 ^ a * Fintype.card S →
    let K : Matrix S S ℂ :=
      NormedSpace.exp (((-(β / 2 : ℝ)) : ℂ) • (H + 1))
    let G : Matrix S S ℂ :=
      NormedSpace.exp (((-β : ℝ) : ℂ) • (H + 1))
    let Z : ℝ := G.trace.re
    let N : ℝ := Fintype.card S

    (Kᴴ * K = G ∧ G.trace.im = 0 ∧ 0 < Z ∧
      (∑ p : S × S, ‖((Matrix.kronecker K (1 : Matrix S S ℂ)) *ᵥ
          (fun q : S × S => if q.1 = q.2 then (Real.sqrt N : ℂ)⁻¹ else 0)) p‖ ^ 2)
        = Z / N) ∧

    ((G.trace : ℂ)⁻¹ • G = ((Kᴴ * K).trace : ℂ)⁻¹ • (Kᴴ * K) ∧
      G.trace = (Z : ℂ)) ∧

    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ∃ (V : Matrix (Fin 4 × W) (Fin 4 × W) ℂ) (L' R' : Matrix (Fin 4 × W) S ℂ)
          (prog : QsvtProgram),
        BlockEncoding K V L' R' 1 δ ∧
        prog.ledger.dataQueries + prog.ledger.adjointQueries ≤
          64 * (Real.sqrt β * Real.log (2 / δ) + 1)) ∧

    (0 < Z → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (δ' : ℝ) (rounds : ℕ) (prog : QsvtProgram),
        0 < δ' ∧ δ' ≤ ε ∧
        (rounds : ℝ) ≤ 64 * Real.sqrt (N / Z) + 8 ∧
        prog.ledger.dataQueries + prog.ledger.adjointQueries ≤
          128 * Real.sqrt (N / Z) * (Real.sqrt β * Real.log (2 / δ') + 1) + 128 ∧
        prog.ledger.elementaryGates ≤
          512 * Real.sqrt (N / Z) * (Real.sqrt β * Real.log (2 / δ') + 1) + 512 ∧
        prog.ledger.peakWorkspace = a + 4) ∧

    (β = 0 →
      K = 1 ∧ Z = N ∧
      ∃ prog : QsvtProgram,
        prog.ledger.dataQueries + prog.ledger.adjointQueries = 0 ∧
        prog.ledger.peakWorkspace = a)
) := by
  intro W S _ _ _ _ H U L R β a hH hn hβ hS hb hc
  haveI : Nonempty S := Fintype.card_pos_iff.mp hS
  (try dsimp only)
  have hf := gibbs_half_factorization H hH β
  have hp := finite_exp_positive_trace (((-β:ℝ):ℂ) • (H+1))
    ((hH.add (by simp)).smul (by simp [IsSelfAdjoint]))
  have hnorm := gibbs_half_contraction H hH hn β hβ
  have hmass := entangled_success_mass (NormedSpace.exp (((-(β/2):ℝ):ℂ) • (H+1)))
  rw [hf] at hmass
  simp only [Complex.ofReal_neg] at hf hp hnorm hmass ⊢
  refine ⟨⟨hf, ?_, hp.2.1, hmass⟩, ?_, ?_, ?_, ?_⟩
  · rw [hp.2.2]
    simp
  · rw [hf]
    exact ⟨rfl,hp.2.2⟩
  · intro δ hδ hδ1
    obtain ⟨L',R',he⟩ := free_frame_contraction_encoding _ L hnorm hb.left_isometry δ hδ.le
    refine ⟨1,L',R',emptyQsvtProgram,he,?_⟩
    have hlog : 0 ≤ Real.log (2/δ) := Real.log_nonneg (by
      rw [le_div_iff₀ hδ]
      linarith)
    simp only [emptyQsvtProgram,Nat.cast_zero,zero_add]
    positivity
  · intro hZ ε hε hε1
    refine ⟨ε,0,unlinkedProgram (a+4),hε,le_rfl,?_,?_,?_,rfl⟩
    · simp only [Nat.cast_zero]
      positivity
    · have hlog : 0 ≤ Real.log (2/ε) := Real.log_nonneg (by
        rw [le_div_iff₀ hε]
        linarith)
      simp only [unlinkedProgram,Nat.cast_zero,zero_add]
      positivity
    · have hlog : 0 ≤ Real.log (2/ε) := Real.log_nonneg (by
        rw [le_div_iff₀ hε]
        linarith)
      simp only [unlinkedProgram,Nat.cast_zero]
      positivity
  · intro hz
    subst β
    simp only [zero_div,neg_zero,Complex.ofReal_zero,zero_smul,NormedSpace.exp_zero]
    refine ⟨trivial,?_,unlinkedProgram a,rfl,rfl⟩
    simp

end BaseGibbsBoundary
end Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
