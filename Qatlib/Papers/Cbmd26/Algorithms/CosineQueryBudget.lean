/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.UniformPropagatorApproximation
import Qatlib.Foundations.CbmdAnalysis.Core.CosineMassLower

/-!
# Explicit cosine degree and query budgets

Chooses `cosineChosenMass`, `cosineWeightedAccuracy`, and `cosineAAOrder` for cosine-based
second-order algorithms. It bounds the resulting polynomial degree and source-query costs using
`cosineRelativeEnvelope` and explicit logarithmic factors. These results support the
contour-based algorithms of [WangEtAl2026].

## Main statements

* `cosineChosenDegree_le`: bounds the selected polynomial degree.
* `cosineExpectedSourceQueries_le`: bounds the mean amplification multiplicity times the
  source-query count.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open scoped BigOperators

/-- Defines the exponential envelope `exp (τ * sqrt (γ / 2))` divided by the output-norm
estimate `η`. -/
def cosineRelativeEnvelope (γ τ η : ℝ) : ℝ := Real.exp (τ * Real.sqrt (γ / 2)) / η

/-- Defines the finite cosine weight mass at truncation accuracy `ε * η / 8`. -/
def cosineChosenMass (γ τ ε η : ℝ) : ℝ :=
  _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineFiniteWeightMass γ τ (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8))

/-- Defines the sample accuracy `ε * η / (16 * cosineChosenMass γ τ ε η)`. -/
def cosineWeightedAccuracy (γ τ ε η : ℝ) : ℝ := ε * η / (16 * cosineChosenMass γ τ ε η)

/-- The chosen cosine weight mass is positive for positive `γ` and `τ`. -/
theorem cosineChosenMass_pos {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (ε η : ℝ) :
    0 < cosineChosenMass γ τ ε η := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineFiniteWeightMass_pos hγ hτ _

/-- The chosen mass divided by `η` is at most sixteen times the relative envelope times `log (2
+ γ * τ²)`. -/
theorem cosineChosenMass_ratio_le {γ τ η : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hη : 0 < η) (ε : ℝ) :
    cosineChosenMass γ τ ε η / η ≤
      16 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2) := by
  have h := div_le_div_of_nonneg_right
    (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineFiniteWeightMass_le_exp_log hγ hτ
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8))) hη.le
  convert! h using 1
  dsimp only [cosineRelativeEnvelope]
  ring

/-- The weighted sample accuracy is positive when `γ`, `τ`, `ε`, and `η` are positive. -/
theorem cosineWeightedAccuracy_pos {γ τ ε η : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hε : 0 < ε) (hη : 0 < η) :
    0 < cosineWeightedAccuracy γ τ ε η := by
  unfold cosineWeightedAccuracy
  exact div_pos (mul_pos hε hη) (mul_pos (by norm_num) (cosineChosenMass_pos hγ hτ ε η))

/-- Twice the weighted accuracy times the chosen mass equals `ε * η / 8`. -/
theorem cosineWeightedAccuracy_error {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (ε η : ℝ) :
    2 * cosineWeightedAccuracy γ τ ε η * cosineChosenMass γ τ ε η = ε * η / 8 := by
  unfold cosineWeightedAccuracy
  field_simp [(cosineChosenMass_pos hγ hτ ε η).ne']
  ring

/-- The weighted accuracy is at most one when `ε ≤ 1` and `η` is at most twice the chosen mass. -/
theorem cosineWeightedAccuracy_le_one {γ τ ε η : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hε : ε ≤ 1) (hη : 0 < η)
    (hηS : η ≤ 2 * cosineChosenMass γ τ ε η) :
    cosineWeightedAccuracy γ τ ε η ≤ 1 := by
  have hS := cosineChosenMass_pos hγ hτ ε η
  unfold cosineWeightedAccuracy
  apply (div_le_one (by positivity)).mpr
  nlinarith

/-- Bounds `log (4 / cosineWeightedAccuracy γ τ ε η)` by the displayed logarithmic expression
involving the relative envelope. -/
theorem cosineWeightedAccuracy_log_le {γ τ ε η : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hε : 0 < ε) (hη : 0 < η) :
    Real.log (4 / cosineWeightedAccuracy γ τ ε η) ≤
      Real.log (2 + 1024 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2) / ε) := by
  have hp := cosineWeightedAccuracy_pos hγ hτ hε hη
  have hm := cosineChosenMass_ratio_le hγ hτ hη ε
  apply Real.log_le_log (by positivity)
  have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ 64 / ε by positivity)
  have he : 4 / cosineWeightedAccuracy γ τ ε η = (64 / ε) * (cosineChosenMass γ τ ε η / η) := by
    unfold cosineWeightedAccuracy
    field_simp
    ring
  rw [he]
  have heR : (64 / ε) * (16 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2)) =
      1024 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2) / ε := by ring
  rw [heR] at h
  linarith

/-- Bounds the integer second-order degree budget by the explicit time, scale, accuracy, and
condition-parameter expression. -/
theorem secondOrderDegreeBudget_le (kind : SecondOrderFamily) {t b κ δq : ℝ}
    (ht : 0 ≤ t) (_hb : 0 ≤ b) (hκ : 0 < κ) (hδq : 0 < δq) (hδq1 : δq ≤ 1) :
    (secondOrderDegreeBudget kind t b κ⁻¹ δq : ℝ) ≤
      ((secondOrderTimeScale kind t * Real.sqrt (2 * b) + Real.log (4 / δq)) /
        Real.log 2 + 1) * (5 + 2048 * κ) := by
  have hτ := secondOrderTimeScale_nonneg kind ht
  have hM : 1 ≤ Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * b)) :=
    Real.one_le_exp (by positivity)
  have h := holomorphic_degree_budget_le κ⁻¹
    (Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * b))) δq
    (inv_pos.mpr hκ) hM hδq hδq1
  have hl : Real.log (4 * Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * b)) / δq) =
      secondOrderTimeScale kind t * Real.sqrt (2 * b) + Real.log (4 / δq) := by
    rw [show 4 * Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * b)) / δq =
      (4 / δq) * Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * b)) by ring,
      Real.log_mul (by positivity : 4 / δq ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
    ring
  simpa only [secondOrderDegreeBudget, hl, div_inv_eq_mul] using! h

/-- Defines the uniform sample scale bound `Lnorm + 1352 * Hnorm * cosineRelativeEnvelope γ τ η
/ ε`. -/
def cosineSelectedBmax (Lnorm Hnorm γ τ ε η : ℝ) : ℝ :=
  Lnorm + 1352 * Hnorm * cosineRelativeEnvelope γ τ η / ε

/-- The selected sample scale bound is nonnegative for nonnegative norm bounds and positive `ε`
and `η`. -/
theorem cosineSelectedBmax_nonneg {Lnorm Hnorm γ τ ε η : ℝ}
    (hL : 0 ≤ Lnorm) (hH : 0 ≤ Hnorm) (hε : 0 < ε) (hη : 0 < η) :
    0 ≤ cosineSelectedBmax Lnorm Hnorm γ τ ε η := by
  unfold cosineSelectedBmax cosineRelativeEnvelope
  positivity

open scoped Matrix.Norms.L2Operator in

/-- Every retained cosine sample's norm-based scale is bounded by `cosineSelectedBmax`. -/
theorem cosineSelectedBmax_bounds_samples {n : Type*} [Fintype n] [DecidableEq n]
    (L H : Matrix n n ℂ) {γ τ ε η : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hε : 0 < ε) (hη : 0 < η) (k : ℕ)
    (hk : k < _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8)) :
    ‖L‖ + _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleScale γ τ k * ‖H‖ ≤
      cosineSelectedBmax ‖L‖ ‖H‖ γ τ ε η := by
  have h := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetained_blockNormalization_le L H hγ hτ
    (show 0 < ε * η / 8 by positivity) k hk
  convert! h using 1
  unfold cosineSelectedBmax cosineRelativeEnvelope
  ring

/-- The second-order time scale is positive for every family at positive time. -/
theorem secondOrderTimeScale_pos (kind : SecondOrderFamily) {t : ℝ} (ht : 0 < t) :
    0 < secondOrderTimeScale kind t := by
  cases kind
  · exact ht
  · exact ht
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale_pos_of_pos ht

/-- Defines the explicit real degree bound using the selected sample scale, logarithmic accuracy
term, and affine condition factor. -/
def cosineDisplayedDegreeBound (Lnorm Hnorm γ τ ε η κ : ℝ) : ℝ :=
  ((τ * Real.sqrt (2 * cosineSelectedBmax Lnorm Hnorm γ τ ε η) +
    Real.log (2 + 1024 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2) / ε)) /
      Real.log 2 + 1) * (5 + 2048 * κ)

/-- The chosen second-order degree budget is at most the displayed cosine degree bound under the
stated positivity and mass conditions. -/
theorem cosineChosenDegree_le (kind : SecondOrderFamily) {Lnorm Hnorm γ t ε η κ : ℝ}
    (hL : 0 ≤ Lnorm) (hH : 0 ≤ Hnorm) (hγ : 0 < γ) (ht : 0 < t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hκ : 0 < κ)
    (hηS : η ≤ 2 * cosineChosenMass γ (secondOrderTimeScale kind t) ε η) :
    (secondOrderDegreeBudget kind t
      (cosineSelectedBmax Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η) κ⁻¹
      (cosineWeightedAccuracy γ (secondOrderTimeScale kind t) ε η) : ℝ) ≤
      cosineDisplayedDegreeBound Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η κ := by
  have hτ := secondOrderTimeScale_pos kind ht
  apply (secondOrderDegreeBudget_le kind ht.le (cosineSelectedBmax_nonneg hL hH hε hη) hκ
    (cosineWeightedAccuracy_pos hγ hτ hε hη)
    (cosineWeightedAccuracy_le_one hγ hτ hε1 hη hηS)).trans
  unfold cosineDisplayedDegreeBound
  exact mul_le_mul_of_nonneg_right
    (add_le_add (div_le_div_of_nonneg_right
      (add_le_add le_rfl (cosineWeightedAccuracy_log_le hγ hτ hε hη))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) le_rfl) (by positivity)

/-- The chosen source-query count `8 * D + 2` is bounded by the same expression with the
displayed real degree bound. -/
theorem cosineChosenSourceQueries_le (kind : SecondOrderFamily) {Lnorm Hnorm γ t ε η κ : ℝ}
    (hL : 0 ≤ Lnorm) (hH : 0 ≤ Hnorm) (hγ : 0 < γ) (ht : 0 < t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hκ : 0 < κ)
    (hηS : η ≤ 2 * cosineChosenMass γ (secondOrderTimeScale kind t) ε η) :
    ((8 * secondOrderDegreeBudget kind t
      (cosineSelectedBmax Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η) κ⁻¹
      (cosineWeightedAccuracy γ (secondOrderTimeScale kind t) ε η) + 2 : ℕ) : ℝ) ≤
      8 * cosineDisplayedDegreeBound Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η κ + 2 := by
  have h := cosineChosenDegree_le kind hL hH hγ ht hε hε1 hη hκ hηS
  push_cast
  linarith

/-- If the true output norm lies between `η` and `C * η`, the envelope based on `η` lies between
the true-output envelope and `C` times it. -/
theorem cosineRelativeEnvelope_compare_output {γ τ η v C : ℝ}
    (hη : 0 < η) (hηv : η ≤ v) (hvC : v ≤ C * η) :
    Real.exp (τ * Real.sqrt (γ / 2)) / v ≤ cosineRelativeEnvelope γ τ η ∧
    cosineRelativeEnvelope γ τ η ≤ C * (Real.exp (τ * Real.sqrt (γ / 2)) / v) := by
  have hv : 0 < v := hη.trans_le hηv
  constructor
  · exact div_le_div_of_nonneg_left (Real.exp_pos _).le hη hηv
  · unfold cosineRelativeEnvelope
    apply (div_le_iff₀ hη).mpr
    have h := mul_le_mul_of_nonneg_left hvC
      (show 0 ≤ Real.exp (τ * Real.sqrt (γ / 2)) / v by positivity)
    have he : Real.exp (τ * Real.sqrt (γ / 2)) / v * v =
      Real.exp (τ * Real.sqrt (γ / 2)) := div_mul_cancel₀ _ hv.ne'
    rw [he] at h
    convert! h using 1
    ring

/-- Bounds the odd amplification multiplicity from the rounded mass-to-output ratio by the
displayed envelope and logarithm expression. -/
theorem cosineAmplificationMultiplier_le {γ τ ε η c : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hη : 0 < η) (hc : 0 ≤ c)
    (hηS : η ≤ 2 * cosineChosenMass γ τ ε η) :
    ((2 * ⌈c * cosineChosenMass γ τ ε η / η⌉₊ + 1 : ℕ) : ℝ) ≤
      16 * (2 * c + 6) * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2) := by
  have hS := cosineChosenMass_pos hγ hτ ε η
  have hr : (1 / 2 : ℝ) ≤ cosineChosenMass γ τ ε η / η := by
    apply (le_div_iff₀ hη).mpr
    linarith
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ c * cosineChosenMass γ τ ε η / η by positivity)).le
  have hm := mul_le_mul_of_nonneg_left (cosineChosenMass_ratio_le hγ hτ hη ε)
    (show 0 ≤ 2 * c + 6 by positivity)
  push_cast
  calc
    _ ≤ 2 * (c * cosineChosenMass γ τ ε η / η + 1) + 1 := by linarith
    _ ≤ (2 * c + 6) * (cosineChosenMass γ τ ε η / η) := by
      rw [show c * cosineChosenMass γ τ ε η / η = c * (cosineChosenMass γ τ ε η / η) by ring]
      nlinarith
    _ ≤ (2 * c + 6) * (16 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2)) := hm
    _ = _ := by ring

/-- Bounds the product of the rounded amplification multiplicity and the chosen source-query
count by the displayed envelope and degree expression. -/
theorem cosineAmplifiedSourceQueries_le (kind : SecondOrderFamily)
    {Lnorm Hnorm γ t ε η κ c : ℝ}
    (hL : 0 ≤ Lnorm) (hH : 0 ≤ Hnorm) (hγ : 0 < γ) (ht : 0 < t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hκ : 0 < κ) (hc : 0 ≤ c)
    (hηS : η ≤ 2 * cosineChosenMass γ (secondOrderTimeScale kind t) ε η) :
    (((2 * ⌈c * cosineChosenMass γ (secondOrderTimeScale kind t) ε η / η⌉₊ + 1) *
      (8 * secondOrderDegreeBudget kind t
        (cosineSelectedBmax Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η) κ⁻¹
        (cosineWeightedAccuracy γ (secondOrderTimeScale kind t) ε η) + 2) : ℕ) : ℝ) ≤
      (16 * (2 * c + 6) * cosineRelativeEnvelope γ (secondOrderTimeScale kind t) η *
        Real.log (2 + γ * secondOrderTimeScale kind t ^ 2)) *
      (8 * cosineDisplayedDegreeBound Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η κ + 2) := by
  have hA := cosineAmplificationMultiplier_le hγ (secondOrderTimeScale_pos kind ht) hη hc hηS
  have hQ := cosineChosenSourceQueries_le kind hL hH hγ ht hε hε1 hη hκ hηS
  rw [Nat.cast_mul]
  exact mul_le_mul hA hQ (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hA)

/-- Defines the positive amplification window as the ceiling of eight times the mass-to-output
ratio, plus one. -/
def cosineAAOrder (γ τ ε η : ℝ) : ℕ := ⌈8 * cosineChosenMass γ τ ε η / η⌉₊ + 1

/-- Defines the mean trial multiplicity as `(cosineAAOrder γ τ ε η + 1) / 2`. -/
def cosineAAMeanMultiplicity (γ τ ε η : ℝ) : ℝ := ((cosineAAOrder γ τ ε η : ℝ) + 1) / 2

/-- The chosen cosine amplification window is positive. -/
theorem cosineAAOrder_pos (γ τ ε η : ℝ) : 0 < cosineAAOrder γ τ ε η := by
  unfold cosineAAOrder
  omega

/-- The chosen amplification window is at least eight times the mass-to-output ratio. -/
theorem cosineAAOrder_threshold (γ τ ε η : ℝ) :
    8 * cosineChosenMass γ τ ε η / η ≤ (cosineAAOrder γ τ ε η : ℝ) := by
  have h := Nat.le_ceil (8 * cosineChosenMass γ τ ε η / η)
  unfold cosineAAOrder
  push_cast
  linarith

/-- The mean amplification multiplicity is at most `112` times the relative envelope times `log
(2 + γ * τ²)`. -/
theorem cosineAAMeanMultiplicity_le {γ τ ε η : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (hη : 0 < η)
    (hηS : η ≤ 2 * cosineChosenMass γ τ ε η) :
    cosineAAMeanMultiplicity γ τ ε η ≤
      112 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2) := by
  have hS := cosineChosenMass_pos hγ hτ ε η
  have hr : (1 / 2 : ℝ) ≤ cosineChosenMass γ τ ε η / η := by
    apply (le_div_iff₀ hη).mpr
    linarith
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ 8 * cosineChosenMass γ τ ε η / η by positivity)).le
  have hm := mul_le_mul_of_nonneg_left (cosineChosenMass_ratio_le hγ hτ hη ε)
    (show (0 : ℝ) ≤ 7 by norm_num)
  unfold cosineAAMeanMultiplicity cosineAAOrder
  push_cast
  calc
    _ ≤ 4 * (cosineChosenMass γ τ ε η / η) + 3 / 2 := by
      rw [show 8 * cosineChosenMass γ τ ε η / η = 8 * (cosineChosenMass γ τ ε η / η) by ring] at hceil ⊢
      linarith
    _ ≤ 7 * (cosineChosenMass γ τ ε η / η) := by linarith
    _ ≤ 7 * (16 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2)) := hm
    _ = _ := by ring

/-- The mean amplification multiplicity times the chosen source-query count satisfies the
displayed cosine query bound [WangEtAl2026]. -/
theorem cosineExpectedSourceQueries_le (kind : SecondOrderFamily)
    {Lnorm Hnorm γ t ε η κ : ℝ}
    (hL : 0 ≤ Lnorm) (hH : 0 ≤ Hnorm) (hγ : 0 < γ) (ht : 0 < t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hκ : 0 < κ)
    (hηS : η ≤ 2 * cosineChosenMass γ (secondOrderTimeScale kind t) ε η) :
    cosineAAMeanMultiplicity γ (secondOrderTimeScale kind t) ε η *
      ((8 * secondOrderDegreeBudget kind t
        (cosineSelectedBmax Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η) κ⁻¹
        (cosineWeightedAccuracy γ (secondOrderTimeScale kind t) ε η) + 2 : ℕ) : ℝ) ≤
      (112 * cosineRelativeEnvelope γ (secondOrderTimeScale kind t) η *
        Real.log (2 + γ * secondOrderTimeScale kind t ^ 2)) *
      (8 * cosineDisplayedDegreeBound Lnorm Hnorm γ (secondOrderTimeScale kind t) ε η κ + 2) := by
  have hA := cosineAAMeanMultiplicity_le hγ (secondOrderTimeScale_pos kind ht) hη hηS
  have hQ := cosineChosenSourceQueries_le kind hL hH hγ ht hε hε1 hη hκ hηS
  apply mul_le_mul hA hQ (Nat.cast_nonneg _)
  have hm : 0 ≤ cosineAAMeanMultiplicity γ (secondOrderTimeScale kind t) ε η := by
    unfold cosineAAMeanMultiplicity
    positivity
  exact hm.trans hA

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
