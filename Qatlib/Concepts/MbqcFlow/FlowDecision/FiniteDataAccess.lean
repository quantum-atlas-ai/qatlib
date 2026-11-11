/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ScopedOracleWorkspace

/-!
# Finite data loading and access guarantees

This module verifies the rational phase and state-preparation constructions of
`FiniteDataAccessDefs`. It proves explicit operator and Euclidean state error bounds,
correctness and rejection properties for dense and sparse loading, and last-write semantics for
Boolean tables.

The finite-register circuit language follows the setting of [NielsenChuang2010].
Preparation-word counts, physical reflection synthesis, clean scoped oracle execution,
dense-read lower bounds, and access charges are stated for the concrete resource accounts
defined here.

## Main statements

* `prepareState_error_le_epsilon`: loaded-state preparation at a chosen positive tolerance.
* `physPrepare_synthesis`: bounded reflection synthesis of the physical preparation matrix.
* `scopedAccess_clean`: logical execution with the workspace bit returned to false.
* `dense_reading_lower_bound`: every universally correct dense loader reads at least the table
  size.
* `clause1_complete`, `clause2_complete`, and `clause3_complete`: collected preparation, access,
  and resource guarantees.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess

open Matrix
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
open scoped Classical BigOperators Matrix.Norms.L2Operator
open Qatlib

set_option autoImplicit false

/-- The squared norm of a complex number with real coordinates `x` and `y` is `x ^ 2 + y ^ 2`. -/
private theorem complexAbs_sq (x y : ℝ) :
    ‖(Complex.ofReal x + Complex.ofReal y * Complex.I)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- The squared distance between two complex numbers is the sum of the squared differences of
their real and imaginary coordinates. -/
private theorem complexDiff_sq (a b p q : ℝ) :
    ‖(Complex.ofReal a + Complex.ofReal b * Complex.I)
        - (Complex.ofReal p + Complex.ofReal q * Complex.I)‖ ^ 2
      = (a - p) ^ 2 + (b - q) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

/-- A nonzero rational complex number has positive squared modulus. -/
private theorem ratSq_pos_of_ne (z : RatComplex) (hz : z ≠ ratZero) : (0 : ℚ) < ratSq z := by
  have hnonneg : 0 ≤ ratSq z := ratSq_nonneg z
  by_contra h
  have hz0 : ratSq z = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hz0' : z.1 ^ 2 + z.2 ^ 2 = 0 := hz0
  have h1 : z.1 = 0 := by
    have hz1 : (z.1 : ℚ) ^ 2 = 0 := by
      have h2pos : (0 : ℚ) ≤ z.2 ^ 2 := by positivity
      have h1pos : (0 : ℚ) ≤ z.1 ^ 2 := by positivity
      linarith
    exact sq_eq_zero_iff.mp hz1
  have h2 : z.2 = 0 := by
    have hz2 : (z.2 : ℚ) ^ 2 = 0 := by
      have h1pos : (0 : ℚ) ≤ z.1 ^ 2 := by positivity
      have h2pos : (0 : ℚ) ≤ z.2 ^ 2 := by positivity
      linarith
    exact sq_eq_zero_iff.mp hz2
  apply hz
  simp only [ratZero]
  exact Prod.ext h1 h2

/-- The rational sign chosen by `ratSign` has square one. -/
private theorem ratSign_sq (q : ℚ) : (ratSign q) ^ 2 = 1 := by
  unfold ratSign
  split_ifs <;> ring

/-- The real absolute value of `ratSign q` is one. -/
private theorem ratSign_abs (q : ℚ) : |(ratSign q : ℝ)| = 1 := by
  unfold ratSign
  split_ifs <;> simp

/-- The square root of a rational squared coordinate divided by a positive mass equals its
absolute value divided by the square root of that mass. -/
private theorem sqrt_sq_over_mass (a : ℚ) (r2 : ℚ) (_hr2 : (0 : ℚ) < r2) :
    Real.sqrt ((a ^ 2 / r2 : ℚ) : ℝ) = |(a : ℝ)| / Real.sqrt (r2 : ℝ) := by
  have hcast : ((a ^ 2 / r2 : ℚ) : ℝ) = ((a : ℝ) ^ 2) / (r2 : ℝ) := by
    push_cast
    ring
  rw [hcast, Real.sqrt_div (sq_nonneg _) (r2 : ℝ), Real.sqrt_sq_eq_abs]

/-- For positive squared modulus, one minus the normalized squared real coordinate equals the
normalized squared imaginary coordinate. -/
private theorem one_sub_ratio (z : RatComplex) (hr2 : (0 : ℚ) < ratSq z) :
    1 - z.1 ^ 2 / ratSq z = z.2 ^ 2 / ratSq z := by
  have hne : ratSq z ≠ 0 := ne_of_gt hr2
  simp only [ratSq] at hne ⊢
  field_simp
  ring

/-- The rational phase approximation lies exactly on the unit circle. -/
theorem phaseApprox_unit (z : RatComplex) (k : ℕ) :
    (phaseApprox z k).1 ^ 2 + (phaseApprox z k).2 ^ 2 = 1 := by
  by_cases hz : z = ratZero
  · subst hz
    simp [phaseApprox, ratZero]
  · simp only [phaseApprox, if_neg hz]
    have hc := rationalPayoffCS_circle (z.1 ^ 2 / ratSq z) k
    have h1 : (ratSign z.1) ^ 2 = 1 := ratSign_sq z.1
    have h2 : (ratSign z.2) ^ 2 = 1 := ratSign_sq z.2
    simp only [mul_pow]
    rw [h1, h2]
    nlinarith [hc]

/-- For nonzero input, the real coordinate of the phase approximation differs from the
normalized real coordinate by at most `16 / 2 ^ k`. -/
private theorem phaseApprox_re_abs (z : RatComplex) (k : ℕ) (hz : z ≠ ratZero) :
    |((phaseApprox z k).1 : ℝ) - (z.1 : ℝ) / Real.sqrt (ratSq z : ℝ)| ≤ 16 / 2 ^ k := by
  have hr2 : (0 : ℚ) < ratSq z := ratSq_pos_of_ne z hz
  have ht0 : (0 : ℚ) ≤ z.1 ^ 2 / ratSq z := div_nonneg (sq_nonneg _) (le_of_lt hr2)
  have ht1 : z.1 ^ 2 / ratSq z ≤ 1 := by
    have hsq : z.1 ^ 2 ≤ ratSq z := by
      have h2 : (z.2 : ℚ) ^ 2 ≤ ratSq z := by
        have h1pos : (0 : ℚ) ≤ z.1 ^ 2 := by positivity
        unfold ratSq
        linarith
      have h2pos : (0 : ℚ) ≤ z.2 ^ 2 := by positivity
      unfold ratSq
      linarith
    exact (div_le_one hr2).mpr hsq
  have hcs := (rationalPayoffCS_sqrt_error (z.1 ^ 2 / ratSq z) k ht0 ht1).2
  rw [sqrt_sq_over_mass z.1 (ratSq z) hr2] at hcs
  have hcast : ((z.1 : ℚ) : ℝ) = (ratSign z.1 : ℝ) * (|(z.1 : ℝ)|) := by
    have h1 : ((z.1 : ℚ) : ℝ) = ((ratSign z.1 * |z.1| : ℚ) : ℝ) := by
      rw [ratSign_mul_abs]
    have h2 : ((ratSign z.1 * |z.1| : ℚ) : ℝ) = (ratSign z.1 : ℝ) * ((|z.1| : ℚ) : ℝ) := by
      norm_cast
    have h3 : ((|z.1| : ℚ) : ℝ) = |(z.1 : ℝ)| := Rat.cast_abs z.1
    calc
      ((z.1 : ℚ) : ℝ) = ((ratSign z.1 * |z.1| : ℚ) : ℝ) := h1
      _ = (ratSign z.1 : ℝ) * ((|z.1| : ℚ) : ℝ) := h2
      _ = (ratSign z.1 : ℝ) * (|(z.1 : ℝ)|) := by rw [h3]
  have habs : |((ratSign z.1 : ℝ) * (|(z.1 : ℝ)|))| = |(z.1 : ℝ)| := by
    rw [abs_mul, ratSign_abs, one_mul]
    exact abs_of_nonneg (abs_nonneg _)
  have hcs' :
      ((ratSign z.1 * (rationalPayoffCS (z.1 ^ 2 / ratSq z) k).2 : ℚ) : ℝ)
        = (ratSign z.1 : ℝ) * (((rationalPayoffCS (z.1 ^ 2 / ratSq z) k).2 : ℚ) : ℝ) := by
      norm_cast
  have hr : Real.sqrt (ratSq z : ℝ) ≠ 0 := by
    have hr2r : (0 : ℝ) < (ratSq z : ℝ) := by exact_mod_cast hr2
    exact ne_of_gt (Real.sqrt_pos.2 hr2r)
  have hkey :
      ((phaseApprox z k).1 : ℝ) - (z.1 : ℝ) / Real.sqrt (ratSq z : ℝ)
        = (ratSign z.1 : ℝ) *
            (((rationalPayoffCS (z.1 ^ 2 / ratSq z) k).2 : ℝ)
              - |(z.1 : ℝ)| / Real.sqrt (ratSq z : ℝ)) := by
    simp only [phaseApprox, if_neg hz]
    rw [hcs', hcast, habs]
    field_simp <;> ring
  rw [hkey, abs_mul, ratSign_abs, one_mul]
  exact hcs

/-- For nonzero input, the imaginary coordinate of the phase approximation differs from the
normalized imaginary coordinate by at most `16 / 2 ^ k`. -/
private theorem phaseApprox_im_abs (z : RatComplex) (k : ℕ) (hz : z ≠ ratZero) :
    |((phaseApprox z k).2 : ℝ) - (z.2 : ℝ) / Real.sqrt (ratSq z : ℝ)| ≤ 16 / 2 ^ k := by
  have hr2 : (0 : ℚ) < ratSq z := ratSq_pos_of_ne z hz
  have ht0 : (0 : ℚ) ≤ z.1 ^ 2 / ratSq z := div_nonneg (sq_nonneg _) (le_of_lt hr2)
  have ht1 : z.1 ^ 2 / ratSq z ≤ 1 := by
    have hsq : z.1 ^ 2 ≤ ratSq z := by
      have h2 : (z.2 : ℚ) ^ 2 ≤ ratSq z := by
        have h1pos : (0 : ℚ) ≤ z.1 ^ 2 := by positivity
        unfold ratSq
        linarith
      have h2pos : (0 : ℚ) ≤ z.2 ^ 2 := by positivity
      unfold ratSq
      linarith
    exact (div_le_one hr2).mpr hsq
  have hcs := (rationalPayoffCS_sqrt_error (z.1 ^ 2 / ratSq z) k ht0 ht1).1
  have hone : 1 - ((z.1 ^ 2 / ratSq z : ℚ) : ℝ) = ((z.2 ^ 2 / ratSq z : ℚ) : ℝ) := by
    have hq := one_sub_ratio z hr2
    exact_mod_cast hq
  rw [hone] at hcs
  rw [sqrt_sq_over_mass z.2 (ratSq z) hr2] at hcs
  have hcast : ((z.2 : ℚ) : ℝ) = (ratSign z.2 : ℝ) * (|(z.2 : ℝ)|) := by
    have h1 : ((z.2 : ℚ) : ℝ) = ((ratSign z.2 * |z.2| : ℚ) : ℝ) := by
      rw [ratSign_mul_abs]
    have h2 : ((ratSign z.2 * |z.2| : ℚ) : ℝ) = (ratSign z.2 : ℝ) * ((|z.2| : ℚ) : ℝ) := by
      norm_cast
    have h3 : ((|z.2| : ℚ) : ℝ) = |(z.2 : ℝ)| := Rat.cast_abs z.2
    calc
      ((z.2 : ℚ) : ℝ) = ((ratSign z.2 * |z.2| : ℚ) : ℝ) := h1
      _ = (ratSign z.2 : ℝ) * ((|z.2| : ℚ) : ℝ) := h2
      _ = (ratSign z.2 : ℝ) * (|(z.2 : ℝ)|) := by rw [h3]
  have habs : |((ratSign z.2 : ℝ) * (|(z.2 : ℝ)|))| = |(z.2 : ℝ)| := by
    rw [abs_mul, ratSign_abs, one_mul]
    exact abs_of_nonneg (abs_nonneg _)
  have hcs' :
      ((ratSign z.2 * (rationalPayoffCS (z.1 ^ 2 / ratSq z) k).1 : ℚ) : ℝ)
        = (ratSign z.2 : ℝ) * (((rationalPayoffCS (z.1 ^ 2 / ratSq z) k).1 : ℚ) : ℝ) := by
      norm_cast
  have hr : Real.sqrt (ratSq z : ℝ) ≠ 0 := by
    have hr2r : (0 : ℝ) < (ratSq z : ℝ) := by exact_mod_cast hr2
    exact ne_of_gt (Real.sqrt_pos.2 hr2r)
  have hkey :
      ((phaseApprox z k).2 : ℝ) - (z.2 : ℝ) / Real.sqrt (ratSq z : ℝ)
        = (ratSign z.2 : ℝ) *
            (((rationalPayoffCS (z.1 ^ 2 / ratSq z) k).1 : ℝ)
              - |(z.2 : ℝ)| / Real.sqrt (ratSq z : ℝ)) := by
    simp only [phaseApprox, if_neg hz]
    rw [hcs', hcast, habs]
    field_simp <;> ring
  rw [hkey, abs_mul, ratSign_abs, one_mul]
  exact hcs

/-- The exact phase of a nonzero rational complex number has norm one. -/
theorem exactPhase_norm (z : RatComplex) (hz : z ≠ ratZero) : ‖exactPhase z‖ = 1 := by
  have hr2 : (0 : ℚ) < ratSq z := ratSq_pos_of_ne z hz
  have hr2r : (0 : ℝ) < (ratSq z : ℝ) := by exact_mod_cast hr2
  have hsq : Real.sqrt (ratSq z : ℝ) ^ 2 = (ratSq z : ℝ) := by
    rw [Real.sq_sqrt]
    exact_mod_cast ratSq_nonneg z
  have hcast : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) = (ratSq z : ℝ) := by
    simp only [ratSq]
    push_cast
    ring
  have hnonneg : (0 : ℝ) ≤ ‖exactPhase z‖ := norm_nonneg _
  have hsq' : ‖exactPhase z‖ ^ 2 = 1 := by
    rw [exactPhase, if_neg hz]
    rw [complexAbs_sq]
    field_simp
    rw [hsq, hcast] <;> ring
  nlinarith

/-- The phase assigned to zero has norm one. -/
theorem exactPhase_zero : ‖exactPhase ratZero‖ = 1 := by
  rw [exactPhase, if_pos rfl]
  simp

/-- The complex phase approximation differs from the exact phase by at most `32 / 2 ^ k` in
norm. -/
theorem phaseApprox_error (z : RatComplex) (k : ℕ) :
    ‖ratToComplex (phaseApprox z k) - exactPhase z‖ ≤ 32 / 2 ^ k := by
  by_cases hz : z = ratZero
  · subst hz
    simp [phaseApprox, exactPhase, ratZero, ratToComplex]
    positivity
  · have hre := phaseApprox_re_abs z k hz
    have him := phaseApprox_im_abs z k hz
    have hsq' : ‖ratToComplex (phaseApprox z k) - exactPhase z‖ ^ 2
        = (((phaseApprox z k).1 : ℝ) - (z.1 : ℝ) / Real.sqrt (ratSq z : ℝ)) ^ 2
          + (((phaseApprox z k).2 : ℝ) - (z.2 : ℝ) / Real.sqrt (ratSq z : ℝ)) ^ 2 := by
      simp only [ratToComplex, exactPhase, if_neg hz]
      rw [complexDiff_sq]
    have hre2 :
        (((phaseApprox z k).1 : ℝ) - (z.1 : ℝ) / Real.sqrt (ratSq z : ℝ)) ^ 2
          ≤ (16 / 2 ^ k) ^ 2 := by
      have hnonneg : (0 : ℝ) ≤ 16 / 2 ^ k := by positivity
      rw [sq_le_sq]
      simpa [abs_of_nonneg hnonneg] using! hre
    have him2 :
        (((phaseApprox z k).2 : ℝ) - (z.2 : ℝ) / Real.sqrt (ratSq z : ℝ)) ^ 2
          ≤ (16 / 2 ^ k) ^ 2 := by
      have hnonneg : (0 : ℝ) ≤ 16 / 2 ^ k := by positivity
      rw [sq_le_sq]
      simpa [abs_of_nonneg hnonneg] using! him
    have hsum : ((16 : ℝ) / 2 ^ k) ^ 2 + ((16 : ℝ) / 2 ^ k) ^ 2 ≤ ((32 : ℝ) / 2 ^ k) ^ 2 := by
      calc
        ((16 : ℝ) / 2 ^ k) ^ 2 + ((16 : ℝ) / 2 ^ k) ^ 2 = 2 * ((16 : ℝ) / 2 ^ k) ^ 2 := by ring
        _ = 512 / (2 ^ k) ^ 2 := by field_simp; ring
        _ ≤ 1024 / (2 ^ k) ^ 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = ((32 : ℝ) / 2 ^ k) ^ 2 := by field_simp; ring
    have hsq'' : ‖ratToComplex (phaseApprox z k) - exactPhase z‖ ^ 2
        ≤ (32 / 2 ^ k) ^ 2 := by
      rw [hsq']
      exact (add_le_add hre2 him2).trans hsum
    have hnonneg : (0 : ℝ) ≤ ‖ratToComplex (phaseApprox z k) - exactPhase z‖ := norm_nonneg _
    have hc : (0 : ℝ) ≤ 32 / 2 ^ k := by positivity
    have h1 : |‖ratToComplex (phaseApprox z k) - exactPhase z‖| ≤ |(32 : ℝ) / 2 ^ k| :=
      sq_le_sq.mp hsq''
    simpa [abs_of_nonneg hnonneg, abs_of_nonneg hc] using! h1

/-- The exact phase diagonal has operator norm at most one. -/
theorem exactPhaseDiagonal_norm_le {D : ℕ} (amp : Option (Fin D) → RatComplex) :
    ‖exactPhaseDiagonal amp‖ ≤ 1 := by
  rw [exactPhaseDiagonal, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro a
  by_cases hz : amp a = ratZero
  · rw [exactPhase, if_pos hz] <;> simp
  · rw [exactPhase_norm _ hz] <;> norm_num

/-- The approximate phase diagonal differs from the exact phase diagonal by at most `32 / 2 ^ k`
in operator norm. -/
theorem phaseDiagonal_error {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    ‖phaseDiagonal k amp - exactPhaseDiagonal amp‖ ≤ 32 / 2 ^ k := by
  have hsub : phaseDiagonal k amp - exactPhaseDiagonal amp
      = Matrix.diagonal (fun a => ratToComplex (phaseApprox (amp a) k) - exactPhase (amp a)) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [phaseDiagonal, exactPhaseDiagonal]
    · simp [phaseDiagonal, exactPhaseDiagonal, hab]
  rw [hsub, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
  intro a
  exact phaseApprox_error (amp a) k

/-- For nonnegative weights of positive total mass, the preparation matrix has operator error at
most `32 * (D + 1) / 2 ^ k`. -/
theorem prepareMatrix_error {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) (hw : ∀ a, 0 ≤ w a)
    (hm : 0 < rationalWeightMass w) :
    ‖prepareMatrix k w amp - exactPrepareMatrix w amp‖ ≤ 32 * (D + 1) / 2 ^ k := by
  have hprep := rational_weight_numerical_word_unitary_and_error D k w hw
  have hideal := rational_weight_ideal_preparation_exact D w hw hm
  have hprep_le : ‖rationalWeightPrepare w k‖ ≤ 1 :=
    l2_norm_unitary_le_one hprep.2.1
  have hideal_le : ‖idealWeightPrepare w‖ ≤ 1 :=
    l2_norm_unitary_le_one hideal.1
  have hdiag_le : ‖exactPhaseDiagonal amp‖ ≤ 1 := exactPhaseDiagonal_norm_le amp
  have hph : ‖phaseDiagonal k amp - exactPhaseDiagonal amp‖ ≤ 32 / 2 ^ k :=
    phaseDiagonal_error k amp
  have hfr : ‖rationalWeightPrepare w k - idealWeightPrepare w‖ ≤ 32 * (D : ℝ) / 2 ^ k :=
    hprep.2.2
  calc
    ‖prepareMatrix k w amp - exactPrepareMatrix w amp‖
        = ‖phaseDiagonal k amp * rationalWeightPrepare w k
            - exactPhaseDiagonal amp * idealWeightPrepare w‖ := rfl
    _ ≤ ‖phaseDiagonal k amp - exactPhaseDiagonal amp‖ * ‖rationalWeightPrepare w k‖
        + ‖exactPhaseDiagonal amp‖ * ‖rationalWeightPrepare w k - idealWeightPrepare w‖ :=
      l2_norm_mul_sub_mul_le (phaseDiagonal k amp) (rationalWeightPrepare w k)
        (exactPhaseDiagonal amp) (idealWeightPrepare w)
    _ ≤ (32 / 2 ^ k) * 1 + 1 * (32 * (D : ℝ) / 2 ^ k) := by
      have ha : ‖phaseDiagonal k amp - exactPhaseDiagonal amp‖ ≤ 32 / 2 ^ k := hph
      have hb : ‖rationalWeightPrepare w k‖ ≤ 1 := hprep_le
      have hc : ‖exactPhaseDiagonal amp‖ ≤ 1 := hdiag_le
      have hd : ‖rationalWeightPrepare w k - idealWeightPrepare w‖
          ≤ 32 * (D : ℝ) / 2 ^ k := hfr
      refine add_le_add ?_ ?_
      · gcongr
      · gcongr
    _ = 32 * (D + 1) / 2 ^ k := by ring

/-- The real modulus of a rational complex number, computed as the square root of `ratSq`. -/
noncomputable def ratAbs (z : RatComplex) : ℝ := Real.sqrt (ratSq z : ℝ)

/-- Multiplication by a real scalar scales the real and imaginary coordinates of a complex
number. -/
private theorem ofReal_scale (a b c : ℝ) :
    (Complex.ofReal a + Complex.ofReal b * Complex.I) * (c : ℂ)
      = Complex.ofReal (a * c) + Complex.ofReal (b * c) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]

/-- Multiplying the exact phase by the modulus recovers the rational complex number embedded in
`ℂ`. -/
theorem exactPhase_mul_abs (z : RatComplex) :
    exactPhase z * ratAbs z = ratToComplex z := by
  by_cases hz : z = ratZero
  · subst hz
    simp [exactPhase, ratZero, ratToComplex, ratAbs, ratSq]
  · have hr2 : (0 : ℚ) < ratSq z := ratSq_pos_of_ne z hz
    have hr2r : (0 : ℝ) < (ratSq z : ℝ) := by exact_mod_cast hr2
    have hr : Real.sqrt (ratSq z : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr2r)
    rw [exactPhase, if_neg hz, ratAbs]
    (try dsimp only)
    rw [ofReal_scale, ratToComplex]
    field_simp

/-- Positive loaded mass implies positive total rational weight. -/
theorem LoadedInput.mass_pos {D : ℕ} (L : LoadedInput D) (h : 0 < L.mass) :
    0 < rationalWeightMass L.weights := by
  rw [LoadedInput.mass_eq]
  exact h

/-- For positive loaded mass, the exact preparation matrix sends the `none` basis state to the
loaded target state. -/
theorem exactPrepareMatrix_target {D : ℕ} (L : LoadedInput D) (hpos : 0 < L.mass) :
    exactPrepareMatrix L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none = loadedTarget L := by
  have hw : ∀ a, 0 ≤ L.weights a := L.weights_nonneg
  have hm : 0 < rationalWeightMass L.weights :=
      Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess.LoadedInput.mass_pos L hpos
  have hid : idealWeightPrepare L.weights *ᵥ Qatlib.Foundations.PureStateMath.Ket none = rationalWeightTarget L.weights :=
    (rational_weight_ideal_preparation_exact D L.weights hw hm).2.1
  have hstep : exactPrepareMatrix L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none
      = exactPhaseDiagonal L.amp *ᵥ rationalWeightTarget L.weights := by
    calc
      exactPrepareMatrix L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none
          = (exactPhaseDiagonal L.amp * idealWeightPrepare L.weights) *ᵥ Qatlib.Foundations.PureStateMath.Ket none := rfl
      _ = exactPhaseDiagonal L.amp *ᵥ (idealWeightPrepare L.weights *ᵥ Qatlib.Foundations.PureStateMath.Ket none) :=
        (Matrix.mulVec_mulVec (Qatlib.Foundations.PureStateMath.Ket none) _ _).symm
      _ = exactPhaseDiagonal L.amp *ᵥ rationalWeightTarget L.weights := by rw [hid]
  rw [hstep]
  funext a
  cases a with
  | none =>
    rw [exactPhaseDiagonal, Matrix.mulVec_diagonal]
    simp [LoadedInput.amp, LoadedInput.weights, exactPhase, ratZero, loadedTarget,
      rationalWeightTarget]
  | some i =>
    have hcast : ((ratSq (L.amplitude i) / rationalWeightMass L.weights : ℚ) : ℝ)
        = (ratSq (L.amplitude i) : ℝ) / (rationalWeightMass L.weights : ℝ) := by
      push_cast
      ring
    have hsqrt : Real.sqrt ((ratSq (L.amplitude i) / rationalWeightMass L.weights : ℚ) : ℝ)
        = ratAbs (L.amplitude i) / Real.sqrt (rationalWeightMass L.weights : ℝ) := by
      rw [hcast, Real.sqrt_div (by exact_mod_cast (ratSq_nonneg (L.amplitude i)))
        (rationalWeightMass L.weights : ℝ)]
      rfl
    have hkey : exactPhase (L.amplitude i) * ((ratAbs (L.amplitude i) : ℂ)
          / (Real.sqrt (rationalWeightMass L.weights : ℝ) : ℂ))
        = ratToComplex (L.amplitude i) / Real.sqrt (rationalWeightMass L.weights : ℝ) := by
      rw [mul_div, exactPhase_mul_abs]
    rw [exactPhaseDiagonal, Matrix.mulVec_diagonal]
    simp only [LoadedInput.amp, LoadedInput.weights, rationalWeightTarget]
    rw [hsqrt, Complex.ofReal_div, hkey]
    simp [loadedTarget, LoadedInput.mass_eq]

/-- For positive loaded mass, preparation from the `none` basis state has Euclidean error at
most `32 * (D + 1) / 2 ^ k`. -/
theorem prepareMatrix_state_error {D : ℕ} (k : ℕ) (L : LoadedInput D) (hpos : 0 < L.mass) :
    ‖stateVector (prepareMatrix k L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (loadedTarget L)‖ ≤ 32 * (D + 1) / 2 ^ k := by
  have hw : ∀ a, 0 ≤ L.weights a := L.weights_nonneg
  have hm : 0 < rationalWeightMass L.weights :=
      Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess.LoadedInput.mass_pos L hpos
  have herr : ‖prepareMatrix k L.weights L.amp - exactPrepareMatrix L.weights L.amp‖
      ≤ 32 * (D + 1) / 2 ^ k := prepareMatrix_error k L.weights L.amp hw hm
  have hket : ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ = 1 := by
    have hsq : ‖stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D)))‖ ^ 2 = 1 := by
      rw [stateVector_norm_sq]
      simp [MeasureProb, BornProb, Qatlib.Foundations.PureStateMath.Ket]
    have hn :=
        norm_nonneg (stateVector (Qatlib.Foundations.PureStateMath.Ket none : QState (Option (Fin D))))
    nlinarith
  have hclose := stateVector_mulVec_norm_le
    (prepareMatrix k L.weights L.amp - exactPrepareMatrix L.weights L.amp) (Qatlib.Foundations.PureStateMath.Ket none)
  rw [hket, mul_one] at hclose
  have htarget : exactPrepareMatrix L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none = loadedTarget L :=
    exactPrepareMatrix_target L hpos
  rw [Matrix.sub_mulVec] at hclose
  rw [htarget] at hclose
  simpa only [stateVector, WithLp.toLp_sub] using! hclose.trans herr

/-- For every natural number `n`, `n + 1 ≤ 2 ^ n`. -/
private theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
    have h2 : n + 2 ≤ 2 * (n + 1) := by omega
    calc n + 2 ≤ 2 * (n + 1) := h2
      _ ≤ 2 * 2 ^ n := h1
      _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Every natural number `n` is at most `2 ^ n`. -/
private theorem le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := succ_le_two_pow n
    omega

/-- For positive rational tolerance, `precisionFor` makes the preparation error bound at most
that tolerance. -/
theorem prepError_le_epsilon {D : ℕ} (ε : ℚ) (hε : 0 < ε) :
    (32 * (D + 1) : ℝ) / 2 ^ precisionFor D ε ≤ (ε : ℝ) := by
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hceil : (64 * (D + 1) : ℚ) ≤ (precisionFor D ε : ℚ) * ε := by
    have h := Nat.le_ceil (64 * (D + 1) / ε)
    have h' : (64 * (D + 1) : ℚ) / ε ≤ (precisionFor D ε : ℚ) := by
      simpa only [precisionFor] using! h
    rw [div_le_iff₀ hε] at h'
    exact h'
  have hmul : (64 * (D + 1) : ℝ) ≤ (precisionFor D ε : ℝ) * (ε : ℝ) := by
    exact_mod_cast hceil
  have hk : precisionFor D ε ≤ 2 ^ precisionFor D ε := le_two_pow _
  have h2 : (precisionFor D ε : ℝ) * (ε : ℝ)
      ≤ (2 ^ precisionFor D ε : ℝ) * (ε : ℝ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (le_of_lt hεr)
  have h3 : (64 * (D + 1) : ℝ) ≤ (2 ^ precisionFor D ε : ℝ) * (ε : ℝ) := hmul.trans h2
  have h4 : (32 * (D + 1) : ℝ) ≤ (2 ^ precisionFor D ε : ℝ) * (ε : ℝ) / 2 := by linarith
  have h5 : (32 * (D + 1) : ℝ) / 2 ^ precisionFor D ε ≤ (ε : ℝ) / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ precisionFor D ε)]
    calc (32 * (D + 1) : ℝ) ≤ (2 ^ precisionFor D ε : ℝ) * (ε : ℝ) / 2 := h4
      _ = (ε : ℝ) / 2 * (2 ^ precisionFor D ε : ℝ) := by ring
  linarith

/-- At precision `precisionFor D ε`, preparation with nonnegative weights and positive mass has
operator error at most `ε`. -/
theorem prepareError_le_epsilon {D : ℕ} (ε : ℚ) (hε : 0 < ε)
    (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w) :
    ‖prepareMatrix (precisionFor D ε) w amp - exactPrepareMatrix w amp‖ ≤ (ε : ℝ) := by
  have herr := prepareMatrix_error (precisionFor D ε) w amp hw hm
  have hbound := prepError_le_epsilon (D := D) ε hε
  linarith

/-- At precision `precisionFor D ε`, a positive-mass loaded input is prepared within Euclidean
error `ε`. -/
theorem prepareState_error_le_epsilon {D : ℕ} (ε : ℚ) (hε : 0 < ε)
    (L : LoadedInput D) (hpos : 0 < L.mass) :
    ‖stateVector (prepareMatrix (precisionFor D ε) L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (loadedTarget L)‖ ≤ (ε : ℝ) := by
  have herr := prepareMatrix_state_error (precisionFor D ε) L hpos
  have hbound := prepError_le_epsilon (D := D) ε hε
  linarith

/-- Evaluating the phase word with identity oracle gives the approximate phase diagonal. -/
theorem phaseWord_eval {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    evaluate 1 (phaseWord k amp) = phaseDiagonal k amp := by
  have h : evaluate 1 (.gate (phaseDiagonal k amp) :: []) = phaseDiagonal k amp := by
    simp only [evaluate, instructionMatrix, Matrix.mul_one]
  rw [phaseWord, h]

/-- Evaluating the preparation word with identity oracle gives the preparation matrix. -/
theorem prepareWord_eval {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) :
    evaluate 1 (prepareWord k w amp) = prepareMatrix k w amp := by
  have h : evaluate 1 (phaseWord k amp) = phaseDiagonal k amp := phaseWord_eval k amp
  rw [prepareWord, evaluate_append, h]
  rfl

/-- The gate count of concatenated adjoint words is the sum of their gate counts. -/
private theorem adjointGateCount_append {H : Type} (cs ds : List (AdjointStep H)) :
    adjointGateCount (cs ++ ds) = adjointGateCount cs + adjointGateCount ds := by
  induction cs with
  | nil => simp [adjointGateCount]
  | cons c cs ih =>
    cases c <;> simp [adjointGateCount, ih] <;> ring

/-- The query count of concatenated adjoint words is the sum of their query counts. -/
private theorem adjointQueryCount_append {H : Type} (cs ds : List (AdjointStep H)) :
    adjointQueryCount (cs ++ ds) = adjointQueryCount cs + adjointQueryCount ds := by
  induction cs with
  | nil => simp [adjointQueryCount]
  | cons c cs ih =>
    cases c <;> simp [adjointQueryCount, ih] <;> ring

/-- An adjoint word containing only gates has gate count equal to its length. -/
private theorem adjointGateCount_eq_length {H : Type} :
    ∀ (cs : List (AdjointStep H)),
      (∀ c ∈ cs, match c with | .gate _ => True | _ => False) →
      adjointGateCount cs = cs.length := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have hcs : ∀ d ∈ cs, match d with | .gate _ => True | _ => False :=
      fun d hd => h d (by simp [hd])
    cases c with
    | gate v => simp [adjointGateCount, ih hcs]
    | forward => exact (h .forward (by simp)).elim
    | backward => exact (h .backward (by simp)).elim

/-- An adjoint word containing only gates has zero query count. -/
private theorem adjointQueryCount_eq_zero {H : Type} :
    ∀ (cs : List (AdjointStep H)),
      (∀ c ∈ cs, match c with | .gate _ => True | _ => False) →
      adjointQueryCount cs = 0 := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have hcs : ∀ d ∈ cs, match d with | .gate _ => True | _ => False :=
      fun d hd => h d (by simp [hd])
    cases c with
    | gate v => simp [adjointQueryCount, ih hcs]
    | forward => exact (h .forward (by simp)).elim
    | backward => exact (h .backward (by simp)).elim

/-- The rational weight preparation word contains exactly `D` gates. -/
theorem rationalWeightWord_gateCount {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) :
    adjointGateCount (rationalWeightWord w k) = D := by
  have h : adjointGateCount (rationalWeightWord w k) = (rationalWeightWord w k).length := by
    apply adjointGateCount_eq_length
    intro c hc
    simp only [rationalWeightWord, List.mem_reverse, List.mem_ofFn] at hc
    obtain ⟨j, hj⟩ := hc
    subst hj
    simp
  rw [h]
  simp [rationalWeightWord, List.length_ofFn, List.length_reverse]

/-- The rational weight preparation word uses no oracle queries. -/
theorem rationalWeightWord_queryCount {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) :
    adjointQueryCount (rationalWeightWord w k) = 0 := by
  apply adjointQueryCount_eq_zero
  intro c hc
  simp only [rationalWeightWord, List.mem_reverse, List.mem_ofFn] at hc
  obtain ⟨j, hj⟩ := hc
  subst hj
  simp

/-- The preparation word contains exactly `D + 1` gates and uses no oracle queries. -/
theorem prepareWord_counts {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) :
    adjointGateCount (prepareWord k w amp) = D + 1 ∧
      adjointQueryCount (prepareWord k w amp) = 0 := by
  have hg : adjointGateCount (phaseWord k amp) = 1 := by
    simp [phaseWord, adjointGateCount]
  have hq : adjointQueryCount (phaseWord k amp) = 0 := by
    simp [phaseWord, adjointQueryCount]
  constructor
  · rw [prepareWord, adjointGateCount_append, hg, rationalWeightWord_gateCount] <;> ring
  · rw [prepareWord, adjointQueryCount_append, hq, rationalWeightWord_queryCount] <;> ring

/-- The dense loader rejects a table with zero total squared modulus. -/
theorem loadDense_rejects_zero_mass (D : ℕ) (xs : DenseTable D)
    (hm : (∑ i : Fin D, ratSq (xs i)) = 0) : loadDense D xs = none := by
  simp [loadDense, hm]

/-- For positive mass, dense loading preserves all amplitudes and records exactly `D` reads. -/
theorem loadDense_spec (D : ℕ) (xs : DenseTable D)
    (hm : 0 < (∑ i : Fin D, ratSq (xs i))) :
    (loadDense D xs).map (fun L => (L.amplitude, L.reads)) = some (xs, D) := by
  simp [loadDense, hm.ne']

/-- The sparse loader rejects any list containing an entry whose position is outside the table. -/
theorem loadSparse_rejects_illegal (D : ℕ) (es : List SparseEntry) (e : SparseEntry)
    (hmem : e ∈ es) (hp : D ≤ e.position) : loadSparse D es = none := by
  have hne : ¬ (∀ e ∈ es, e.position < D) := by
    intro h
    have := h e hmem
    omega
  rw [loadSparse, if_neg hne]

/-- For legal positions and nonzero resolved mass, sparse loading returns the resolved
amplitudes and charges one read per list entry. -/
theorem loadSparse_spec (D : ℕ) (es : List SparseEntry)
    (hleg : ∀ e ∈ es, e.position < D)
    (hm : (∑ i : Fin D, ratSq (sparseResolve es i)) ≠ 0) :
    (loadSparse D es).map (fun L => (L.amplitude, L.reads))
      = some ((fun a => sparseResolve es a), es.length) := by
  rw [loadSparse, if_pos hleg, if_neg hm]
  rfl

/-- The scoped bit oracle has the stated XOR matrix entries and is unitary. -/
theorem scopedAccess_query (n : ℕ) (f : Reg n → Bool) (a b : Bool) (x y : Reg n) :
    scopedBitOracle f (a, x) (b, y) = (if x = y ∧ a = (b ^^ f y) then 1 else 0) ∧
      scopedBitOracle f ∈ Matrix.unitaryGroup (Bool × Reg n) ℂ :=
  scoped_bit_oracle_actual_toggle_unitary n f a b x y

/-- Compiling a single scoped phase step uses two oracle queries and one gate. -/
theorem scopedAccess_step_cost (n : ℕ) (z : ℂ) :
    QueryCount (scopedCompile [ScopedOracleStep.phase (n := n) z]) = 2 ∧
      GateCount (scopedCompile [ScopedOracleStep.phase (n := n) z]) = 1 := by
  rw [scoped_phase_word_actual_compile]
  constructor <;> rfl

/-- Running a compiled scoped program on a false workspace bit implements its logical matrix and
returns the workspace bit to false. -/
theorem scopedAccess_clean (n : ℕ) (f : Reg n → Bool) (w : List (ScopedOracleStep n))
    (ψ : QState (Reg n)) :
    Run (scopedBitOracle f) (scopedCompile w) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)
      = TensorState (Qatlib.Foundations.PureStateMath.Ket false) (scopedLogicalMatrix f w *ᵥ ψ) :=
  scoped_run_clean f w ψ

/-- The scoped allocation frame is isometric, initializes a false workspace bit, and gives the
stated wire trace with peak `n + 1`. -/
theorem scopedAccess_peak_space (n : ℕ) (w : List (ScopedOracleStep n)) :
    (scopedAllocationFrame n)ᴴ * scopedAllocationFrame n = 1 ∧
      (∀ ψ : QState (Reg n), scopedAllocationFrame n *ᵥ ψ = TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) ∧
      scopedWireTrace w = [n] ++ List.replicate ((scopedCompile w).length + 1) (n + 1) ++ [n] ∧
      (scopedWireTrace w).foldl max 0 = n + 1 :=
  scoped_allocation_release_and_peak_trace n w

/-- The conjugate product of a complex number with real coordinates `a` and `b` equals `a ^ 2 +
b ^ 2`. -/
private theorem star_ofReal_add_mul_I (a b : ℝ) :
    (starRingEnd ℂ) (Complex.ofReal a + Complex.ofReal b * Complex.I)
      * (Complex.ofReal a + Complex.ofReal b * Complex.I) = (a ^ 2 + b ^ 2 : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_apply]
  simp [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- A diagonal matrix is unitary when the conjugate product of each diagonal entry with itself
is one. -/
private theorem diagonal_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℂ)
    (hd : ∀ i, starRingEnd ℂ (d i) * d i = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.sum_eq_single x]
    · simpa [Matrix.star_apply, Matrix.diagonal_apply, mul_comm] using! hd x
    · intro k _ hk
      simp [Matrix.star_apply, Matrix.diagonal_apply, Ne.symm hk]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkx : k = x
    · subst hkx
      simp [Matrix.star_apply, Matrix.diagonal_apply, hxy, Ne.symm hxy]
    · simp [Matrix.star_apply, Matrix.diagonal_apply, hkx, Ne.symm hkx]

/-- The phase diagonal on the physical register is unitary. -/
theorem physPhaseDiagonal_unitary (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    physPhaseDiagonal D w xs k ∈ Matrix.unitaryGroup (Reg w) ℂ := by
  have hdiag : Matrix.diagonal (fun x => ratToComplex (phaseApprox (physAmp D w xs x) k))
      ∈ Matrix.unitaryGroup (Reg w) ℂ := by
    apply diagonal_unitaryGroup
    intro x
    rw [ratToComplex, star_ofReal_add_mul_I]
    exact_mod_cast (phaseApprox_unit (physAmp D w xs x) k)
  rw [physPhaseDiagonal]
  exact hdiag

/-- The magnitude preparation matrix on the physical register is unitary. -/
theorem physMag_unitary (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    physMag D w xs k ∈ Matrix.unitaryGroup (Reg w) ℂ :=
  (relabelGate_mem_unitaryGroup (slotEquiv w).symm
    (rationalWeightPrepare (slotWeight D w xs) k)).2
    (rational_weight_numerical_word_unitary_and_error (2 ^ w - 1) k (slotWeight D w xs)
      (fun _ => ratSq_nonneg _)).2.1

/-- The full preparation matrix on the physical register is unitary. -/
theorem physPrepare_unitary (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    physPrepare D w xs k ∈ Matrix.unitaryGroup (Reg w) ℂ :=
  (Matrix.unitaryGroup (Reg w) ℂ).mul_mem (physPhaseDiagonal_unitary D w xs k)
    (physMag_unitary D w xs k)

/-- The physical preparation matrix has a legal reflection circuit with at most `128 * (w + 1) ^
2 * 4 ^ w` gates and no queries, acting correctly on every state embedded by
`knownFrameEmbed`. -/
theorem physPrepare_synthesis (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    ∃ gs : List (ReflectionGate (w + (w + 1))), reflectionLegal gs ∧
      gs.length ≤ 128 * (w + 1) ^ 2 * 4 ^ w ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg w),
        Run 1 (reflectionCompile gs) (knownFrameEmbed w ψ) =
          knownFrameEmbed w (physPrepare D w xs k *ᵥ ψ) :=
  known_unitary_actual_clean_local_synthesis w (physPrepare D w xs k)
    (physPrepare_unitary D w xs k)

/-- For positive `D`, the register size selected by `addressBitsFor D` has at most `2 * D` basis
states. -/
theorem slotCount_le (D : ℕ) (hD : 0 < D) : 2 ^ addressBitsFor D ≤ 2 * D := by
  have hlog : 2 ^ Nat.log2 D ≤ D :=
    (Nat.le_log2 (n := D) (k := Nat.log2 D) (Nat.ne_of_gt hD)).mp le_rfl
  have hexp : 2 ^ (Nat.log2 D + 1) = 2 ^ Nat.log2 D * 2 := by
    rw [pow_succ]
  rw [addressBitsFor, hexp]
  nlinarith

/-- For positive `D` and the selected address width, the reflection gate bound is at most `512 *
(w + 1) ^ 2 * D ^ 2`. -/
theorem physGateCount_le (D w : ℕ) (hD : 0 < D) (hw : w = addressBitsFor D) :
    128 * (w + 1) ^ 2 * 4 ^ w ≤ 512 * (w + 1) ^ 2 * D ^ 2 := by
  have h2 : 2 ^ w ≤ 2 * D := by rw [hw]; exact slotCount_le D hD
  have h4 : 4 ^ w ≤ 4 * D ^ 2 := by
    calc 4 ^ w = (2 * 2) ^ w := by rw [show (2 : ℕ) * 2 = 4 by norm_num]
      _ = 2 ^ w * 2 ^ w := by rw [mul_pow]
      _ = (2 ^ w) ^ 2 := by rw [← pow_two]
      _ ≤ (2 * D) ^ 2 := by gcongr
      _ = 4 * D ^ 2 := by ring
  nlinarith [h4]

/-- The scoped logical matrix is unitary when every data gate is unitary and every phase
parameter has norm one. -/
theorem scopedLogicalMatrix_unitary {n : ℕ} (f : Reg n → Bool) (w : List (ScopedOracleStep n))
    (hU : ∀ U, ScopedOracleStep.data U ∈ w → U ∈ Matrix.unitaryGroup (Reg n) ℂ)
    (hz : ∀ z, ScopedOracleStep.phase z ∈ w → ‖z‖ = 1) :
    scopedLogicalMatrix f w ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction w with
  | nil => simp [scopedLogicalMatrix]
  | cons s w ih =>
    have hstep : scopedStepMatrix f s ∈ Matrix.unitaryGroup (Reg n) ℂ := by
      cases s with
      | data U =>
        have h := hU U (by simp)
        simpa [scopedStepMatrix] using! h
      | phase z =>
        have hz1 : ‖z‖ = 1 := hz z (by simp)
        have hstar : starRingEnd ℂ z * z = 1 := by
          rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, hz1]
          norm_num
        have hdiagonal : Matrix.diagonal (fun x => if f x then z else 1)
            ∈ Matrix.unitaryGroup (Reg n) ℂ := by
          apply diagonal_unitaryGroup
          intro x
          by_cases hfx : f x
          · simp only [hfx, if_pos]
            exact hstar
          · simp only [hfx, if_neg]
            simp [starRingEnd_apply]
        simpa [scopedStepMatrix, scopedPhaseGate] using! hdiagonal
    have hUw : ∀ U, ScopedOracleStep.data U ∈ w → U ∈ Matrix.unitaryGroup (Reg n) ℂ := by
      intro U hU'
      exact hU U (by simp [hU'])
    have hzw : ∀ z, ScopedOracleStep.phase z ∈ w → ‖z‖ = 1 := by
      intro z hz'
      exact hz z (by simp [hz'])
    rw [scopedLogicalMatrix]
    exact (Matrix.unitaryGroup (Reg n) ℂ).mul_mem (ih hUw hzw) hstep

/-- Under the unitary data-gate and unit-modulus phase hypotheses, the scoped logical matrix has
a legal reflection circuit with at most `128 * (n + 1) ^ 2 * 4 ^ n` gates and no queries on
the known embedded frame. -/
theorem scopedAccess_synthesis {n : ℕ} (f : Reg n → Bool) (w : List (ScopedOracleStep n))
    (hU : ∀ U, ScopedOracleStep.data U ∈ w → U ∈ Matrix.unitaryGroup (Reg n) ℂ)
    (hz : ∀ z, ScopedOracleStep.phase z ∈ w → ‖z‖ = 1) :
    ∃ gs : List (ReflectionGate (n + (n + 1))), reflectionLegal gs ∧
      gs.length ≤ 128 * (n + 1) ^ 2 * 4 ^ n ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
          knownFrameEmbed n (scopedLogicalMatrix f w *ᵥ ψ) :=
  known_unitary_actual_clean_local_synthesis n (scopedLogicalMatrix f w)
    (scopedLogicalMatrix_unitary f w hU hz)

/-- The amplitude at a nonpivot option slot equals its physical slot amplitude. -/
theorem slotAmpW_some (D w : ℕ) (xs : DenseTable D) (j : Fin (2 ^ w - 1)) :
    slotAmpW D w xs (some j) = physSlotAmp D w xs j := by
  rfl

/-- An in-range physical slot carries the corresponding dense-table amplitude. -/
theorem physSlotAmp_of_lt (D w : ℕ) (xs : DenseTable D) (j : Fin (2 ^ w - 1))
    (hj : j.val < D) :
    physSlotAmp D w xs j = xs ⟨j.val, hj⟩ := by
  simp [physSlotAmp, hj]

/-- A physical slot outside the dense-table range carries zero amplitude. -/
theorem physSlotAmp_of_not_lt (D w : ℕ) (xs : DenseTable D) (j : Fin (2 ^ w - 1))
    (hj : ¬ j.val < D) :
    physSlotAmp D w xs j = ratZero := by
  simp [physSlotAmp, hj]

/-- The loaded physical input has mass `slotMass D w xs`. -/
theorem physLoaded_mass (D w : ℕ) (xs : DenseTable D) :
    (physLoaded D w xs).mass = slotMass D w xs := by
  have hamp : (physLoaded D w xs).amplitude = physSlotAmp D w xs := rfl
  have hnone : ratSq (slotAmpW D w xs none) = 0 := by
    simp [slotAmpW, ratSq, ratZero]
  have hsome : ∀ j : Fin (2 ^ w - 1),
      ratSq (physSlotAmp D w xs j) = ratSq (slotAmpW D w xs (some j)) := by
    intro j
    rw [slotAmpW_some]
  rw [LoadedInput.mass, hamp]
  unfold slotMass slotWeight
  rw [Fintype.sum_option, hnone, zero_add]
  exact Finset.sum_congr rfl fun j _ => hsome j

/-- The loaded physical input has weights `slotWeight D w xs`. -/
theorem physLoaded_weights (D w : ℕ) (xs : DenseTable D) :
    (physLoaded D w xs).weights = slotWeight D w xs := by
  funext a
  cases a with
  | none => simp [LoadedInput.weights, slotWeight, slotAmpW, ratSq, ratZero]
  | some j =>
    show ratSq ((physLoaded D w xs).amplitude j)
        = ratSq (slotAmpW D w xs (some j))
    rw [slotAmpW_some]
    rfl

/-- The loaded physical input has amplitudes `slotAmpW D w xs`. -/
theorem physLoaded_amp (D w : ℕ) (xs : DenseTable D) :
    (physLoaded D w xs).amp = slotAmpW D w xs := by
  funext a
  cases a with
  | none => simp [LoadedInput.amp, slotAmpW]
  | some j =>
    show (physLoaded D w xs).amplitude j = slotAmpW D w xs (some j)
    rw [slotAmpW_some]
    rfl

/-- When `D < 2 ^ w`, dense-table indices correspond bijectively to the nonpivot slot indices
below `D`. -/
def usedSlotsEquiv (D : ℕ) {w : ℕ} (hD : D < 2 ^ w) :
    Fin D ≃ {j : Fin (2 ^ w - 1) // j.val < D} where
  toFun i :=
    ⟨⟨i.val, by
          have hi : i.val < D := i.isLt
          have h2w1 : 1 ≤ 2 ^ w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
          omega⟩, by
          have hi : i.val < D := i.isLt
          omega⟩
  invFun j := ⟨j.val, by
        have hj : j.val.val < D := j.property
        omega⟩
  left_inv i := Fin.ext rfl
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- When the register has room for all entries and the pivot, slot mass equals the total squared
modulus of the dense table. -/
theorem slotMass_eq (D w : ℕ) (xs : DenseTable D) (hD : D < 2 ^ w) :
    slotMass D w xs = ∑ j : Fin D, ratSq (xs j) := by
  have hA : (∑ i : {j : Fin (2 ^ w - 1) // j.val < D}, ratSq (physSlotAmp D w xs i))
      = ∑ i : {j : Fin (2 ^ w - 1) // j.val < D}, ratSq (xs ⟨i.val, i.property⟩) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [physSlotAmp_of_lt D w xs i i.property]
  have hB : (∑ i : {j : Fin (2 ^ w - 1) // ¬ j.val < D}, ratSq (physSlotAmp D w xs i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [physSlotAmp_of_not_lt D w xs i i.property]
    simp [ratSq, ratZero]
  have hsplit : (∑ j : Fin (2 ^ w - 1), ratSq (physSlotAmp D w xs j))
      = ∑ i : {j : Fin (2 ^ w - 1) // j.val < D}, ratSq (xs ⟨i.val, i.property⟩) := by
    have h := Fintype.sum_subtype_add_sum_subtype
      (fun j : Fin (2 ^ w - 1) => j.val < D)
      (fun j : Fin (2 ^ w - 1) => ratSq (physSlotAmp D w xs j))
    rw [hA, hB, add_zero] at h
    exact h.symm
  have hfin : (∑ i : {j : Fin (2 ^ w - 1) // j.val < D}, ratSq (xs ⟨i.val, i.property⟩))
      = ∑ j : Fin D, ratSq (xs j) := by
    symm
    refine Fintype.sum_equiv (usedSlotsEquiv D hD)
      (fun i : Fin D => ratSq (xs i))
      (fun j : {j : Fin (2 ^ w - 1) // j.val < D} => ratSq (xs ⟨j.val, j.property⟩)) ?_
    intro x
    have hx : x = ⟨(usedSlotsEquiv D hD x).val, (usedSlotsEquiv D hD x).property⟩ := by
      apply Fin.ext
      rfl
    exact congrArg (fun z : Fin D => ratSq (xs z)) hx
  exact (physLoaded_mass D w xs).symm.trans (hsplit.trans hfin)

/-- A positive-mass dense table has positive slot mass when all its entries fit in the register. -/
theorem slotMass_pos (D w : ℕ) (xs : DenseTable D) (hD : D < 2 ^ w)
    (hm : 0 < ∑ j : Fin D, ratSq (xs j)) :
    0 < slotMass D w xs := by
  rw [slotMass_eq D w xs hD]
  exact hm

/-- Relabeling a matrix evaluates its entries at the inverse images of the new row and column
indices. -/
private theorem relabelGate_apply {I J : Type*} (e : I ≃ J) (U : Matrix I I ℂ) (j i : J) :
    relabelGate e U j i = U (e.symm j) (e.symm i) := by
  show Matrix.reindex e e U j i = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Matrix action commutes with simultaneous relabeling of the matrix and state. -/
private theorem relabelGate_mulVec_relabelState {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ) (v : QState I) :
    relabelGate e U *ᵥ relabelState e v = relabelState e (U *ᵥ v) := by
  have h := applyGate_relabelGate e U v
  rwa [ApplyGate] at h

/-- Relabeling a basis state sends its label through the indexing equivalence. -/
private theorem relabelState_ket {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (x : I) :
    relabelState e (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (e x) := by
  funext j
  simp only [relabelState_apply, Qatlib.Foundations.PureStateMath.Ket]
  by_cases h : e.symm j = x
  · rw [if_pos h, if_pos ((Equiv.symm_apply_eq e).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((Equiv.symm_apply_eq e).mpr h'))]

/-- Relabeling a finite state preserves its Euclidean norm. -/
private theorem stateVector_relabelState_norm {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (v : QState I) :
    ‖stateVector (relabelState e v)‖ = ‖stateVector v‖ := by
  have h1 : ‖stateVector (relabelState e v)‖ ^ 2 = ∑ j, ‖(relabelState e v) j‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have h2 : ‖stateVector v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have h3 : (∑ j, ‖(relabelState e v) j‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
    calc
      (∑ j, ‖(relabelState e v) j‖ ^ 2) = ∑ j, ‖v (e.symm j)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rfl
      _ = ∑ i, ‖v i‖ ^ 2 := Equiv.sum_comp e.symm (fun i : I => ‖v i‖ ^ 2)
  have hsq : ‖stateVector (relabelState e v)‖ ^ 2 = ‖stateVector v‖ ^ 2 := by
    rw [h1, h2, h3]
  have hn1 := norm_nonneg (stateVector (relabelState e v))
  have hn2 := norm_nonneg (stateVector v)
  nlinarith

/-- Relabeling two finite states preserves their Euclidean distance. -/
private theorem stateVector_sub_relabelState_norm {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (v w : QState I) :
    ‖stateVector (relabelState e v) - stateVector (relabelState e w)‖
      = ‖stateVector v - stateVector w‖ := by
  have hsub : relabelState e (v - w) = relabelState e v - relabelState e w := by
    funext j
    rfl
  have hdiff : stateVector (relabelState e v) - stateVector (relabelState e w)
      = stateVector (relabelState e (v - w)) := by
    rw [hsub]
    simp only [stateVector, WithLp.toLp_sub]
  rw [hdiff]
  exact stateVector_relabelState_norm e (v - w)

/-- The physical phase diagonal is the option-slot phase diagonal relabeled onto the register. -/
theorem physPhaseDiagonal_eq (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    physPhaseDiagonal D w xs k
      = relabelGate (slotEquiv w).symm (phaseDiagonal k (slotAmpW D w xs)) := by
  ext j j'
  rw [relabelGate_apply, Equiv.symm_symm]
  simp only [physPhaseDiagonal, Matrix.diagonal_apply, phaseDiagonal, Matrix.diagonal_apply]
  by_cases hjj : j = j'
  · subst j'
    simp [physAmp]
  · have hne : (slotEquiv w) j ≠ (slotEquiv w) j' := by
      intro h
      apply hjj
      exact (slotEquiv w).injective h
    simp only [if_neg hne, if_neg hjj]

/-- The physical preparation matrix is the option-slot preparation matrix relabeled onto the
register. -/
theorem physPrepare_eq (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    physPrepare D w xs k
      = relabelGate (slotEquiv w).symm
          (prepareMatrix k (slotWeight D w xs) (slotAmpW D w xs)) := by
  rw [physPrepare, physPhaseDiagonal_eq, physMag, prepareMatrix]
  rw [← CircuitRelabel.relabelGate_mul]

/-- Preparation of the physical pivot state is the relabeling of preparation from the `none`
slot. -/
theorem physPrepare_ket (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w)
      = relabelState (slotEquiv w).symm
          (prepareMatrix k (slotWeight D w xs) (slotAmpW D w xs) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) := by
  have hpiv : relabelState (slotEquiv w).symm (Qatlib.Foundations.PureStateMath.Ket none) = Qatlib.Foundations.PureStateMath.Ket (pivotSlot w) := by
    rw [relabelState_ket]
    rfl
  rw [physPrepare_eq, ← hpiv, relabelGate_mulVec_relabelState]

/-- The physical target is the relabeling of the loaded option-slot target. -/
theorem physTarget_eq (D w : ℕ) (xs : DenseTable D) :
    physTarget D w xs = relabelState (slotEquiv w).symm (loadedTarget (physLoaded D w xs)) := by
  have hmass : (physLoaded D w xs).mass = slotMass D w xs := physLoaded_mass D w xs
  funext j
  rw [physTarget, relabelState_apply, Equiv.symm_symm]
  have hamp : physAmp D w xs j = slotAmpW D w xs (slotEquiv w j) := rfl
  cases hslot : slotEquiv w j with
  | none =>
    rw [hamp, hslot]
    simp [slotAmpW, ratZero, ratToComplex, loadedTarget]
  | some j' =>
    rw [hamp, hslot, slotAmpW_some]
    simp only [loadedTarget]
    have hamp2 : (physLoaded D w xs).amplitude j' = physSlotAmp D w xs j' := rfl
    rw [hamp2, hmass]

/-- For positive slot mass, physical preparation from the pivot has Euclidean error at most `32
* 2 ^ w / 2 ^ k`. -/
theorem physPrepare_state_error (D w : ℕ) (xs : DenseTable D) (k : ℕ)
    (hmass : 0 < slotMass D w xs) :
    ‖stateVector (physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w))
        - stateVector (physTarget D w xs)‖ ≤ 32 * ((2 ^ w : ℕ) : ℝ) / 2 ^ k := by
  have hL : (physLoaded D w xs).mass = slotMass D w xs := physLoaded_mass D w xs
  have hpos : 0 < (physLoaded D w xs).mass := by rw [hL]; exact hmass
  have hw : (physLoaded D w xs).weights = slotWeight D w xs := physLoaded_weights D w xs
  have ha : (physLoaded D w xs).amp = slotAmpW D w xs := physLoaded_amp D w xs
  have herr := prepareMatrix_state_error k (physLoaded D w xs) hpos
  rw [hw, ha] at herr
  have hdiff : ‖stateVector (physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w))
        - stateVector (physTarget D w xs)‖
      = ‖stateVector (prepareMatrix k (slotWeight D w xs) (slotAmpW D w xs) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (loadedTarget (physLoaded D w xs))‖ := by
    rw [physPrepare_ket, physTarget_eq]
    exact stateVector_sub_relabelState_norm (slotEquiv w).symm _ _
  rw [hdiff]
  have h2w1 : 1 ≤ 2 ^ w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
  have hid : (((2 ^ w - 1 : ℕ) : ℝ)) + 1 = ((2 ^ w : ℕ) : ℝ) := by
    have h : 2 ^ w - 1 + 1 = 2 ^ w := by omega
    exact_mod_cast h
  calc
    ‖stateVector (prepareMatrix k (slotWeight D w xs) (slotAmpW D w xs) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (loadedTarget (physLoaded D w xs))‖
        ≤ 32 * ((((2 ^ w - 1 : ℕ) : ℝ)) + 1) / 2 ^ k := herr
    _ = 32 * ((2 ^ w : ℕ) : ℝ) / 2 ^ k := by rw [hid]

/-- For positive `D`, its selected address width, and positive slot mass, physical preparation
error is at most `64 * D / 2 ^ k`. -/
theorem physPrepare_state_error_le (D w : ℕ) (xs : DenseTable D) (k : ℕ)
    (hD : 0 < D) (hw : w = addressBitsFor D) (hmass : 0 < slotMass D w xs) :
    ‖stateVector (physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w))
        - stateVector (physTarget D w xs)‖ ≤ 64 * D / 2 ^ k := by
  have herr := physPrepare_state_error D w xs k hmass
  have h2w : 2 ^ w ≤ 2 * D := by rw [hw]; exact slotCount_le D hD
  have h2w' : ((2 ^ w : ℕ) : ℝ) ≤ ((2 * D : ℕ) : ℝ) := by exact_mod_cast h2w
  calc
    ‖stateVector (physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w))
        - stateVector (physTarget D w xs)‖ ≤ 32 * ((2 ^ w : ℕ) : ℝ) / 2 ^ k := herr
    _ ≤ 32 * ((2 * D : ℕ) : ℝ) / 2 ^ k := by gcongr
    _ = 64 * D / 2 ^ k := by rw [Nat.cast_mul]; ring

/-- The physical resource account has bit-time charge `(2 * (2 ^ w - 1) * k + 2 * D * k) * (b +
1)`. -/
theorem physAccount_bitTime (D w : ℕ) (k b : ℕ) :
    (physAccount D w k b).bitTime
      = (2 * (2 ^ w - 1) * k + 2 * D * k) * (b + 1) := by
  simp [ResourceAccount.bitTime, physAccount, phaseComparisons]

/-- For nonzero input, each of the two square-root bracket computations used for phase
approximation records exactly `k` comparisons. -/
theorem phaseApprox_bracket_comparisons (z : RatComplex) (k : ℕ) (hz : z ≠ ratZero) :
    (rationalSqrtBracket (z.1 ^ 2 / ratSq z) k).2.2 = k ∧
      (rationalSqrtBracket (1 - z.1 ^ 2 / ratSq z) k).2.2 = k := by
  have hr2 : 0 < ratSq z := by
    have hz1 : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (Prod.ext h.1 h.2)
    rcases hz1 with h | h
    · have hp : 0 < z.1 ^ 2 + z.2 ^ 2 := by positivity
      simpa only [ratSq] using! hp
    · have hp : 0 < z.1 ^ 2 + z.2 ^ 2 := by positivity
      simpa only [ratSq] using! hp
  have hq0 : (0 : ℚ) ≤ z.1 ^ 2 / ratSq z := by
    positivity
  have hq1 : z.1 ^ 2 / ratSq z ≤ 1 := by
    have h1 : z.1 ^ 2 ≤ ratSq z := by
      have hsq : ratSq z = z.1 ^ 2 + z.2 ^ 2 := rfl
      nlinarith
    exact (div_le_one hr2).mpr h1
  have h1 := rational_sqrt_bracket_actual_interval_and_comparisons
    (z.1 ^ 2 / ratSq z) k hq0 hq1
  (try dsimp only at h1)
  have h2 := rational_sqrt_bracket_actual_interval_and_comparisons
    (1 - z.1 ^ 2 / ratSq z) k (by linarith) (by linarith)
  (try dsimp only at h2)
  exact ⟨h1.2.2.2.2.2.2.left, h2.2.2.2.2.2.2.left⟩

/-- The phase comparison charge is the number of entries times the per-label comparison charge. -/
theorem phaseComparisons_eq (D k : ℕ) : phaseComparisons D k = D * phaseLabelComparisons k := by
  simp only [phaseComparisons, phaseLabelComparisons]
  ring

/-- For positive `D` and its selected address width, the physical bit-time charge is bounded by
`(2 * (2 * D) * k + 2 * D * k) * (b + 1)`. -/
theorem physAccount_bitTime_le (D w : ℕ) (hD : 0 < D) (hw : w = addressBitsFor D)
    (k b : ℕ) :
    (physAccount D w k b).bitTime ≤ (2 * (2 * D) * k + 2 * D * k) * (b + 1) := by
  have h2 : 2 ^ w ≤ 2 * D := by rw [hw]; exact slotCount_le D hD
  have hle : 2 ^ w - 1 ≤ 2 * D := by omega
  have h1 : 2 * (2 ^ w - 1) ≤ 2 * (2 * D) := by nlinarith
  have h2' : 2 * (2 ^ w - 1) * k ≤ 2 * (2 * D) * k := Nat.mul_le_mul_right k h1
  have h3 : 2 * (2 ^ w - 1) * k + 2 * D * k ≤ 2 * (2 * D) * k + 2 * D * k := by omega
  have h4 := Nat.mul_le_mul_right (b + 1) h3
  simpa [ResourceAccount.bitTime, physAccount, phaseComparisons] using! h4

/-- The physical resource account records `w + (w + 1)` peak qubits and `D` peak classical
cells. -/
theorem physAccount_peak (D w : ℕ) (k b : ℕ) :
    (physAccount D w k b).peakQubits = w + (w + 1) ∧
      (physAccount D w k b).peakCells = D := ⟨rfl, rfl⟩

/-- The maximum wire count in the scoped program trace is `n + 1`. -/
theorem scopedAccess_peakQubits (n : ℕ) (w : List (ScopedOracleStep n)) :
    (scopedWireTrace w).foldl max 0 = n + 1 :=
  (scopedAccess_peak_space n w).2.2.2

/-- A conditional-update fold leaves its initial value unchanged if no entry has the requested
key. -/
private theorem foldl_noMatch {α β : Type} (key : α → ℕ) (val : α → β) (a : ℕ) :
    ∀ (z : β) (l : List α),
      (∀ p ∈ l, key p ≠ a) →
      l.foldl (fun acc p => if key p = a then val p else acc) z = z := by
  intro z l
  induction l generalizing z with
  | nil => intro _; rfl
  | cons p l ih =>
    intro h
    have hp : key p ≠ a := h p (by simp)
    have hl : ∀ q ∈ l, key q ≠ a := by
      intro q hq
      exact h q (by simp [hq])
    rw [List.foldl_cons, ih _ hl]
    simp [hp]

/-- A conditional-update fold returns a selected entry's value when that entry matches the key
and no later entry matches. -/
private theorem foldl_lastWrite {α β : Type} (key : α → ℕ) (val : α → β) :
    ∀ (a : ℕ) (v : β) (pre post : List α),
      (∀ p ∈ post, key p ≠ a) →
      ∀ (z : β) (e : α),
        key e = a → val e = v →
        (pre ++ e :: post).foldl (fun acc p => if key p = a then val p else acc) z = v := by
  intro a v pre
  induction pre with
  | nil =>
    intro post hpost z e hkey hval
    rw [List.nil_append, List.foldl_cons]
    have hz : (if key e = a then val e else z) = v := by simp [hkey, hval]
    rw [hz, foldl_noMatch key val a v post hpost]
  | cons e0 pre ih =>
    intro post hpost z e hkey hval
    rw [List.cons_append, List.foldl_cons,
      ih post hpost ((fun acc p => if key p = a then val p else acc) z e0) e hkey hval]

/-- A legal Boolean entry list builds a table whose values are computed by a last-write fold
starting from false. -/
theorem buildBoolTable_spec (D : ℕ) (es : List (ℕ × Bool))
    (hleg : ∀ p ∈ es, p.1 < D) :
    ∃ T : Fin D → Bool, buildBoolTable D es = some T ∧
      ∀ a, T a = es.foldl (fun acc e => if e.1 = a.val then e.2 else acc) false := by
  refine ⟨fun a => es.foldl (fun acc e => if e.1 = a.val then e.2 else acc) false, ?_, ?_⟩
  · rw [buildBoolTable, if_pos hleg]
  · intro a
    rfl

/-- For legal Boolean entries, the last write to an address determines the built table's value
there. -/
theorem buildBoolTable_repeated (D : ℕ) (es : List (ℕ × Bool)) (a : Fin D) (v : Bool)
    (hleg : ∀ p ∈ es, p.1 < D)
    (hpreL hpostL : List (ℕ × Bool))
    (hes : es = hpreL ++ (a.val, v) :: hpostL)
    (hnoLater : ∀ p ∈ hpostL, p.1 ≠ a.val) :
    ∃ T : Fin D → Bool, buildBoolTable D es = some T ∧ T a = v := by
  obtain ⟨T, hT, hfold⟩ := buildBoolTable_spec D es hleg
  refine ⟨T, hT, ?_⟩
  rw [hfold a, hes]
  exact foldl_lastWrite (fun e : ℕ × Bool => e.1) (fun e : ℕ × Bool => e.2)
    a.val v hpreL hpostL hnoLater false (a.val, v) rfl rfl

/-- The last sparse entry at an address determines its resolved rational complex amplitude. -/
theorem sparseResolve_lastWrite (D : ℕ) (es : List SparseEntry) (a : Fin D) (v : RatComplex)
    (hpreL hpostL : List SparseEntry)
    (hes : es = hpreL ++ ⟨a.val, v⟩ :: hpostL)
    (hnoLater : ∀ p ∈ hpostL, p.position ≠ a.val) :
    sparseResolve es a = v := by
  rw [sparseResolve, hes]
  exact foldl_lastWrite (fun e : SparseEntry => e.position)
    (fun e : SparseEntry => e.value) a.val v hpreL hpostL hnoLater ratZero ⟨a.val, v⟩
    rfl rfl

/-- The Boolean table builder rejects a list containing an out-of-range address. -/
theorem buildBoolTable_rejects_illegal (D : ℕ) (es : List (ℕ × Bool)) (p : ℕ) (v : Bool)
    (hmem : (p, v) ∈ es) (hp : D ≤ p) : buildBoolTable D es = none := by
  have hne : ¬ (∀ p ∈ es, p.1 < D) := by
    intro h
    have := h (p, v) hmem
    omega
  rw [buildBoolTable, if_neg hne]

/-- The chosen address width provides strictly more basis states than the table size. -/
theorem addressBitsFor_covers (D : ℕ) : D < 2 ^ addressBitsFor D :=
  addressBitsFor_sufficient D

/-- The Boolean table oracle preserves the address and XORs the addressed table value into the
target bit. -/
theorem controlledAccess_ket (D : ℕ) (T : Fin D → Bool) (a : Fin D) (b : Bool) :
    BitOracleOn T *ᵥ Qatlib.Foundations.PureStateMath.Ket (a, b) = Qatlib.Foundations.PureStateMath.Ket (a, b ^^ T a) := by
  have h := applyGate_bitOracleOn_ket T a b
  simpa [ApplyGate] using! h

/-- Applying the Boolean table oracle twice gives the identity matrix. -/
theorem controlledAccess_inv (D : ℕ) (T : Fin D → Bool) :
    BitOracleOn T * BitOracleOn T = 1 :=
  bitOracleOn_mul_self T

/-- The Boolean table oracle is unitary. -/
theorem controlledAccess_unitary (D : ℕ) (T : Fin D → Bool) :
    BitOracleOn T ∈ Matrix.unitaryGroup (Fin D × Bool) ℂ :=
  bitOracleOn_unitary T

/-- An access contract's table oracle XORs the addressed table value into the target bit. -/
theorem AccessContract_query (D : ℕ) (c : AccessContract D) (a : Fin D) (b : Bool) :
    BitOracleOn c.table *ᵥ Qatlib.Foundations.PureStateMath.Ket (a, b) = Qatlib.Foundations.PureStateMath.Ket (a, b ^^ c.table a) :=
  controlledAccess_ket D c.table a b

/-- An access contract's table oracle is its own inverse. -/
theorem AccessContract_inverse (D : ℕ) (c : AccessContract D) :
    BitOracleOn c.table * BitOracleOn c.table = 1 :=
  controlledAccess_inv D c.table

/-- A contract constructed from a table satisfies its precondition obligation. -/
theorem constructedContract_obligation (D : ℕ) (T : Fin D → Bool) (paid : ℕ) :
    (constructedContract D T paid).preconditionObligation :=
  Or.inl rfl

/-- A granted contract satisfies its obligation when its declared access preconditions hold. -/
theorem grantedContract_obligation (D : ℕ) (T : Fin D → Bool) (p : AccessPreconditions)
    (paid : ℕ) (h : p.satisfiedBy) :
    (grantedContract D T p paid).preconditionObligation :=
  Or.inr h

/-- A granted contract fails its obligation when its declared access preconditions do not hold. -/
theorem grantedContract_obligation_ne (D : ℕ) (T : Fin D → Bool) (p : AccessPreconditions)
    (paid : ℕ) (h : ¬ p.satisfiedBy) :
    ¬ (grantedContract D T p paid).preconditionObligation := by
  intro hconj
  rcases hconj with hk | hs
  · simp [grantedContract] at hk
  · exact h hs

/-- For nonnegative weights, rational magnitude preparation records exactly `2 * D * k`
comparisons. -/
theorem magnitudeComparisons {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (hw : ∀ a, 0 ≤ w a) :
    rationalWeightComparisons w k = 2 * D * k :=
  (rational_weight_data_ranges_and_actual_comparisons D k w hw).2.2

/-- The sum of two comparison charges of `2 * D * k`, for magnitude and phase processing. -/
def totalComparisons (D : ℕ) (k : ℕ) : ℕ := 2 * D * k + 2 * D * k

/-- The workspace count `D + (D + 1)` assigned to a table of size `D`. -/
def peakWorkspace (D : ℕ) : ℕ := D + (D + 1)

/-- Any dense loader that recovers every table entry on every input must read at least `D`
distinct entries. -/
theorem dense_reading_lower_bound (D : ℕ) (L : DenseLoader D)
    (h : ∀ (xs : DenseTable D) (a : Fin D), L.run xs a = xs a) :
    D ≤ L.reads.card :=
  denseLoader_reads_card_ge D L h

/-- A compiled scoped program uses twice its phase-step count in queries and one gate per source
step. -/
theorem scopedAccess_counts (n : ℕ) (w : List (ScopedOracleStep n)) :
    QueryCount (scopedCompile w) = 2 * scopedPhaseCount w ∧
      GateCount (scopedCompile w) = w.length :=
  (scoped_program_actual_query_and_gate_counts n w).2

/-- The total access charge splits into paid entries and the charge for `m` accesses, and bounds
each part separately. -/
theorem accessContract_charge_split (D : ℕ) (c : AccessContract D) (m : ℕ) :
    c.totalCharge m = c.paidEntries + m * (Nat.log2 D + 1 + c.perAccess) ∧
      c.paidEntries ≤ c.totalCharge m ∧
      m * (Nat.log2 D + 1 + c.perAccess) ≤ c.totalCharge m := by
  have h : c.totalCharge m = c.paidEntries + m * (Nat.log2 D + 1 + c.perAccess) := by
    simp [AccessContract.totalCharge, addressBitsFor]
  refine ⟨h, ?_, ?_⟩
  · rw [h]
    omega
  · rw [h]
    omega

/-- A contract charged by a universally correct dense loader's read count pays for at least `D`
entries. -/
theorem denseBuild_charges_reads (D : ℕ) (T : Fin D → Bool) (L : DenseLoader D)
    (h : ∀ (xs : DenseTable D) (a : Fin D), L.run xs a = xs a) :
    D ≤ (constructedContract D T L.reads.card).paidEntries := by
  rw [constructedContract]
  exact dense_reading_lower_bound D L h

/-- A contract built using the full dense loader pays for exactly `D` entries. -/
theorem denseBuild_paidEntries (D : ℕ) (T : Fin D → Bool) :
    (constructedContract D T (fullDenseLoader D).reads.card).paidEntries = D := by
  rw [constructedContract]
  simp [fullDenseLoader_reads]

/-- A contract charged for `D` constructed entries has total charge at least `D`, with the
stated setup-plus-access formula. -/
theorem totalCharge_not_poly_log (D : ℕ) (T : Fin D → Bool) (m : ℕ)
    (_hD : 0 < D) :
    D ≤ (constructedContract D T D).totalCharge m ∧
      (constructedContract D T D).totalCharge m
        = D + m * (Nat.log2 D + 1 + (constructedContract D T D).perAccess) := by
  have hsplit := accessContract_charge_split D (constructedContract D T D) m
  have hpaid : (constructedContract D T D).paidEntries = D := rfl
  have hper : (constructedContract D T D).perAccess = 1 := rfl
  refine ⟨?_, ?_⟩
  · rw [hsplit.1, hpaid]
    omega
  · rw [hsplit.1, hpaid, hper]

/-- The conjunction of the stated squared-modulus, exact phase normalization, read-count,
comparison-count, bit-time, and preparation-word counting conventions. -/
def DeclaredConventions : Prop :=

  (∀ z : RatComplex, ratSq z = z.1 ^ 2 + z.2 ^ 2) ∧

  (∀ (z : RatComplex) (k : ℕ), (phaseApprox z k).1 ^ 2 + (phaseApprox z k).2 ^ 2 = 1) ∧

  (∀ (D : ℕ) (xs : DenseTable D), (fullDenseLoader D).reads.card = D) ∧

  (∀ (D : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ), (∀ a, 0 ≤ w a) →
    rationalWeightComparisons w k = 2 * D * k) ∧

  (∀ a : ResourceAccount,
    a.bitTime = a.comparisons * (a.bits.amplitudeBits + 1) + a.queries * a.bits.addressBits) ∧

  (∀ (D : ℕ) (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex),
    adjointGateCount (prepareWord k w amp) = D + 1 ∧
      adjointQueryCount (prepareWord k w amp) = 0) ∧

  (∀ (D k : ℕ), phaseComparisons D k = D * phaseLabelComparisons k) ∧
  (∀ (z : RatComplex) (k : ℕ) (hz : z ≠ ratZero),
    (rationalSqrtBracket (z.1 ^ 2 / ratSq z) k).2.2 = k ∧
      (rationalSqrtBracket (1 - z.1 ^ 2 / ratSq z) k).2.2 = k)

/-- The finite data-access definitions satisfy `DeclaredConventions`. -/
theorem declaredConventions_hold : DeclaredConventions := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rfl
  · intro z k
    exact phaseApprox_unit z k
  · intro D xs
    exact fullDenseLoader_reads D
  · intro D k w hw
    exact magnitudeComparisons k w hw
  · intro a
    rfl
  · intro D k w amp
    exact prepareWord_counts k w amp
  · intro D k
    exact phaseComparisons_eq D k
  · intro z k hz
    exact phaseApprox_bracket_comparisons z k hz

/-- Collects phase normalization, dense and sparse loading specifications, exact target
preparation, and operator and state error bounds for abstract and physical preparation. -/
theorem clause1_complete :
    (∀ (z : RatComplex) (k : ℕ), (phaseApprox z k).1 ^ 2 + (phaseApprox z k).2 ^ 2 = 1) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
      (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w),
      ‖prepareMatrix k w amp - exactPrepareMatrix w amp‖ ≤ 32 * (D + 1) / 2 ^ k) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex),
      evaluate 1 (prepareWord k w amp) = prepareMatrix k w amp) ∧
    (∀ (D : ℕ) (xs : DenseTable D) (hm : 0 < (∑ i : Fin D, ratSq (xs i))),
      (loadDense D xs).map (fun L => (L.amplitude, L.reads)) = some (xs, D)) ∧
    (∀ {D : ℕ} (L : LoadedInput D) (hpos : 0 < L.mass),
      exactPrepareMatrix L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none = loadedTarget L) ∧
    (∀ {D : ℕ} (k : ℕ) (L : LoadedInput D) (hpos : 0 < L.mass),
      ‖stateVector (prepareMatrix k L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (loadedTarget L)‖ ≤ 32 * (D + 1) / 2 ^ k) ∧
    (∀ (D : ℕ) (es : List SparseEntry)
      (hleg : ∀ e ∈ es, e.position < D)
      (hm : (∑ i : Fin D, ratSq (sparseResolve es i)) ≠ 0),
      (loadSparse D es).map (fun L => (L.amplitude, L.reads))
        = some ((fun a => sparseResolve es a), es.length)) ∧
    (∀ {D : ℕ} (ε : ℚ) (hε : 0 < ε)
      (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex)
      (hw : ∀ a, 0 ≤ w a) (hm : 0 < rationalWeightMass w),
      ‖prepareMatrix (precisionFor D ε) w amp - exactPrepareMatrix w amp‖ ≤ (ε : ℝ)) ∧
    (∀ {D : ℕ} (ε : ℚ) (hε : 0 < ε) (L : LoadedInput D) (hpos : 0 < L.mass),
      ‖stateVector (prepareMatrix (precisionFor D ε) L.weights L.amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (loadedTarget L)‖ ≤ (ε : ℝ)) ∧
    (∀ (D w : ℕ) (xs : DenseTable D) (k : ℕ) (hmass : 0 < slotMass D w xs),
      ‖stateVector (physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w))
          - stateVector (physTarget D w xs)‖ ≤ 32 * ((2 ^ w : ℕ) : ℝ) / 2 ^ k) ∧
    (∀ (D w : ℕ) (xs : DenseTable D) (k : ℕ) (hD : 0 < D) (hw : w = addressBitsFor D)
      (hmass : 0 < slotMass D w xs),
      ‖stateVector (physPrepare D w xs k *ᵥ Qatlib.Foundations.PureStateMath.Ket (pivotSlot w))
          - stateVector (physTarget D w xs)‖ ≤ 64 * D / 2 ^ k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z k
    exact phaseApprox_unit z k
  · intro D k w amp hw hm
    exact prepareMatrix_error k w amp hw hm
  · intro D k w amp
    exact prepareWord_eval k w amp
  · intro D xs hm
    exact loadDense_spec D xs hm
  · intro D L hpos
    exact exactPrepareMatrix_target L hpos
  · intro D k L hpos
    exact prepareMatrix_state_error k L hpos
  · intro D es hleg hm
    exact loadSparse_spec D es hleg hm
  · intro D ε hε w amp hw hm
    exact prepareError_le_epsilon ε hε w amp hw hm
  · intro D ε hε L hpos
    exact prepareState_error_le_epsilon ε hε L hpos
  · intro D w xs k hmass
    exact physPrepare_state_error D w xs k hmass
  · intro D w xs k hD hw hmass
    exact physPrepare_state_error_le D w xs k hD hw hmass

/-- Collects Boolean and sparse last-write semantics, invalid-address rejection, oracle action
and inverse laws, access obligations, and clean scoped execution with its workspace trace. -/
theorem clause2_complete :
    (∀ (D : ℕ) (es : List (ℕ × Bool)) (p : ℕ) (v : Bool),
      (p, v) ∈ es → D ≤ p → buildBoolTable D es = none) ∧
    (∀ (D : ℕ) (es : List (ℕ × Bool)) (hleg : ∀ p ∈ es, p.1 < D),
      ∃ T : Fin D → Bool, buildBoolTable D es = some T ∧
        ∀ a, T a = es.foldl (fun acc e => if e.1 = a.val then e.2 else acc) false) ∧
    (∀ (D : ℕ) (es : List (ℕ × Bool)) (a : Fin D) (v : Bool)
      (hleg : ∀ p ∈ es, p.1 < D)
      (hpreL hpostL : List (ℕ × Bool))
      (hes : es = hpreL ++ (a.val, v) :: hpostL)
      (hnoLater : ∀ p ∈ hpostL, p.1 ≠ a.val),
      ∃ T : Fin D → Bool, buildBoolTable D es = some T ∧ T a = v) ∧
    (∀ (D : ℕ) (es : List SparseEntry) (a : Fin D) (v : RatComplex)
      (hpreL hpostL : List SparseEntry)
      (hes : es = hpreL ++ ⟨a.val, v⟩ :: hpostL)
      (hnoLater : ∀ p ∈ hpostL, p.position ≠ a.val),
      sparseResolve es a = v) ∧
    (∀ (D : ℕ) (T : Fin D → Bool) (a : Fin D) (b : Bool),
      BitOracleOn T *ᵥ Qatlib.Foundations.PureStateMath.Ket (a, b) = Qatlib.Foundations.PureStateMath.Ket (a, b ^^ T a)) ∧
    (∀ (D : ℕ) (T : Fin D → Bool), BitOracleOn T * BitOracleOn T = 1) ∧
    (∀ (D : ℕ), D < 2 ^ addressBitsFor D) ∧
    (∀ (D : ℕ) (c : AccessContract D) (a : Fin D) (b : Bool),
      BitOracleOn c.table *ᵥ Qatlib.Foundations.PureStateMath.Ket (a, b) = Qatlib.Foundations.PureStateMath.Ket (a, b ^^ c.table a)) ∧
    (∀ (D : ℕ) (c : AccessContract D), BitOracleOn c.table * BitOracleOn c.table = 1) ∧
    (∀ (D : ℕ) (T : Fin D → Bool) (paid : ℕ),
      (constructedContract D T paid).preconditionObligation) ∧
    (∀ (D : ℕ) (T : Fin D → Bool) (p : AccessPreconditions) (paid : ℕ),
      p.satisfiedBy → (grantedContract D T p paid).preconditionObligation) ∧
    (∀ (D : ℕ) (T : Fin D → Bool) (p : AccessPreconditions) (paid : ℕ),
      ¬ p.satisfiedBy → ¬ (grantedContract D T p paid).preconditionObligation) ∧
    (∀ (n : ℕ) (f : Reg n → Bool) (a b : Bool) (x y : Reg n),
      scopedBitOracle f (a, x) (b, y) = (if x = y ∧ a = (b ^^ f y) then 1 else 0) ∧
        scopedBitOracle f ∈ Matrix.unitaryGroup (Bool × Reg n) ℂ) ∧
    (∀ (n : ℕ) (z : ℂ),
      QueryCount (scopedCompile [ScopedOracleStep.phase (n := n) z]) = 2 ∧
        GateCount (scopedCompile [ScopedOracleStep.phase (n := n) z]) = 1) ∧
    (∀ (n : ℕ) (f : Reg n → Bool) (w : List (ScopedOracleStep n)) (ψ : QState (Reg n)),
      Run (scopedBitOracle f) (scopedCompile w) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)
        = TensorState (Qatlib.Foundations.PureStateMath.Ket false) (scopedLogicalMatrix f w *ᵥ ψ)) ∧
    (∀ (n : ℕ) (w : List (ScopedOracleStep n)),
      (scopedAllocationFrame n)ᴴ * scopedAllocationFrame n = 1 ∧
        (∀ ψ : QState (Reg n), scopedAllocationFrame n *ᵥ ψ = TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) ∧
        scopedWireTrace w = [n] ++ List.replicate ((scopedCompile w).length + 1) (n + 1) ++ [n] ∧
        (scopedWireTrace w).foldl max 0 = n + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact buildBoolTable_rejects_illegal
  · exact buildBoolTable_spec
  · exact buildBoolTable_repeated
  · exact sparseResolve_lastWrite
  · exact controlledAccess_ket
  · exact controlledAccess_inv
  · exact addressBitsFor_covers
  · exact AccessContract_query
  · exact AccessContract_inverse
  · exact constructedContract_obligation
  · exact grantedContract_obligation
  · exact grantedContract_obligation_ne
  · exact scopedAccess_query
  · exact scopedAccess_step_cost
  · exact scopedAccess_clean
  · exact scopedAccess_peak_space

/-- Collects preparation counts, dense-read lower bounds, declared conventions, reflection
synthesis and physical resource bounds, scoped counts, access charges, and slot-mass
preservation. -/
theorem clause3_complete :
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (amp : Option (Fin D) → RatComplex),
      adjointGateCount (prepareWord k w amp) = D + 1 ∧
        adjointQueryCount (prepareWord k w amp) = 0) ∧
    (∀ {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ) (hw : ∀ a, 0 ≤ w a),
      rationalWeightComparisons w k = 2 * D * k) ∧
    (∀ (D : ℕ) (L : DenseLoader D),
      (∀ (xs : DenseTable D) (a : Fin D), L.run xs a = xs a) → D ≤ L.reads.card) ∧
    DeclaredConventions ∧
    (∀ (D w : ℕ) (xs : DenseTable D) (k : ℕ),
      ∃ gs : List (ReflectionGate (w + (w + 1))), reflectionLegal gs ∧
        gs.length ≤ 128 * (w + 1) ^ 2 * 4 ^ w ∧
        QueryCount (reflectionCompile gs) = 0 ∧
        GateCount (reflectionCompile gs) = gs.length ∧
        ∀ ψ : QState (Reg w),
          Run 1 (reflectionCompile gs) (knownFrameEmbed w ψ) =
            knownFrameEmbed w (physPrepare D w xs k *ᵥ ψ)) ∧
    (∀ (D : ℕ) (hD : 0 < D), 2 ^ addressBitsFor D ≤ 2 * D) ∧
    (∀ (D w : ℕ) (hD : 0 < D) (hw : w = addressBitsFor D),
      128 * (w + 1) ^ 2 * 4 ^ w ≤ 512 * (w + 1) ^ 2 * D ^ 2) ∧
    (∀ (D w : ℕ) (k b : ℕ),
      (physAccount D w k b).bitTime = (2 * (2 ^ w - 1) * k + 2 * D * k) * (b + 1)) ∧
    (∀ (D w : ℕ) (hD : 0 < D) (hw : w = addressBitsFor D) (k b : ℕ),
      (physAccount D w k b).bitTime ≤ (2 * (2 * D) * k + 2 * D * k) * (b + 1)) ∧
    (∀ (D w : ℕ) (k b : ℕ),
      (physAccount D w k b).peakQubits = w + (w + 1) ∧
        (physAccount D w k b).peakCells = D) ∧
    (∀ (n : ℕ) (f : Reg n → Bool) (w : List (ScopedOracleStep n))
      (hU : ∀ U, ScopedOracleStep.data U ∈ w → U ∈ Matrix.unitaryGroup (Reg n) ℂ)
      (hz : ∀ z, ScopedOracleStep.phase z ∈ w → ‖z‖ = 1),
      ∃ gs : List (ReflectionGate (n + (n + 1))), reflectionLegal gs ∧
        gs.length ≤ 128 * (n + 1) ^ 2 * 4 ^ n ∧
        QueryCount (reflectionCompile gs) = 0 ∧
        GateCount (reflectionCompile gs) = gs.length ∧
        ∀ ψ : QState (Reg n),
          Run 1 (reflectionCompile gs) (knownFrameEmbed n ψ) =
            knownFrameEmbed n (scopedLogicalMatrix f w *ᵥ ψ)) ∧
    (∀ (n : ℕ) (w : List (ScopedOracleStep n)),
      QueryCount (scopedCompile w) = 2 * scopedPhaseCount w ∧
        GateCount (scopedCompile w) = w.length) ∧
    (∀ (D : ℕ) (c : AccessContract D) (m : ℕ),
      c.totalCharge m = c.paidEntries + m * (Nat.log2 D + 1 + c.perAccess) ∧
        c.paidEntries ≤ c.totalCharge m ∧
        m * (Nat.log2 D + 1 + c.perAccess) ≤ c.totalCharge m) ∧
    (∀ (D : ℕ) (T : Fin D → Bool) (L : DenseLoader D),
      (∀ (xs : DenseTable D) (a : Fin D), L.run xs a = xs a) →
        D ≤ (constructedContract D T L.reads.card).paidEntries) ∧
    (∀ (D : ℕ) (T : Fin D → Bool) (m : ℕ) (hD : 0 < D),
      D ≤ (constructedContract D T D).totalCharge m ∧
        (constructedContract D T D).totalCharge m
          = D + m * (Nat.log2 D + 1 + (constructedContract D T D).perAccess)) ∧
    (∀ (D w : ℕ) (xs : DenseTable D) (hD : D < 2 ^ w),
      slotMass D w xs = ∑ j : Fin D, ratSq (xs j)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D k w amp
    exact prepareWord_counts k w amp
  · intro D k w hw
    exact magnitudeComparisons k w hw
  · intro D L h
    exact dense_reading_lower_bound D L h
  · exact declaredConventions_hold
  · intro D w xs k
    exact physPrepare_synthesis D w xs k
  · intro D hD
    exact slotCount_le D hD
  · intro D w hD hw
    exact physGateCount_le D w hD hw
  · intro D w k b
    exact physAccount_bitTime D w k b
  · intro D w hD hw k b
    exact physAccount_bitTime_le D w hD hw k b
  · intro D w k b
    exact physAccount_peak D w k b
  · intro n f w hU hz
    exact scopedAccess_synthesis f w hU hz
  · exact scopedAccess_counts
  · exact accessContract_charge_split
  · exact denseBuild_charges_reads
  · exact totalCharge_not_poly_log
  · exact slotMass_eq

end Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
