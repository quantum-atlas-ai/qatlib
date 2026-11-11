/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.SmoothPayoff
import Qatlib.Papers.MonteCarloInt20.QaeLaw.StepPayoff
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Papers.MonteCarloInt20.QaeLaw.ActualReadout

/-!
# Native decoding and payoff bounds for finite QAE readout

Relates the prepared finite QAE law to rational decoding and records linear and
affine payoff errors under the explicit phase assumptions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff Qatlib.Papers.MonteCarloInt20.QaeLaw.Smooth Qatlib.Papers.MonteCarloInt20.QaeLaw.Step
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds


namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual

open Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual

/-! The next bridge keeps the actual finite phase law in view while replacing the
paper's real scalar by the executable rational decoder. -/

/-- The actual finite QAE output remains normalized after native decoding: its
weighted output is in `[0,1]`, and its difference from the same finite law's
ideal scalar expectation is bounded by the requested dyadic tolerance. -/
theorem native_finite_output_expectation_bridge {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let law := aeLaw M A j S hA hM
    0 ≤ law.expect (fun z => (nativeAEDecode M k z : ℝ)) ∧
      law.expect (fun z => (nativeAEDecode M k z : ℝ)) ≤ 1 ∧
      |law.expect (fun z => (nativeAEDecode M k z : ℝ)) -
        law.expect (fun z => aeEstimate M z)| ≤ ((2 : ℝ)⁻¹) ^ k := by
  dsimp only
  let law := aeLaw M A j S hA hM
  have hscalar (z : Fin M) := native_ae_computed_scalar_precision M k z
  have hnative0 (z : Fin M) : (0 : ℝ) ≤ (nativeAEDecode M k z : ℝ) := by
    exact_mod_cast (hscalar z).1
  have hnative1 (z : Fin M) : (nativeAEDecode M k z : ℝ) ≤ 1 := by
    exact_mod_cast (hscalar z).2.1
  have hmean0 : 0 ≤ law.expect (fun z => (nativeAEDecode M k z : ℝ)) := by
    rw [FinDist.expect]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (law.nonneg z) (hnative0 z))
  have hmean1 : law.expect (fun z => (nativeAEDecode M k z : ℝ)) ≤ 1 := by
    rw [FinDist.expect]
    calc
      (∑ z, law.prob z * (nativeAEDecode M k z : ℝ)) ≤
          ∑ z, law.prob z * 1 := by
        exact Finset.sum_le_sum (fun z _ =>
          mul_le_mul_of_nonneg_left (hnative1 z) (law.nonneg z))
      _ = 1 := by simp [law.sum_one]
  have hdiff :
      law.expect (fun z => (nativeAEDecode M k z : ℝ)) -
        law.expect (fun z => aeEstimate M z) =
      ∑ z, law.prob z * ((nativeAEDecode M k z : ℝ) - aeEstimate M z) := by
    simp only [FinDist.expect]
    calc
      (∑ z, law.prob z * (nativeAEDecode M k z : ℝ)) -
          ∑ z, law.prob z * aeEstimate M z =
          ∑ z, (law.prob z * (nativeAEDecode M k z : ℝ) -
            law.prob z * aeEstimate M z) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ z, law.prob z * ((nativeAEDecode M k z : ℝ) - aeEstimate M z) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
  have habs :
      |∑ z, law.prob z * ((nativeAEDecode M k z : ℝ) - aeEstimate M z)| ≤
        ∑ z, law.prob z * ((2 : ℝ)⁻¹) ^ k := by
    calc
      |∑ z, law.prob z * ((nativeAEDecode M k z : ℝ) - aeEstimate M z)| ≤
          ∑ z, |law.prob z * ((nativeAEDecode M k z : ℝ) - aeEstimate M z)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, law.prob z * ((2 : ℝ)⁻¹) ^ k := by
        exact Finset.sum_le_sum (fun z _ => by
          rw [abs_mul, abs_of_nonneg (law.nonneg z)]
          exact mul_le_mul_of_nonneg_left (hscalar z).2.2 (law.nonneg z))
  refine ⟨hmean0, hmean1, ?_⟩
  rw [hdiff]
  calc
    |∑ z, law.prob z * ((nativeAEDecode M k z : ℝ) - aeEstimate M z)| ≤
        ∑ z, law.prob z * ((2 : ℝ)⁻¹) ^ k := habs
    _ = ((2 : ℝ)⁻¹) ^ k := by
      rw [← Finset.sum_mul, law.sum_one, one_mul]

/-! The executable decoder can also consume the paper's finite BHMT success
event directly.  This wrapper keeps the physical prepared-QAE law and its
success threshold in the Monte Carlo paper namespace. -/

/-- Native finite decoding preserves the prepared-QAE BHMT success lower bound,
with the dyadic decoder error added to the paper's finite tolerance. -/
theorem actual_native_bhmt_success {I : Type} [Fintype I] [DecidableEq I]
    (M k : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let a := MeasureProb (preparedAAState A j) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |(nativeAEDecode M k z : ℝ) - a| ≤
        2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
          Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 := by
  exact Qatlib.Concepts.AmplitudeCore.PreparedReadout.native_ae_same_record_bhmt_success
    I M k hM A j S hA

/-! A linear payoff is the primary bounded-error consumer of the actual
prepared-QAE law.  Keeping it as a named theorem avoids repeatedly
instantiating the smooth-payoff machinery with a constant derivative. -/

/-- The actual finite QAE law has a `|D| / M` error bound for the linear payoff. -/
theorem actual_linear_payoff_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/2)
    (ha : MeasureProb (preparedAAState A j) S=Real.sin (θ*Real.pi)^2) (D : ℝ) :
    |(∑ k,(aeLaw M A j S hA hM).prob k*(D*aeEstimate M k))-D*target θ| ≤
      |D|/(M:ℝ) := by
  have h := actual_smooth_payoff_error M hM A j S hA θ hθ0 hθ1 ha D
    (fun x => x) (fun _ => 1) 0
    (by intro x; convert! (hasDerivAt_id x) using 1)
    (by simpa using (LipschitzWith.const (1 : ℝ)))
  simpa using h

/-- The affine payoff consumer has the same physical `|α D| / M` error,
independent of its additive offset. -/
theorem actual_affine_payoff_error {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1/2)
    (ha : MeasureProb (preparedAAState A j) S=Real.sin (θ*Real.pi)^2)
    (D α β : ℝ) :
    |(∑ k,(aeLaw M A j S hA hM).prob k*(α*(D*aeEstimate M k)+β))-
      (α*(D*target θ)+β)| ≤ |α| * |D| / (M:ℝ) := by
  have h := actual_smooth_payoff_error M hM A j S hA θ hθ0 hθ1 ha D
    (fun x => α*x + β) (fun _ => α) 0
    (by intro x
        simpa using ((hasDerivAt_id x).const_mul α).add_const β)
    (by simpa using (LipschitzWith.const (α : ℝ)))
  simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using h

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Actual
