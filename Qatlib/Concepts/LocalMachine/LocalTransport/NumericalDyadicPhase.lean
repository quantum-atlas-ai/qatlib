/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalPiApproximation
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate

/-!
# Numerical dyadic phase circuits

`numericalDyadicPhase` uses rational approximations to pi and repeated Cayley-phase squaring to
approximate dyadic complex phases while retaining exact unit modulus. `numericalGateMatrix`
replaces controlled phases in local QFT words while preserving the Hadamard and swap gates, in
the Fourier-circuit setting of [NielsenChuang2010].

The module proves a per-gate error of at most `2^(-k)`, a word error bounded by the gate count
times this quantity, exact circuit counts, and explicit arithmetic term and squaring counters.

## Main statements

* `numerical_dyadic_phase_exact_unitarity_and_error`: combine exact unit modulus with a dyadic
  phase-error bound.
* `numericalProgramMatrix_error`: bound accumulated operator error for a gate word.
* `numerical_dyadic_program_actual_error_and_counts`: bound state error and give exact gate and
  query counts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The signed rational approximation to `2 * pi / 2^j` obtained from `piRatApprox (k + 4)`. -/
def numericalPhaseRat (j : ℕ) (neg : Bool) (k : ℕ) : ℚ :=
  (if neg then (-1 : ℚ) else (1 : ℚ)) * (2 * piRatApprox (k + 4)) / ((2 ^ j : ℕ) : ℚ)

/-- A Gaussian rational phase formed by a counted Cayley approximation to one eighth of the
target angle followed by three squarings. -/
def numericalDyadicPhase (j : ℕ) (neg : Bool) (k : ℕ) : GaussianRat :=
  (squareLoop (countedCayleyPhase (numericalPhaseRat j neg k / 8) (k + 4)).1 3).1

/-- Rewrite the eightfold Cayley-angle error as a scaled arctangent remainder. -/
private theorem cayley_eighth_factor (x : ℚ) (k : ℕ) :
    8 * rationalCayleyAngle (x : ℝ) (k + 4) - 8 * (x : ℝ)
      = 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
        * (Real.arctan ((x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
          - (x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))) := by
  have hcast : ((2 ^ (k + 4) : ℕ) : ℝ) = ((2 : ℝ) ^ k) * 16 := by
    push_cast [Nat.pow_add]
    ring
  rw [rationalCayleyAngle, hcast]
  field_simp
  ring

/-- For a rational input of absolute value at most one, the eightfold Cayley-angle error is at
most `2^(-k) / 384`. -/
private theorem cayley_eighth_error (x : ℚ) (k : ℕ) (hx : |(x : ℝ)| ≤ 1) :
    |8 * rationalCayleyAngle (x : ℝ) (k + 4) - 8 * (x : ℝ)|
      ≤ ((2 : ℝ) ⁻¹) ^ k / 384 := by
  have hNpos : (0 : ℝ) < 2 * ((2 ^ (k + 4) : ℕ) : ℝ) := by positivity
  have hstep := rational_cayley_derived_arctan_remainder ((x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
  have htabs : |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))|
      ≤ 1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)) := by
    rw [abs_div, abs_of_pos hNpos]
    have hc : |(x : ℝ)| * (2 * ((2 ^ (k + 4) : ℕ) : ℝ))
        ≤ ((1 : ℝ)) * (2 * ((2 ^ (k + 4) : ℕ) : ℝ)) :=
      _root_.mul_le_mul hx (le_refl _) (le_of_lt hNpos) (by norm_num)
    exact (_root_.div_le_div_iff₀ hNpos hNpos).mpr hc
  have hcast : ((2 ^ (k + 4) : ℕ) : ℝ) = ((2 : ℝ) ^ k) * 16 := by
    push_cast [Nat.pow_add]
    ring
  have hcube : |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))| ^ 3
      ≤ (1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))) ^ 3 := by
    have h2 := _root_.mul_le_mul htabs htabs (abs_nonneg _) (by positivity)
    have h3 := _root_.mul_le_mul h2 htabs (abs_nonneg _) (by positivity)
    rwa [show |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))|
            * |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))|
            * |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))|
        = |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))| ^ 3 from by ring,
      show (1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
            * (1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
            * (1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
        = (1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))) ^ 3 from by ring] at h3
  have hdiv : |(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))| ^ 3 / 3
      ≤ (1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))) ^ 3 / 3 := by
    linarith [hcube]
  have h1 : 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
      * |Real.arctan ((x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
        - (x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))|
      ≤ 2 / (3 * ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k) * 256) := by
    have hm : 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
        * |Real.arctan ((x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ)))
          - (x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))|
      ≤ 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
          * (|(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))| ^ 3 / 3) :=
      _root_.mul_le_mul (le_refl _) hstep (by positivity) (by positivity)
    have hc2 : 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
        * (|(x : ℝ) / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))| ^ 3 / 3)
      ≤ 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
          * ((1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))) ^ 3 / 3) :=
      _root_.mul_le_mul (le_refl _) hdiv (by positivity) (by positivity)
    have heq : 16 * ((2 ^ (k + 4) : ℕ) : ℝ)
          * ((1 / (2 * ((2 ^ (k + 4) : ℕ) : ℝ))) ^ 3 / 3)
      = 2 / (3 * ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k) * 256) := by
      rw [hcast]
      field_simp
      ring
    refine hm.trans (hc2.trans ?_)
    rw [heq]
  have h2 : 2 / (3 * ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k) * 256) ≤ ((2 : ℝ) ⁻¹) ^ k / 384 := by
    have hw : ((2 : ℝ) ⁻¹) ^ k = 1 / ((2 : ℝ) ^ k) := by
      rw [inv_eq_one_div, _root_.div_pow, one_pow]
    have h2k1 : (1 : ℝ) ≤ ((2 : ℝ) ^ k) := by
      exact_mod_cast Nat.one_le_pow' k 1
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ k) := by positivity
    rw [hw, _root_.div_le_div_iff₀
      (by positivity : (0 : ℝ) < 3 * ((2:ℝ) ^ k) * ((2:ℝ) ^ k) * 256)
      (by positivity : (0 : ℝ) < 384)]
    field_simp
    nlinarith [h2k1, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
  rw [cayley_eighth_factor, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 16 * ((2 ^ (k + 4) : ℕ) : ℝ))]
  exact h1.trans h2

/-- Scaling a rational approximation to pi by `2 / 2^j` gives absolute error at most twice the
original error bound. -/
private theorem scaled_pi_error (r : ℚ) (j : ℕ) {ε : ℝ} (h : |((r : ℝ)) - Real.pi| ≤ ε) :
    |((2 : ℝ)) * (r : ℝ) / ((2 ^ j : ℕ) : ℝ)
      - 2 * Real.pi / ((2 ^ j : ℕ) : ℝ)| ≤ 2 * ε := by
  have hc : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow' j 1
  have hscale : ((2 : ℝ)) * (r : ℝ) / ((2 ^ j : ℕ) : ℝ)
      - 2 * Real.pi / ((2 ^ j : ℕ) : ℝ)
      = 2 * (((r : ℝ)) - Real.pi) / ((2 ^ j : ℕ) : ℝ) := by
    field_simp
  rw [hscale, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by positivity : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ))]
  calc 2 * |(((r : ℝ)) - Real.pi)| / ((2 ^ j : ℕ) : ℝ)
      ≤ 2 * |(((r : ℝ)) - Real.pi)| :=
        _root_.div_le_self (by positivity) hc
    _ ≤ 2 * ε := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

/-- The angle derived from `numericalPhaseRat` differs from the target dyadic phase angle by at
most `2^(-(k + 5))`. -/
private theorem numerical_phase_angle_deviation (j k : ℕ) (neg : Bool) :
    |8 * ((numericalPhaseRat j neg k / 8 : ℚ) : ℝ) - dyadicPhaseAngle j neg|
      ≤ ((2 : ℝ) ⁻¹) ^ (k + 5) := by
  have hpi := (rational_machin_pi_computed_precision.2 (k + 4)).2.2

  have hbound : ((2 : ℝ) ⁻¹) ^ k * ((2 : ℝ) ⁻¹) ^ 5 = ((2 : ℝ) ⁻¹) ^ (k + 5) := by
    rw [← pow_add]
  have hcalc : (2 : ℝ) * (((2 : ℝ) ⁻¹) ^ (k + 4 + 2)) = ((2 : ℝ) ⁻¹) ^ (k + 5) := by
    have h1 : ((2 : ℝ) ⁻¹) ^ (k + 4 + 2)
        = ((2 : ℝ) ⁻¹) ^ (k + 5) * ((2 : ℝ) ⁻¹) := by
      rw [show k + 4 + 2 = (k + 5) + 1 from by omega, pow_succ]
    rw [h1]
    field_simp
  have hdev : |((2 : ℝ)) * ((piRatApprox (k + 4) : ℚ) : ℝ) / ((2 ^ j : ℕ) : ℝ)
      - 2 * Real.pi / ((2 ^ j : ℕ) : ℝ)| ≤ ((2 : ℝ) ⁻¹) ^ (k + 5) :=
    (scaled_pi_error (piRatApprox (k + 4)) j hpi).trans (le_of_eq hcalc)
  have hcastj : ((2 : ℝ) ^ j) = ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    ring
  cases neg with
  | false =>
      have hq : ((numericalPhaseRat j false k / 8 : ℚ) : ℝ)
          = ((piRatApprox (k + 4) : ℚ) : ℝ) / (4 * ((2 ^ j : ℕ) : ℝ)) := by
        rw [numericalPhaseRat]
        norm_num
        field_simp
        ring
      have hθ : dyadicPhaseAngle j false = 2 * Real.pi / (2 ^ j : ℝ) := rfl
      rw [hq, hθ, hcastj]
      have hscale : 8 * (((piRatApprox (k + 4) : ℚ) : ℝ) / (4 * ((2 ^ j : ℕ) : ℝ)))
          = 2 * ((piRatApprox (k + 4) : ℚ) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by
        field_simp
        ring
      rw [hscale]
      exact hdev
  | true =>
      have hq : ((numericalPhaseRat j true k / 8 : ℚ) : ℝ)
          = -(((piRatApprox (k + 4) : ℚ) : ℝ) / (4 * ((2 ^ j : ℕ) : ℝ))) := by
        rw [numericalPhaseRat]
        norm_num
        field_simp
        ring
      have hθ : dyadicPhaseAngle j true = -(2 * Real.pi / (2 ^ j : ℝ)) := rfl
      rw [hq, hθ, hcastj]
      have hscale : 8 * -(((piRatApprox (k + 4) : ℚ) : ℝ) / (4 * ((2 ^ j : ℕ) : ℝ)))
          = -(2 * ((piRatApprox (k + 4) : ℚ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
        field_simp
        ring
      rw [hscale, show -(2 * ((piRatApprox (k + 4) : ℚ) : ℝ) / ((2 ^ j : ℕ) : ℝ))
          - -(2 * Real.pi / ((2 ^ j : ℕ) : ℝ))
          = -((2 * ((piRatApprox (k + 4) : ℚ) : ℝ) / ((2 ^ j : ℕ) : ℝ))
            - 2 * Real.pi / ((2 ^ j : ℕ) : ℝ)) from by ring, abs_neg]
      exact hdev

/-- The numerical Gaussian rational phase has norm exactly one and differs from the target
dyadic exponential by at most `2^(-k)`. -/
theorem numerical_dyadic_phase_exact_unitarity_and_error (j k : ℕ) (neg : Bool) :
    ‖gaussianRatComplex (numericalDyadicPhase j neg k)‖ = 1 ∧
    ‖gaussianRatComplex (numericalDyadicPhase j neg k)
      - Complex.exp ((dyadicPhaseAngle j neg : ℂ) * Complex.I)‖ ≤ ((2 : ℝ) ⁻¹) ^ k := by
  set x : ℚ := numericalPhaseRat j neg k / 8 with hxdef

  have hsquare : gaussianRatComplex (numericalDyadicPhase j neg k)
      = (gaussianRatComplex (countedCayleyPhase x (k + 4)).1) ^ (2 ^ 3 : ℕ) := by
    rw [numericalDyadicPhase]
    exact (squareLoop_value_and_counts (countedCayleyPhase x (k + 4)).1 3).1
  have hnorm : ‖gaussianRatComplex (numericalDyadicPhase j neg k)‖ = 1 := by
    rw [hsquare, norm_pow, gaussianRatComplex_countedCayleyPhase_norm]
    norm_num
  refine ⟨hnorm, ?_⟩

  have hzc := gaussianRatComplex_countedCayleyPhase_eq_exp x (k + 4)
  have hexp8 : (gaussianRatComplex (countedCayleyPhase x (k + 4)).1) ^ (2 ^ 3 : ℕ)
      = Complex.exp (((8 * rationalCayleyAngle (x : ℝ) (k + 4) : ℝ) : ℂ) * Complex.I) := by
    rw [hzc, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hr4 := (rational_machin_pi_computed_precision.2 (k + 4)).2.1
  have h2j : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow' j 1
  have hx8 : |(x : ℝ)| ≤ 1 := by
    have hc4 : (0 : ℝ) < 4 * ((2 ^ j : ℕ) : ℝ) := by positivity
    have hle : ((piRatApprox (k + 4) : ℚ) : ℝ) ≤ 4 := by
      exact_mod_cast (le_of_lt (rational_machin_pi_computed_precision.2 (k + 4)).2.1)
    have hpos : (0 : ℝ) < ((piRatApprox (k + 4) : ℚ) : ℝ) := by
      exact_mod_cast (rational_machin_pi_computed_precision.2 (k + 4)).1
    have h4c : (4 : ℝ) ≤ 4 * ((2 ^ j : ℕ) : ℝ) := by nlinarith [h2j]
    rw [hxdef]
    cases neg with
    | false =>
        have hval : ((numericalPhaseRat j false k / 8 : ℚ) : ℝ)
            = ((piRatApprox (k + 4) : ℚ) : ℝ) / (4 * ((2 ^ j : ℕ) : ℝ)) := by
          rw [numericalPhaseRat]
          norm_num
          field_simp
          ring
        rw [hval, abs_div, abs_of_pos hc4, abs_of_pos hpos]
        exact (_root_.div_le_one hc4).mpr (le_trans hle h4c)
    | true =>
        have hval : ((numericalPhaseRat j true k / 8 : ℚ) : ℝ)
            = -(((piRatApprox (k + 4) : ℚ) : ℝ) / (4 * ((2 ^ j : ℕ) : ℝ))) := by
          rw [numericalPhaseRat]
          norm_num
          field_simp
          ring
        rw [hval, abs_neg, abs_of_nonneg
          (_root_.div_nonneg (le_of_lt hpos) (le_of_lt hc4))]
        exact (_root_.div_le_one hc4).mpr (le_trans hle h4c)

  have hcayley := cayley_eighth_error x k hx8
  have hdev := numerical_phase_angle_deviation j k neg
  have htri : ‖Complex.exp (((8 * rationalCayleyAngle (x : ℝ) (k + 4) : ℝ) : ℂ) * Complex.I)
      - Complex.exp ((dyadicPhaseAngle j neg : ℂ) * Complex.I)‖
      ≤ ((2 : ℝ) ⁻¹) ^ k := by
    have hl := norm_exp_mul_I_sub_le (8 * rationalCayleyAngle (x : ℝ) (k + 4))
      (dyadicPhaseAngle j neg)
    refine hl.trans ?_
    have hsplit : 8 * rationalCayleyAngle (x : ℝ) (k + 4) - dyadicPhaseAngle j neg
        = (8 * rationalCayleyAngle (x : ℝ) (k + 4) - 8 * (x : ℝ))
          + (8 * (x : ℝ) - dyadicPhaseAngle j neg) := by ring
    rw [hsplit]
    have h5 : ((2 : ℝ) ⁻¹) ^ (k + 5)
        = ((2 : ℝ) ⁻¹) ^ k * (1 / 32) := by
      rw [show ((2 : ℝ) ⁻¹) ^ (k + 5) = ((2 : ℝ) ⁻¹) ^ k * ((2 : ℝ) ⁻¹) ^ 5 from by
        rw [← pow_add],
        show ((2 : ℝ) ⁻¹) ^ 5 = 1 / 32 from by norm_num]
    have hB32 : |8 * (x : ℝ) - dyadicPhaseAngle j neg|
        ≤ ((2 : ℝ) ⁻¹) ^ k * (1 / 32) :=
      hdev.trans (le_of_eq h5)
    have hwpos : (0 : ℝ) ≤ ((2 : ℝ) ⁻¹) ^ k :=
      pow_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ⁻¹) k
    have hsmall : (13 : ℝ) / 384 < 1 := by norm_num
    calc |(8 * rationalCayleyAngle (x : ℝ) (k + 4) - 8 * (x : ℝ))
            + (8 * (x : ℝ) - dyadicPhaseAngle j neg)|
        ≤ |8 * rationalCayleyAngle (x : ℝ) (k + 4) - 8 * (x : ℝ)|
            + |8 * (x : ℝ) - dyadicPhaseAngle j neg| :=
          _root_.abs_add_le _ _
      _ ≤ ((2 : ℝ) ⁻¹) ^ k / 384 + ((2 : ℝ) ⁻¹) ^ k * (1 / 32) :=
          add_le_add hcayley hB32
      _ = ((2 : ℝ) ⁻¹) ^ k * (13 / 384) := by ring
      _ ≤ ((2 : ℝ) ⁻¹) ^ k := mul_le_of_le_one_right hwpos (le_of_lt hsmall)
  rw [hsquare, hexp8]
  exact htri

/-- Interpret a local QFT gate using the numerical dyadic phase for controlled-phase gates and
the exact matrix for Hadamard and swap gates. -/
noncomputable def numericalGateMatrix {n : ℕ} (k : ℕ) (g : LocalQFTGate n) :
    Matrix (Reg n) (Reg n) ℂ :=
  match g with
  | .h a => localGateMatrix (.h a)
  | .swap a c => localGateMatrix (.swap a c)
  | .cp a c e neg => Matrix.diagonal fun x =>
      if x a && x c then gaussianRatComplex (numericalDyadicPhase e neg k) else 1

/-- The numerical controlled-phase error is diagonal, with the scalar phase error on basis
states where both selected bits are true and zero elsewhere. -/
theorem numericalGateMatrix_cp_sub (n : ℕ) (k : ℕ) (a c : Fin n) (e : ℕ) (neg : Bool) :
    numericalGateMatrix k (.cp a c e neg) - localGateMatrix (.cp a c e neg)
      = Matrix.diagonal fun x : Reg n =>
        if x a && x c then (gaussianRatComplex (numericalDyadicPhase e neg k)
          - Complex.exp ((dyadicPhaseAngle e neg : ℂ) * Complex.I)) else 0 := by
  show Matrix.diagonal _ - Matrix.diagonal _ = _
  rw [Matrix.diagonal_sub]
  congr 1
  funext x
  by_cases h : x a && x c
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, sub_self]

/-- Every numerical local QFT gate matrix is exactly unitary. -/
theorem numericalGateMatrix_unitary {n : ℕ} (k : ℕ) (g : LocalQFTGate n) :
    numericalGateMatrix k g ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  cases g with
  | h a => exact localGateMatrix_h_unitary n a
  | swap a c => exact localGateMatrix_swap_unitary n a c
  | cp a c e neg =>
      have hnorm := (numerical_dyadic_phase_exact_unitarity_and_error e k neg).1
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      simp only [numericalGateMatrix]
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext x
      split_ifs with h
      · rw [Pi.star_apply, if_pos h, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq, hnorm]
        norm_num
      · rw [Pi.star_apply, if_neg h]
        simp

/-- Each numerical local QFT gate matrix differs from its exact matrix in operator norm by at
most `2^(-k)`. -/
theorem numericalGateMatrix_error {n : ℕ} (k : ℕ) (g : LocalQFTGate n) :
    ‖numericalGateMatrix k g - localGateMatrix g‖ ≤ ((2 : ℝ) ⁻¹) ^ k := by
  cases g with
  | h a => rw [numericalGateMatrix]; rw [sub_self, norm_zero]; positivity
  | swap a c => rw [numericalGateMatrix]; rw [sub_self, norm_zero]; positivity
  | cp a c e neg =>
      rw [numericalGateMatrix_cp_sub, Matrix.l2_opNorm_diagonal,
        pi_norm_le_iff_of_nonneg (by positivity)]
      intro b
      by_cases h : b a && b c
      · rw [if_pos h]
        exact (numerical_dyadic_phase_exact_unitarity_and_error e k neg).2
      · rw [if_neg h, norm_zero]
        positivity

/-- Compile a local QFT gate word into fixed circuit gates using numerical gate matrices at
precision `k`. -/
noncomputable def numericalDyadicCircuit {n : ℕ} (k : ℕ) (gs : List (LocalQFTGate n)) :
    Circuit (Reg n) :=
  gs.map (fun g => Step.gate (numericalGateMatrix k g))

/-- The matrix of a numerical local gate word, recursively multiplying each successive gate on
the left in execution order. -/
noncomputable def numericalProgramMatrix {n : ℕ} (k : ℕ) :
    List (LocalQFTGate n) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g :: gs => numericalProgramMatrix k gs * numericalGateMatrix k g

/-- Compiling the empty numerical gate word gives the empty circuit. -/
@[simp] theorem numericalDyadicCircuit_nil {n : ℕ} (k : ℕ) :
    numericalDyadicCircuit k ([] : List (LocalQFTGate n)) = [] := rfl

/-- Compiling a nonempty word places its numerical head gate before the compiled tail. -/
@[simp] theorem numericalDyadicCircuit_cons {n : ℕ} (k : ℕ) (g : LocalQFTGate n)
    (gs : List (LocalQFTGate n)) :
    numericalDyadicCircuit k (g :: gs) =
      Step.gate (numericalGateMatrix k g) :: numericalDyadicCircuit k gs := rfl

/-- The numerical circuit acts by its program matrix, has unitary gates and unitary program
matrix, uses no queries, and has one gate per word letter. -/
theorem numericalDyadicProgram_run (n k : ℕ) (gs : List (LocalQFTGate n))
    (ψ : QState (Reg n)) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (numericalDyadicCircuit k gs) ψ =
      ApplyGate (numericalProgramMatrix k gs) ψ ∧
    IsUnitaryCircuit (numericalDyadicCircuit k gs) ∧
    numericalProgramMatrix k gs ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
    QueryCount (numericalDyadicCircuit k gs) = 0 ∧
    GateCount (numericalDyadicCircuit k gs) = gs.length := by
  have run : ∀ (gs : List (LocalQFTGate n)) (ψ : QState (Reg n)),
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (numericalDyadicCircuit k gs) ψ =
        ApplyGate (numericalProgramMatrix k gs) ψ := by
    intro gs
    induction gs with
    | nil => intro _; simp [numericalProgramMatrix]
    | cons g gs ih =>
        intro ψ
        rw [numericalDyadicCircuit_cons, run_gate, ih, numericalProgramMatrix, applyGate_mul]
  have unitary : ∀ (gs : List (LocalQFTGate n)),
      numericalProgramMatrix k gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
    intro gs
    induction gs with
    | nil => exact (Matrix.unitaryGroup (Reg n) ℂ).one_mem
    | cons g gs ih =>
        rw [numericalProgramMatrix]
        exact Submonoid.mul_mem (Matrix.unitaryGroup (Reg n) ℂ) ih
          (numericalGateMatrix_unitary k g)
  have wellFormed : ∀ (gs : List (LocalQFTGate n)),
      IsUnitaryCircuit (numericalDyadicCircuit k gs) := by
    intro gs
    induction gs with
    | nil => exact isUnitaryCircuit_nil
    | cons g gs ih =>
        rw [numericalDyadicCircuit_cons, isUnitaryCircuit_gate]
        exact ⟨numericalGateMatrix_unitary k g, ih⟩
  have queryCount : ∀ (gs : List (LocalQFTGate n)),
      QueryCount (numericalDyadicCircuit k gs) = 0 := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih => exact ih
  have gateCount : ∀ (gs : List (LocalQFTGate n)),
      GateCount (numericalDyadicCircuit k gs) = gs.length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih => simp [ih]
  exact ⟨run gs ψ, wellFormed gs, unitary gs, queryCount gs, gateCount gs⟩

/-- The numerical program matrix is the product of the reversed list of numerical gate matrices. -/
theorem numericalProgramMatrix_eq_reverse_prod {n : ℕ} (k : ℕ)
    (gs : List (LocalQFTGate n)) :
    numericalProgramMatrix k gs = (gs.reverse.map (numericalGateMatrix k)).prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [numericalProgramMatrix, List.reverse_cons, List.map_append, List.prod_append, ih]

/-- The operator error of a numerical gate word is at most its length times `2^(-k)`. -/
theorem numericalProgramMatrix_error {n : ℕ} (k : ℕ) :
    ∀ gs : List (LocalQFTGate n),
    ‖numericalProgramMatrix k gs - localProgramMatrix gs‖
      ≤ (gs.length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
  intro gs
  rw [numericalProgramMatrix_eq_reverse_prod, localProgramMatrix_eq_reverse_prod]
  simpa only [List.length_reverse] using
    l2_norm_list_map_prod_sub_prod_le_of_le gs.reverse
      (numericalGateMatrix k) localGateMatrix (((2 : ℝ) ⁻¹) ^ k)
      (fun g _ => l2_norm_unitary_le_one (numericalGateMatrix_unitary k g))
      (fun g _ => l2_norm_unitary_le_one (localGateMatrix_unitary g))
      (fun g _ => numericalGateMatrix_error k g)

/-- A numerical local QFT circuit is unitary, has zero queries and one gate per letter, and
approximates the exact action on normalized inputs within `length * 2^(-k)`. -/
theorem numerical_dyadic_program_actual_error_and_counts :
    ∀ (n k : ℕ) (gs : List (LocalQFTGate n)),
    IsUnitaryCircuit (numericalDyadicCircuit k gs) ∧
    QueryCount (numericalDyadicCircuit k gs) = 0 ∧
    GateCount (numericalDyadicCircuit k gs) = gs.length ∧
    ∀ ψ : QState (Reg n), Normalized ψ →
      ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ)
          (numericalDyadicCircuit k gs) ψ
        - ApplyGate (localProgramMatrix gs) ψ)‖
        ≤ (gs.length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
  intro n k gs
  obtain ⟨-, isU, -, qc, gc⟩ := numericalDyadicProgram_run n k gs (Ket (ZeroStr n))
  refine ⟨isU, qc, gc, fun ψ hψ => ?_⟩
  have run := (numericalDyadicProgram_run n k gs ψ).1
  have hsub : ApplyGate (numericalProgramMatrix k gs) ψ - ApplyGate (localProgramMatrix gs) ψ
      = ApplyGate (numericalProgramMatrix k gs - localProgramMatrix gs) ψ := by
    funext i
    simp only [ApplyGate, Pi.sub_apply, Matrix.sub_mulVec]
  rw [run, hsub]
  calc ‖toEuclidean_fromVec (ApplyGate (numericalProgramMatrix k gs - localProgramMatrix gs) ψ)‖
      ≤ ‖numericalProgramMatrix k gs - localProgramMatrix gs‖ * ‖toEuclidean_fromVec ψ‖ :=
        norm_applyGate_le _ _
    _ = ‖numericalProgramMatrix k gs - localProgramMatrix gs‖ := by
        rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one]
    _ ≤ (gs.length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := numericalProgramMatrix_error k gs

/-- The numerical phase squaring counter `(k + 4) + 3`. -/
def numericalPhaseSquarings (k : ℕ) : ℕ := (k + 4) + 3

/-- The numerical phase squaring counter equals `k + 7`. -/
@[simp] theorem numericalPhaseSquarings_eq (k : ℕ) :
    numericalPhaseSquarings k = k + 7 := rfl

/-- Sum twice the phase squaring count for each controlled-phase gate, with zero contribution
from other gate types. -/
def numericalDyadicTermCount {n : ℕ} (k : ℕ) : List (LocalQFTGate n) → ℕ
  | [] => 0
  | g :: gs => numericalDyadicTermCount k gs +
      (match g with
       | .cp _ _ _ _ => 2 * numericalPhaseSquarings k
       | _ => 0)

/-- Sum the phase squaring count for each controlled-phase gate, with zero contribution from
other gate types. -/
def numericalDyadicSquaringCount {n : ℕ} (k : ℕ) : List (LocalQFTGate n) → ℕ
  | [] => 0
  | g :: gs => numericalDyadicSquaringCount k gs +
      (match g with
       | .cp _ _ _ _ => numericalPhaseSquarings k
       | _ => 0)

/-- The numerical term counter is `2 * (k + 7)` times the number of controlled-phase gates. -/
theorem numericalDyadicTermCount_eq {n : ℕ} (k : ℕ) :
    ∀ gs : List (LocalQFTGate n),
    numericalDyadicTermCount k gs = 2 * (k + 7) * gs.countP
      (fun g => match g with | .cp _ _ _ _ => true | _ => false) := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      cases g with
      | h a =>
          have hunf : numericalDyadicTermCount k (LocalQFTGate.h a :: gs)
              = numericalDyadicTermCount k gs := rfl
          have hc : List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
              (LocalQFTGate.h a :: gs)
              = List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) gs := rfl
          rw [hunf, ih, hc]
      | cp a c e neg =>
          have hunf : numericalDyadicTermCount k (LocalQFTGate.cp a c e neg :: gs)
              = numericalDyadicTermCount k gs + 2 * numericalPhaseSquarings k := rfl
          have hc : List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
              (LocalQFTGate.cp a c e neg :: gs)
              = 1 + List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) gs := by
              rw [List.countP_cons]
              simp
              omega
          rw [hunf, ih, hc, numericalPhaseSquarings_eq]
          ring
      | swap a c =>
          have hunf : numericalDyadicTermCount k (LocalQFTGate.swap a c :: gs)
              = numericalDyadicTermCount k gs := rfl
          have hc : List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
              (LocalQFTGate.swap a c :: gs)
              = List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) gs := rfl
          rw [hunf, ih, hc]

/-- The numerical squaring counter is `k + 7` times the number of controlled-phase gates. -/
theorem numericalDyadicSquaringCount_eq {n : ℕ} (k : ℕ) :
    ∀ gs : List (LocalQFTGate n),
    numericalDyadicSquaringCount k gs = (k + 7) * gs.countP
      (fun g => match g with | .cp _ _ _ _ => true | _ => false) := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      cases g with
      | h a =>
          have hunf : numericalDyadicSquaringCount k (LocalQFTGate.h a :: gs)
              = numericalDyadicSquaringCount k gs := rfl
          have hc : List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
              (LocalQFTGate.h a :: gs)
              = List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) gs := rfl
          rw [hunf, ih, hc]
      | cp a c e neg =>
          have hunf : numericalDyadicSquaringCount k (LocalQFTGate.cp a c e neg :: gs)
              = numericalDyadicSquaringCount k gs + numericalPhaseSquarings k := rfl
          have hc : List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
              (LocalQFTGate.cp a c e neg :: gs)
              = 1 + List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) gs := by
              rw [List.countP_cons]
              simp
              omega
          rw [hunf, ih, hc, numericalPhaseSquarings_eq]
          ring
      | swap a c =>
          have hunf : numericalDyadicSquaringCount k (LocalQFTGate.swap a c :: gs)
              = numericalDyadicSquaringCount k gs := rfl
          have hc : List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
              (LocalQFTGate.swap a c :: gs)
              = List.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) gs := rfl
          rw [hunf, ih, hc]

end Qatlib.Concepts.LocalMachine.LocalTransport
