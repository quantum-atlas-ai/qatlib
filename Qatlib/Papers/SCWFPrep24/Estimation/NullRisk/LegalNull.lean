/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PauliStates
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.GridParity

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

/-!
# Legal Null

The two actual checkerboard colors have exactly opposite source Bloch coordinates in every one of the six Pauli frames.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The two actual checkerboard colors have exactly opposite source Bloch coordinates in every one of the six Pauli frames. -/
theorem pauliCheckerBasis_bloch_opposite (a : Fin 3) (b color : Bool) (i : Fin 3) :
    qubitBloch (pauliCheckerBasis a b (!color)) i =
      -qubitBloch (pauliCheckerBasis a b color) i := by
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases a <;> cases b <;> cases color <;> fin_cases i <;>
    simp [qubitBloch, pauliField, pauliCheckerBasis, sixPauliState,
      Qatlib.Foundations.PureStateMath.boolEquivFin2] <;> field_simp <;> nlinarith [hr]

/-- A bijective parity-flipping physical shift cancels the complete input's Bloch sum for every fixed hidden phase assignment. -/
theorem checkerboard_global_bloch_zero {A : Type*} [Fintype A]
    (parity : A → Bool) (ζ : A → ℂ) (basis : Bool → Bool → ℂ)
    (hζ : ∀ x, Complex.normSq (ζ x) = 1)
    (hb : ∀ b i, qubitBloch (basis (!b)) i = -qubitBloch (basis b) i)
    (e : A ≃ A) (he : ∀ x, parity (e x) = !(parity x)) (i : Fin 3) :
    (∑ x, qubitBloch (checkerboardSpinor parity ζ basis x) i) = 0 := by
  have hf (x : A) : qubitBloch (checkerboardSpinor parity ζ basis (e x)) i =
      -qubitBloch (checkerboardSpinor parity ζ basis x) i := by
    change qubitBloch (fun s => ζ (e x)*basis (parity (e x)) s) i =
      -qubitBloch (fun s => ζ x*basis (parity x) s) i
    rw [qubitBloch_scale, qubitBloch_scale, hζ, hζ, one_mul, one_mul, he, hb]
  have hs := Equiv.sum_comp e (fun x => qubitBloch (checkerboardSpinor parity ζ basis x) i)
  simp_rw [hf, Finset.sum_neg_distrib] at hs
  linarith

/-- The literal canonical periodic double shift preserves the actual checkerboard parity, including every wrap edge. -/
theorem gridParity_double_shift (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (j : Fin d) (x : Fin d → Fin N) :
    gridParity d N hN (periodicDoubleShift d N j x) = gridParity d N hN x := by
  have hs := congrArg (fun e : (Fin d → Fin N) ≃ (Fin d → Fin N) => e x)
    (periodic_unit_shift_square d N j)
  change periodicUnitShift d N j (periodicUnitShift d N j x) =
    periodicDoubleShift d N j x at hs
  rw [← hs, gridParity_unit_shift, gridParity_unit_shift, Bool.not_not]

/-- Identical checkerboard colors at a physical double shift have zero actual singlet probability for every fixed pair of hidden phases. -/
theorem checkerboard_same_color_bell_zero {A : Type*}
    (parity : A → Bool) (ζ : A → ℂ) (basis : Bool → Bool → ℂ)
    (x y : A) (hxy : parity y = parity x) :
    bellProbability (checkerboardSpinor parity ζ basis x)
      (checkerboardSpinor parity ζ basis y) = 0 := by
  simp only [bellProbability, determinant, checkerboardSpinor, hxy]
  have hz : ζ x*basis (parity x) false*(ζ y*basis (parity x) true) -
      ζ x*basis (parity x) true*(ζ y*basis (parity x) false) = 0 := by ring
  rw [hz, map_zero, zero_div]

/-- Each actual six-frame phased periodic null input obeys the original zero global Bloch promise for every Pauli coordinate. -/
theorem actual_null_periodic_global_bloch_zero (d N : ℕ) [NeZero N]
    (hN : 2 ∣ N) (j : Fin d) (axis : Fin 3) (sign : Bool)
    (ω : (Fin d → Fin N) → Fin 4) (i : Fin 3) :
    (∑ x, qubitBloch (checkerboardSpinor (gridParity d N hN)
      (fun x => fourthPhase (ω x)) (pauliCheckerBasis axis sign) x) i) = 0 :=
  checkerboard_global_bloch_zero _ _ _ (fun x => fourthPhase_normSq (ω x))
    (pauliCheckerBasis_bloch_opposite axis sign) (periodicUnitShift d N j)
    (gridParity_unit_shift d N hN j) i

/-- Every actual six-frame phased periodic null input has exactly zero public double-shift Bell probability, with no phase averaging or discarded current term. -/
theorem actual_null_periodic_double_bell_zero (d N : ℕ) [NeZero N]
    (hN : 2 ∣ N) (axis : Fin 3) (sign : Bool)
    (ω : (Fin d → Fin N) → Fin 4) (j : Fin d) (x : Fin d → Fin N) :
    bellProbability (checkerboardSpinor (gridParity d N hN)
      (fun x => fourthPhase (ω x)) (pauliCheckerBasis axis sign) x)
      (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
        (pauliCheckerBasis axis sign) (periodicDoubleShift d N j x)) = 0 :=
  checkerboard_same_color_bell_zero _ _ _ _ _ (gridParity_double_shift d N hN j x)

/-- Every actual member of the six-frame phased periodic null prior has zero full original loss at the actual physical mesh size. -/
theorem actual_null_periodic_full_original_loss_zero (d N : ℕ) [NeZero N]
    (hN : 2 ∣ N) (axis : Fin 3) (sign : Bool)
    (ω : (Fin d → Fin N) → Fin 4) (lam : ℝ) :
    spinorDiscreteLoss
      (real0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
        (pauliCheckerBasis axis sign)))
      (imag0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
        (pauliCheckerBasis axis sign)))
      (real1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
        (pauliCheckerBasis axis sign)))
      (imag1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
        (pauliCheckerBasis axis sign)))
      (fun _ _ => 0) (periodicUnitShift d N) (2*Real.pi/N) 1 lam = 0 :=
  phased_periodic_full_original_loss_zero d N hN _
    (pauliCheckerBasis_orthogonal axis sign) ω lam

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
