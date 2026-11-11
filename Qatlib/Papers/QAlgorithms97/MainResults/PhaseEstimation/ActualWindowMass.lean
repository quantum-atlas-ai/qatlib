/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualReadout
import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Actual phase-estimation window mass and a sufficient extra-bit budget

Paper: R. Cleve, A. Ekert, C. Macchiavello, M. Mosca, *Quantum Algorithms
Revisited*, arXiv:quant-ph/9708016 (fixed PDF `quant-ph_9708016.pdf`).

This module measures the circular-window mass of the actual executed
supplied-powered-device word `PoweredProgram.word m`, bridges it to the
existing BHMT window model, and derives an explicit sufficient extra-bit
budget for the fine-grid phase error.  It is juxtaposed with, and does not
replace, the promoted
`Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.AmplifiedPrecision`:
that module owns the published bit prescription `phasePrecisionBits` and the
corrected budget theorem `amplified_precision_corrected`, while the sharper
published budget `m = n + ⌈log₂(1/(2ε) + 1/2)⌉` remains a task-card target
that the sufficient budget below does not certify.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation

/-- The actual circular-window measurement of the complete supplied-powered-device word. -/
def actualWindowMass {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (U : Matrix I I ℂ) (φ r : ℝ) (ψ : QState I) : ℝ :=
  MeasureProb (PoweredProgram.execute U (PoweredProgram.word m)
    (TensorState (Ket (ZeroStr m)) ψ))
    ((Finset.univ.filter fun z : Reg m =>
      bhmt11CircleDist (((bitVecEquiv m z).val : ℝ) / (2 ^ m : ℝ)) φ ≤ r) ×ˢ
        (Finset.univ : Finset I))

/-- A window of the actual executed experiment has exactly the existing BHMT window mass. -/
theorem actualWindowMass_eq {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (U : Matrix I I ℂ) (φ r : ℝ) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    actualWindowMass m U φ r ψ = bhmt11WindowMass (2 ^ m) φ r := by
  rw [actualWindowMass, PoweredProgram.word_run m U φ ψ hψ,
    measureProb_tensorState_left hn]
  simp only [MeasureProb, Finset.sum_filter, bhmt11WindowMass, BornProb]
  apply Fintype.sum_equiv (bitVecEquiv m)
  intro z
  simp only [relabelState, Function.comp_apply, Equiv.symm_symm]
  rw [actual_kernel_bhmt (2 ^ m) (Nat.two_pow_pos m)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- The existing circular tail bound applies to the full physical powered-device execution. -/
theorem actual_window_tail {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (U : Matrix I I ℂ) (φ : ℝ) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ)
    (k : ℝ) (hk : 1 < k) :
    1 - 1 / (2 * (k - 1)) ≤ actualWindowMass m U φ (k / (2 ^ m : ℝ)) ψ := by
  rw [actualWindowMass_eq m U φ _ ψ hn hψ]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    bhmt_phase_estimation_theorem11_tail (2 ^ m) φ (Nat.two_pow_pos m) k hk

/-- An explicitly stronger extra-bit budget suffices for the actual fine-grid phase error; the published sharper budget remains open. -/
theorem amplified_precision_of_sufficient_budget {I : Type} [Fintype I] [DecidableEq I]
    (n t : ℕ) (ε : ℝ) (hε : 0 < ε) (ht : 2 + 1 / ε ≤ (2 : ℝ) ^ t)
    (U : Matrix I I ℂ) (φ : ℝ) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    1 - ε ≤ actualWindowMass (n + t) U φ (1 / (2 : ℝ) ^ (n + 1)) ψ := by
  let k : ℝ := (2 : ℝ) ^ t / 2
  have hk : 1 < k := by
    have hi : 0 < 1 / ε := by positivity
    dsimp [k]
    linarith
  have hr : k / (2 : ℝ) ^ (n + t) = 1 / (2 : ℝ) ^ (n + 1) := by
    dsimp [k]
    rw [pow_add, pow_succ]
    field_simp
  have hb : 1 / (2 * (k - 1)) ≤ ε := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (k - 1))).2
    have hm := mul_le_mul_of_nonneg_right ht hε.le
    have he : (1 / ε) * ε = 1 := by field_simp
    dsimp [k]
    nlinarith
  have htail := actual_window_tail (n + t) U φ ψ hn hψ k hk
  rw [hr] at htail
  linarith

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
