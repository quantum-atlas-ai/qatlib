/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualReadout

/-!
# Exact dyadic readout of the actual phase-estimation word

Paper: R. Cleve, A. Ekert, C. Macchiavello, M. Mosca, *Quantum Algorithms
Revisited*, arXiv:quant-ph/9708016 (fixed PDF `quant-ph_9708016.pdf`).

The promoted module
`Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualReadout`
covers the nearest-grid case.  This module adds the dyadic case: a dyadic
eigenphase `a/2^m` is recovered exactly by the complete executed
supplied-powered-device word `PoweredProgram.word m`, including the `m = 0`
and `m = 1` boundary registers, and the dyadic label is read with
probability one from any normalized data eigenstate.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation

/-- A dyadic eigenphase is recovered exactly by the same complete word, including zero- and one-bit registers. -/
theorem actual_dyadic_run {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : Fin (2 ^ m)) (U : Matrix I I ℂ) (ψ : QState I)
    (hψ : U.mulVec ψ =
      Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (2 ^ m : ℝ) : ℝ)) • ψ) :
    PoweredProgram.execute U (PoweredProgram.word m) (TensorState (Ket (ZeroStr m)) ψ) =
      TensorState (Ket ((bitVecEquiv m).symm a)) ψ := by
  rw [PoweredProgram.word_run m U ((a.val : ℝ) / (2 ^ m : ℝ)) ψ hψ]
  have hk : qpeKernel (2 ^ m) ((a.val : ℝ) / (2 ^ m : ℝ) : ℝ) = Ket a := by
    funext z
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (offgrid_phase_geometric_and_periodic (2 ^ m) 0 z (Nat.two_pow_pos m)).2.2 a
  rw [hk]
  congr 1
  funext z
  simp [Qatlib.Foundations.PureStateMath.BornBridge.relabelState,
    Qatlib.Foundations.PureStateMath.Ket, Equiv.apply_eq_iff_eq_symm_apply]

/-- Reading the dyadic label in the actual experiment has probability one for every normalized data eigenstate. -/
theorem actual_dyadic_readout {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : Fin (2 ^ m)) (U : Matrix I I ℂ) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ =
      Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (2 ^ m : ℝ) : ℝ)) • ψ) :
    MeasureProb (PoweredProgram.execute U (PoweredProgram.word m)
      (TensorState (Ket (ZeroStr m)) ψ))
      ({(bitVecEquiv m).symm a} ×ˢ (Finset.univ : Finset I)) = 1 := by
  rw [actual_dyadic_run m a U ψ hψ, measureProb_tensorState_left hn]
  simp [MeasureProb, BornProb, Qatlib.Foundations.PureStateMath.Ket]

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
