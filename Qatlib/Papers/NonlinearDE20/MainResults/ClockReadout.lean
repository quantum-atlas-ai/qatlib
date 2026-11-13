/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.ForcingModel.ClockPostselect
import Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
import Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn

/-!
# Clock readout by a unitary projection program

The projection `clockProjection` retains a chosen clock block of a finite history. The module
constructs its unitary projection program, computes the successful branch and its Born
probability, and recovers Euler amplitudes from the explicit history inverse used in
[LloydEtAl2020].

## Main statements

* `clock_program_unitary`: The projection program for a clock projection is unitary on the
  direct sum of two history spaces.
* `native_clock_Born`: For a unit history vector, the native readout success probability is the
  sum of squared norms of its selected clock amplitudes.
* `inverse_history_clock_amplitude`: Selecting clock value `k` from the inverse history solution
  returns the corresponding Euler recurrence amplitude.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.NonlinearDE20.MainResults.ClockReadout
open Qatlib.Papers.NonlinearDE20.ForcingModel.Counter
open Qatlib.Papers.NonlinearDE20.HistorySystem.History
open Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn

/-- The diagonal projection onto the system subspace with clock value `k`. -/
def clockProjection {I : Type} [DecidableEq I] (N : ℕ) (k : Fin N) :
    Matrix (Fin N × I) (Fin N × I) ℂ :=
  diagonal (fun p => if p.1 = k then 1 else 0)

/-- The clock projection is self-adjoint. -/
theorem clockProjection_star {I : Type} [DecidableEq I] (N : ℕ) (k : Fin N) :
    (clockProjection (I := I) N k)ᴴ = clockProjection N k := by
  simp [clockProjection, Matrix.diagonal_conjTranspose]

/-- The clock projection is idempotent. -/
theorem clockProjection_square {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (k : Fin N) :
    clockProjection (I := I) N k * clockProjection N k = clockProjection N k := by
  rw [clockProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> norm_num

/-- The clock projection preserves amplitudes at clock value `k` and sets all other clock
amplitudes to zero. -/
theorem clockProjection_action {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (k : Fin N) (X : Fin N × I → ℂ) (p : Fin N × I) :
    (clockProjection N k *ᵥ X) p = if p.1 = k then X p else 0 := by
  simp [clockProjection, Matrix.mulVec_diagonal, ite_mul]

/-- The clock projection has operator norm at most one. -/
theorem clockProjection_norm {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (k : Fin N) :
    ‖clockProjection (I := I) N k‖ ≤ 1 := by
  rw [clockProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro p
  split_ifs <;> norm_num

/-- The projection program for a clock projection is unitary on the direct sum of two history
spaces [LloydEtAl2020]. -/
theorem clock_program_unitary {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (k : Fin N) :
    program (clockProjection (I := I) N k) ∈ Matrix.unitaryGroup ((Fin N × I) ⊕ (Fin N × I)) ℂ :=
  program_unitary _ (clockProjection_star N k) (clockProjection_square N k)

/-- The successful program branch contains precisely the selected clock amplitudes. -/
theorem clock_program_success {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (k : Fin N) (X : Fin N × I → ℂ) (p : Fin N × I) :
    (program (clockProjection N k) *ᵥ Sum.elim X 0) (Sum.inl p) =
      if p.1 = k then X p else 0 := by
  rw [program_blocks]
  simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using
    clockProjection_action N k X p

/-- For a unit history vector, the native readout success probability is the sum of squared
norms of its selected clock amplitudes [LloydEtAl2020]. -/
theorem native_clock_Born {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (k : Fin N) (x : EuclideanSpace ℂ (Fin N × I)) (hx : ‖x‖ = 1) :
    (((readout (clockProjection N k) (clockProjection_norm N k)).measure
      (MState.pure (ketOfUnit x hx))) true : ℝ) = ∑ i : I, ‖x (k,i)‖ ^ 2 := by
  rw [native_success_Born_unit, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [clockProjection_action]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- Selecting clock value `k` from the inverse history solution returns the corresponding Euler
recurrence amplitude [LloydEtAl2020]. -/
theorem inverse_history_clock_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (T : ℕ) (K : Matrix I I ℂ) (g : ℕ → I → ℂ) (k : Fin (T+1)) (i : I) :
    (program (clockProjection (T+1) k) *ᵥ
      Sum.elim (historyInverse (T+1) K *ᵥ (fun p => g p.1.val p.2)) 0) (Sum.inl (k,i)) =
        eulerSequence K g k.val i := by
  rw [clock_program_success]
  rw [← eulerHistory_eq_inverse]
  simp [eulerHistory]

end Qatlib.Papers.NonlinearDE20.MainResults.ClockReadout
