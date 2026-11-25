/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NonlinearDE20.MainResults.ClockReadout
public import Mathlib.Tactic

@[expose] public section

/-!
# Clock slice success mass as a coherent fraction

The history vector of [LloydEtAl2020] is produced before normalization. This module normalizes it
by the inverse square root of its total mass and shows that the native clock readout succeeds on a
chosen clock slice with probability equal to the slice mass divided by the total mass.

## Main statements

* `massScale`: the inverse square root of the total mass, as a complex scalar.
* `unitOfMass`: the ket obtained by scaling a vector of positive mass by `massScale`.
* `clock_slice_success_mass`: the clock readout success probability is the slice mass over the
  total history mass.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Classical ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.NonlinearDE20.MainResults.ClockMass

open Qatlib.Papers.NonlinearDE20.MainResults.ClockReadout
open Qatlib.Papers.NonlinearDE20.HistorySystem.History
open Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument
open Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn

/-- The inverse square root of the total mass of a vector, as a complex scalar. -/
def massScale {ι : Type} [Fintype ι] (h : ι → ℂ) : ℂ :=
  ((Real.sqrt (∑ q, Complex.normSq (h q)))⁻¹ : ℂ)

/-- The squared norm of the mass scale is the inverse of the total mass. -/
theorem massScale_normSq {ι : Type} [Fintype ι] (h : ι → ℂ)
    (hn : 0 < ∑ q, Complex.normSq (h q)) :
    ‖massScale h‖ ^ 2 = (∑ q, Complex.normSq (h q))⁻¹ := by
  have hS : 0 < ∑ q, Complex.normSq (h q) := hn
  have hsqrt : 0 < Real.sqrt (∑ q, Complex.normSq (h q)) := Real.sqrt_pos.mpr hS
  rw [massScale, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt,
    inv_pow, Real.sq_sqrt hS.le]

/-- Normalizing a vector of positive mass by the inverse square root of that mass gives a ket. -/
def unitOfMass {ι : Type} [Fintype ι] (h : ι → ℂ)
    (hn : 0 < ∑ p, Complex.normSq (h p)) : Ket ι where
  vec p := massScale h * h p
  normalized' := by
    have hS : 0 < ∑ q, Complex.normSq (h q) := hn
    calc ∑ x, ‖massScale h * h x‖ ^ 2 = ∑ x, ‖massScale h‖ ^ 2 * ‖h x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [norm_mul, mul_pow]
      _ = ‖massScale h‖ ^ 2 * ∑ x, ‖h x‖ ^ 2 := by rw [Finset.mul_sum]
      _ = (∑ q, Complex.normSq (h q))⁻¹ * ∑ x, Complex.normSq (h x) := by
          rw [massScale_normSq h hn]
          simp only [Complex.normSq_eq_norm_sq]
      _ = 1 := inv_mul_cancel₀ hS.ne'

/-- The clock readout succeeds on the slice of clock value `k` with probability equal to the slice
mass of the history divided by its total mass [LloydEtAl2020]. -/
theorem clock_slice_success_mass {I : Type} [Fintype I] [DecidableEq I]
    (T : ℕ) (K : Matrix I I ℂ) (g : ℕ → I → ℂ) (k : Fin (T+1))
    (h : Fin (T+1) × I → ℂ)
    (hh : h = historyInverse (T+1) K *ᵥ (fun p => g p.1.val p.2))
    (hn : 0 < ∑ p, Complex.normSq (h p)) :
    ((readout (clockProjection (T+1) k) (clockProjection_norm (T+1) k)).measure
        (MState.pure (unitOfMass h hn)) true : ℝ) =
      (∑ i : I, Complex.normSq (eulerSequence K g k.val i)) / (∑ p, Complex.normSq (h p)) := by
  have hS : 0 < ∑ p, Complex.normSq (h p) := hn
  have hval : ∀ (j : Fin (T+1)) (i : I), h (j,i) = eulerSequence K g j.val i := by
    intro j i
    rw [hh, ← eulerHistory_eq_inverse]
    rfl
  let x : EuclideanSpace ℂ (Fin (T+1) × I) := WithLp.toLp 2 fun p => massScale h * h p
  have hxval : ∀ p, x p = massScale h * h p := fun p => rfl
  have hxn : ‖x‖ = 1 := by
    have h2 : ‖x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ p, ‖x p‖ ^ 2 = ∑ p, ‖massScale h‖ ^ 2 * ‖h p‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hxval p, norm_mul, mul_pow]
        _ = ‖massScale h‖ ^ 2 * ∑ p, ‖h p‖ ^ 2 := by rw [Finset.mul_sum]
        _ = (∑ q, Complex.normSq (h q))⁻¹ * ∑ p, Complex.normSq (h p) := by
            rw [massScale_normSq h hn]
            simp only [Complex.normSq_eq_norm_sq]
        _ = 1 := inv_mul_cancel₀ hS.ne'
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]
  have hket : ketOfUnit x hxn = unitOfMass h hn := by
    apply Ket.ext
    intro p
    exact hxval p
  rw [← hket, native_clock_Born (T+1) k x hxn]
  calc ∑ i : I, ‖x (k,i)‖ ^ 2
      = ∑ i : I, ‖massScale h‖ ^ 2 * ‖h (k,i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hxval (k,i), norm_mul, mul_pow]
    _ = ‖massScale h‖ ^ 2 * ∑ i : I, ‖h (k,i)‖ ^ 2 := by rw [Finset.mul_sum]
    _ = (∑ p, Complex.normSq (h p))⁻¹ *
          ∑ i : I, Complex.normSq (eulerSequence K g k.val i) := by
        rw [massScale_normSq h hn]
        simp only [hval k, Complex.normSq_eq_norm_sq]
    _ = (∑ i : I, Complex.normSq (eulerSequence K g k.val i)) / (∑ p, Complex.normSq (h p)) := by
        rw [div_eq_inv_mul, mul_comm]

end Qatlib.Papers.NonlinearDE20.MainResults.ClockMass
