/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity

/-!
# Euclidean bounds for spin readouts

Represents finite histories and spin readouts as Euclidean vectors and proves their squared and
unsquared sensitivity bounds. These estimates transfer the coordinate regularity of the AMP spin
readout to the vector setting used in [GohMuller2026].

## Main statements

* `spinReadout_l2`: bounds the spin-vector distance by `2 * √T` times the history distance.
* `actual_amp_spin_readout_l2`: specializes the estimate to actual AMP histories.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical BigOperators
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.SpinReadoutL2

/-- The Euclidean vector obtained by flattening a finite history over its time and site indices. -/
def historyVector {T N : ℕ} (h : Fin (T+1)→Fin N→ℝ) : EuclideanSpace ℝ (Fin (T+1)×Fin N) :=
  WithLp.toLp 2 (fun p => h p.1 p.2)

/-- The spin readout of a finite history, regarded as a Euclidean vector. -/
def spinVector {T N : ℕ} (s : ℕ→ℝ) (h : Fin (T+1)→Fin N→ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (spinReadout s T h)

/-- For schedules in `[0, 1]`, the squared spin-vector distance is at most `4 * T` times the
squared history-vector distance. -/
theorem spinReadout_l2_sq {T N : ℕ} (s : ℕ→ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (h h' : Fin (T+1)→Fin N→ℝ) :
    ‖spinVector s h-spinVector s h'‖^2≤4*(T:ℝ)*‖historyVector h-historyVector h'‖^2 := by
  have hcoord (i : Fin N) : (spinReadout s T h i-spinReadout s T h' i)^2≤
      4*(T:ℝ)*(∑ a,(h a i-h' a i)^2) := by
    have hb := fCoord_lipschitz_l2 s T T le_rfl hs (fun a => h a i) (fun a => h' a i)
    have hnon : 0≤∑ a,(h a i-h' a i)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
    calc
      _ = |spinReadout s T h i-spinReadout s T h' i|^2 := (sq_abs _).symm
      _ ≤ (2*Real.sqrt (T:ℝ)*Real.sqrt (∑ a,(h a i-h' a i)^2))^2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg T),Real.sq_sqrt hnon]; ring
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(spinReadout s T h i-spinReadout s T h' i)^2)≤
    4*(T:ℝ)*(∑ p : Fin (T+1)×Fin N,(h p.1 p.2-h' p.1 p.2)^2)
  calc
    _ ≤ ∑ i,4*(T:ℝ)*(∑ a,(h a i-h' a i)^2) := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by rw [← Finset.mul_sum,Fintype.sum_prod_type,Finset.sum_comm]

/-- For schedules in `[0, 1]`, the spin-vector distance is at most `2 * √T` times the
history-vector distance. -/
theorem spinReadout_l2 {T N : ℕ} (s : ℕ→ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (h h' : Fin (T+1)→Fin N→ℝ) :
    ‖spinVector s h-spinVector s h'‖≤2*Real.sqrt (T:ℝ)*‖historyVector h-historyVector h'‖ := by
  have hsq := spinReadout_l2_sq s hs h h'
  have hc : (2*Real.sqrt (T:ℝ)*‖historyVector h-historyVector h'‖)^2=
      4*(T:ℝ)*‖historyVector h-historyVector h'‖^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg T)]
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hsq.trans_eq hc.symm)

/-- For schedules in `[0, 1]` through `T`, the distance between two actual AMP spin outputs is
at most `2 * √T` times the distance between their history vectors [GohMuller2026]. -/
theorem actual_amp_spin_readout_l2 {r N : ℕ} (M : ℝ) (s : ℕ→ℝ) (T : ℕ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (J J' : Fin N→(Fin r→Fin N)→ℝ) (seed seed' : Fin N→ℝ) :
    ‖(WithLp.toLp 2 (spinOutput M J seed s T) : EuclideanSpace ℝ (Fin N))-
      WithLp.toLp 2 (spinOutput M J' seed' s T)‖≤
      2*Real.sqrt (T:ℝ)*‖historyVector (ampHistory M J seed s T)-historyVector (ampHistory M J' seed' s T)‖ :=
  spinReadout_l2 s hs _ _

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.SpinReadoutL2
