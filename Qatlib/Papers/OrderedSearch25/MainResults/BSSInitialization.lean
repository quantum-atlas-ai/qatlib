/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OrderedSearch25.MainResults.CyclicTrace
public import Qatlib.Papers.OrderedSearch25.MainResults.SourceProp22BlockDiagonal

@[expose] public section

/-!
# Initial cyclic traces and phase blocks in Proposition 21

The all-ones initial sum of the source matrix family and its cyclic
transport determine every cyclic trace of the member at label zero.
The phase matrix used in the same proposition has sign determined by
whether its two coordinates belong to the same half.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators
open Qatlib.Papers.OrderedSearch25.MainResults
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

namespace Qatlib.Papers.OrderedSearch25.MainResults

/-- The signs on the four coordinate blocks of the phase matrix are
those of Equation (90). -/
theorem bss_phase_blocks (n : ℕ) (i j : Fin n) :
    bssE0 n (halfL n i) (halfL n j) = 1 ∧
    bssE0 n (halfL n i) (halfR n j) = -1 ∧
    bssE0 n (halfR n i) (halfL n j) = -1 ∧
    bssE0 n (halfR n i) (halfR n j) = 1 := by
  simp [bssE0_eq_prod, halfL, halfR, i.isLt, j.isLt]

/-- Equations (91) and (95) of Proposition 21 give the unscaled cyclic
trace in Equation (103) using the source direction of label transport. -/
theorem cyc_trace_one_of_initial_sum {n : ℕ} [NeZero n]
    (M : Fin (2 * n) → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hsum : (∑ i, M i) = Matrix.of (fun _ _ => (1 : ℂ)))
    (hinv : ∀ i x y, M ((finShiftEquiv (2 * n)).symm i)
      (finShiftEquiv (2 * n) x) (finShiftEquiv (2 * n) y) = M i x y)
    (j : Fin (2 * n)) :
    cycTrace (M 0) j = 1 := by
  have orbit (a : ℕ) (x y : Fin (2 * n)) :
      M (cycShiftPow (2 * n) a 0) x y =
        M 0 (cycShiftPow (2 * n) a x) (cycShiftPow (2 * n) a y) := by
    induction a generalizing x y with
    | zero => simp [cycShiftPow]
    | succ a ih =>
      have ht := hinv (finShiftEquiv (2 * n) (cycShiftPow (2 * n) a 0)) x y
      rw [Equiv.symm_apply_apply] at ht
      calc
        _ = M (finShiftEquiv (2 * n) (cycShiftPow (2 * n) a 0)) x y := by
          simp [cycShiftPow, pow_succ', Equiv.Perm.mul_apply]
        _ = M (cycShiftPow (2 * n) a 0)
            (finShiftEquiv (2 * n) x) (finShiftEquiv (2 * n) y) := ht.symm
        _ = M 0 (cycShiftPow (2 * n) a (finShiftEquiv (2 * n) x))
            (cycShiftPow (2 * n) a (finShiftEquiv (2 * n) y)) := ih _ _
        _ = _ := by simp [cycShiftPow, pow_succ, Equiv.Perm.mul_apply]
  have hfam (i : Fin (2 * n)) :
      M i = (M 0).submatrix (cycShiftPow (2 * n) i.val) (cycShiftPow (2 * n) i.val) := by
    have hi : cycShiftPow (2 * n) i.val 0 = i := by
      apply Fin.ext
      rw [cycShiftPow_val]
      simpa using Nat.mod_eq_of_lt i.isLt
    ext x y
    simpa only [hi, Matrix.submatrix_apply] using orbit i.val x y
  have htoeplitz : toeplitzOf (M 0) = Matrix.of (fun _ _ => (1 : ℂ)) := by
    rw [← sum_transport_eq_toeplitz, ← hsum]
    exact Finset.sum_congr rfl (fun i _ => (hfam i).symm)
  rw [← toeplitzOf_apply_zero, htoeplitz, Matrix.of_apply]

end Qatlib.Papers.OrderedSearch25.MainResults
