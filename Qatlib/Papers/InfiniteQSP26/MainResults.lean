/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LaurentPolys.FiniteBitCost.FiniteQSPGates

/-!
# Perturbation bounds for finite QSP bridge operators

This module proves operator-norm stability estimates for the finite QSP bridge operators used in
the setting of [AlexisEtAl2026]. Phase errors bounded by `δ` through depth `d` produce an
operator error at most `(2 * d + 1) * δ`, and each matrix entry is bounded by the operator norm.

## Main statements

* `rhw_qsp_bridge_qsp_difference`: bounds the operator error from uniformly perturbed phases.
* `rhw_qsp_bridge_entry_bound`: bounds a matrix entry by the Euclidean operator norm.

## References

* [Alexis et al., 2026][AlexisEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.InfiniteQSP26.MainResults
open Polynomial Matrix
open Qatlib.Concepts.LaurentPolys.FiniteBitCost
open scoped Matrix.Norms.L2Operator

/-- For unitary `A` and `D`, the Euclidean operator norm of `A * B - C * D` is at most `‖B - D‖
+ ‖A - C‖`. -/
theorem rhw_qsp_bridge_mul_error (A B C D : Matrix Bool Bool ℂ)
    (hA : A∈Matrix.unitaryGroup Bool ℂ) (hD : D∈Matrix.unitaryGroup Bool ℂ) :
    ‖A*B-C*D‖≤‖B-D‖+‖A-C‖ := by
  have he : A*B-C*D=A*(B-D)+(A-C)*D := by noncomm_ring
  rw [he]
  have h := norm_add_le (A*(B-D)) ((A-C)*D)
  rw [CStarRing.norm_mem_unitary_mul _ hA,CStarRing.norm_mul_mem_unitary _ hD] at h
  exact h

/-- For `x ∈ [0, 1]` and `δ ≥ 0`, phase sequences differing by at most `δ` through index `d`
give depth-`d` QSP bridge operators differing by at most `(2 * d + 1) * δ` in Euclidean
operator norm. This is a finite perturbation estimate in the setting of [AlexisEtAl2026]. -/
theorem rhw_qsp_bridge_qsp_difference (ψ χ : ℕ → ℝ) (d : ℕ) (x δ : ℝ) (hx : 0≤x) (hx1 : x≤1)
    (_hδ : 0≤δ) (h : ∀ k≤d, |ψ k-χ k|≤δ) :
    ‖Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeOperator ψ x d-Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeOperator χ x d‖≤((2*d+1:ℕ):ℝ)*δ := by
  have hs := Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_signal_unitary x hx hx1
  induction d with
  | zero => simpa only [Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeOperator,Nat.mul_zero,Nat.zero_add,Nat.cast_one,one_mul] using
      (Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_phase_diff (ψ 0) (χ 0)).trans (h 0 le_rfl)
  | succ d ih =>
    let P := Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgePhase (ψ (d+1))
    let R := Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgePhase (χ (d+1))
    let W := Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeSignal x
    let A := Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeOperator ψ x d
    let B := Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeOperator χ x d
    have hprev := ih (fun k hk => h k (by omega))
    have hp : ‖P-R‖≤δ :=
        (Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_phase_diff _ _).trans
        (h (d+1) le_rfl)
    have hP : P∈Matrix.unitaryGroup Bool ℂ :=
        Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_phase_unitary _
    have hR : R∈Matrix.unitaryGroup Bool ℂ :=
        Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_phase_unitary _
    have hA : A∈Matrix.unitaryGroup Bool ℂ :=
        Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_qsp_unitary ψ x d hx hx1
    have hB : B∈Matrix.unitaryGroup Bool ℂ :=
        Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhw_qsp_bridge_qsp_unitary χ x d hx hx1
    have hW : W∈Matrix.unitaryGroup Bool ℂ := hs
    have hwaw : W*A*W∈Matrix.unitaryGroup Bool ℂ :=
      (Matrix.unitaryGroup Bool ℂ).mul_mem ((Matrix.unitaryGroup Bool ℂ).mul_mem hW hA) hW
    have hwbw : W*B*W∈Matrix.unitaryGroup Bool ℂ :=
      (Matrix.unitaryGroup Bool ℂ).mul_mem ((Matrix.unitaryGroup Bool ℂ).mul_mem hW hB) hW
    have hm : ‖W*A*W-W*B*W‖=‖A-B‖ := by
      rw [← sub_mul,← mul_sub,CStarRing.norm_mul_mem_unitary _ hW,CStarRing.norm_mem_unitary_mul _ hW]
    have h1 :=
        Qatlib.Papers.InfiniteQSP26.MainResults.rhw_qsp_bridge_mul_error P (W*A*W) R (W*B*W) hP hwbw
    have h2 := Qatlib.Papers.InfiniteQSP26.MainResults.rhw_qsp_bridge_mul_error (P*(W*A*W)) P (R*(W*B*W)) R
      ((Matrix.unitaryGroup Bool ℂ).mul_mem hP hwaw) hR
    rw [hm] at h1
    change ‖P*W*A*W*P-R*W*B*W*R‖≤_
    simp only [mul_assoc] at h1 h2 ⊢
    change ‖A-B‖≤((2*d+1:ℕ):ℝ)*δ at hprev
    push_cast at hprev ⊢
    linarith only [h1,h2,hp,hprev]

/-- The norm of each entry of a complex two-by-two matrix is at most its Euclidean operator
norm. -/
theorem rhw_qsp_bridge_entry_bound (M : Matrix Bool Bool ℂ) (i j : Bool) : ‖M i j‖≤‖M‖ := by
  let e : EuclideanSpace ℂ Bool := PiLp.single 2 j (1:ℂ)
  have hn : ‖e‖=1 := by simp [e,PiLp.norm_single]
  have he : e.ofLp=Pi.single j (1:ℂ) := rfl
  have h := Matrix.l2_opNorm_mulVec M e
  rw [hn,mul_one,he,Matrix.mulVec_single_one] at h
  have hc := PiLp.norm_apply_le ((EuclideanSpace.equiv Bool ℂ).symm (fun k => M k j)) i
  exact hc.trans h

end Qatlib.Papers.InfiniteQSP26.MainResults
