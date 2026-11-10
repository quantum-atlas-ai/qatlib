/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation

namespace Qatlib.Foundations.MatrixGeometry.AxisRotations.History

def historyProduct (s : ℕ → ℝ) : (t : ℕ) → (Fin t → ℝ) → Mat3
  | 0, _ => 1
  | t+1, x => rotationStep (s (t+1)) (x (Fin.last t)) *
      historyProduct s t (fun j => x j.castSucc)

def phi (s : ℕ → ℝ) (t : ℕ) (x : Fin t → ℝ) : ℝ := historyProduct s t x 2 0

theorem history_unitary (s : ℕ → ℝ) (t : ℕ) (x : Fin t → ℝ) :
    historyProduct s t x ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  induction t with
  | zero => exact one_mem _
  | succ t ih => exact mul_mem (step_unitary _ _) (ih _)

theorem history_norm (s : ℕ → ℝ) (t : ℕ) (x : Fin t → ℝ) : ‖historyProduct s t x‖=1 :=
  CStarRing.norm_of_mem_unitary (history_unitary s t x)

theorem zero_step_column (s : ℝ) : (fun i : Fin 3 => rotationStep s 0 i 0)=![1,0,0] := by
  ext i
  fin_cases i <;> simp [rotationStep, driverAngle, problemAngle, Matrix.mul_apply, Fin.sum_univ_three]

theorem zero_history_column (s : ℕ → ℝ) (t : ℕ) :
    (fun i : Fin 3 => historyProduct s t (fun _ => 0) i 0)=![1,0,0] := by
  induction t with
  | zero => ext i; fin_cases i <;> norm_num [historyProduct, Matrix.one_apply]
  | succ t ih =>
    ext i
    change (rotationStep (s (t+1)) 0 * historyProduct s t (fun _ => 0)) i 0=_
    simp only [Matrix.mul_apply]
    have hc (j : Fin 3) : historyProduct s t (fun _ => 0) j 0=(![1,0,0] : Fin 3 → ℝ) j :=
      congrFun ih j
    simp_rw [hc]
    simpa [Fin.sum_univ_three] using congrFun (zero_step_column (s (t+1))) i

theorem phi_zero (s : ℕ → ℝ) (t : ℕ) : phi s t (fun _ => 0)=0 := by
  exact congrFun (zero_history_column s t) 2

theorem history_difference (s : ℕ → ℝ) (t : ℕ) (x y : Fin t → ℝ) :
    ‖historyProduct s t x-historyProduct s t y‖ ≤
      ∑ j : Fin t, 2 * |s (j+1)| * |x j-y j| := by
  induction t with
  | zero => simp [historyProduct]
  | succ t ih =>
    let A := rotationStep (s (t+1)) (x (Fin.last t))
    let B := rotationStep (s (t+1)) (y (Fin.last t))
    let P := historyProduct s t (fun j => x j.castSucc)
    let Q := historyProduct s t (fun j => y j.castSucc)
    have he : A*P-B*Q=A*(P-Q)+(A-B)*Q := by noncomm_ring
    change ‖A*P-B*Q‖≤_
    rw [he]
    calc
      _ ≤ ‖A*(P-Q)‖+‖(A-B)*Q‖ := norm_add_le _ _
      _ ≤ ‖A‖*‖P-Q‖+‖A-B‖*‖Q‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = ‖P-Q‖+‖A-B‖ := by rw [show ‖A‖=1 from step_norm _ _, show ‖Q‖=1 from history_norm _ _ _]; ring
      _ ≤ (∑ j : Fin t, 2 * |s (j+1)| * |x j.castSucc-y j.castSucc|) +
          2 * |s (t+1)| * |x (Fin.last t)-y (Fin.last t)| :=
        add_le_add (ih _ _) (step_difference_le _ _ _)
      _ = _ := by rw [Fin.sum_univ_castSucc]; rfl

theorem matrix_entry_le_opNorm (A : Mat3) (i j : Fin 3) : |A i j|≤‖A‖ := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single j 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  have h1 := Matrix.l2_opNorm_mulVec A e
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin 3) ℝ).symm (A *ᵥ e)) i
  have hv : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (A *ᵥ e)).ofLp i=A i j := by
    simp [e]
  rw [he, mul_one] at h1
  simpa only [hv, Real.norm_eq_abs] using h2.trans h1

theorem phi_difference_sum (s : ℕ → ℝ) (t : ℕ) (x y : Fin t → ℝ) :
    |phi s t x-phi s t y|≤∑ j : Fin t, 2 * |s (j+1)| * |x j-y j| := by
  exact (matrix_entry_le_opNorm (historyProduct s t x-historyProduct s t y) 2 0).trans
    (history_difference s t x y)

theorem phi_difference_l2 (s : ℕ → ℝ) (t : ℕ) (x y : Fin t → ℝ) :
    |phi s t x-phi s t y|≤2*Real.sqrt (∑ j : Fin t, s (j+1)^2)*
      Real.sqrt (∑ j : Fin t, (x j-y j)^2) := by
  apply (phi_difference_sum s t x y).trans
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
    (fun j : Fin t => |s (j+1)|) (fun j : Fin t => |x j-y j|)
  simp only [sq_abs] at hs
  have hn : 0≤∑ j : Fin t, |s (j+1)| * |x j-y j| := Finset.sum_nonneg (fun _ _ => by positivity)
  have hroot : ∑ j : Fin t, |s (j+1)| * |x j-y j|≤
      Real.sqrt (∑ j : Fin t, s (j+1)^2)*Real.sqrt (∑ j : Fin t, (x j-y j)^2) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq hn]
    exact Real.sqrt_le_sqrt hs
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  nlinarith

theorem continuous_step (s : ℝ) : Continuous (rotationStep s) := by
  apply Continuous.mul continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [problemAngle] <;> fun_prop

theorem continuous_history (s : ℕ → ℝ) (t : ℕ) : Continuous (historyProduct s t) := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    exact ((continuous_step _).comp (continuous_apply _)).mul
      (ih.comp (continuous_pi (fun j => continuous_apply j.castSucc)))

theorem continuous_phi (s : ℕ → ℝ) (t : ℕ) : Continuous (phi s t) := by
  exact ((continuous_apply 0).comp (continuous_apply 2)).comp (continuous_history s t)

end Qatlib.Foundations.MatrixGeometry.AxisRotations.History
