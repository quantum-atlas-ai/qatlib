/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LaurentPolys.FiniteBitCost.FiniteQSPAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Gate identities and continuity for the QSP bridge

Hadamard conjugation relates the bridge factors and diagonal matrices to the phase and signal
gates. The module proves exact trigonometric formulas, unitarity of these gates and the
recursive QSP operator, and Lipschitz bounds for phase perturbations. These identities connect
polynomial constructions with the quantum signal processing framework [LowChuang2017].

## Main statements

* `rhw_qsp_bridge_had_elem`: a normalized coefficient factor becomes a phase gate.
* `rhw_qsp_bridge_phase_diff`: the phase-gate norm perturbation bound.
* `rhw_qsp_bridge_qsp_unitary`: unitarity for signal values in `[0, 1]`.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.FiniteBitCost
open Polynomial Matrix
open scoped Matrix.Norms.L2Operator

/-- Expands Hadamard conjugation of an arbitrary bridge matrix into its four transformed
entries. -/
theorem rhw_qsp_bridge_had_mat (a b c d : ℂ) : Hadamard*rhwQSPBridgeMatrix a b c d*Hadamard=
    rhwQSPBridgeMatrix ((a+b+c+d)/2) ((a-b+c-d)/2) ((a+b-c-d)/2) ((a-b-c+d)/2) := by
  ext i j
  cases i <;> cases j <;> simp [Hadamard,rhwQSPBridgeMatrix,Matrix.mul_apply]
  all_goals ring_nf
  all_goals norm_num [sqrt2_sq]
  all_goals ring

/-- Hadamard conjugation preserves products of two-by-two matrices. -/
theorem rhw_qsp_bridge_had_mul (A B : Matrix Bool Bool ℂ) :
    Hadamard*(A*B)*Hadamard=(Hadamard*A*Hadamard)*(Hadamard*B*Hadamard) := by
  simp only [mul_assoc]
  rw [← mul_assoc Hadamard Hadamard,hadamard_mul_self,one_mul]

/-- The inverse of `exp (i*θ)` equals `cos θ - i*sin θ` for real `θ`. -/
theorem rhw_qsp_bridge_exp_inv (θ : ℝ) : (Complex.exp ((θ:ℂ)*Complex.I))⁻¹=
    (Real.cos θ:ℂ)-(Real.sin θ:ℂ)*Complex.I := by
  rw [← Complex.exp_neg,← neg_mul,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  ring

/-- Expresses the bridge phase gate using the trigonometric entries `cos θ ± i*sin θ`. -/
theorem rhw_qsp_bridge_phase_exp (θ : ℝ) : rhwQSPBridgePhase θ=
    rhwQSPBridgeMatrix ((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I) 0 0
      ((Real.cos θ:ℂ)-(Real.sin θ:ℂ)*Complex.I) := by
  unfold rhwQSPBridgePhase
  rw [Complex.exp_ofReal_mul_I,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  congr 1
  ring

/-- For `θ` in `[0, π/2]`, Hadamard conjugation of the bridge diagonal at `exp (i*θ)` equals the
signal gate at `cos θ`. -/
theorem rhw_qsp_bridge_had_signal (θ : ℝ) (hθ : θ∈Set.Icc (0:ℝ) (Real.pi/2)) :
    Hadamard*rhwQSPBridgeDiagonal (Complex.exp ((θ:ℂ)*Complex.I))*Hadamard=rhwQSPBridgeSignal (Real.cos θ) := by
  have hs : 0≤Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hroot : Real.sqrt (1-Real.cos θ^2)=Real.sin θ := by
    rw [← Real.sin_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg hs]
  rw [rhwQSPBridgeDiagonal,rhw_qsp_bridge_had_mat,rhw_qsp_bridge_exp_inv,Complex.exp_ofReal_mul_I]
  simp only [rhwQSPBridgeSignal,hroot]
  congr 1 <;> ring

/-- For `φ` in `(-π/2, π/2)`, the bridge factor of `i * tan φ` has diagonal entries `cos φ` and
off-diagonal entries `i*sin φ`. -/
theorem rhw_qsp_bridge_elem_angle (φ : ℝ) (hφ : φ∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) :
    rhwQSPBridgeFactor (rhwQSPBridgeCoefficient φ)=rhwQSPBridgeMatrix (Real.cos φ:ℂ) (Complex.I*(Real.sin φ:ℂ))
      (Complex.I*(Real.sin φ:ℂ)) (Real.cos φ:ℂ) := by
  have hc := Real.cos_pos_of_mem_Ioo hφ
  have hn : Complex.normSq (rhwQSPBridgeCoefficient φ)=Real.tan φ^2 := by
    simp only [rhwQSPBridgeCoefficient,Complex.normSq_mul,Complex.normSq_I,one_mul,Complex.normSq_ofReal,pow_two]
  have hs : (Real.cos φ:ℂ)*(Real.tan φ:ℂ)=(Real.sin φ:ℂ) := by
    exact_mod_cast (mul_comm (Real.cos φ) (Real.tan φ)).trans (Real.tan_mul_cos hc.ne')
  simp only [rhwQSPBridgeFactor,hn,Real.inv_sqrt_one_add_tan_sq hc]
  simp only [rhwQSPBridgeCoefficient,star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  congr 1
  · calc
      _ = Complex.I*((Real.cos φ:ℂ)*(Real.tan φ:ℂ)) := by ring
      _ = _ := by rw [hs]
  · calc
      _ = Complex.I*((Real.cos φ:ℂ)*(Real.tan φ:ℂ)) := by ring
      _ = _ := by rw [hs]

/-- For `φ` in `(-π/2, π/2)`, Hadamard conjugation sends the bridge factor of its phase
coefficient to the phase gate at `φ`. -/
theorem rhw_qsp_bridge_had_elem (φ : ℝ) (hφ : φ∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) :
    Hadamard*rhwQSPBridgeFactor (rhwQSPBridgeCoefficient φ)*Hadamard=rhwQSPBridgePhase φ := by
  rw [rhw_qsp_bridge_elem_angle φ hφ,rhw_qsp_bridge_had_mat,rhw_qsp_bridge_phase_exp]
  congr 1 <;> ring

/-- The distance between the unit complex phases at real angles `a` and `b` is at most `|a -
b|`. -/
theorem rhw_qsp_bridge_phase_chord (a b : ℝ) :
    ‖Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((b:ℂ)*Complex.I)‖≤|a-b| := by
  have he : Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((b:ℂ)*Complex.I)=
      Complex.exp ((b:ℂ)*Complex.I)*(Complex.exp (Complex.I*((a-b:ℝ):ℂ))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The diagonal matrix with entries `exp (i*a)` and `exp (-i*a)` is unitary. -/
theorem rhw_qsp_bridge_diagonal_phase_unitary (a : ℝ) :
    (Matrix.diagonal (fun i : Bool => if i then Complex.exp (-(a:ℂ)*Complex.I)
      else Complex.exp ((a:ℂ)*Complex.I)))∈Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal,← Matrix.diagonal_one]
  congr 1
  funext i
  cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true,Pi.star_apply]
  all_goals rw [Complex.star_def,← Complex.exp_conj]
  all_goals simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_neg]
  all_goals rw [← Complex.exp_add]
  all_goals convert Complex.exp_zero using 1
  all_goals ring

/-- The operator-norm difference between the diagonal phase matrices at `a` and `b` is at most
`|a - b|`. -/
theorem rhw_qsp_bridge_diagonal_phase_norm_diff (a b : ℝ) :
    ‖(Matrix.diagonal (fun i : Bool => if i then Complex.exp (-(a:ℂ)*Complex.I)
      else Complex.exp ((a:ℂ)*Complex.I)))-
      (Matrix.diagonal (fun i : Bool => if i then Complex.exp (-(b:ℂ)*Complex.I)
      else Complex.exp ((b:ℂ)*Complex.I)))‖≤|a-b| := by
  rw [Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
  intro i
  cases i
  · exact rhw_qsp_bridge_phase_chord a b
  · simpa only [Complex.ofReal_neg,neg_sub_neg,abs_sub_comm] using!
      rhw_qsp_bridge_phase_chord (-a) (-b)

/-- Identifies the bridge phase gate with the corresponding diagonal matrix of opposite complex
phases. -/
theorem rhw_qsp_bridge_phase_diagonal (a : ℝ) : rhwQSPBridgePhase a=Matrix.diagonal (fun i : Bool =>
    if i then Complex.exp (-(a:ℂ)*Complex.I) else Complex.exp ((a:ℂ)*Complex.I)) := by
  ext i j
  cases i <;> cases j <;> simp [rhwQSPBridgePhase,rhwQSPBridgeMatrix]

/-- Every bridge phase gate at a real angle is unitary. -/
theorem rhw_qsp_bridge_phase_unitary (a : ℝ) : rhwQSPBridgePhase a∈Matrix.unitaryGroup Bool ℂ := by
  rw [rhw_qsp_bridge_phase_diagonal]
  exact rhw_qsp_bridge_diagonal_phase_unitary a

/-- The operator-norm difference between bridge phase gates is bounded by the absolute
difference of their angles. -/
theorem rhw_qsp_bridge_phase_diff (a b : ℝ) : ‖rhwQSPBridgePhase a-rhwQSPBridgePhase b‖≤|a-b| := by
  rw [rhw_qsp_bridge_phase_diagonal,rhw_qsp_bridge_phase_diagonal]
  exact rhw_qsp_bridge_diagonal_phase_norm_diff a b

/-- The bridge diagonal at `exp (i*θ)` equals the bridge phase gate at `θ`. -/
theorem rhw_qsp_bridge_diag_phase (θ : ℝ) : rhwQSPBridgeDiagonal (Complex.exp ((θ:ℂ)*Complex.I))=rhwQSPBridgePhase θ := by
  simp only [rhwQSPBridgeDiagonal,rhwQSPBridgePhase]
  rw [← Complex.exp_neg]
  congr 2
  ring

/-- The bridge signal gate is unitary for `0 ≤ x ≤ 1`. -/
theorem rhw_qsp_bridge_signal_unitary (x : ℝ) (hx : 0≤x) (hx1 : x≤1) : rhwQSPBridgeSignal x∈Matrix.unitaryGroup Bool ℂ := by
  let θ := Real.arccos x
  have hθ : θ∈Set.Icc (0:ℝ) (Real.pi/2) :=
    ⟨Real.arccos_nonneg x,Real.arccos_le_pi_div_two.mpr hx⟩
  have he := rhw_qsp_bridge_had_signal θ hθ
  rw [Real.cos_arccos (by linarith) hx1,rhw_qsp_bridge_diag_phase] at he
  rw [← he]
  exact (Matrix.unitaryGroup Bool ℂ).mul_mem
    ((Matrix.unitaryGroup Bool ℂ).mul_mem hadamard_unitary (rhw_qsp_bridge_phase_unitary θ)) hadamard_unitary

/-- For signal value `x` in `[0, 1]`, every operator in the symmetric bridge QSP recursion is
unitary. -/
theorem rhw_qsp_bridge_qsp_unitary (ψ : ℕ → ℝ) (x : ℝ) (d : ℕ) (hx : 0≤x) (hx1 : x≤1) :
    rhwQSPBridgeOperator ψ x d∈Matrix.unitaryGroup Bool ℂ := by
  have hs := rhw_qsp_bridge_signal_unitary x hx hx1
  induction d with
  | zero => exact rhw_qsp_bridge_phase_unitary _
  | succ d ih =>
    exact (Matrix.unitaryGroup Bool ℂ).mul_mem
      ((Matrix.unitaryGroup Bool ℂ).mul_mem
        ((Matrix.unitaryGroup Bool ℂ).mul_mem
          ((Matrix.unitaryGroup Bool ℂ).mul_mem (rhw_qsp_bridge_phase_unitary _) hs) ih) hs) (rhw_qsp_bridge_phase_unitary _)

end Qatlib.Concepts.LaurentPolys.FiniteBitCost
