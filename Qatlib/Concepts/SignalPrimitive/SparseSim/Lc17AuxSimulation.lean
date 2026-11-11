/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.SparseSim.Lc17AuxWalkBranch
import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Walk Branch Extraction and Error Bounds

This module connects scalar QSP amplitudes to compressed sparse-walk simulation, in the setting
of [LowChuang2017]. `lcPositiveEigenAngle` chooses a representative in `[0, 2 * π]`, and the
angle lemmas relate both walk eigenphases to the same sine value, including the saturated
endpoints.

`lcSimWord_frame_action` expresses the compressed circuit on a balanced pair of walk
eigenvectors through `lcPlusAmp`. Frame contraction and orthogonal-pair norm identities transfer
scalar response errors to a state error; `lcOutput_guarantee` turns this into squared error at
most `ε ^ 2` and output mass at least `1 - 2 * ε` when `ε ≤ 1 / 2`.

## Main statements

- `lcEigenAngles_sin` and `lcEigenAngles_saturated` identify the walk-angle branches.
- `lcSimWord_frame_action` computes the compressed action on the balanced eigenvector pair.
* `lcBalanced_error_bound` and `lcOutput_guarantee` establish the state and output-mass
  estimates.

## References

- [Low and Chuang, 2017][LowChuang2017].
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.SignalPrimitive.SparseSim

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Matrix.Norms.L2Operator

/-- The representative of `arcsin s` obtained by adding `2 * π` when it is negative, placing the
angle in `[0, 2 * π]`. -/
noncomputable def lcPositiveEigenAngle (s : ℝ) : ℝ :=
  if 0 ≤ Real.arcsin s then Real.arcsin s else Real.arcsin s + 2 * Real.pi

/-- The chosen positive eigenangle lies in the closed interval `[0, 2 * π]` for every real `s`. -/
theorem lcPositiveEigenAngle_mem (s : ℝ) :
    lcPositiveEigenAngle s ∈ Set.Icc 0 (2 * Real.pi) := by
  have h1 := Real.neg_pi_div_two_le_arcsin s
  have h2 := Real.arcsin_le_pi_div_two s
  unfold lcPositiveEigenAngle
  split_ifs with h
  · exact ⟨h, by linarith [Real.pi_pos]⟩
  · exact ⟨by linarith [Real.pi_pos], by linarith⟩

/-- The complex phase of `lcPositiveEigenAngle s` equals the phase of `arcsin s`. -/
theorem lcPositiveEigenAngle_phase (s : ℝ) :
    Complex.exp (Complex.I * (lcPositiveEigenAngle s : ℂ)) =
      Complex.exp (Complex.I * (Real.arcsin s : ℂ)) := by
  unfold lcPositiveEigenAngle
  split_ifs
  · rfl
  · rw [Complex.ofReal_add, mul_add, Complex.exp_add,
      show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I, mul_one]

/-- The phase of `π - arcsin s` is the negative of the phase of `-arcsin s`. -/
theorem lcNegativeEigenAngle_phase (s : ℝ) :
    Complex.exp (Complex.I * ((Real.pi - Real.arcsin s : ℝ) : ℂ)) =
      -Complex.exp (Complex.I * (-(Real.arcsin s : ℂ))) := by
  rw [Complex.ofReal_sub, mul_sub, sub_eq_add_neg, Complex.exp_add,
    show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_pi_mul_I, neg_one_mul, ← mul_neg]

/-- When `|s| ≤ 1`, both `lcPositiveEigenAngle s` and `π - arcsin s` have sine equal to `s`. -/
theorem lcEigenAngles_sin (s : ℝ) (hs : |s| ≤ 1) :
    Real.sin (lcPositiveEigenAngle s) = s ∧ Real.sin (Real.pi - Real.arcsin s) = s := by
  have h := Real.sin_arcsin (abs_le.mp hs).1 (abs_le.mp hs).2
  constructor
  · unfold lcPositiveEigenAngle
    split_ifs
    · exact h
    · rw [Real.sin_add_two_pi]; exact h
  · rw [Real.sin_pi_sub]; exact h

/-- At `|s| = 1`, the two chosen walk eigenangles coincide. -/
theorem lcEigenAngles_saturated (s : ℝ) (hs : |s| = 1) :
    lcPositiveEigenAngle s = Real.pi - Real.arcsin s := by
  rcases abs_eq (show (0 : ℝ) ≤ 1 by norm_num) |>.mp hs with h | h
  · rw [h, lcPositiveEigenAngle, Real.arcsin_one]
    rw [if_pos (by positivity : 0 ≤ Real.pi / 2)]
    ring
  · rw [h, lcPositiveEigenAngle, Real.arcsin_neg_one]
    rw [if_neg (by linarith [Real.pi_pos] : ¬0 ≤ -(Real.pi / 2))]
    ring

section Helpers
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The cross matrix `Lᴴ * R` of two isometries has operator norm at most one. -/
theorem lcFrame_cross_norm (L R : Matrix W I ℂ) (hL : IsIsometry L) (hR : IsIsometry R) :
    ‖Lᴴ * R‖ ≤ 1 := by
  calc
    _ ≤ ‖Lᴴ‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖L‖ * ‖R‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ 1 * 1 := mul_le_mul (isometry_norm_le hL) (isometry_norm_le hR)
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

/-- If `c • H` is a contraction and `ψ` is a normalized eigenvector of `H` with real eigenvalue
`ev`, then `|c * ev| ≤ 1`. -/
theorem lcFrame_eigen_bound (H : Matrix I I ℂ) (c : ℝ) (ψ : I → ℂ) (ev : ℝ)
    (hH : ‖(c : ℂ) • H‖ ≤ 1) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1)
    (hev : H *ᵥ ψ = (ev : ℂ) • ψ) : |c * ev| ≤ 1 := by
  have hn : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hh := l2_norm_mulVec_fromVec_le ((c : ℂ) • H) ψ
  rw [Matrix.smul_mulVec, hev, smul_smul,
    show (c : ℂ) * (ev : ℂ) = ((c * ev : ℝ) : ℂ) by push_cast; rfl] at hh
  have hval : ‖toEuclidean_fromVec (((c * ev : ℝ) : ℂ) • ψ)‖ = |c * ev| := by
    change ‖((c * ev : ℝ) : ℂ) • toEuclidean_fromVec ψ‖ = _
    rw [norm_smul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hval, hn, mul_one] at hh
  exact hh.trans hH

/-- The adjoint of an isometry does not increase the Euclidean norm of a workspace vector. -/
theorem lcFrame_adjoint_contraction (L : Matrix W I ℂ) (hL : IsIsometry L) (z : W → ℂ) :
    ‖toEuclidean_fromVec (Lᴴ *ᵥ z)‖ ≤ ‖toEuclidean_fromVec z‖ := by
  have hh := l2_norm_mulVec_fromVec_le Lᴴ z
  rw [Matrix.l2_opNorm_conjTranspose] at hh
  exact hh.trans (by simpa only [one_mul] using!
    mul_le_mul_of_nonneg_right (isometry_norm_le hL) (norm_nonneg (toEuclidean_fromVec z)))

/-- Applying `(lcPlusFrame L)ᴴ` to a product branch gives `Lᴴ *ᵥ w` scaled by `(a 0 + a 1) /
sqrt 2`. -/
theorem lcPlusFrame_adjoint_branch (L : Matrix W I ℂ) (a : Fin 2 → ℂ) (w : W → ℂ) :
    (lcPlusFrame L)ᴴ *ᵥ lcBranchVector a w =
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a 0 + a 1)) • (Lᴴ *ᵥ w) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, lcPlusFrame, Matrix.conjTranspose_apply,
    Matrix.of_apply, Complex.real_smul, lcBranchVector, Fintype.sum_prod_type,
    Fin.sum_univ_two, star_mul, Complex.star_def, Complex.conj_ofReal, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The overlap of a two-dimensional matrix between uniform ancilla vectors equals the `(0, 0)`
entry of `lcHad * M * lcHad`. -/
theorem lcPlusCorner_qubit (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      ((M *ᵥ (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ))) 0 +
       (M *ᵥ (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ))) 1)) =
      (lcHad * M * lcHad) 0 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two,
    lcHad, Matrix.smul_apply, Complex.real_smul]
  norm_num
  ring

/-- On a walk eigenvector of eigenphase `θ`, extraction of an even-length simulation word from
the uniform ancilla branch gives `lcPlusAmp phis θ • (Lᴴ *ᵥ w)`. -/
theorem lcSimWord_extracted_branch (L : Matrix W I ℂ) (V : Matrix W W ℂ)
    (w : W → ℂ) (θ : ℝ) (hV : V ∈ Matrix.unitaryGroup W ℂ)
    (hw : V *ᵥ w = Complex.exp (Complex.I * (θ : ℂ)) • w)
    (phis : List ℝ) (hlen : Even phis.length) :
    (lcPlusFrame L)ᴴ *ᵥ (lcSimWord V phis *ᵥ
      lcBranchVector (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) w) =
      lcPlusAmp phis θ • (Lᴴ *ᵥ w) := by
  rw [lcSimWord_branch V w θ hV hw phis hlen, lcPlusFrame_adjoint_branch,
    lcPlusCorner_qubit]
  rfl

omit [Fintype W] [DecidableEq W] in

/-- For a fixed ancilla vector, the product-branch construction preserves addition of workspace
vectors. -/
theorem lcBranchVector_add (a : Fin 2 → ℂ) (u v : W → ℂ) :
    lcBranchVector a (u + v) = lcBranchVector a u + lcBranchVector a v := by
  funext i
  simp [lcBranchVector, mul_add]

omit [Fintype W] [DecidableEq W] in

/-- For a fixed ancilla vector, the product-branch construction commutes with complex scalar
multiplication of the workspace vector. -/
theorem lcBranchVector_smul (a : Fin 2 → ℂ) (u : W → ℂ) (z : ℂ) :
    lcBranchVector a (z • u) = z • lcBranchVector a u := by
  funext i
  simp only [lcBranchVector, Pi.smul_apply, smul_eq_mul]
  ring

/-- Computes the compressed even-length simulation word when `L *ᵥ ψ` is a balanced phased sum
of two walk eigenvectors. Each eigenbranch is multiplied by its scalar amplitude `lcPlusAmp
phis θ` before applying `Lᴴ`. -/
theorem lcSimWord_frame_action (L : Matrix W I ℂ) (V : Matrix W W ℂ)
    (ψ : I → ℂ) (wp wm : W → ℂ) (ap am θp θm : ℝ)
    (hV : V ∈ Matrix.unitaryGroup W ℂ)
    (hwp : V *ᵥ wp = Complex.exp (Complex.I * (θp : ℂ)) • wp)
    (hwm : V *ᵥ wm = Complex.exp (Complex.I * (θm : ℂ)) • wm)
    (hbal : L *ᵥ ψ = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (Complex.exp (Complex.I * (ap : ℂ)) • wp + Complex.exp (Complex.I * (am : ℂ)) • wm))
    (phis : List ℝ) (hlen : Even phis.length) :
    compress (lcPlusFrame L) (lcSimWord V phis) (lcPlusFrame L) *ᵥ ψ =
      Lᴴ *ᵥ (((1 / Real.sqrt 2 : ℝ) : ℂ) •
        ((Complex.exp (Complex.I * (ap : ℂ)) * lcPlusAmp phis θp) • wp +
         (Complex.exp (Complex.I * (am : ℂ)) * lcPlusAmp phis θm) • wm)) := by
  unfold compress
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, lcPlusFrame_branch, hbal,
    lcBranchVector_smul, lcBranchVector_add, lcBranchVector_smul, lcBranchVector_smul]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add]
  rw [lcSimWord_extracted_branch L V wp θp hV hwp phis hlen,
    lcSimWord_extracted_branch L V wm θm hV hwm phis hlen]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, smul_smul]

/-- For orthogonal normalized vectors `wp` and `wm`, the squared Euclidean norm of `a • wp + b •
wm` is `‖a‖ ^ 2 + ‖b‖ ^ 2`. -/
theorem lcOrthogonal_normSq (wp wm : W → ℂ) (a b : ℂ)
    (hp : ∑ i, ‖wp i‖ ^ 2 = 1) (hm : ∑ i, ‖wm i‖ ^ 2 = 1)
    (ho : star wp ⬝ᵥ wm = 0) :
    ‖toEuclidean_fromVec (a • wp + b • wm)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hpp : star wp ⬝ᵥ wp = 1 := by
    change Qatlib.Foundations.PureStateMath.Inner wp wp = 1
    rw [inner_self, ← Complex.ofReal_sum, hp, Complex.ofReal_one]
  have hmm : star wm ⬝ᵥ wm = 1 := by
    change Qatlib.Foundations.PureStateMath.Inner wm wm = 1
    rw [inner_self, ← Complex.ofReal_sum, hm, Complex.ofReal_one]
  have hom : star wm ⬝ᵥ wp = 0 := by
    have hh := congrArg star ho
    rw [star_dotProduct, star_star, star_zero] at hh
    simpa only [dotProduct_comm] using! hh
  rw [norm_toEuclidean_sq_eq_re_inner]
  unfold Qatlib.Foundations.PureStateMath.Inner
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hpp, hmm, ho, hom, smul_eq_mul, mul_zero, mul_one,
    zero_add, add_zero, Complex.add_re]
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- A balanced phased combination of two orthogonal normalized vectors has Euclidean norm at
most `ε` when both scalar error coefficients have norm at most the nonnegative `ε`. -/
theorem lcBalanced_error_bound (wp wm : W → ℂ) (ap am ε : ℝ) (a b : ℂ)
    (hp : ∑ i, ‖wp i‖ ^ 2 = 1) (hm : ∑ i, ‖wm i‖ ^ 2 = 1)
    (ho : star wp ⬝ᵥ wm = 0) (hε : 0 ≤ ε) (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) :
    ‖toEuclidean_fromVec (((1 / Real.sqrt 2 : ℝ) : ℂ) •
      ((Complex.exp (Complex.I * (ap : ℂ)) * a) • wp +
       (Complex.exp (Complex.I * (am : ℂ)) * b) • wm))‖ ≤ ε := by
  have hn : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow,
      Real.sq_sqrt (by norm_num)]
  have hphase : ∀ t : ℝ, ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hsq : ‖toEuclidean_fromVec (((1 / Real.sqrt 2 : ℝ) : ℂ) •
      ((Complex.exp (Complex.I * (ap : ℂ)) * a) • wp +
       (Complex.exp (Complex.I * (am : ℂ)) * b) • wm))‖ ^ 2 =
      (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
    change ‖((1 / Real.sqrt 2 : ℝ) : ℂ) • toEuclidean_fromVec
      ((Complex.exp (Complex.I * (ap : ℂ)) * a) • wp +
       (Complex.exp (Complex.I * (am : ℂ)) * b) • wm)‖ ^ 2 = _
    rw [norm_smul, mul_pow, hn, lcOrthogonal_normSq wp wm _ _ hp hm ho,
      norm_mul, norm_mul, hphase, hphase, one_mul, one_mul]
    ring
  have haa : ‖a‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg a]
  have hbb : ‖b‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg b]
  nlinarith [norm_nonneg (toEuclidean_fromVec (((1 / Real.sqrt 2 : ℝ) : ℂ) •
    ((Complex.exp (Complex.I * (ap : ℂ)) * a) • wp +
     (Complex.exp (Complex.I * (am : ℂ)) * b) • wm)))]

/-- If an output vector is within Euclidean distance `ε` of a unit-modulus multiple of a
normalized vector, with `0 ≤ ε ≤ 1 / 2`, then its squared coordinate error is at most `ε ^
2` and its total squared norm is at least `1 - 2 * ε`. -/
theorem lcOutput_guarantee (ψ y : I → ℂ) (e : ℂ) (ε : ℝ)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (he : ‖e‖ = 1) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (herr : ‖toEuclidean_fromVec (y - e • ψ)‖ ≤ ε) :
    (∑ i, ‖y i - e * ψ i‖ ^ 2) ≤ ε ^ 2 ∧ 1 - 2 * ε ≤ ∑ i, ‖y i‖ ^ 2 := by
  have hn : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hnE : ‖toEuclidean_fromVec (e • ψ)‖ = 1 := by
    change ‖e • toEuclidean_fromVec ψ‖ = 1
    rw [norm_smul, he, hn, one_mul]
  have hrev := norm_sub_norm_le (toEuclidean_fromVec (e • ψ)) (toEuclidean_fromVec y)
  rw [hnE, norm_sub_rev,
    show toEuclidean_fromVec y - toEuclidean_fromVec (e • ψ) =
      toEuclidean_fromVec (y - e • ψ) by rfl] at hrev
  have hlow : 1 - ε ≤ ‖toEuclidean_fromVec y‖ := by linarith
  refine ⟨?_, ?_⟩
  · have hh : ‖toEuclidean_fromVec (y - e • ψ)‖ ^ 2 ≤ ε ^ 2 := by
      nlinarith [norm_nonneg (toEuclidean_fromVec (y - e • ψ))]
    simpa only [norm_toEuclidean_fromVec_sq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using! hh
  · rw [← norm_toEuclidean_fromVec_sq]
    have hlow0 : 0 ≤ 1 - ε := by linarith
    nlinarith [norm_nonneg (toEuclidean_fromVec y), sq_nonneg ε]

end Helpers
end Qatlib.Concepts.SignalPrimitive.SparseSim
