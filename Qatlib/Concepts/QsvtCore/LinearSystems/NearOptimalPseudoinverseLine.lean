/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QsvtCore.LinearSystems.PseudoinverseState

/-!
# Phase words for near optimal inversion

This module realizes the scaled near optimal reciprocal polynomial by a source real phase word
with explicit compilation counts. Under a positive singular value gap, the adjoint word block
encodes the scaled pseudoinverse; a separate construction lifts the input encoding into the
source clean frames. The mathematical background is developed in [GilyenSuLowWiebe2019].

## Main statements

* `nearOptimalReciprocal_exact_word`: exact encoding of the scaled odd polynomial response.
* `nearOptimalReciprocal_inverse_word`: pseudoinverse approximation with error `2 * c * ε`.
* `nearOptimalReciprocal_clean_input_encoding`: an input encoding in the enlarged clean
  workspace.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.LinearSystems
open Polynomial Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- For the stated `κ` and `ε`, a phase word of length `2 * J + 1` exactly encodes the odd
response `c * g` and has compilation counts `(2 * J + 1, 2 * J, 2 * J + 2, 2 * J + 1)`. -/
theorem nearOptimalReciprocal_exact_word
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (henc : ProjectedUnitaryEncoding A U L R) :
    let J := nearOptimalReciprocalJ κ ε
    let c : ℝ := (4*(J : ℝ))⁻¹
    let g := nearOptimalReciprocalPolynomial κ ε
    ∃ Φ : List ℝ, Φ.length = 2*J+1 ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((c*g.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) = (2*J+1,2*J,2*J+2,2*J+1) := by
  (try dsimp only)
  let J := nearOptimalReciprocalJ κ ε
  let g := nearOptimalReciprocalPolynomial κ ε
  let c : ℝ := (4*(J : ℝ))⁻¹
  let p : Polynomial ℝ := C c*g
  let d : ℕ := 2*J+1
  obtain ⟨_, _, hgdeg, hgpar, _, _⟩ := nearOptimalReciprocal_family_degree_parity κ ε hκ hε hε1
  have hpdeg : p.degree ≤ (d : WithBot ℕ) := by
    apply degree_le_of_natDegree_le
    have hgn := natDegree_le_of_degree_le hgdeg
    apply (natDegree_mul_le (p := C c) (q := g)).trans
    simpa only [natDegree_C, zero_add] using! hgn
  have hpar : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d p := by
    change g.comp (-X) = C ((-1 : ℝ)^d)*g at hgpar
    unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    change (C c*g).comp (-X) = C ((-1 : ℝ)^d)*(C c*g)
    rw [mul_comp, C_comp, hgpar]
    ring
  have hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1 := by
    intro x hx
    simp only [p, eval_mul, eval_C]
    exact nearOptimalReciprocal_scale_bounded κ ε hκ hε hε1.le x hx
  obtain ⟨Φ, hlen, hodd, _, hcounts⟩ := source_length_cpp_real_singular_transform
    H I O A U L R p d henc (by dsimp [d]; omega) hpdeg hpar hbound
  refine ⟨Φ, hlen, ?_, ?_⟩
  · simpa only [p, eval_mul, eval_C] using! hodd (by dsimp [d]; omega)
  · dsimp only [d] at hcounts
    have he : (2*J+1)/2=J := by omega
    have ho : (2*J+1+1)/2=J+1 := by omega
    simpa only [he, ho, mul_add, mul_one] using! hcounts

/-- With positive singular values at least `κ⁻¹`, the exact reciprocal word also gives a scaled
pseudoinverse block encoding of error `2 * c * ε` via its adjoint; see
[GilyenSuLowWiebe2019]. -/
theorem nearOptimalReciprocal_inverse_word
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (κ ε : ℝ)
    (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε < 1/2)
    (henc : ProjectedUnitaryEncoding A U L R)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → κ⁻¹ ≤ matrixSingularValues A i) :
    let J := nearOptimalReciprocalJ κ ε
    let c : ℝ := (4*(J : ℝ))⁻¹
    let g := nearOptimalReciprocalPolynomial κ ε
    ∃ Φ : List ℝ, Φ.length = 2*J+1 ∧
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x : ℝ => ((c*g.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) = (2*J+1,2*J,2*J+2,2*J+1) ∧
      BlockEncoding ((c : ℂ) • matrixPseudoinverse A)
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)ᴴ
        (sourceAverageClean R) (sourceAverageClean L) 1 (2*c*ε) := by
  (try dsimp only)
  let J := nearOptimalReciprocalJ κ ε
  let c : ℝ := (4*(J : ℝ))⁻¹
  let g := nearOptimalReciprocalPolynomial κ ε
  have hJ := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1.le).2.1
  change 2 ≤ J at hJ
  have hJr : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hc : 0 < c := by dsimp [c]; positivity
  have herror : 0 ≤ 2*c*ε := by positivity
  have hA : ‖A‖ ≤ 1 := by
    rw [← henc.encoded]
    exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
      (unitary_norm_le_one henc.unitary)
  obtain ⟨Φ, hlen, hexact, hcounts⟩ := nearOptimalReciprocal_exact_word
    H I O A U L R κ ε hκ hε hε1 henc
  have herr : ‖(oddSingularTransform A (fun x : ℝ => ((c*g.eval x : ℝ) : ℂ)))ᴴ-
      (c : ℂ) • matrixPseudoinverse A‖ ≤ 2*c*ε := by
    rw [← inverseTransform_adjoint A c, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    apply oddSingularTransform_error_le_positive A _ _ herror
    intro i hi
    have hx : matrixSingularValues A i ∈ Set.Icc κ⁻¹ 1 :=
      ⟨hgap i hi, (matrixSingularValues_le_spectralNorm A i).trans hA⟩
    have he : ((c*g.eval (matrixSingularValues A i) : ℝ) : ℂ)-(c : ℂ)/(matrixSingularValues A i : ℂ) =
        ((c*(g.eval (matrixSingularValues A i)-(matrixSingularValues A i)⁻¹) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
    calc
      _ ≤ c*(2*ε) := mul_le_mul_of_nonneg_left
        ((nearOptimalReciprocal_error_bounds κ ε hκ hε hε1).2.2.2.1 _ hx) hc.le
      _ = _ := by ring
  have hb := (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding.adjoint hexact)).perturb herror
    (show ‖(c : ℂ) • matrixPseudoinverse A-
      (oddSingularTransform A (fun x : ℝ => ((c*g.eval x : ℝ) : ℂ)))ᴴ‖ ≤ 2*c*ε by
        rw [norm_sub_rev]
        exact herr)
  exact ⟨Φ, hlen, hexact, hcounts, by simpa only [zero_add] using! hb⟩

/-- For the stated parameters, the reciprocal scale `(4 * nearOptimalReciprocalJ κ ε)⁻¹` is
positive and at most `(4 * κ)⁻¹`. -/
theorem nearOptimalReciprocal_scale_parameters (κ ε : ℝ) (hκ : 1 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    0 < (4*(nearOptimalReciprocalJ κ ε : ℝ))⁻¹ ∧
    (4*(nearOptimalReciprocalJ κ ε : ℝ))⁻¹ ≤ (4*κ)⁻¹ := by
  let b := nearOptimalReciprocalB κ ε
  let J := nearOptimalReciprocalJ κ ε
  let L := Real.log (κ/ε)
  have hb := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1).1
  have hJ := (nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1).2.1
  change 1 ≤ b at hb
  change 2 ≤ J at hJ
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hJr : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hκ0 : 0 < κ := by linarith
  have hratio2 : 2 ≤ κ/ε := (le_div_iff₀ hε).mpr (by linarith)
  have hL : 1/2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio2
    linarith [Real.log_two_gt_d9]
  have hbLower : κ*κ*L ≤ (b : ℝ) := Nat.le_ceil _
  have hratio8 : 8 ≤ 4*(b : ℝ)/ε := (le_div_iff₀ hε).mpr (by nlinarith)
  have hlog8 : 2 < Real.log (8 : ℝ) := by
    have hh : Real.log (8 : ℝ)=3*Real.log 2 := by
      simpa only [Nat.cast_ofNat, show (2 : ℝ)^3=8 by norm_num] using! Real.log_pow 2 3
    rw [hh]
    linarith [Real.log_two_gt_d9]
  have hlog : 2 ≤ Real.log (4*(b : ℝ)/ε) :=
    (hlog8.trans_le (Real.log_le_log (by norm_num) hratio8)).le
  have hA : κ^2 ≤ (b : ℝ)*Real.log (4*(b : ℝ)/ε) := by
    have hm1 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
    have hm2 := mul_le_mul_of_nonneg_left (show 1 ≤ 2*L by linarith) (sq_nonneg κ)
    nlinarith
  have hs := Real.sqrt_le_sqrt hA
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hκ0] at hs
  have hj : Real.sqrt ((b : ℝ)*Real.log (4*(b : ℝ)/ε)) ≤ (J : ℝ) := Nat.le_ceil _
  have hkJ : κ ≤ (J : ℝ) := hs.trans hj
  refine ⟨by change 0 < (4*(J : ℝ))⁻¹; positivity, ?_⟩
  change (4*(J : ℝ))⁻¹ ≤ (4*κ)⁻¹
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
    (mul_le_mul_of_nonneg_left hkJ (by norm_num : (0 : ℝ) ≤ 4))

/-- Every projected unitary encoding has a unitary realization on the enlarged workspace with
`sourceAverageClean` frames. -/
theorem nearOptimalReciprocal_clean_input_encoding (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (henc : ProjectedUnitaryEncoding A U L R) :
    ∃ V : Matrix (Bool×(Bool×H)) (Bool×(Bool×H)) ℂ,
      ProjectedUnitaryEncoding A V (sourceAverageClean L) (sourceAverageClean R) := by
  let F := TensorGate (1 : Matrix Bool Bool ℂ) U
  have hflag : ProjectedUnitaryEncoding A F (flagFrame L) (flagFrame R) := by
    refine ⟨tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem henc.unitary,
      flagFrame_isIsometry henc.left_isometry, flagFrame_isIsometry henc.right_isometry, ?_⟩
    change (flagFrame L)ᴴ*(TensorGate (1 : Matrix Bool Bool ℂ) U)*(flagFrame R) = A
    rw [← henc.encoded]
    ext o i
    simp [compress, TensorGate, flagFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type]
  have hav := average_projectedEncoding hflag hflag
  have hA : (2 : ℂ)⁻¹ • (A+A) = A := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hL : sourceAverageClean L=averageFrame (flagFrame L) := by
    unfold sourceAverageClean
    have he : cppCleanFrame L=flagFrame L := by ext ⟨b,h⟩ i; cases b <;> rfl
    rw [he]
    congr 1
    exact Subsingleton.elim _ _
  have hR : sourceAverageClean R=averageFrame (flagFrame R) := by
    unfold sourceAverageClean
    have he : cppCleanFrame R=flagFrame R := by ext ⟨b,h⟩ i; cases b <;> rfl
    rw [he]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨averageCircuit F F, ?_⟩
  rw [hL,hR]
  simpa only [hA] using! hav

end Qatlib.Concepts.QsvtCore.LinearSystems
