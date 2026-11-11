/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Products of unitary block encodings with shared ancillas

This module proves frame-defect, leakage, and product-error bounds for scale-one block encodings
of unitary operators using a common isometry. Products retain the shared frame, with error
bounded by the square of the sum of the individual square-root errors, following the product
bounds of [GilyenSuLowWiebe2019].

## Main statements

* `shared_ancilla_unitary_frame_and_leakage`: frame-defect and leakage estimates.
* `shared_ancilla_unitary_pair_error`: the two-factor product error.
* `shared_ancilla_heterogeneous_word_encoding`: the family product with heterogeneous errors.

## References

* [Gilyén, Su, Low, and Wiebe, 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.SharedAncilla.AncillaProduct
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The norm of a finite-dimensional orthogonal projector is at most one. -/
theorem shared_projector_norm_le_one {H : Type} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) : ‖P‖ ≤ 1 := by
  have he : ‖P‖*‖P‖ = ‖P‖ := by
    have hh : Pᴴ = P := hP.2
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,hh,hP.1]
  nlinarith [norm_nonneg P]

/-- Taking conjugate transposes preserves a scale-one block encoding with the same input and
output frame and the same error. -/
theorem shared_encoding_adjoint {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ} {δ : ℝ}
    (h : BlockEncoding A U F F 1 δ) : BlockEncoding Aᴴ Uᴴ F F 1 δ := by
  refine ⟨adjoint_unitary h.unitary,h.left_isometry,h.right_isometry,by norm_num,h.error_nonneg,?_⟩
  have he : Aᴴ-compress F Uᴴ F = (A-compress F U F)ᴴ := by
    simp [compress,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  simpa only [one_smul,he,Matrix.l2_opNorm_conjTranspose] using h.error_le

/-- A scale-one shared-frame block encoding of a unitary `A` has frame defect `‖U * F - F * A‖`
at most `sqrt (2 * δ)`. -/
theorem shared_frame_defect {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (δ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding A U F F 1 δ) :
    ‖U*F-F*A‖ ≤ Real.sqrt (2*δ) := by
  have hδ := h.error_nonneg
  have hU : Uᴴ*U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using h.unitary.1
  have hAA : Aᴴ*A = 1 := by simpa only [Matrix.star_eq_conjTranspose] using hA.1
  have hF : Fᴴ*F = 1 := h.left_isometry
  have hnA : ‖A‖ ≤ 1 := isometry_norm_le hAA
  have herr : ‖A-compress F U F‖ ≤ δ := by simpa only [one_smul] using h.error_le
  have hUF : (U*F)ᴴ*(U*F) = 1 := by
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Uᴴ U F,hU,Matrix.one_mul,hF]
  have hFA : (F*A)ᴴ*(F*A) = 1 := by
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Fᴴ F A,hF,Matrix.one_mul,hAA]
  have he : (U*F-F*A)ᴴ*(U*F-F*A) =
      Aᴴ*(A-compress F U F)+(A-compress F U F)ᴴ*A := by
    rw [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hUF,hFA]
    simp only [compress,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_assoc,Matrix.conjTranspose_conjTranspose,hAA]
    abel
  have hs : ‖U*F-F*A‖^2 ≤ 2*δ := by
    rw [pow_two,← Matrix.l2_opNorm_conjTranspose_mul_self,he]
    calc
      _ ≤ ‖Aᴴ*(A-compress F U F)‖+‖(A-compress F U F)ᴴ*A‖ := norm_add_le _ _
      _ ≤ ‖Aᴴ‖*‖A-compress F U F‖+‖(A-compress F U F)ᴴ‖*‖A‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ ≤ 1*δ+δ*1 := by rw [Matrix.l2_opNorm_conjTranspose,Matrix.l2_opNorm_conjTranspose]; gcongr
      _ = _ := by ring
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (by norm_num) h.error_nonneg)).mpr hs

/-- A scale-one shared-frame block encoding of a unitary has frame defect and both displayed
leakage norms at most `sqrt (2 * δ)`. -/
theorem shared_ancilla_unitary_frame_and_leakage :
∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
 (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (δ : ℝ),
 A∈Matrix.unitaryGroup I ℂ → BlockEncoding A U F F 1 δ →
 ‖U*F-F*A‖ ≤ Real.sqrt (2*δ) ∧
 ‖(1-F*Fᴴ)*U*F‖ ≤ Real.sqrt (2*δ) ∧
 ‖Fᴴ*U*(1-F*Fᴴ)‖ ≤ Real.sqrt (2*δ) := by
  intro H I _ _ _ _ A U F δ hA h
  have hp := isOrthogonalProjector_compl (rangeProjector_isOrthogonalProjector h.left_isometry)
  have hn : ‖(1-F*Fᴴ:Matrix H H ℂ)‖ ≤ 1 := shared_projector_norm_le_one hp
  have hf : (1-F*Fᴴ)*F = 0 := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,h.left_isometry,Matrix.mul_one,sub_self]
  have hl (V : Matrix H H ℂ) (B : Matrix I I ℂ) (hv : ‖V*F-F*B‖ ≤ Real.sqrt (2*δ)) :
      ‖(1-F*Fᴴ)*V*F‖ ≤ Real.sqrt (2*δ) := by
    have he : (1-F*Fᴴ)*V*F = (1-F*Fᴴ)*(V*F-F*B) := by
      rw [Matrix.mul_sub,← Matrix.mul_assoc _ F B,hf,Matrix.zero_mul,sub_zero,Matrix.mul_assoc]
    rw [he]
    exact (Matrix.l2_opNorm_mul _ _).trans
        ((mul_le_mul hn hv (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hd := shared_frame_defect A U F δ hA h
  refine ⟨hd,hl U A hd,?_⟩
  have had := shared_frame_defect Aᴴ Uᴴ F δ (adjoint_unitary hA) (shared_encoding_adjoint h)
  have hb := hl Uᴴ Aᴴ had
  have he : Fᴴ*U*(1-F*Fᴴ) = ((1-F*Fᴴ)*Uᴴ*F)ᴴ := by
    simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rwa [he,Matrix.l2_opNorm_conjTranspose]

/-- Multiplying shared-frame scale-one block encodings of unitaries with errors `δ` and `ε`
yields a block encoding of their product with error `δ + ε + 2 * sqrt (δ * ε)`. See
[GilyenSuLowWiebe2019]. -/
theorem shared_ancilla_unitary_pair_error :
∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
 (A B : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ) (δ ε : ℝ),
 A∈Matrix.unitaryGroup I ℂ → B∈Matrix.unitaryGroup I ℂ →
 BlockEncoding A U F F 1 δ → BlockEncoding B V F F 1 ε →
 BlockEncoding (A*B) (U*V) F F 1 (δ+ε+2*Real.sqrt (δ*ε)) := by
  intro H I _ _ _ _ A B U V F δ ε hA hB hu hv
  have hδ := hu.error_nonneg
  have hε := hv.error_nonneg
  have hF : Fᴴ*F = 1 := hu.left_isometry
  let Q : Matrix H H ℂ := 1-F*Fᴴ
  have hQ : Q*Q = Q := (isOrthogonalProjector_compl
    (rangeProjector_isOrthogonalProjector hu.left_isometry)).1
  have hleak : ‖Fᴴ*U*Q*V*F‖ ≤ 2*Real.sqrt (δ*ε) := by
    have hl := (shared_ancilla_unitary_frame_and_leakage H I A U F δ hA hu).2.2
    have hr := (shared_ancilla_unitary_frame_and_leakage H I B V F ε hB hv).2.1
    have he : Fᴴ*U*Q*V*F = (Fᴴ*U*Q)*(Q*V*F) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Q (V*F),hQ]
    have hs : Real.sqrt (2*δ)*Real.sqrt (2*ε) = 2*Real.sqrt (δ*ε) := by
      rw [← Real.sqrt_mul (mul_nonneg (by norm_num) hδ)]
      have he : 2*δ*(2*ε) = 4*(δ*ε) := by ring
      rw [he,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    rw [he]
    exact (Matrix.l2_opNorm_mul _ _).trans
        ((mul_le_mul hl hr (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq hs)
  have hcu := l2_norm_compress_le_one hu.left_isometry hu.unitary hu.right_isometry
  have hbn : ‖B‖ ≤ 1 := isometry_norm_le (by simpa only [Matrix.star_eq_conjTranspose] using! hB.1)
  have heU : ‖A-compress F U F‖ ≤ δ := by simpa only [one_smul] using hu.error_le
  have heV : ‖B-compress F V F‖ ≤ ε := by simpa only [one_smul] using hv.error_le
  refine ⟨(Matrix.unitaryGroup H ℂ).mul_mem hu.unitary hv.unitary,hu.left_isometry,hu.right_isometry,
    by norm_num,by positivity,?_⟩
  rw [one_smul]
  have he : A*B-compress F (U*V) F =
      (A-compress F U F)*B+compress F U F*(B-compress F V F)-(Fᴴ*U*Q*V*F) := by
    dsimp [compress,Q]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_assoc,Matrix.one_mul]
    abel
  rw [he]
  calc
    _ ≤ (‖(A-compress F U F)*B‖+‖compress F U F*(B-compress F V F)‖)+‖Fᴴ*U*Q*V*F‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (δ+ε)+2*Real.sqrt (δ*ε) := by
      apply add_le_add _ hleak
      apply add_le_add
      · exact (Matrix.l2_opNorm_mul _ _).trans
          ((mul_le_mul heU hbn (norm_nonneg _) hδ).trans_eq (mul_one _))
      · exact (Matrix.l2_opNorm_mul _ _).trans
          ((mul_le_mul hcu heV (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

/-- The ordered product of a matrix family along a list of indices, with the identity for the
empty list. -/
noncomputable def unitaryFamilyEvaluate {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (U : Fin m → Matrix H H ℂ) : List (Fin m) → Matrix H H ℂ
  | [] => 1
  | i :: cs => U i * unitaryFamilyEvaluate U cs

/-- The list of all indices in `Fin m` in their natural order. -/
def unitaryFamilyWord (m : ℕ) : List (Fin m) := List.ofFn id

/-- The square of the sum of the square roots of the individual errors in a finite family. -/
noncomputable def sharedAncillaWordError {m : ℕ} (e : Fin m → ℝ) : ℝ := (∑ i, Real.sqrt (e i))^2

/-- Evaluating any index list in a family of unitary matrices gives a unitary matrix. -/
theorem unitaryFamilyEvaluate_unitary {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (A : Fin m → Matrix H H ℂ) (ha : ∀ i,A i ∈ Matrix.unitaryGroup H ℂ) (cs : List (Fin m)) :
    unitaryFamilyEvaluate A cs ∈ Matrix.unitaryGroup H ℂ := by
  induction cs with
  | nil => exact (Matrix.unitaryGroup H ℂ).one_mem
  | cons i cs ih => exact (Matrix.unitaryGroup H ℂ).mul_mem (ha i) ih

/-- A list product of shared-frame scale-one block encodings of unitaries has error bounded by
the square of the sum of the square roots of the errors along the list. -/
theorem shared_word_encoding_list {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {m : ℕ} (A : Fin m → Matrix I I ℂ) (U : Fin m → Matrix H H ℂ) (F : Matrix H I ℂ)
    (e : Fin m → ℝ) (hF : IsIsometry F)
    (hs : ∀ i,A i ∈ Matrix.unitaryGroup I ℂ ∧ BlockEncoding (A i) (U i) F F 1 (e i)) (cs : List (Fin m)) :
    BlockEncoding (unitaryFamilyEvaluate A cs) (unitaryFamilyEvaluate U cs) F F 1
      (((cs.map (fun i => Real.sqrt (e i))).sum)^2) := by
  induction cs with
  | nil =>
    refine ⟨(Matrix.unitaryGroup H ℂ).one_mem,hF,hF,by norm_num,by norm_num,?_⟩
    have hFF : Fᴴ*F = 1 := hF
    simp [unitaryFamilyEvaluate,compress,hFF]
  | cons i cs ih =>
    have h := shared_ancilla_unitary_pair_error H I (A i) (unitaryFamilyEvaluate A cs)
      (U i) (unitaryFamilyEvaluate U cs) F (e i) (((cs.map (fun i => Real.sqrt (e i))).sum)^2)
      (hs i).1 (unitaryFamilyEvaluate_unitary A (fun i => (hs i).1) cs) (hs i).2 ih
    have he : e i+((cs.map (fun i => Real.sqrt (e i))).sum)^2+
        2*Real.sqrt (e i*((cs.map (fun i => Real.sqrt (e i))).sum)^2) =
        (Real.sqrt (e i)+(cs.map (fun i => Real.sqrt (e i))).sum)^2 := by
      rw [Real.sqrt_mul (hs i).2.error_nonneg,Real.sqrt_sq (List.sum_nonneg (fun x hx => by
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx; exact Real.sqrt_nonneg _))]
      nlinarith [Real.sq_sqrt (hs i).2.error_nonneg]
    simpa only [unitaryFamilyEvaluate,List.map_cons,List.sum_cons,he] using h

/-- The natural-order product of a unitary family with shared-frame scale-one block encodings is
block encoded by the corresponding implementation product with error bound
`sharedAncillaWordError e`. See [GilyenSuLowWiebe2019]. -/
theorem shared_ancilla_heterogeneous_word_encoding :
∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
 (m : ℕ) (A : Fin m→Matrix I I ℂ) (U : Fin m→Matrix H H ℂ) (F : Matrix H I ℂ) (e : Fin m→ℝ),
 IsIsometry F → (∀i,A i∈Matrix.unitaryGroup I ℂ ∧ BlockEncoding (A i) (U i) F F 1 (e i)) →
 BlockEncoding (unitaryFamilyEvaluate A (unitaryFamilyWord m))
  (unitaryFamilyEvaluate U (unitaryFamilyWord m)) F F 1 (sharedAncillaWordError e) := by
  intro H I _ _ _ _ m A U F e hF hs
  have he : ((unitaryFamilyWord m).map (fun i => Real.sqrt (e i))).sum = ∑ i,Real.sqrt (e i) := by
    simp [unitaryFamilyWord,List.map_ofFn,List.sum_ofFn]
  simpa only [he,sharedAncillaWordError] using
      shared_word_encoding_list A U F e hF hs (unitaryFamilyWord m)

end Qatlib.Concepts.SharedAncilla.AncillaProduct
