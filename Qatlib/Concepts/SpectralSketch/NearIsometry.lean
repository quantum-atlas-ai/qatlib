/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.BlockEncoding.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Execution.WorkspaceCP

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SpectralSketch.NearIsometry
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def nearColumnPolar {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] (A : Matrix H I ℂ) : Matrix H I ℂ :=
  oddSingularTransform A (fun x=> if 0< x then 1 else 0)

theorem nearColumnPolar_singular_bounds {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix H I ℂ) (α : ℝ) (hα : 0 ≤ α) (hsmall : α<1)
    (hGram : ‖Aᴴ*A-1‖ ≤ α) (i : Fin (Fintype.card I)) :
    0< matrixSingularValues A i ∧ |matrixSingularValues A i-1| ≤ α := by
  let v := rightSingularBasis A i
  have hact : (Aᴴ*A-1).toEuclideanLin v=
      ((matrixSingularValues A i : ℂ)^2-1) • v := by
    rw [map_sub,LinearMap.sub_apply,gram_apply_rightSingularBasis,
      Matrix.toLpLin_one,LinearMap.id_apply]
    rw [sub_smul,one_smul]
  have hbound : ‖(Aᴴ*A-1).toEuclideanLin v‖ ≤ α := by
    have h := Matrix.l2_opNorm_mulVec (Aᴴ*A-1) v
    simpa only [v,norm_rightSingularBasis,mul_one] using! h.trans
      (mul_le_mul_of_nonneg_right hGram (norm_nonneg v))
  have hg : |(matrixSingularValues A i)^2-1| ≤ α := by
    rw [hact,norm_smul,← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,norm_rightSingularBasis,mul_one] at hbound
    exact hbound
  have hnonneg := matrixSingularValues_nonneg A i
  have hs := abs_le.mp hg
  have hpos : 0< matrixSingularValues A i := by nlinarith
  refine ⟨hpos,?_⟩
  apply abs_le.mpr
  by_cases hi : 1 ≤ matrixSingularValues A i
  · constructor <;> nlinarith
  · have hi' : matrixSingularValues A i ≤ 1 := le_of_not_ge hi
    constructor <;> nlinarith

theorem nearColumnPolar_full_support {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix H I ℂ)
    (hpos : ∀ i : Fin (Fintype.card I),0< matrixSingularValues A i) :
    singularSupport A=1 ∧ nearColumnPolar A=leftSingularColumns A*(basisColumns (rightSingularBasis A))ᴴ ∧
      matrixPseudoinverse A*A=1 := by
  have hz (i : Fin (Fintype.card I)) : matrixSingularValues A i ≠ 0 := ne_of_gt (hpos i)
  have hs : singularSupport A=1 := by
    unfold singularSupport
    simp only [if_neg (hz _),Matrix.diagonal_one]
  have hp : nearColumnPolar A=leftSingularColumns A*(basisColumns (rightSingularBasis A))ᴴ := by
    unfold nearColumnPolar oddSingularTransform
    simp only [if_pos (hpos _),Matrix.diagonal_one,Matrix.mul_one]
  refine ⟨hs,hp,?_⟩
  rw [matrixPseudoinverse_mul,hs,Matrix.mul_one,basisColumns_mul_adjoint]

theorem nearColumnPolar_isometry {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix H I ℂ)
    (hpos : ∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i) :
    IsIsometry (nearColumnPolar A) := by
  obtain ⟨hs,hp,_⟩ := nearColumnPolar_full_support A hpos
  have hL : (leftSingularColumns A)ᴴ*leftSingularColumns A=1 :=
    (leftSingularColumns_gram A).trans hs
  change (nearColumnPolar A)ᴴ*nearColumnPolar A=1
  rw [hp,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  calc
    basisColumns (rightSingularBasis A)*(leftSingularColumns A)ᴴ*
        (leftSingularColumns A*(basisColumns (rightSingularBasis A))ᴴ)=
      basisColumns (rightSingularBasis A)*((leftSingularColumns A)ᴴ*leftSingularColumns A)*
        (basisColumns (rightSingularBasis A))ᴴ := by simp only [Matrix.mul_assoc]
    _=1 := by rw [hL,Matrix.mul_one,basisColumns_mul_adjoint]

set_option maxHeartbeats 800000 in

theorem nearColumnPolar_range {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix H I ℂ)
    (hpos : ∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i) :
    LinearMap.range (nearColumnPolar A).toEuclideanLin=LinearMap.range A.toEuclideanLin := by
  let V := basisColumns (rightSingularBasis A)
  let D : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
    diagonal (fun i => (matrixSingularValues A i : ℂ))
  let E : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
    diagonal (fun i => (matrixSingularValues A i : ℂ)⁻¹)
  have hDE : D*E=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos _))),Matrix.diagonal_one]
  have hp := (nearColumnPolar_full_support A hpos).2.1
  have ha : A=leftSingularColumns A*D*Vᴴ := (oddSingularTransform_id A).symm
  have hPA : nearColumnPolar A*(V*D*Vᴴ)=A := by
    rw [hp]
    calc
      leftSingularColumns A*Vᴴ*(V*D*Vᴴ)=leftSingularColumns A*(Vᴴ*V)*D*Vᴴ := by
        simp only [Matrix.mul_assoc]
      _=leftSingularColumns A*D*Vᴴ := by simp [V]
      _=A := ha.symm
  have hAP : A*(V*E*Vᴴ)=nearColumnPolar A := by
    calc
      A*(V*E*Vᴴ)=(leftSingularColumns A*D*Vᴴ)*(V*E*Vᴴ) :=
        congrArg (fun X : Matrix H I ℂ => X*(V*E*Vᴴ)) ha
      _=leftSingularColumns A*D*(Vᴴ*V)*E*Vᴴ := by
        simp only [Matrix.mul_assoc]
      _=leftSingularColumns A*(D*E)*Vᴴ := by simp [V,Matrix.mul_assoc]
      _=leftSingularColumns A*Vᴴ := by rw [hDE,Matrix.mul_one]
      _=nearColumnPolar A := hp.symm
  have hle (X : Matrix H I ℂ) (Y : Matrix I I ℂ) :
      LinearMap.range (X*Y).toEuclideanLin ≤ LinearMap.range X.toEuclideanLin := by
    rw [Matrix.toLpLin_mul_same]
    exact LinearMap.range_comp_le_range Y.toEuclideanLin X.toEuclideanLin
  apply le_antisymm
  · calc
      LinearMap.range (nearColumnPolar A).toEuclideanLin=
          LinearMap.range (A*(V*E*Vᴴ)).toEuclideanLin := congrArg
        (fun X : Matrix H I ℂ => LinearMap.range X.toEuclideanLin) hAP.symm
      _ ≤ LinearMap.range A.toEuclideanLin := hle _ _
  · calc
      LinearMap.range A.toEuclideanLin=
          LinearMap.range (nearColumnPolar A*(V*D*Vᴴ)).toEuclideanLin := congrArg
        (fun X : Matrix H I ℂ => LinearMap.range X.toEuclideanLin) hPA.symm
      _ ≤ LinearMap.range (nearColumnPolar A).toEuclideanLin := hle _ _

theorem nearColumnPolar_sandwich_base {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A P : Matrix H I ℂ) (α : ℝ) (_hα : 0 ≤ α)
    (hP : IsIsometry P) (hd : ‖A-P‖ ≤ α) (Y : Matrix I I ℂ) :
    ‖A*Y*Aᴴ-P*Y*Pᴴ‖ ≤ α*‖Y*Aᴴ‖+α*‖Y‖ := by
  have hp : ‖P‖ ≤ 1 := (Qatlib.Concepts.BlockEncoding.Encoding.IsIsometry.norm_le_one hP)
  have hPY : ‖P*Y‖ ≤ ‖Y‖ := (Matrix.l2_opNorm_mul P Y).trans
    ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _))
  have hAdj : ‖(A-P)ᴴ‖ ≤ α := by simpa only [Matrix.l2_opNorm_conjTranspose] using! hd
  have he : A*Y*Aᴴ-P*Y*Pᴴ=(A-P)*(Y*Aᴴ)+(P*Y)*(A-P)ᴴ := by
    simp only [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub,← Matrix.mul_assoc]
    abel
  rw [he]
  calc
    ‖(A-P)*(Y*Aᴴ)+(P*Y)*(A-P)ᴴ‖ ≤ ‖(A-P)*(Y*Aᴴ)‖+‖(P*Y)*(A-P)ᴴ‖ := norm_add_le _ _
    _ ≤ α*‖Y*Aᴴ‖+α*‖Y‖ := add_le_add
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
      ((Matrix.l2_opNorm_mul _ _).trans (by
        have h := mul_le_mul hPY hAdj (norm_nonneg _) (norm_nonneg _)
        simpa only [mul_comm] using! h))

set_option maxHeartbeats 800000 in

theorem near_isometry_polar_range_pseudoinverse_and_error : ∀ (H I : Type)
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] (A : Matrix H I ℂ) (α : ℝ),
    0 ≤ α → α<1 → ‖Aᴴ*A-1‖ ≤ α →
    IsIsometry (nearColumnPolar A) ∧
    LinearMap.range (nearColumnPolar A).toEuclideanLin=LinearMap.range A.toEuclideanLin ∧
    ‖A-nearColumnPolar A‖ ≤ α ∧ ‖matrixPseudoinverse A‖ ≤ (1-α)⁻¹ ∧
    (∀ Y : Matrix I I ℂ,
      ‖A*Y*Aᴴ-(nearColumnPolar A)*Y*(nearColumnPolar A)ᴴ‖ ≤ (2*α+α^2)*‖Y‖ ∧
      ‖A*Y*Aᴴ-(nearColumnPolar A)*Y*(nearColumnPolar A)ᴴ‖ ≤
        α*(2-α)/(1-α)^2*‖A*Y*Aᴴ‖) := by
  intro H I _ _ _ _ A α hα hsmall hGram
  have hscalar := nearColumnPolar_singular_bounds A α hα hsmall hGram
  have hpos (i : Fin (Fintype.card I)) : 0 < matrixSingularValues A i := (hscalar i).1
  have hiso := nearColumnPolar_isometry A hpos
  have hdist : ‖A-nearColumnPolar A‖ ≤ α := by
    have h := oddSingularTransform_error_le A (fun x => (x : ℂ))
      (fun x => if 0<x then 1 else 0) hα (fun i => ?_)
    · simpa only [oddSingularTransform_id,nearColumnPolar] using! h
    · simpa only [if_pos (hpos _),← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs] using! (hscalar i).2
  have hδ : 0 < 1-α := by linarith
  have hinv : ‖matrixPseudoinverse A‖ ≤ (1-α)⁻¹ :=
    matrixPseudoinverse_norm_le hδ (fun i _ => by have h := (abs_le.mp (hscalar i).2).1; linarith)
  refine ⟨hiso,nearColumnPolar_range A hpos,hdist,hinv,?_⟩
  intro Y
  have hbase := nearColumnPolar_sandwich_base A (nearColumnPolar A) α hα hiso hdist Y
  have hnormA : ‖A‖ ≤ 1+α := by
    calc
      ‖A‖=‖nearColumnPolar A+(A-nearColumnPolar A)‖ := by congr 1; abel
      _ ≤ ‖nearColumnPolar A‖+‖A-nearColumnPolar A‖ := norm_add_le _ _
      _ ≤ 1+α := add_le_add (Qatlib.Concepts.BlockEncoding.Encoding.IsIsometry.norm_le_one hiso) hdist
  have hYA : ‖Y*Aᴴ‖ ≤ ‖Y‖*(1+α) := (Matrix.l2_opNorm_mul _ _).trans (by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_left hnormA (norm_nonneg _))
  have hleft : matrixPseudoinverse A*A=1 := (nearColumnPolar_full_support A hpos).2.2
  have hright : Aᴴ*(matrixPseudoinverse A)ᴴ=1 := by
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_one] using!
        congrArg Matrix.conjTranspose hleft
  have hYAid : Y*Aᴴ=matrixPseudoinverse A*(A*Y*Aᴴ) := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hleft,Matrix.one_mul]
  have hYid : Y=matrixPseudoinverse A*(A*Y*Aᴴ)*(matrixPseudoinverse A)ᴴ := by
    symm
    calc
      matrixPseudoinverse A*(A*Y*Aᴴ)*(matrixPseudoinverse A)ᴴ=
        (matrixPseudoinverse A*A)*Y*(Aᴴ*(matrixPseudoinverse A)ᴴ) := by simp only [Matrix.mul_assoc]
      _=Y := by rw [hleft,hright,Matrix.one_mul,Matrix.mul_one]
  have hi0 : 0 ≤ (1-α)⁻¹ := inv_nonneg.mpr hδ.le
  have hYArel : ‖Y*Aᴴ‖ ≤ (1-α)⁻¹*‖A*Y*Aᴴ‖ := by
    rw [hYAid]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hYrel : ‖Y‖ ≤ ((1-α)⁻¹)^2*‖A*Y*Aᴴ‖ := by
    have h1 := Matrix.l2_opNorm_mul (matrixPseudoinverse A*(A*Y*Aᴴ)) (matrixPseudoinverse A)ᴴ
    have h2 := Matrix.l2_opNorm_mul (matrixPseudoinverse A) (A*Y*Aᴴ)
    rw [Matrix.l2_opNorm_conjTranspose] at h1
    calc
      ‖Y‖=‖matrixPseudoinverse A*(A*Y*Aᴴ)*(matrixPseudoinverse A)ᴴ‖ := congrArg norm hYid
      _ ≤
          (‖matrixPseudoinverse A‖*‖A*Y*Aᴴ‖)*‖matrixPseudoinverse A‖ :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      _ ≤ ((1-α)⁻¹)^2*‖A*Y*Aᴴ‖ := by
        have hs := (sq_le_sq₀ (norm_nonneg _) hi0).mpr hinv
        nlinarith [norm_nonneg (A*Y*Aᴴ)]
  have hcoeff : α*((1-α)⁻¹+((1-α)⁻¹)^2)=α*(2-α)/(1-α)^2 := by
    field_simp
    ring
  constructor
  · calc
      ‖A*Y*Aᴴ-nearColumnPolar A*Y*(nearColumnPolar A)ᴴ‖ ≤
          α*(‖Y‖*(1+α))+α*‖Y‖ := hbase.trans (add_le_add
        (mul_le_mul_of_nonneg_left hYA hα) le_rfl)
      _=(2*α+α^2)*‖Y‖ := by ring
  · calc
      ‖A*Y*Aᴴ-nearColumnPolar A*Y*(nearColumnPolar A)ᴴ‖ ≤
          α*((1-α)⁻¹*‖A*Y*Aᴴ‖)+α*(((1-α)⁻¹)^2*‖A*Y*Aᴴ‖) :=
        hbase.trans (add_le_add (mul_le_mul_of_nonneg_left hYArel hα)
          (mul_le_mul_of_nonneg_left hYrel hα))
      _=α*((1-α)⁻¹+((1-α)⁻¹)^2)*‖A*Y*Aᴴ‖ := by ring
      _=α*(2-α)/(1-α)^2*‖A*Y*Aᴴ‖ := by rw [hcoeff]

theorem near_isometry_zero_range_boundary : ∀ (H I : Type) [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Nonempty I],
    ‖(0:Matrix H I ℂ)ᴴ*(0:Matrix H I ℂ)-(1:Matrix I I ℂ)‖=1 ∧
    ¬∃ F : Matrix H I ℂ,IsIsometry F ∧ LinearMap.range F.toEuclideanLin=⊥ := by
  intro H I _ _ _ _ _
  refine ⟨?_,?_⟩
  · simp
  · rintro ⟨F,hF,hr⟩
    have hz : F.toEuclideanLin=0 := LinearMap.range_eq_bot.mp hr
    have hzero : F=0 := Matrix.toEuclideanLin.injective (by simpa using! hz)
    have hi : (0 : Matrix I I ℂ)=1 := by simpa [IsIsometry,hzero] using! hF
    have he :=
        congrArg (fun M : Matrix I I ℂ => M (Classical.arbitrary I) (Classical.arbitrary I)) hi
    simp at he

end Qatlib.Concepts.SpectralSketch.NearIsometry
