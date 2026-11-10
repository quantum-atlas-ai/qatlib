/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem sourceRectCert_of_gram {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {w : ℝ} (h : gramFilteredCert A Z w) :
    sourceRectCert n A Z w := by
  obtain ⟨Q,hQ,u,v,hu,hv,heq⟩ := h
  exact sourceRectCert_of_finiteWitness (fun r j => u j r) (fun s j => v j s)
    (by simpa only [dotProduct,Pi.star_apply] using! heq) hu hv

theorem sourceFunctionEvaluation_budget_nonneg {E : Type} [Fintype E] :
    0 ≤ 2*(1-1/(Fintype.card E : ℝ)) := by
  by_cases hz : Fintype.card E = 0
  · simp [hz]
  have hcard : (1 : ℝ) ≤ Fintype.card E := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hh : 1/(Fintype.card E : ℝ) ≤ 1 := by
    simpa using! one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hcard
  linarith

theorem sourceUnfiltered_functionEvaluation {X E : Type} [Fintype E] [DecidableEq E]
    (f : X → E) : sourceUnfiltered (gramFunctionEvaluationMatrix f) ≤
      ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ))) :=
  sourceRectValue_le_of_cert sourceFunctionEvaluation_budget_nonneg
    (sourceRectCert_of_gram (gramFilteredCert_gramFunctionEvaluation f))

theorem sourceAlphabet_masked_real_symmetrization {X E : Type} [Fintype X] [DecidableEq X]
    [DecidableEq E] {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (f : X → E) (M : Matrix X X ℂ)
    (hM : ∀ j, ‖(sourceAlphabetDelta input j ⊙ gramFunctionEvaluationMatrix f) ⊙ M‖ ≤ 1) :
    ∃ Γ : Matrix X X ℂ, Γ.IsHermitian ∧
      (∀ x y, f x=f y → Γ x y=0) ∧
      (∀ j, ‖sourceAlphabetDelta input j ⊙ Γ‖ ≤ 1) ∧
      (∀ x y, (Γ x y).im=0) ∧
      ‖gramFunctionEvaluationMatrix f ⊙ M‖ ≤ ‖Γ‖ := by
  let Q := gramFunctionEvaluationMatrix f ⊙ M
  by_cases hz : Q=0
  · refine ⟨0,Matrix.isHermitian_zero,?_,?_,by simp,?_⟩
    · simp
    · intro j; simp
    · change ‖Q‖ ≤ ‖(0 : Matrix X X ℂ)‖
      rw [hz]
  obtain ⟨u,v,hu,hv,hpair⟩ := gamma2_norm_singular_pair Q hz
  obtain ⟨p,q,hC,hbound⟩ := gamma2_balanced_real_compression Q u v hu hv hpair
  let C := Matrix.fromRows (Matrix.diagonal p) (Matrix.diagonal q)
  let B := Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ) Q Qᴴ 0*C
  let Γ := gamma2RealPart B
  have hherm : Γ.IsHermitian := gamma2RealPart_isHermitian B
    (Matrix.isHermitian_conjTranspose_mul_mul C
      (Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero))
  refine ⟨Γ,hherm,?_,?_,?_,hbound⟩
  · intro x y hxy
    have hq : Q x y=0 := by simp [Q,Matrix.hadamard_apply,gramFunctionEvaluationMatrix,hxy]
    have hq' : Q y x=0 := by simp [Q,Matrix.hadamard_apply,gramFunctionEvaluationMatrix,hxy.symm]
    have hb : B x y=0 := by
      dsimp only [B,C]
      rw [gamma2_paired_compression]
      simp [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.conjTranspose_apply,hq,hq']
    simp [Γ,gamma2RealPart,hb]
  · intro j
    have hmask (x y : X) : star (sourceAlphabetDelta input j y x)=sourceAlphabetDelta input j x y := by
      by_cases he : input x j=input y j
      · simp only [sourceAlphabetDelta,if_pos he,if_pos he.symm,star_zero]
      · simp only [sourceAlphabetDelta,if_neg he,if_neg (Ne.symm he),star_one]
    have he : sourceAlphabetDelta input j ⊙ Q=
        (sourceAlphabetDelta input j ⊙ gramFunctionEvaluationMatrix f) ⊙ M := by
      ext x y
      simp only [Q,Matrix.hadamard_apply]
      ring
    have hreal : sourceAlphabetDelta input j ⊙ Γ=gamma2RealPart (sourceAlphabetDelta input j ⊙ B) := by
      ext x y
      by_cases hxy : input x j=input y j <;>
        simp [Γ,gamma2RealPart,Matrix.hadamard_apply,sourceAlphabetDelta,hxy]
    rw [hreal]
    apply (gamma2RealPart_norm_le _).trans
    change ‖sourceAlphabetDelta input j ⊙ (Cᴴ*Matrix.fromBlocks 0 Q Qᴴ 0*C)‖ ≤ 1
    rw [gamma2_masked_compression p q Q (sourceAlphabetDelta input j) hmask]
    have hd := gamma2_hermitian_dilation_norm_le (sourceAlphabetDelta input j ⊙ Q)
      (by rw [he]; exact hM j)
    calc
      _ ≤ ‖Cᴴ‖*‖Matrix.fromBlocks (0 : Matrix X X ℂ)
          (sourceAlphabetDelta input j ⊙ Q) (sourceAlphabetDelta input j ⊙ Q)ᴴ 0‖*‖C‖ :=
        (Matrix.l2_opNorm_mul (Cᴴ*Matrix.fromBlocks (0 : Matrix X X ℂ)
          (sourceAlphabetDelta input j ⊙ Q) (sourceAlphabetDelta input j ⊙ Q)ᴴ 0) C).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Cᴴ _) (norm_nonneg C))
      _ ≤ 1*1*1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
      _ = 1 := by norm_num
  · intro x y
    simp [Γ,gamma2RealPart]

theorem sourceAdversary_eq_masked {X E : Type} [Fintype X] [DecidableEq X]
    [DecidableEq E] {n q : ℕ} (input : X → Fin n → Fin (q+1)) (f : X → E) :
    sourceAdversary (sourceAlphabetDelta input) f=
      sourceRectValue (gramFunctionEvaluationMatrix f)
        (fun j => sourceAlphabetDelta input j ⊙ gramFunctionEvaluationMatrix f) := by
  rw [(rectangularSchurDuality X X n (gramFunctionEvaluationMatrix f)
    (fun j => sourceAlphabetDelta input j ⊙ gramFunctionEvaluationMatrix f)).1]
  unfold sourceAdversary sourceRectDual
  apply le_antisymm
  · apply iSup_le
    intro Γ
    have he : gramFunctionEvaluationMatrix f ⊙ Γ.val=Γ.val := by
      ext x y
      by_cases hh : f x=f y
      · simp [Matrix.hadamard_apply,gramFunctionEvaluationMatrix,hh,Γ.property.2.2.1 x y hh]
      · simp [Matrix.hadamard_apply,gramFunctionEvaluationMatrix,hh]
    have hf (j : Fin n) : ‖(sourceAlphabetDelta input j ⊙ gramFunctionEvaluationMatrix f) ⊙ Γ.val‖ ≤ 1 := by
      rw [Matrix.hadamard_assoc,he,Matrix.hadamard_comm]
      exact Γ.property.2.2.2 j
    exact le_iSup_of_le ⟨Γ.val,hf⟩ (by rw [he])
  · apply iSup_le
    intro M
    obtain ⟨Γ,hherm,hzero,hfilter,hreal,hbound⟩ :=
      sourceAlphabet_masked_real_symmetrization input f M.val M.property
    exact le_iSup_of_le ⟨Γ,hherm,hreal,hzero,fun j => by
      rw [Matrix.hadamard_comm]; exact hfilter j⟩ (ENNReal.ofReal_le_ofReal hbound)

theorem sourceFunctionEvaluation_hadamard_self {X E : Type} [DecidableEq E] (f : X → E) :
    gramFunctionEvaluationMatrix f ⊙ gramFunctionEvaluationMatrix f=gramFunctionEvaluationMatrix f := by
  ext x y
  by_cases hh : f x=f y <;> simp [gramFunctionEvaluationMatrix,Matrix.hadamard_apply,hh]

theorem functionEvaluationNormSandwich : FunctionEvaluationNormSandwich := by
  intro X E _ _ _ _ n q input f
  let A := gramFunctionEvaluationMatrix f
  let Z := sourceAlphabetDelta input
  have hU := sourceUnfiltered_functionEvaluation f
  have he := sourceAdversary_eq_masked input f
  refine ⟨hU,he,?_,?_⟩
  · rw [he]
    have hh := sourceRectValue_hadamard_filters_le A A Z
    simpa only [A,Z,sourceFunctionEvaluation_hadamard_self] using! hh
  · by_cases hz : A=0
    · change sourceRectValue A Z ≤ _
      rw [hz,sourceRectValue_zero]
      exact zero_le
    have hh := sourceRectValue_hadamard_reverse_le A A Z (Or.inr hz)
    calc
      sourceRectValue A Z ≤ sourceRectValue A (fun j => Z j ⊙ A)*sourceUnfiltered A := hh
      _ ≤ sourceRectValue A (fun j => Z j ⊙ A)*ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ))) :=
        mul_le_mul le_rfl hU zero_le zero_le
      _ = ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ)))*sourceAdversary Z f := by rw [← he,mul_comm]

end Qatlib.Concepts.GramQueryCore.FilteredNorm
