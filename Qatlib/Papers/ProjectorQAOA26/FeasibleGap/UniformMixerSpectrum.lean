/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.RayleighBounds
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformSecular
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem uniformMixer_eigenvalue_cases (z : ℝ)
    (hz : hasRealEigenvalue (uniformMixer (I := I)) z) : z = 0 ∨ z = 1 := by
  obtain ⟨x,hx,he⟩ := hz
  have hid := learnedGenerator_idempotent (uniformReference (I := I)) uniformReference_normalized
  change uniformMixer * uniformMixer = uniformMixer at hid
  have hh := congrArg (fun M : Matrix I I ℂ => M *ᵥ x) hid
  change (uniformMixer * uniformMixer) *ᵥ x = uniformMixer *ᵥ x at hh
  rw [← Matrix.mulVec_mulVec,he,Matrix.mulVec_smul,he,smul_smul] at hh
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  have hv := congrArg (fun v : I → ℂ => v i) hh
  simp only [Pi.smul_apply,smul_eq_mul] at hv
  have hc : (z : ℂ) * (z : ℂ) = (z : ℂ) := mul_right_cancel₀ hi' hv
  have hr : z*z=z := by exact_mod_cast hc
  rcases mul_eq_zero.mp (show z*(z-1)=0 by nlinarith) with h|h
  · exact Or.inl h
  · exact Or.inr (by linarith)

omit [Nonempty I] in

theorem uniformMixer_zero_line (x : I → ℂ)
    (hx : uniformMixer *ᵥ x = (0 : ℂ) • x) :
    ∃ c : ℂ, x = c • (uniformReference (I := I)) := by
  refine ⟨l2inner uniformReference x,?_⟩
  have hh : x - l2inner uniformReference x • uniformReference = 0 := by
    simpa only [uniformMixer,learnedGenerator,Matrix.sub_mulVec,Matrix.one_mulVec,
      rankOne_mulVec,zero_smul] using! hx
  exact sub_eq_zero.mp hh

theorem uniformMixer_zero_eigenvalue : hasRealEigenvalue (uniformMixer (I := I)) 0 := by
  refine ⟨uniformReference,uniformReference_ne_zero,?_⟩
  simp only [uniformMixer,learnedGenerator,Matrix.sub_mulVec,Matrix.one_mulVec,
    rankOne_mulVec,l2inner_self_of_norm uniformReference_normalized,one_smul,
    sub_self,Complex.ofReal_zero,zero_smul]

theorem uniformMixer_lowest_pair (hL : 2 ≤ Fintype.card I) :
    (uniformMixer_hermitian (I := I)).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩=0 ∧
      (uniformMixer_hermitian (I := I)).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩=1 := by
  let hM := uniformMixer_hermitian (I := I)
  let last : Fin (Fintype.card I) := ⟨Fintype.card I-1,by omega⟩
  let pen : Fin (Fintype.card I) := ⟨Fintype.card I-2,by omega⟩
  obtain ⟨i,hi⟩ := eigenvalue_index hM 0 uniformMixer_zero_eigenvalue
  have hlast_le : hM.eigenvalues₀ last ≤ 0 := by
    rw [← hi]
    apply hM.eigenvalues₀_antitone
    change i.val ≤ Fintype.card I-1
    omega
  have hlast : hM.eigenvalues₀ last=0 := by
    rcases uniformMixer_eigenvalue_cases _ (native_eigenvalue hM last) with h|h
    · exact h
    · linarith
  have hpen : hM.eigenvalues₀ pen=1 := by
    rcases uniformMixer_eigenvalue_cases _ (native_eigenvalue hM pen) with h|h
    · have he := simple_eigenvalue_index hM 0 uniformReference uniformMixer_zero_line pen last h hlast
      have hv := congrArg Fin.val he
      dsimp [pen,last] at hv
      omega
    · exact h
  exact ⟨hlast,hpen⟩

theorem spectralGap_zero (E : I → ℝ) (hL : 2 ≤ Fintype.card I) : spectralGap E hL 0=1 := by
  obtain ⟨h0,h1⟩ := uniformMixer_lowest_pair (I := I) hL
  unfold spectralGap
  simp only [hamiltonian,sub_zero,one_smul,zero_smul,add_zero]
  rw [h0,h1]
  norm_num

end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
