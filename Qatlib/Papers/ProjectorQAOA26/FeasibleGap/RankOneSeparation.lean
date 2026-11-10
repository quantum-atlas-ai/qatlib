/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.RootSeparation
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.RayleighBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem rankOne_zero_diagonal (E : I → ℝ) (zero : I) (hzero : E zero=0) (a : ℝ) :
    ((rankOneOperator E a) zero zero).re= -a/(Fintype.card I:ℝ) := by
  simp only [rankOneOperator,diagonalMinusRankOne,Matrix.sub_apply,Matrix.diagonal_apply_eq,
    Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply,Complex.star_def,Complex.mul_conj]
  rw [uniformReference_weight zero]
  simp [hzero,div_eq_mul_inv]

theorem rankOne_lowest_signs (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (hL : 2≤Fintype.card I) (a : ℝ) (ha : 0<a) :
    (rankOneOperator_hermitian E a).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩<0 ∧
      0<(rankOneOperator_hermitian E a).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩ := by
  let hK:=rankOneOperator_hermitian E a
  let last : Fin (Fintype.card I):=⟨Fintype.card I-1,by omega⟩
  let pen : Fin (Fintype.card I):=⟨Fintype.card I-2,by omega⟩
  have hneg : hK.eigenvalues₀ last<0 := by
    have hh:=native_min_le_diagonal hK zero
    rw [rankOne_zero_diagonal E zero hzero a] at hh
    exact lt_of_le_of_lt hh (div_neg_of_neg_of_pos (neg_neg_of_pos ha)
      (Nat.cast_pos.mpr Fintype.card_pos))
  have hn : ∀ i,0≤E i := by
    intro i
    by_cases hi : i=zero
    · subst i;rw [hzero]
    · linarith [hE i hi]
  have hpos : 0<hK.eigenvalues₀ pen := by
    by_contra hc
    have hle : hK.eigenvalues₀ pen≤0 := le_of_not_gt hc
    rcases eq_or_lt_of_le hle with hz|hz
    · exact rankOne_zero_not_eigenvalue E zero hzero hE a ha.ne'
        (by simpa [hz] using! native_eigenvalue hK pen)
    · have hpLast:=negative_nonpole E hn _ hneg
      have hpPen:=negative_nonpole E hn _ hz
      have heLast:=(actual_secular_iff_eigenvalue E a _ hpLast).mpr (native_eigenvalue hK last)
      have hePen:=(actual_secular_iff_eigenvalue E a _ hpPen).mpr (native_eigenvalue hK pen)
      have heq : hK.eigenvalues₀ pen=hK.eigenvalues₀ last :=
        (uniformCurve_strictMono_negative E hn).injOn hz hneg
          (mul_left_cancel₀ ha.ne' (hePen.trans heLast.symm))
      have he:=simple_eigenvalue_index hK (hK.eigenvalues₀ last)
        (resolventVector E uniformReference (hK.eigenvalues₀ last))
        (actual_nonpole_line E a _ hpLast) pen last heq rfl
      have hv:=congrArg Fin.val he
      dsimp [pen,last] at hv
      omega
  exact ⟨hneg,hpos⟩

theorem rankOne_gap_lower (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (hL : 2≤Fintype.card I) (a : ℝ) (ha : 0<a) :
    1/(2*Real.sqrt (Fintype.card I:ℝ))≤
      (rankOneOperator_hermitian E a).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩-
      (rankOneOperator_hermitian E a).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩ := by
  let hK:=rankOneOperator_hermitian E a
  let lo:=hK.eigenvalues₀ ⟨Fintype.card I-1,by omega⟩
  let hi:=hK.eigenvalues₀ ⟨Fintype.card I-2,by omega⟩
  obtain ⟨hlo,hhi⟩:=rankOne_lowest_signs E zero hzero hE hL a ha
  change lo<0 at hlo
  change 0<hi at hhi
  change _≤hi-lo
  by_cases hbig : 1/2≤hi
  · have hcard : (1:ℝ)≤Fintype.card I := by exact_mod_cast (show 1≤Fintype.card I by omega)
    have hs : 1≤Real.sqrt (Fintype.card I:ℝ) := (Real.one_le_sqrt).mpr hcard
    have hbound : 1/(2*Real.sqrt (Fintype.card I:ℝ))≤1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    linarith
  · have hn : ∀ i,0≤E i := by
      intro i
      by_cases h : i=zero
      · subst i;rw [hzero]
      · linarith [hE i h]
    have heLo:=(actual_secular_iff_eigenvalue E a lo (negative_nonpole E hn lo hlo)).mpr
      (native_eigenvalue hK _)
    have heHi:=(actual_secular_iff_eigenvalue E a hi
      (small_positive_nonpole E zero hzero hE hi ⟨hhi,by linarith⟩)).mpr (native_eigenvalue hK _)
    have heq : uniformCurve E (-(-lo))=uniformCurve E hi := by
      simpa using! mul_left_cancel₀ ha.ne' (heLo.trans heHi.symm)
    have hh:=two_root_separation E zero hzero hE (-lo) hi (by linarith) hhi (by linarith) heq
    simpa only [neg_add_eq_sub,add_comm] using! hh
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
