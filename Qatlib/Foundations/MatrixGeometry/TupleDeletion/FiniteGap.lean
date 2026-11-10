/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I : Type*} [Fintype I]

theorem finite_pair_sum_gap (B : I → I → ℝ) (q : I → ℝ) (a : ℝ)
    (hdiag : ∀ i,B i i=a*q i) (hoff : ∀ i j,i ≠ j → -(q i)-(q j) ≤ 2*B i j) :
    (a-(Fintype.card I : ℝ)+1)*(∑ i : I,q i) ≤ ∑ i : I,∑ j : I,B i j := by
  have hp (i j : I) : (if i=j then (a+1)*q i else 0)-q i/2-q j/2 ≤ B i j := by
    by_cases h : i=j
    · subst j
      rw [if_pos rfl,hdiag]
      linarith
    · rw [if_neg h]
      linarith [hoff i j h]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun j _ => hp i j))
  have hc : (∑ i : I,∑ j : I,((if i=j then (a+1)*q i else 0)-q i/2-q j/2))=
      (a-(Fintype.card I : ℝ)+1)*(∑ i : I,q i) := by
    simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,if_true,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.sum_div,← Finset.mul_sum]
    ring
  rw [hc] at hs
  exact hs
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
