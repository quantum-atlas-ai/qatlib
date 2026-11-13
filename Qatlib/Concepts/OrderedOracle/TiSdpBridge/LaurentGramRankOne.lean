/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGramShift
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGramSchur

/-!
# Rank one Gram representatives

The Lean declarations show that a nonzero positive semidefinite matrix has an outer Gram
representative with the same generalized traces and a first diagonal entry at least as large. A
maximizer of that entry equals its Schur vector outer Gram matrix, yielding rank one
representatives. This supports the Laurent Gram framework of [ChildsLandahlParrilo2007] with
positivity tools from [Bhatia1997].

## Main statements

* `maximal_gram_eq_outer`: a nonzero maximizer of the first diagonal entry equals its Schur
  vector outer Gram matrix.
* `exists_outer_gram`: an outer Gram representative preserves all generalized traces and does
  not decrease the first diagonal entry.
* `exists_rank_one_gram`: the representative can be chosen positive semidefinite of rank one.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped Classical BigOperators ComplexOrder
variable {n : ℕ} [NeZero n]

omit [NeZero n] in

/-- The generalized trace of a sum of matrices is the sum of their generalized traces at the
same offset. -/
theorem genTrace_add (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℤ) :
    genTrace (A+B) k=genTrace A k+genTrace B k := by
  have hpoint (i j : Fin n) :
      (if (j.val : ℤ)-(i.val : ℤ)=k then A i j+B i j else 0)=
        (if (j.val : ℤ)-(i.val : ℤ)=k then A i j else 0)+
        (if (j.val : ℤ)-(i.val : ℤ)=k then B i j else 0) := by split_ifs <;> simp
  unfold genTrace
  simp_rw [Matrix.add_apply,hpoint,Finset.sum_add_distrib]

/-- A nonzero positive semidefinite matrix of positive size that maximizes its first diagonal
entry among matrices with the same generalized traces equals the outer Gram matrix of its
Schur vector. -/
theorem maximal_gram_eq_outer (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) (hB0 : B≠0)
    (hmax : ∀ C : Matrix (Fin n) (Fin n) ℂ,C.PosSemidef →
      (∀ k : ℤ,genTrace C k=genTrace B k) → C 0 0≤B 0 0) :
    B=gramOuter (gramSchurVector B) := by
  have ha := maximal_gram_first_pos B hB hB0 hmax
  let R := gramOuter (gramSchurVector B)
  let P := B-R
  have hP := gram_schur_residual B hB ha
  have hPdiag : P 0 0=0 := hP.2
  have hdecomp : R+P=B := by dsimp [P]; abel
  have hP0 : P=0 := by
    by_contra hp
    obtain ⟨r,hr,hzero⟩ := exists_first_positive_gram_diagonal P hP.1 hp
    let E := Equiv.addRight r
    let C := R+P.submatrix E E
    have hC : C.PosSemidef := (gramOuter_posSemidef _).add (hP.1.submatrix E)
    have htrace (k : ℤ) : genTrace C k=genTrace B k := by
      rw [genTrace_add,genTrace_zero_prefix_shift P hP.1.isHermitian r hzero,← genTrace_add,hdecomp]
    have hm := hmax C hC htrace
    have hE : E (0 : Fin n)=r := by simp [E]
    have hR : R 0 0=B 0 0 := by
      have h := congrFun (congrFun hdecomp 0) 0
      simpa only [Matrix.add_apply,hPdiag,add_zero] using h
    have hreal := (Complex.le_def.mp hm).1
    change (R 0 0+P (E 0) (E 0)).re≤(B 0 0).re at hreal
    rw [hE,hR,Complex.add_re] at hreal
    linarith
  have h := hdecomp
  rw [hP0,add_zero] at h
  exact h.symm

omit [NeZero n] in

/-- An outer Gram matrix with a nonzero diagonal entry has rank one. -/
theorem gramOuter_rank_one_of_diag_ne_zero (v : Fin n → ℂ) (r : Fin n)
    (hr : gramOuter v r r≠0) : (gramOuter v).rank=1 := by
  have hle : (gramOuter v).rank≤1 := by
    change (Matrix.vecMulVec (star v) v).rank≤1
    exact Matrix.rank_vecMulVec_le _ _
  have hs : (gramOuter v).submatrix (fun _ : Fin 1 => r) (fun _ : Fin 1 => r)=
      Matrix.diagonal (fun _ : Fin 1 => gramOuter v r r) := by
    ext i j
    have hij : i=j := Subsingleton.elim _ _
    simp [Matrix.submatrix_apply,Matrix.diagonal,hij]
  have hlow := Matrix.rank_submatrix_le (gramOuter v) (fun _ : Fin 1 => r) (fun _ : Fin 1 => r)
  rw [hs,Matrix.rank_diagonal] at hlow
  simp [hr] at hlow
  omega

/-- Every nonzero positive semidefinite matrix of positive size has an outer Gram representative
of rank one with the same generalized traces and a first diagonal entry at least as large. -/
theorem exists_outer_gram (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hA0 : A≠0) :
    ∃ v : Fin n → ℂ,(gramOuter v).rank=1 ∧
      (∀ k : ℤ,genTrace (gramOuter v) k=genTrace A k) ∧ A 0 0≤gramOuter v 0 0 := by
  obtain ⟨B,hB,htrace,hfirst,hmax⟩ := exists_maximal_gram A hA 0
  have hB0 : B≠0 := by
    intro hz
    have h := htrace 0
    rw [genTrace_zero,genTrace_zero,hz,Matrix.trace_zero] at h
    exact hA0 (hA.trace_eq_zero_iff.mp h.symm)
  have hm (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef)
      (ht : ∀ k : ℤ,genTrace C k=genTrace B k) : C 0 0≤B 0 0 :=
    hmax C hC (fun k => (ht k).trans (htrace k))
  have he := maximal_gram_eq_outer B hB hB0 hm
  have ha := maximal_gram_first_pos B hB hB0 hm
  have hdiag : gramOuter (gramSchurVector B) 0 0≠0 := by
    rw [← he]
    intro hz
    rw [hz] at ha
    norm_num at ha
  refine ⟨gramSchurVector B,gramOuter_rank_one_of_diag_ne_zero _ 0 hdiag,?_,?_⟩
  · simpa only [← he] using htrace
  · simpa only [← he] using hfirst

/-- Every nonzero positive semidefinite matrix of positive size has a positive semidefinite rank
one representative with the same generalized traces and a first diagonal entry at least as
large. -/
theorem exists_rank_one_gram (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hA0 : A≠0) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ,B.PosSemidef ∧ B.rank=1 ∧
      (∀ k : ℤ,genTrace B k=genTrace A k) ∧ A 0 0≤B 0 0 := by
  obtain ⟨v,hr,ht,hf⟩ := exists_outer_gram A hA hA0
  exact ⟨gramOuter v,gramOuter_posSemidef v,hr,ht,hf⟩
end Qatlib.Concepts.OrderedOracle.TiSdpBridge
