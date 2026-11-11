/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceOriginalComplement
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRoundingBound
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Fin.Rev
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: CircleInput.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Polynomial
open scoped BigOperators

/-- The finite construction in `NativeSourceCircleInput` satisfies `even_array_expand` under the displayed hypotheses. -/
private theorem even_array_expand {d : ℕ} (a : Fin (d+d+1) → ℚ)
    (ha : ∀ i,Odd i.val → a i=0) :
    Polynomial.ofFn (d+d+1) a=Polynomial.expand ℚ 2 (Polynomial.ofFn (d+1) (sourceP a)) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_expand (by decide : 0<2)]
  by_cases hk : k<d+d+1
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    by_cases he : 2∣k
    · rw [ite_eq_left he,Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega : k/2<d+1)]
      change a ⟨k,hk⟩=a ⟨2*(k/2),by omega⟩
      congr 1
      apply Fin.ext
      exact (Nat.mul_div_cancel' he).symm
    · rw [ite_eq_right he]
      apply ha
      change Odd k
      refine ⟨k/2,?_⟩
      have hm : k%2≠0 := by intro h; exact he (Nat.dvd_iff_mod_eq_zero.mpr h)
      have hb := Nat.mod_lt k (by decide : 0<2)
      omega
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    by_cases he : 2∣k
    · rw [ite_eq_left he]
      have hmul := Nat.mul_div_cancel' he
      have hle : d+1 ≤ k/2 := by omega
      rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hle]
    · rw [ite_eq_right he]

/-- Construction for source Shifted Polynomial in the native source circle input model. -/
def sourceShiftedPolynomial (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ[X] :=
  Polynomial.ofFn (sourceDegree cs N E+sourceDegree cs N E+1) (sourceLiftedArray cs N E)

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceShifted_expand` under the displayed hypotheses. -/
theorem sourceShifted_expand (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) :
    sourceShiftedPolynomial cs N E=Polynomial.expand ℚ 2 (sourceInputP cs N E) :=
  even_array_expand _ (sourceLiftedArray_odd_zero cs N E hparity hd)

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceInputP_eval_square` under the displayed hypotheses. -/
theorem sourceInputP_eval_square (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (t : ℂ) :
    (sourceInputP cs N E).eval₂ (Rat.castHom ℂ) (t^2)=
      (sourceShiftedPolynomial cs N E).eval₂ (Rat.castHom ℂ) t := by
  rw [sourceShifted_expand cs N E hparity hd,Polynomial.expand_eq_comp_X_pow]
  simp only [Polynomial.eval₂_comp,Polynomial.eval₂_X_pow]

/-- The finite construction in `NativeSourceCircleInput` satisfies `exp_pair` under the displayed hypotheses. -/
private theorem exp_pair (d j : ℕ) (hj : j ≤ d) (z : ℂ) :
    Complex.exp (((d-j : ℕ) : ℂ)*z)+Complex.exp (((d+j : ℕ) : ℂ)*z)=
      Complex.exp ((d : ℂ)*z)*(2*Complex.cosh ((j : ℂ)*z)) := by
  rw [Nat.cast_sub hj,Nat.cast_add,sub_mul,add_mul,sub_eq_add_neg,
    Complex.exp_add,Complex.exp_add,Complex.two_cosh]
  ring

/-- A general finite palindromic exponential sum, used at the same input
coefficient function. This is not an alternate circle polynomial input. -/
private theorem palindromic_exp_sum (a : ℕ → ℚ) (d : ℕ) (z : ℂ) :
    (∑ i : Fin (d+d+1),(a (Nat.dist i.val d) : ℂ)*Complex.exp ((i.val : ℂ)*z))=
      Complex.exp ((d : ℂ)*z)*((a 0 : ℂ)+
        ∑ j : Fin d,(a (j.val+1) : ℂ)*(2*Complex.cosh (((j.val+1 : ℕ) : ℂ)*z))) := by
  let L : Fin d → ℂ := fun j => (a (j.val+1) : ℂ)*Complex.exp (((d-(j.val+1) : ℕ) : ℂ)*z)
  let H : Fin d → ℂ := fun j => (a (j.val+1) : ℂ)*Complex.exp (((d+(j.val+1) : ℕ) : ℂ)*z)
  have hl : (∑ i : Fin d,(a (Nat.dist i.val d) : ℂ)*Complex.exp ((i.val : ℂ)*z))=∑ j,L j := by
    calc
      _ = ∑ i : Fin d,(a (Nat.dist i.rev.val d) : ℂ)*Complex.exp ((i.rev.val : ℂ)*z) := by
        apply Fintype.sum_equiv Fin.revPerm
        intro i
        simp only [Fin.revPerm_apply,Fin.rev_rev]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := i.isLt
        have hv : i.rev.val=d-(i.val+1) := Fin.val_rev i
        have he : Nat.dist i.rev.val d=i.val+1 := by
          rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt i.rev.isLt),hv]
          omega
        dsimp only [L]
        rw [he,hv]
  have hr : (∑ j : Fin (d+1),(a (Nat.dist (d+j.val) d) : ℂ)*
      Complex.exp (((d+j.val : ℕ) : ℂ)*z))=
      (a 0 : ℂ)*Complex.exp ((d : ℂ)*z)+∑ j,H j := by
    rw [Fin.sum_univ_succ]
    have hdist (k : ℕ) : Nat.dist (d+k) d=k := by simp [Nat.dist]
    simp only [Fin.val_zero,Nat.add_zero,Nat.dist_self,Fin.val_succ,hdist,H]
  have hs : (∑ i : Fin (d+d+1),(a (Nat.dist i.val d) : ℂ)*Complex.exp ((i.val : ℂ)*z))=
      (∑ j,L j)+((a 0 : ℂ)*Complex.exp ((d : ℂ)*z)+∑ j,H j) := by
    change (∑ i : Fin (d+(d+1)),(a (Nat.dist i.val d) : ℂ)*Complex.exp ((i.val : ℂ)*z))=_
    rw [Fin.sum_univ_add]
    change (∑ i : Fin d,(a (Nat.dist i.val d) : ℂ)*Complex.exp ((i.val : ℂ)*z))+
      (∑ j : Fin (d+1),(a (Nat.dist (d+j.val) d) : ℂ)*Complex.exp (((d+j.val : ℕ) : ℂ)*z))=_
    rw [hl,hr]
  rw [hs]
  calc
    _ = (a 0 : ℂ)*Complex.exp ((d : ℂ)*z)+∑ j : Fin d,(L j+H j) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = (a 0 : ℂ)*Complex.exp ((d : ℂ)*z)+
        ∑ j : Fin d,Complex.exp ((d : ℂ)*z)*
          ((a (j.val+1) : ℂ)*(2*Complex.cosh (((j.val+1 : ℕ) : ℂ)*z))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [L,H]
      rw [← mul_add,exp_pair d (j.val+1) j.isLt z]
      ring
    _ = _ := by rw [mul_add,Finset.mul_sum]; ring

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Polynomial
open scoped BigOperators

/-- Mathematical zero-default coefficient view of the actual finite array. -/
def sourceAAt (cs : List ℚ) (N : ℕ) (E : ℚ) (j : ℕ) : ℚ :=
  (List.ofFn (sourceCoefficient cs N E)).getD j 0

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceAAt_of_lt` under the displayed hypotheses. -/
theorem sourceAAt_of_lt (cs : List ℚ) (N : ℕ) (E : ℚ) (j : ℕ) (hj : j<N+1) :
    sourceAAt cs N E j=sourceCoefficient cs N E ⟨j,hj⟩ := by
  simp only [sourceAAt,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hj,Option.getD_some]

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceAAt_tail` under the displayed hypotheses. -/
theorem sourceAAt_tail (cs : List ℚ) (N : ℕ) (E : ℚ) (j : ℕ)
    (hj : sourceDegree cs N E < j) : sourceAAt cs N E j=0 := by
  by_cases hi : j<N+1
  · rw [sourceAAt_of_lt cs N E j hi]
    exact sourceArrayDegree_tail_zero (sourceCoefficient cs N E) ⟨j,hi⟩ hj
  · simp only [sourceAAt,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right hi,Option.getD_none]

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceLiftedArray_asAt` under the displayed hypotheses. -/
private theorem sourceLiftedArray_asAt (cs : List ℚ) (N : ℕ) (E : ℚ)
    (i : Fin (sourceDegree cs N E+sourceDegree cs N E+1)) :
    sourceLiftedArray cs N E i=sourceAAt cs N E (Nat.dist i.val (sourceDegree cs N E)) := by
  have hj : Nat.dist i.val (sourceDegree cs N E)<N+1 := by
    have hi := i.isLt
    have hd := sourceDegree_le cs N E
    simp only [Nat.dist]
    omega
  unfold sourceLiftedArray
  change sourceCoefficient cs N E ⟨Nat.dist i.val (sourceDegree cs N E),hj⟩=_
  exact (sourceAAt_of_lt cs N E _ hj).symm

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceShifted_eval_exp` under the displayed hypotheses. -/
private theorem sourceShifted_eval_exp (cs : List ℚ) (N : ℕ) (E : ℚ) (z : ℂ) :
    (sourceShiftedPolynomial cs N E).eval₂ (Rat.castHom ℂ) (Complex.exp z)=
      ∑ i : Fin (sourceDegree cs N E+sourceDegree cs N E+1),
        (sourceAAt cs N E (Nat.dist i.val (sourceDegree cs N E)) : ℂ)*
          Complex.exp ((i.val : ℂ)*z) := by
  unfold sourceShiftedPolynomial
  rw [Polynomial.ofFn_eq_sum_monomial,Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro i _
  rw [sourceLiftedArray_asAt,Complex.exp_nat_mul]
  rfl

/-- The finite construction in `NativeSourceCircleInput` satisfies `sourceOutput_cosh_sum` under the displayed hypotheses. -/
private theorem sourceOutput_cosh_sum (cs : List ℚ) (N : ℕ) (E : ℚ) (theta : ℝ) :
    (((nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval (Real.cos theta) : ℝ) : ℂ)=
      (sourceAAt cs N E 0 : ℂ)+∑ j : Fin (sourceDegree cs N E),
        (sourceAAt cs N E (j.val+1) : ℂ)*
          (2*Complex.cosh (((j.val+1 : ℕ) : ℂ)*((theta : ℂ)*Complex.I))) := by
  let d := sourceDegree cs N E
  let f : ℕ → ℂ := fun j =>
    (((if j=0 then (1 : ℚ) else 2)*sourceAAt cs N E j : ℚ) : ℂ)*
      (Real.cos ((j : ℝ)*theta) : ℂ)
  have hn : (((nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval (Real.cos theta) : ℝ) : ℂ)=∑ j : Fin (N+1),f j.val := by
    rw [sourceOutput_cos]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    have he : sourceOutputCoefficient cs N E j=
        (if j.val=0 then 1 else 2)*sourceAAt cs N E j.val := by
      rw [sourceOutputCoefficient,sourceWeight,sourceAAt_of_lt cs N E j.val j.isLt]
    rw [he]
    simp only [f, Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_natCast]
  have ht : (∑ j : Fin (N+1),f j.val)=∑ j : Fin (d+1),f j.val := by
    rw [← Finset.sum_range,← Finset.sum_range]
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (sourceDegree_le cs N E)))
    intro j _ hj
    have hjd : d<j := by
      have hb : d+1 ≤ j := by simpa only [Finset.mem_range,not_lt] using hj
      omega
    have hz := sourceAAt_tail cs N E j hjd
    simp only [f,hz,mul_zero,Rat.cast_zero,zero_mul]
  rw [hn,ht,Fin.sum_univ_succ]
  have h0 : f 0=(sourceAAt cs N E 0 : ℂ) := by simp [f]
  change f 0 + (∑ i : Fin d, f (i.val+1)) = _
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hc : Complex.cosh (((j.val+1 : ℕ) : ℂ)*((theta : ℂ)*Complex.I))=
      (Real.cos (((j.val+1 : ℕ) : ℝ)*theta) : ℂ) := by
    rw [show (((j.val+1 : ℕ) : ℂ)*((theta : ℂ)*Complex.I))=
      ((((j.val+1 : ℕ) : ℝ)*theta : ℝ) : ℂ)*Complex.I by push_cast; ring,
      Complex.cosh_mul_I,← Complex.ofReal_cos]
  simp only [f,ite_eq_right (Nat.succ_ne_zero j.val),Rat.cast_mul,Rat.cast_ofNat,hc]
  ring

/-- Same original-input P at every exponential point. The coefficient sum
on the right is the actual regularized output, not an ideal substitute. -/
theorem sourceInputP_circle (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (theta : ℝ) :
    (sourceInputP cs N E).eval₂ (Rat.castHom ℂ)
        (Complex.exp (2*((theta : ℂ)*Complex.I)))=
      Complex.exp ((sourceDegree cs N E : ℂ)*((theta : ℂ)*Complex.I))*
        (((nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval (Real.cos theta) : ℝ) : ℂ) := by
  let z : ℂ := (theta : ℂ)*Complex.I
  have he : Complex.exp (2*z)=(Complex.exp z)^2 := by
    simpa only [Nat.cast_ofNat] using Complex.exp_nat_mul z 2
  rw [he,sourceInputP_eval_square cs N E hparity hd,
    sourceShifted_eval_exp,palindromic_exp_sum,← sourceOutput_cosh_sum cs N E theta]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
