/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Rat.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: ComplementSquare.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Polynomial
open scoped BigOperators

/-- Construction for even Index in the native source complement square model. -/
private def evenIndex {d : ℕ} (i : Fin (d+1)) : Fin (d+d+1) := ⟨2*i.val,by omega⟩

/-- The finite construction in `NativeSourceComplementSquare` satisfies `even_sum` under the displayed hypotheses. -/
private theorem even_sum {d : ℕ} (f : Fin (d+d+1) → ℚ)
    (hf : ∀ i,Odd i.val → f i=0) :
    (∑ i,f i)=∑ j : Fin (d+1),f (evenIndex j) := by
  classical
  have hfilter : (∑ i∈Finset.univ.filter (fun i : Fin (d+d+1) => Even i.val),f i)=
      ∑ i,f i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have he : ¬Even i.val := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
    exact hf i (Nat.not_even_iff_odd.mp he)
  rw [← hfilter]
  symm
  refine Finset.sum_bij (fun j _ => evenIndex j) ?_ ?_ ?_ ?_
  · intro j _
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,⟨j.val,by simp [evenIndex,two_mul]⟩⟩
  · intro i _ j _ he
    apply Fin.ext
    have hv := congrArg Fin.val he
    dsimp only [evenIndex] at hv
    omega
  · intro i hi
    have he : Even i.val := (Finset.mem_filter.mp hi).2
    obtain ⟨j,hj⟩ := he
    have hjlt : j<d+1 := by have h := i.isLt; omega
    refine ⟨⟨j,hjlt⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    dsimp only [evenIndex]
    omega
  · intro j _
    rfl

/-- Construction for source P in the native source complement square model. -/
def sourceP {d : ℕ} (a : Fin (d+d+1) → ℚ) : Fin (d+1) → ℚ := fun j => a (evenIndex j)

/-- Construction for source Complement Cell in the native source complement square model. -/
def sourceComplementCell {d : ℕ} (a : Fin (d+d+1) → ℚ) (k : Fin (d+d+1)) : ℚ :=
  (if k.val=d then 1 else 0)-
    ∑ i,∑ j,if i.val+j.val=2*k.val then a i*a j else 0

/-- Construction for convolution in the native source complement square model. -/
def convolution {d e : ℕ} (a : Fin (d+1) → ℚ) (b : Fin (e+1) → ℚ) :
    Fin (d+e+1) → ℚ := fun k => ∑ i,∑ j,if i.val+j.val=k.val then a i*b j else 0

/-- The finite construction in `NativeSourceComplementSquare` satisfies `convolution_polynomial` under the displayed hypotheses. -/
private theorem convolution_polynomial {d e : ℕ}
    (a : Fin (d+1) → ℚ) (b : Fin (e+1) → ℚ) :
    Polynomial.ofFn (d+e+1) (convolution a b)=
      Polynomial.ofFn (d+1) a*Polynomial.ofFn (e+1) b := by
  apply Polynomial.ext
  intro k
  by_cases hk : k<d+e+1
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    simp only [convolution,Polynomial.ofFn_eq_sum_monomial,Finset.sum_mul,
      Finset.mul_sum,Polynomial.monomial_mul_monomial,Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial]
    exact Finset.sum_comm
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    symm
    simp only [Polynomial.ofFn_eq_sum_monomial,Finset.sum_mul,Finset.mul_sum,
      Polynomial.monomial_mul_monomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hij : j.val+i.val≠k := by have hi := i.isLt; have hj := j.isLt; omega
    simp [hij]

/-- The finite construction in `NativeSourceComplementSquare` satisfies `sourceComplementCell_reindex` under the displayed hypotheses. -/
private theorem sourceComplementCell_reindex {d : ℕ} (a : Fin (d+d+1) → ℚ)
    (ha : ∀ i,Odd i.val → a i=0) (k : Fin (d+d+1)) :
    sourceComplementCell a k=(if k.val=d then 1 else 0)-
      ∑ p : Fin (d+1),∑ q : Fin (d+1),
        if p.val+q.val=k.val then sourceP a p*sourceP a q else 0 := by
  unfold sourceComplementCell
  congr 1
  calc
    _ = ∑ p : Fin (d+1),∑ j : Fin (d+d+1),
        if (evenIndex p).val+j.val=2*k.val then a (evenIndex p)*a j else 0 := by
      apply even_sum
      intro i hi
      simp only [ha i hi,zero_mul,ite_self,Finset.sum_const_zero]
    _ = ∑ p : Fin (d+1),∑ q : Fin (d+1),
        if (evenIndex p).val+(evenIndex q).val=2*k.val
          then a (evenIndex p)*a (evenIndex q) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      apply even_sum
      intro j hj
      simp only [ha j hj,mul_zero,ite_self]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      have he : (evenIndex p).val+(evenIndex q).val=2*k.val ↔ p.val+q.val=k.val := by
        dsimp only [evenIndex]
        omega
      simp only [he,sourceP]

/-- Same actual convolution cells, not a supplied alternate polynomial. -/
theorem sourceComplement_polynomial {d : ℕ} (a : Fin (d+d+1) → ℚ)
    (ha : ∀ i,Odd i.val → a i=0) :
    Polynomial.ofFn (d+d+1) (sourceComplementCell a)=
      X^d-(Polynomial.ofFn (d+1) (sourceP a))^2 := by
  have hv : sourceComplementCell a=
      (fun k => if k.val=d then (1 : ℚ) else 0)-
      (fun k : Fin (d+d+1) =>
        ∑ p : Fin (d+1),∑ q : Fin (d+1),
          if p.val+q.val=k.val then sourceP a p*sourceP a q else 0) := by
    funext k
    exact sourceComplementCell_reindex a ha k
  have hmono : Polynomial.ofFn (d+d+1) (fun k => if k.val=d then (1 : ℚ) else 0)=X^d := by
    apply Polynomial.ext
    intro k
    by_cases hk : k<d+d+1
    · simp only [Polynomial.ofFn_coeff_eq_val_of_lt _ hk,Polynomial.coeff_X_pow]
    · have hkd : k≠d := by omega
      simp only [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk),
        Polynomial.coeff_X_pow,ite_eq_right hkd]
  rw [hv,map_sub,hmono,pow_two]
  congr 1
  have hc := convolution_polynomial (sourceP a) (sourceP a)
  exact hc

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
