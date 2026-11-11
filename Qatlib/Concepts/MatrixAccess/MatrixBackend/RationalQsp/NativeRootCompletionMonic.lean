/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootReturnedCompleteness
import Mathlib.Algebra.Polynomial.OfFn
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Source complete_coefficients: zero initialization, ordered negative update
at i followed by positive update at i+1, and repeated multiplication over the
actual returned root list. Uses existing Gaussian multiplication and Polynomial.ofFn.
No normalization, interpreter or bit-fee theorem is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Polynomial
open scoped BigOperators

/-- Rational Gaussian pair multiplication `(a + bi)(c + di) = (ac - bd) + (ad + bc)i`. -/
def gaussianRatMul (u v : ℚ × ℚ) : ℚ × ℚ :=
  (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletion_decode_zero` under the displayed hypotheses. -/
private theorem rootCompletion_decode_zero : rootRationalCoordinate (0,0)=0 := by
  apply Complex.ext <;> simp [rootRationalCoordinate]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletion_decode_add` under the displayed hypotheses. -/
private theorem rootCompletion_decode_add (u v : ℚ×ℚ) :
    rootRationalCoordinate (u+v)=rootRationalCoordinate u+rootRationalCoordinate v := by
  apply Complex.ext <;> simp [rootRationalCoordinate]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletion_decode_sub` under the displayed hypotheses. -/
private theorem rootCompletion_decode_sub (u v : ℚ×ℚ) :
    rootRationalCoordinate (u-v)=rootRationalCoordinate u-rootRationalCoordinate v := by
  apply Complex.ext <;> simp [rootRationalCoordinate]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletion_decode_mul` under the displayed hypotheses. -/
private theorem rootCompletion_decode_mul (u v : ℚ×ℚ) :
    rootRationalCoordinate (gaussianRatMul u v)=rootRationalCoordinate u*rootRationalCoordinate v := by
  apply Complex.ext <;> simp [rootRationalCoordinate,gaussianRatMul] <;> ring

/-- The SAME existing power-coefficient representation on a typed array. -/
def rootCompletionStatePolynomial {n : ℕ} (a : Fin n → ℚ×ℚ) : ℂ[X] :=
  Polynomial.ofFn n (fun i => rootRationalCoordinate (a i))

/-- Source order matters for the state: first subtract rho*a[i] at i,
then add a[i] at i+1 in that updated output state. -/
def rootCompletionLinearStep {n : ℕ} (rho : ℚ×ℚ) (a : Fin n → ℚ×ℚ)
    (s : Fin (n+1) → ℚ×ℚ) (i : Fin n) : Fin (n+1) → ℚ×ℚ :=
  let t := fun k => if k=i.castSucc then s k-gaussianRatMul rho (a i) else s k
  fun k => if k=i.succ then t k+a i else t k

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionLinearStep_coordinate` under the displayed hypotheses. -/
theorem rootCompletionLinearStep_coordinate {n : ℕ} (rho : ℚ×ℚ)
    (a : Fin n → ℚ×ℚ) (s : Fin (n+1) → ℚ×ℚ) (i : Fin n) (k : Fin (n+1)) :
    rootRationalCoordinate (rootCompletionLinearStep rho a s i k)=
      rootRationalCoordinate (s k)+
      (if k=i.castSucc then -(rootRationalCoordinate rho*rootRationalCoordinate (a i)) else 0)+
      (if k=i.succ then rootRationalCoordinate (a i) else 0) := by
  have hne : i.castSucc≠i.succ := by
    intro he
    have hv := congrArg Fin.val he
    change i.val=i.val+1 at hv
    omega
  by_cases hk : k=i.castSucc
  · subst k
    simp only [rootCompletionLinearStep,ite_true,ite_eq_right hne]
    rw [rootCompletion_decode_sub,rootCompletion_decode_mul]
    simp only [add_zero,sub_eq_add_neg]
  · by_cases hl : k=i.succ
    · subst k
      simp only [rootCompletionLinearStep,ite_true,ite_eq_right (Ne.symm hne)]
      rw [rootCompletion_decode_add]
      simp only [add_zero]
    · simp only [rootCompletionLinearStep,ite_eq_right hk,ite_eq_right hl,add_zero]

/-- Exact polynomial effect for an arbitrary initial output state. -/
theorem rootCompletionLinearStep_polynomial {n : ℕ} (rho : ℚ×ℚ)
    (a : Fin n → ℚ×ℚ) (s : Fin (n+1) → ℚ×ℚ) (i : Fin n) :
    rootCompletionStatePolynomial (rootCompletionLinearStep rho a s i)=
      rootCompletionStatePolynomial s+
        monomial i.val (-(rootRationalCoordinate rho*rootRationalCoordinate (a i)))+
        monomial (i.val+1) (rootRationalCoordinate (a i)) := by
  classical
  simp only [rootCompletionStatePolynomial,Polynomial.ofFn_eq_sum_monomial]
  simp_rw [rootCompletionLinearStep_coordinate,map_add]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hdelta (j : Fin (n+1)) (v : ℂ) :
      (∑ k : Fin (n+1),monomial k.val (if k=j then v else 0))=monomial j.val v := by
    calc
      _=(∑ k : Fin (n+1),if k=j then monomial k.val v else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k=j
        · simp only [ite_eq_left hk]
        · simp only [ite_eq_right hk,Polynomial.monomial_zero_right]
      _=_ := by simp
  rw [hdelta,hdelta]
  rfl

/-- Actual ascending iteration, from the literal all-zero allocated output. -/
def rootCompletionLinearLoop {n : ℕ} (rho : ℚ×ℚ) (a : Fin n → ℚ×ℚ) :
    Fin (n+1) → ℚ×ℚ :=
  (List.finRange n).foldl (rootCompletionLinearStep rho a) (fun _ => (0,0))

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionFold_polynomial` under the displayed hypotheses. -/
private theorem rootCompletionFold_polynomial {n : ℕ} (rho : ℚ×ℚ)
    (a : Fin n → ℚ×ℚ) (l : List (Fin n)) (s : Fin (n+1) → ℚ×ℚ) :
    rootCompletionStatePolynomial (l.foldl (rootCompletionLinearStep rho a) s)=
      rootCompletionStatePolynomial s+(l.map (fun i =>
        monomial i.val (-(rootRationalCoordinate rho*rootRationalCoordinate (a i)))+
        monomial (i.val+1) (rootRationalCoordinate (a i)))).sum := by
  induction l generalizing s with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons,ih,rootCompletionLinearStep_polynomial]
    simp only [List.map_cons,List.sum_cons,add_assoc]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionLinearLoop_polynomial` under the displayed hypotheses. -/
theorem rootCompletionLinearLoop_polynomial {n : ℕ} (rho : ℚ×ℚ) (a : Fin n → ℚ×ℚ) :
    rootCompletionStatePolynomial (rootCompletionLinearLoop rho a)=
      (X-C (rootRationalCoordinate rho))*rootCompletionStatePolynomial a := by
  classical
  unfold rootCompletionLinearLoop
  rw [rootCompletionFold_polynomial]
  have hz : rootCompletionStatePolynomial (fun _ : Fin (n+1) => ((0,0) : ℚ×ℚ))=0 := by
    simp only [rootCompletionStatePolynomial,rootCompletion_decode_zero]
    change Polynomial.ofFn (n+1) (0 : Fin (n+1) → ℂ)=0
    exact map_zero _
  rw [hz,zero_add,← List.ofFn_eq_map,Fin.sum_ofFn]
  rw [rootCompletionStatePolynomial,Polynomial.ofFn_eq_sum_monomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_mul,Polynomial.X_mul_monomial,Polynomial.C_mul_monomial,Polynomial.monomial_neg]
  exact add_comm _ _

/-- Existing Polynomial.ofFn applied to the actual dynamic list. -/
def rootCompletionListPolynomial (a : List (ℚ×ℚ)) : ℂ[X] :=
  rootCompletionStatePolynomial (fun i : Fin a.length => a.get i)

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionListPolynomial_ofFn` under the displayed hypotheses. -/
theorem rootCompletionListPolynomial_ofFn {n : ℕ} (a : Fin n → ℚ×ℚ) :
    rootCompletionListPolynomial (List.ofFn a)=rootCompletionStatePolynomial a := by
  apply Polynomial.ext
  intro k
  simp only [rootCompletionListPolynomial,rootCompletionStatePolynomial]
  by_cases hk : k<n
  · have hk' : k<(List.ofFn a).length := by
      simpa only [List.length_ofFn] using hk
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk',Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    simp only [List.get_eq_getElem,List.getElem_ofFn]
  · have hk' : (List.ofFn a).length≤k := by
      simpa only [List.length_ofFn] using (le_of_not_gt hk)
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hk',
      Polynomial.ofFn_coeff_eq_zero_of_ge _ (le_of_not_gt hk)]

/-- One source root update includes allocation, all ordered cell updates and
conversion back to the dynamic coefficient list. No trimming is performed. -/
def rootCompletionLinearList (rho : ℚ×ℚ) (a : List (ℚ×ℚ)) : List (ℚ×ℚ) :=
  List.ofFn (rootCompletionLinearLoop rho (fun i : Fin a.length => a.get i))

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionLinearList_polynomial` under the displayed hypotheses. -/
theorem rootCompletionLinearList_polynomial (rho : ℚ×ℚ) (a : List (ℚ×ℚ)) :
    rootCompletionListPolynomial (rootCompletionLinearList rho a)=
      (X-C (rootRationalCoordinate rho))*rootCompletionListPolynomial a := by
  rw [rootCompletionLinearList,rootCompletionListPolynomial_ofFn,
    rootCompletionLinearLoop_polynomial]
  rfl

/-- The same emitted instruction list satisfies `rootCompletionLinearList_length` with the displayed gate and query accounting. -/
theorem rootCompletionLinearList_length (rho : ℚ×ℚ) (a : List (ℚ×ℚ)) :
    (rootCompletionLinearList rho a).length=a.length+1 := by
  simp [rootCompletionLinearList]

/-- Actual source initialization [ONE], with no sorting or coordinate dedup. -/
def rootCompletionMonicCoefficients (roots : List (ℚ×ℚ)) : List (ℚ×ℚ) :=
  roots.foldl (fun a rho => rootCompletionLinearList rho a) [(1,0)]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionRootsFold_polynomial` under the displayed hypotheses. -/
private theorem rootCompletionRootsFold_polynomial (roots a : List (ℚ×ℚ)) :
    rootCompletionListPolynomial (roots.foldl (fun a rho => rootCompletionLinearList rho a) a)=
      rootCompletionListPolynomial a*(roots.map (fun rho => X-C (rootRationalCoordinate rho))).prod := by
  induction roots generalizing a with
  | nil => simp
  | cons rho roots ih =>
    rw [List.foldl_cons,ih,rootCompletionLinearList_polynomial]
    simp only [List.map_cons,List.prod_cons]
    ring

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionMonicCoefficients_polynomial` under the displayed hypotheses. -/
theorem rootCompletionMonicCoefficients_polynomial (roots : List (ℚ×ℚ)) :
    rootCompletionListPolynomial (rootCompletionMonicCoefficients roots)=
      (roots.map (fun rho => X-C (rootRationalCoordinate rho))).prod := by
  rw [rootCompletionMonicCoefficients,rootCompletionRootsFold_polynomial]
  have h : rootCompletionListPolynomial [(1,0)]=1 := by
    have hone : rootRationalCoordinate (1,0)=1 := by
      apply Complex.ext <;> simp [rootRationalCoordinate]
    simp [rootCompletionListPolynomial,rootCompletionStatePolynomial,
      Polynomial.ofFn_eq_sum_monomial,hone]
  rw [h,one_mul]

/-- The same emitted instruction list satisfies `rootCompletionRootsFold_length` with the displayed gate and query accounting. -/
private theorem rootCompletionRootsFold_length (roots a : List (ℚ×ℚ)) :
    (roots.foldl (fun a rho => rootCompletionLinearList rho a) a).length=
      a.length+roots.length := by
  induction roots generalizing a with
  | nil => simp
  | cons rho roots ih =>
    rw [List.foldl_cons,ih,rootCompletionLinearList_length,List.length_cons]
    omega

/-- The same emitted instruction list satisfies `rootCompletionMonicCoefficients_length` with the displayed gate and query accounting. -/
theorem rootCompletionMonicCoefficients_length (roots : List (ℚ×ℚ)) :
    (rootCompletionMonicCoefficients roots).length=roots.length+1 := by
  rw [rootCompletionMonicCoefficients,rootCompletionRootsFold_length]
  simp [Nat.add_comm]

/-- The following source loop adds the actual Gaussian coefficient entries. -/
def rootCompletionCoefficientSum (a : List (ℚ×ℚ)) : ℚ×ℚ :=
  a.foldl (fun s c => s+c) (0,0)

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionCoefficientSum_fold` under the displayed hypotheses. -/
private theorem rootCompletionCoefficientSum_fold (a : List (ℚ×ℚ)) (s : ℚ×ℚ) :
    rootRationalCoordinate (a.foldl (fun s c => s+c) s)=
      rootRationalCoordinate s+(a.map rootRationalCoordinate).sum := by
  induction a generalizing s with
  | nil => simp
  | cons c a ih =>
    rw [List.foldl_cons,ih,rootCompletion_decode_add]
    simp only [List.map_cons,List.sum_cons,add_assoc]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionListPolynomial_eval_one` under the displayed hypotheses. -/
theorem rootCompletionListPolynomial_eval_one (a : List (ℚ×ℚ)) :
    (rootCompletionListPolynomial a).eval 1=(a.map rootRationalCoordinate).sum := by
  classical
  have he : (rootCompletionListPolynomial a).eval 1=
      ∑ i : Fin a.length,rootRationalCoordinate (a.get i) := by
    simp [rootCompletionListPolynomial,rootCompletionStatePolynomial,
      Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum]
  have ho : List.ofFn (fun i : Fin a.length => rootRationalCoordinate (a.get i))=
      a.map rootRationalCoordinate := by
    simpa only [List.map_ofFn,Function.comp_def] using
      congrArg (List.map rootRationalCoordinate) (List.ofFn_get a)
  rw [he,← Fin.sum_ofFn,ho]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionCoefficientSum_decode` under the displayed hypotheses. -/
theorem rootCompletionCoefficientSum_decode (a : List (ℚ×ℚ)) :
    rootRationalCoordinate (rootCompletionCoefficientSum a)=
      (rootCompletionListPolynomial a).eval 1 := by
  rw [rootCompletionCoefficientSum,rootCompletionCoefficientSum_fold,
    rootCompletion_decode_zero,zero_add,rootCompletionListPolynomial_eval_one]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionMonicCoefficients_eval` under the displayed hypotheses. -/
theorem rootCompletionMonicCoefficients_eval (roots : List (ℚ×ℚ)) (z : ℂ) :
    (rootCompletionListPolynomial (rootCompletionMonicCoefficients roots)).eval z=
      (roots.map (fun rho => z-rootRationalCoordinate rho)).prod := by
  rw [rootCompletionMonicCoefficients_polynomial,Polynomial.eval_list_prod]
  simp only [List.map_map,Function.comp_def,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_C]

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionUnitProduct_ne_zero` under the displayed hypotheses. -/
private theorem rootCompletionUnitProduct_ne_zero (roots : List (ℚ×ℚ)) :
    (∀ q∈roots,‖rootRationalCoordinate q‖<1) →
      (roots.map (fun q => 1-rootRationalCoordinate q)).prod≠0 := by
  induction roots with
  | nil => intro _; simp
  | cons q roots ih =>
    intro hinside
    rw [List.map_cons,List.prod_cons]
    apply mul_ne_zero
    · intro he
      have hq := hinside q (by simp)
      have hv : rootRationalCoordinate q=1 := (sub_eq_zero.mp he).symm
      rw [hv,norm_one] at hq
      exact (lt_irrefl 1) hq
    · exact ih (fun r hr => hinside r (List.mem_cons_of_mem q hr))

/-- Nonzero normalization denominator from the actual inside points, without
an externally supplied radial gap or final approximation answer. -/
theorem rootCompletionMonicCoefficients_sum_norm2_pos (roots : List (ℚ×ℚ))
    (hinside : ∀ q∈roots,‖rootRationalCoordinate q‖<1) :
    let g1 := rootCompletionCoefficientSum (rootCompletionMonicCoefficients roots)
    0<g1.1^2+g1.2^2 := by
  dsimp only
  have hv : rootRationalCoordinate
      (rootCompletionCoefficientSum (rootCompletionMonicCoefficients roots))≠0 := by
    rw [rootCompletionCoefficientSum_decode,rootCompletionMonicCoefficients_eval]
    exact rootCompletionUnitProduct_ne_zero roots hinside
  have hn := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [rootRationalCoordinate_sq_norm] at hn
  exact_mod_cast hn

/-- The finite construction in `NativeRootCompletionMonic` satisfies `rootCompletionPair_inside` under the displayed hypotheses. -/
private theorem rootCompletionPair_inside {qs : List (ℚ×ℚ)} {zs : List ℂ} {eta : ℚ}
    (h : List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
      ‖rootRationalCoordinate q-z‖≤(eta : ℝ)) qs zs) :
    ∀ q∈qs,‖rootRationalCoordinate q‖<1 := by
  induction h with
  | nil => simp
  | cons hhead htail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with he|he
    · subst q; exact hhead.1
    · exact ih q he

/-- Same original target and raw certificate guards, actual coefficient loop
and sum, complete ideal inside list, and the REAL positive source g1 norm2.
This is the typed root-to-monic input bridge, not full phase/error/runtime. -/
theorem rootDecodedCertificate_completion_normalizer (m : ℕ) (target : List ℤ)
    (content : ℤ) (f : Fin m → RootIntegerFactorData) (eta : ℚ)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients target)
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) eta) :
    ∃ zs : List ℂ,
      (zs : Multiset ℂ)=(rootIntegerListPolynomial target).roots.filter (fun z => ‖z‖<1) ∧
      List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
        ‖rootRationalCoordinate q-z‖≤(eta : ℝ)) (rootDecodedReturnList f eta) zs ∧
      (rootCompletionMonicCoefficients (rootDecodedReturnList f eta)).length=zs.length+1 ∧
      let g1 := rootCompletionCoefficientSum
        (rootCompletionMonicCoefficients (rootDecodedReturnList f eta))
      0<g1.1^2+g1.2^2 := by
  obtain ⟨zs,hm,hpair⟩ :=
    rootDecodedCertificate_returned m target content f eta hcontent hguard haccepted
  refine ⟨zs,hm,hpair,?_,?_⟩
  · rw [rootCompletionMonicCoefficients_length,hpair.length_eq]
  · exact rootCompletionMonicCoefficients_sum_norm2_pos _ (rootCompletionPair_inside hpair)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
