/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceRegularization
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeChebyshevCertificate
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input CFD source bridge: RoundingBound.
The nonconstant branch uses the computed surviving degree.
This module does not certify spectral completion, deflation, interpreter refinement or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open scoped BigOperators

/-- Construction for source Weight in the native source rounding bound model. -/
def sourceWeight {N : ℕ} (j : Fin (N+1)) : ℚ := if j.val=0 then 1 else 2

/-- Construction for source Output Coefficient in the native source rounding bound model. -/
def sourceOutputCoefficient (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (N+1)) : ℚ :=
  sourceWeight j*sourceCoefficient cs N E j

/-- Construction for source Rounding Mass in the native source rounding bound model. -/
def sourceRoundingMass (cs : List ℚ) (N : ℕ) (E : ℚ) : ℚ :=
  ∑ j : Fin (N+1),|sourceOutputCoefficient cs N E j-
    (1-sourceInputU cs N E/8)*cs.getD j.val 0|

/-- The finite construction in `NativeSourceRoundingBound` satisfies `sourceWeight_pos` under the displayed hypotheses. -/
theorem sourceWeight_pos {N : ℕ} (j : Fin (N+1)) : 0<sourceWeight j := by
  unfold sourceWeight
  split_ifs <;> norm_num

/-- The estimate `sourceCoefficient_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceCoefficient_error (cs : List ℚ) (N : ℕ) (E : ℚ) (j : Fin (N+1)) :
    |sourceOutputCoefficient cs N E j-(1-sourceInputU cs N E/8)*cs.getD j.val 0|<
      sourceWeight j*sourceGrid N (sourceInputU cs N E) := by
  let w := sourceWeight j
  let s := 1-sourceInputU cs N E/8
  let c := cs.getD j.val 0
  let h := sourceGrid N (sourceInputU cs N E)
  have hw : 0<w := sourceWeight_pos j
  have he : w*rootGridTruncate (s*c/w) h-s*c=
      w*(rootGridTruncate (s*c/w) h-s*c/w) := by
    field_simp [ne_of_gt hw]
  change |w*rootGridTruncate (s*c/w) h-s*c|<w*h
  rw [he,abs_mul,abs_of_pos hw]
  exact mul_lt_mul_of_pos_left
    (rootGridTruncate_spec (s*c/w) h (sourceGrid_pos N (sourceInputU cs N E))).2 hw

/-- The finite construction in `NativeSourceRoundingBound` satisfies `sourceWeight_sum` under the displayed hypotheses. -/
theorem sourceWeight_sum (N : ℕ) :
    (∑ j : Fin (N+1),sourceWeight j)=2*(N : ℚ)+1 := by
  rw [Fin.sum_univ_succ]
  have h0 : sourceWeight (0 : Fin (N+1))=1 := by simp [sourceWeight]
  have hs : ∀ j : Fin N,sourceWeight j.succ=2 := by intro j; simp [sourceWeight]
  simp only [h0,hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The finite construction in `NativeSourceRoundingBound` satisfies `sourceRoundingMass_lt` under the displayed hypotheses. -/
theorem sourceRoundingMass_lt (cs : List ℚ) (N : ℕ) (E : ℚ) :
    sourceRoundingMass cs N E < (2*(N : ℚ)+1)*sourceGrid N (sourceInputU cs N E) := by
  have hs : (∑ j : Fin (N+1),|sourceOutputCoefficient cs N E j-
      (1-sourceInputU cs N E/8)*cs.getD j.val 0|)<
      ∑ j : Fin (N+1),sourceWeight j*sourceGrid N (sourceInputU cs N E) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact (sourceCoefficient_error cs N E j).le
    · exact ⟨0,Finset.mem_univ _,sourceCoefficient_error cs N E 0⟩
  rw [← Finset.sum_mul,sourceWeight_sum] at hs
  exact hs

/-- The finite construction in `NativeSourceRoundingBound` satisfies `sourceRoundingMass_small` under the displayed hypotheses. -/
theorem sourceRoundingMass_small (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E) :
    sourceRoundingMass cs N E ≤ sourceInputU cs N E/32 := by
  let u := sourceInputU cs N E
  have hu : 0<u := sourceInputU_pos cs N E hE
  have hg := sourceGrid_upper N u hu
  calc
    _ ≤ (2*(N : ℚ)+1)*sourceGrid N u := (sourceRoundingMass_lt cs N E).le
    _ ≤ (2*(N : ℚ)+1)*(u/(64*(N+1 : ℚ))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = ((2*(N : ℚ)+1)*u)/(64*(N+1 : ℚ)) := by ring
    _ ≤ u/32 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℚ)<32)).mpr
      nlinarith


/-- Construction for source Output List in the native source rounding bound model. -/
def sourceOutputList (cs : List ℚ) (N : ℕ) (E : ℚ) : List ℚ :=
  List.ofFn (sourceOutputCoefficient cs N E)

/-- Construction for source Padded List in the native source rounding bound model. -/
def sourcePaddedList (cs : List ℚ) (N : ℕ) : List ℚ :=
  List.ofFn (fun j : Fin (N+1) => cs.getD j.val 0)

/-- Construction for source Error List in the native source rounding bound model. -/
def sourceErrorList (cs : List ℚ) (N : ℕ) (E : ℚ) : List ℚ :=
  List.ofFn (fun j : Fin (N+1) => sourceOutputCoefficient cs N E j-
    (1-sourceInputU cs N E/8)*cs.getD j.val 0)

/-- The finite construction in `NativeSourceRoundingBound` satisfies `cheb_zero` under the displayed hypotheses. -/
private theorem cheb_zero (cs : List ℚ) : ∀ j,
    (∀ k,cs.getD k 0=0) → nativeChebyshevPolynomialFrom j cs=0 := by
  induction cs with
  | nil => intro j _; rfl
  | cons c cs ih =>
    intro j h
    have hc : c=0 := by simpa using h 0
    have ht : ∀ k,cs.getD k 0=0 := by intro k; simpa using h (k+1)
    simp only [nativeChebyshevPolynomialFrom,hc,Rat.cast_zero,Polynomial.C_0,
      zero_mul,zero_add]
    exact ih (j+1) ht

/-- The finite construction in `NativeSourceRoundingBound` satisfies `cheb_getD_eq` under the displayed hypotheses. -/
private theorem cheb_getD_eq (xs : List ℚ) : ∀ ys j,
    (∀ k,xs.getD k 0=ys.getD k 0) →
    nativeChebyshevPolynomialFrom j xs=nativeChebyshevPolynomialFrom j ys := by
  induction xs with
  | nil =>
    intro ys j h
    change 0=nativeChebyshevPolynomialFrom j ys
    symm
    apply cheb_zero
    intro k
    simpa using (h k).symm
  | cons c cs ih =>
    intro ys j h
    cases ys with
    | nil =>
      change nativeChebyshevPolynomialFrom j (c::cs)=0
      apply cheb_zero
      intro k
      simpa using h k
    | cons d ds =>
      have hc : c=d := by simpa using h 0
      have ht : ∀ k,cs.getD k 0=ds.getD k 0 := by intro k; simpa using h (k+1)
      simp only [nativeChebyshevPolynomialFrom,hc,ih ds (j+1) ht]

/-- The finite construction in `NativeSourceRoundingBound` satisfies `cheb_ofFn` under the displayed hypotheses. -/
private theorem cheb_ofFn (m : ℕ) : ∀ (f : Fin m → ℚ) j,
    nativeChebyshevPolynomialFrom j (List.ofFn f)=
      ∑ i : Fin m,Polynomial.C (f i : ℝ)*Polynomial.Chebyshev.T ℝ ((j+i.val : ℕ) : ℤ) := by
  induction m with
  | zero => intro f j; simp [nativeChebyshevPolynomialFrom]
  | succ m ih =>
    intro f j
    rw [List.ofFn_succ,nativeChebyshevPolynomialFrom,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he : j+1+i.val=j+(i.val+1) := by omega
    rw [he]

/-- The finite construction in `NativeSourceRoundingBound` satisfies `sourcePadded_polynomial` under the displayed hypotheses. -/
private theorem sourcePadded_polynomial (cs : List ℚ) (N : ℕ)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0) (j : ℕ) :
    nativeChebyshevPolynomialFrom j (sourcePaddedList cs N)=nativeChebyshevPolynomialFrom j cs := by
  apply cheb_getD_eq
  intro k
  unfold sourcePaddedList
  by_cases hk : k<N+1
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hk,Option.getD_some]
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right hk,Option.getD_none]
    exact (htail k (Nat.le_of_not_gt hk)).symm

/-- The estimate `sourceError_polynomial` retains the actual parameter, input-error and normalization budgets. -/
private theorem sourceError_polynomial (cs : List ℚ) (N : ℕ) (E : ℚ) :
    nativeChebyshevPolynomialFrom 0 (sourceErrorList cs N E)=
      nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)-
      Polynomial.C ((1-sourceInputU cs N E/8 : ℚ) : ℝ)*
        nativeChebyshevPolynomialFrom 0 (sourcePaddedList cs N) := by
  unfold sourceErrorList sourceOutputList sourcePaddedList
  rw [cheb_ofFn,cheb_ofFn,cheb_ofFn,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Rat.cast_sub,Rat.cast_mul,Polynomial.C_sub,Polynomial.C_mul]
  ring

/-- The estimate `sourceError_mass` retains the actual parameter, input-error and normalization budgets. -/
private theorem sourceError_mass (cs : List ℚ) (N : ℕ) (E : ℚ) :
    nativeChebyshevMass (sourceErrorList cs N E)=sourceRoundingMass cs N E := by
  unfold nativeChebyshevMass sourceErrorList
  rw [List.map_ofFn,Fin.sum_ofFn]
  rfl

/-- Error against the ORIGINAL complete target, using its exact-zero tail
check. No coefficient l1 promise is required. -/
theorem sourceOutput_error (cs : List ℚ) (N : ℕ) (E : ℚ)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0) (x : ℝ) (hx : x∈Set.Icc (-1 : ℝ) 1) :
    |(nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x-
      ((1-sourceInputU cs N E/8 : ℚ) : ℝ)*(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤
      (sourceRoundingMass cs N E : ℝ) := by
  have h := nativeChebyshevPolynomialFrom_eval_bound 0 (sourceErrorList cs N E) x hx
  rw [sourceError_polynomial,sourcePadded_polynomial cs N htail 0] at h
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,sourceError_mass] at h
  exact h

/-- Actual regularized polynomial has the source's strict gap, derived from
its ORIGINAL interval supnorm promise, raw data and computed rounding. -/
theorem sourceOutput_uniform_gap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x| ≤
        1-3*(sourceInputU cs N E : ℝ)/32 := by
  let u := sourceInputU cs N E
  have hu : (u : ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (sourceInputU_le_half cs N E)
  have hs : 0 ≤ 1-(u : ℝ)/8 := by linarith
  have hm : (sourceRoundingMass cs N E : ℝ) ≤ (u : ℝ)/32 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (sourceRoundingMass_small cs N E hE)
  intro x hx
  have he : |(nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x-
      (1-(u : ℝ)/8)*(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤
      (sourceRoundingMass cs N E : ℝ) := by
    simpa only [Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using
      sourceOutput_error cs N E htail x hx
  have hp : |(1-(u : ℝ)/8)*(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1-(u : ℝ)/8 := by
    rw [abs_mul,abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left (hnorm x hx) hs).trans_eq (mul_one _)
  calc
    _ = |((nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval x-
        (1-(u : ℝ)/8)*(nativeChebyshevPolynomialFrom 0 cs).eval x)+
        (1-(u : ℝ)/8)*(nativeChebyshevPolynomialFrom 0 cs).eval x| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (sourceRoundingMass cs N E : ℝ)+(1-(u : ℝ)/8) := add_le_add he hp
    _ ≤ 1-3*(u : ℝ)/32 := by linarith


/-- Same actual output on cosine points, ready for the unit-circle P identity. -/
theorem sourceOutput_cos (cs : List ℚ) (N : ℕ) (E : ℚ) (theta : ℝ) :
    (nativeChebyshevPolynomialFrom 0 (sourceOutputList cs N E)).eval (Real.cos theta)=
      ∑ j : Fin (N+1),(sourceOutputCoefficient cs N E j : ℝ)*
        Real.cos ((j.val : ℝ)*theta) := by
  unfold sourceOutputList
  rw [cheb_ofFn,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Nat.zero_add,
    Polynomial.Chebyshev.T_real_cos,Int.cast_natCast]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
