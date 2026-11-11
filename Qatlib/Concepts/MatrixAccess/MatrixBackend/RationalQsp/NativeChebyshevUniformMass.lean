/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeChebyshevCertificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Completeness bound for the actual finite posterior Chebyshev mass.
The whole exact residual is required. This does not assert numerical synthesis
success, construct missing coefficients, or account for producer bit costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Polynomial MeasureTheory
open Polynomial.Chebyshev

/-- The finite construction in `NativeChebyshevUniformMass` satisfies `chebMoment_cons` under the displayed hypotheses. -/
private theorem chebMoment_cons (c : ℚ) (cs : List ℚ) (j k : ℕ) :
    (∫ x, (nativeChebyshevPolynomialFrom j (c::cs)).eval x *
      (T ℝ (k : ℤ)).eval x ∂measureT) =
    (c : ℝ)*(∫ x, (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x ∂measureT) +
    ∫ x, (nativeChebyshevPolynomialFrom (j+1) cs).eval x *
      (T ℝ (k : ℤ)).eval x ∂measureT := by
  simp only [nativeChebyshevPolynomialFrom,eval_add,eval_mul,eval_C,add_mul,mul_assoc]
  rw [integral_add (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)),integral_const_mul]

/-- The finite construction in `NativeChebyshevUniformMass` satisfies `chebMoment_above` under the displayed hypotheses. -/
private theorem chebMoment_above (cs : List ℚ) (j k : ℕ) (h : k<j) :
    (∫ x, (nativeChebyshevPolynomialFrom j cs).eval x *
      (T ℝ (k : ℤ)).eval x ∂measureT)=0 := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    rw [chebMoment_cons,integral_eval_T_real_mul_eval_T_real_measureT_of_ne
      (by omega : j≠k),ih (j+1) (by omega)]
    simp

/-- The finite construction in `NativeChebyshevUniformMass` satisfies `chebMoment_diagonal` under the displayed hypotheses. -/
private theorem chebMoment_diagonal (k : ℕ) :
    (∫ x, (T ℝ (k : ℤ)).eval x * (T ℝ (k : ℤ)).eval x ∂measureT)=
      if k=0 then Real.pi else Real.pi/2 := by
  split_ifs with hk
  · subst k
    exact integral_eval_T_real_mul_self_measureT_zero
  · exact integral_T_real_mul_self_measureT_of_ne_zero hk

/-- The finite construction in `NativeChebyshevUniformMass` satisfies `chebMoment_from` under the displayed hypotheses. -/
private theorem chebMoment_from (cs : List ℚ) (j k : ℕ) (h : j≤k) :
    (∫ x, (nativeChebyshevPolynomialFrom j cs).eval x *
      (T ℝ (k : ℤ)).eval x ∂measureT)=
    ((cs[k-j]?.getD 0 : ℚ) : ℝ)*(if k=0 then Real.pi else Real.pi/2) := by
  induction cs generalizing j with
  | nil => simp [nativeChebyshevPolynomialFrom]
  | cons c cs ih =>
    rw [chebMoment_cons]
    by_cases hj : j=k
    · subst j
      rw [chebMoment_diagonal,chebMoment_above cs (k+1) k (by omega)]
      simp
    · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hj,
        ih (j+1) (by omega)]
      have he : k-j=(k-(j+1))+1 := by omega
      simp [he]

/-- The estimate `chebMoment_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem chebMoment_bound (cs : List ℚ) (u : ℝ)
    (hu : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 cs).eval x|≤u) (k : ℕ) :
    |∫ x, (nativeChebyshevPolynomialFrom 0 cs).eval x *
      (T ℝ (k : ℤ)).eval x ∂measureT|≤u*Real.pi := by
  have hu0 : 0≤u := (abs_nonneg _).trans (hu 0 (by norm_num))
  rw [integral_measureT_eq_integral_cos]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=0) (b:=Real.pi) (C:=u)
    (f:=fun θ => (nativeChebyshevPolynomialFrom 0 cs).eval (Real.cos θ) *
      (T ℝ (k : ℤ)).eval (Real.cos θ)) (by
        intro θ _
        rw [Real.norm_eq_abs,abs_mul]
        have hx : Real.cos θ∈Set.Icc (-1 : ℝ) 1 :=
          ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
        calc
          _ ≤ u*1 := mul_le_mul (hu _ hx) (nativeChebyshev_eval_bound k _ hx)
            (abs_nonneg _) hu0
          _ = u := mul_one _)
  simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos Real.pi_pos] using hb

/-- The finite construction in `NativeChebyshevUniformMass` satisfies `nativeChebyshevCoefficient_of_uniform` under the displayed hypotheses. -/
theorem nativeChebyshevCoefficient_of_uniform (cs : List ℚ) (u : ℝ)
    (hu : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 cs).eval x|≤u) (k : ℕ) :
    |((cs[k]?.getD 0 : ℚ) : ℝ)|≤2*u := by
  have hu0 : 0≤u := (abs_nonneg _).trans (hu 0 (by norm_num))
  have hb := chebMoment_bound cs u hu k
  rw [chebMoment_from cs 0 k (by omega),Nat.sub_zero,abs_mul] at hb
  by_cases hk : k=0
  · subst k
    simp only [ite_true,abs_of_pos Real.pi_pos] at hb
    have h := le_of_mul_le_mul_right hb Real.pi_pos
    linarith
  · simp only [hk,ite_false,abs_of_pos (by positivity : 0<Real.pi/2)] at hb
    apply le_of_mul_le_mul_right (a:=Real.pi) (a0:=Real.pi_pos)
    nlinarith

/-- The finite construction in `NativeChebyshevUniformMass` satisfies `chebMass_cast` under the displayed hypotheses. -/
private theorem chebMass_cast (cs : List ℚ) :
    (nativeChebyshevMass cs : ℝ)=(cs.map (fun q : ℚ => |(q : ℝ)|)).sum := by
  induction cs with
  | nil => simp [nativeChebyshevMass]
  | cons c cs ih =>
    change ((|c|+nativeChebyshevMass cs : ℚ) : ℝ)=_
    push_cast
    simpa only [List.map_cons,List.sum_cons] using congrArg (fun x : ℝ => |(c : ℝ)|+x) ih

/-- A uniform bound for the complete actual residual pays only a linear
coefficient factor. No phase-production success or residual identity is assumed. -/
theorem nativeChebyshevMass_of_uniform (cs : List ℚ) (u : ℝ)
    (hu : ∀ x∈Set.Icc (-1 : ℝ) 1,
      |(nativeChebyshevPolynomialFrom 0 cs).eval x|≤u) :
    (nativeChebyshevMass cs : ℝ)≤2*(cs.length : ℝ)*u := by
  have hs := List.sum_le_card_nsmul (cs.map (fun q : ℚ => |(q : ℝ)|)) (2*u) (by
    intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hc
    have h := nativeChebyshevCoefficient_of_uniform cs u hu k
    simpa only [hk,Option.getD_some] using h)
  rw [←chebMass_cast] at hs
  simpa only [List.length_map,nsmul_eq_mul,mul_assoc,mul_left_comm] using hs

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
