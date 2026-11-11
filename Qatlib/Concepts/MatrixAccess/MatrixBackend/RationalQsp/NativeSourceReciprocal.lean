/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceCompletionAccuracy
import Mathlib.Algebra.Polynomial.Reverse
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Actual original-input H: reciprocal roots, multiplicity and source guards.
This does not certify the full proposer, interpreter, spectral deflation or fees. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Polynomial

/-- The estimate `sourceInputP_degree_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceInputP_degree_bound (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceInputP cs N E).natDegree ≤ sourceDegree cs N E := by
  unfold sourceInputP
  have h := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ sourceDegree cs N E+1)
    (sourceP (sourceLiftedArray cs N E))
  omega

/-- The finite construction in `NativeSourceReciprocal` satisfies `sourceInputP_reflect` under the displayed hypotheses. -/
theorem sourceInputP_reflect (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceInputP cs N E).reflect (sourceDegree cs N E)=sourceInputP cs N E := by
  let d := sourceDegree cs N E
  unfold sourceInputP
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_reflect]
  by_cases hi : i ≤ d
  · rw [Polynomial.revAt_le hi,
      Polynomial.ofFn_coeff_eq_val_of_lt _ (show d-i<d+1 by omega),
      Polynomial.ofFn_coeff_eq_val_of_lt _ (show i<d+1 by omega)]
    unfold sourceP sourceLiftedArray
    congr 1
    apply Fin.ext
    change Nat.dist (2*(d-i)) d=Nat.dist (2*i) d
    simp only [Nat.dist]
    omega
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]

/-- The finite construction in `NativeSourceReciprocal` satisfies `sourceF_reflect` under the displayed hypotheses. -/
theorem sourceF_reflect (cs : List ℚ) (N : ℕ) (E : ℚ) :
    (sourceF cs N E).reflect (2*sourceDegree cs N E)=sourceF cs N E := by
  unfold sourceF
  rw [Polynomial.reflect_map,Polynomial.reflect_sub,pow_two,
    show 2*sourceDegree cs N E=sourceDegree cs N E+sourceDegree cs N E by omega,
    Polynomial.reflect_mul _ _ (sourceInputP_degree_bound cs N E)
      (sourceInputP_degree_bound cs N E),sourceInputP_reflect,
    Polynomial.reflect_monomial,Polynomial.revAt_le (by omega :
      sourceDegree cs N E ≤ sourceDegree cs N E+sourceDegree cs N E),
    Nat.add_sub_cancel_left]

/-- The finite construction in `NativeSourceReciprocal` satisfies `sourceIntegerComplement_inverse_zero` under the displayed hypotheses. -/
theorem sourceIntegerComplement_inverse_zero (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E) (rho : ℂ) (hrho : rho≠0) :
    (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval (rho⁻¹)=0 ↔
      (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval rho=0 := by
  rw [sourceIntegerComplement_eval_zero_iff cs N E hparity hd,
    sourceIntegerComplement_eval_zero_iff cs N E hparity hd]
  letI : Invertible rho := invertibleOfNonzero hrho
  have h := Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℂ) rho
    (2*sourceDegree cs N E) (sourceF cs N E) (sourceF_natDegree_le cs N E)
  rw [sourceF_reflect] at h
  simpa only [invOf_eq_inv,Polynomial.eval₂_id, sourceF] using h

/-- The finite construction in `NativeSourceReciprocal` satisfies `sourceIntegerComplement_outside_gap` under the displayed hypotheses. -/
theorem sourceIntegerComplement_outside_gap (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (rho : ℂ) (hrho : 1<‖rho‖)
    (hroot : (rootIntegerListPolynomial (sourceIntegerComplement cs N E)).eval rho=0) :
    1+(sourceGamma0 cs N E : ℝ) ≤ ‖rho‖ := by
  have hrpos : 0<‖rho‖ := lt_trans (by norm_num) hrho
  have hrne : rho≠0 := norm_pos_iff.mp hrpos
  have hinv : ‖rho⁻¹‖<1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hrho
  have hzero := (sourceIntegerComplement_inverse_zero cs N E hparity hd rho hrne).mpr hroot
  have hgap := sourceIntegerComplement_inside_gap cs N E hE htail hparity hd hnorm
    (rho⁻¹) hinv hzero
  rw [norm_inv,inv_eq_one_div] at hgap
  have hm := (div_le_iff₀ hrpos).mp hgap
  have hg : (0 : ℝ) ≤ (sourceGamma0 cs N E : ℝ) := by
    exact_mod_cast (sourceGamma0_pos cs N E hE hd).le
  have hgain := le_mul_of_one_le_right hg hrho.le
  nlinarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
