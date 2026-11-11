/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeRootCompletionMonic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Next accuracy bridge for the ACTUAL monic coefficient loop. Uses existing
Mathlib finite-product and exponential inequalities. Ideal-root matching and
gaps here are helper premises, to be derived in the same raw-input consumer.
This is not a new main algorithm taking final response errors as answers. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open scoped BigOperators

/-- The finite construction in `NativeRootCompletionProductBound` satisfies `rootCompletion_product_defect` under the displayed hypotheses. -/
private theorem rootCompletion_product_defect {n : ℕ} (u : Fin n → ℂ) (s : ℝ)
    (hsum : (Finset.univ.sum (fun i : Fin n => norm (u i))) ≤ s) (hs : s ≤ 1) :
    ‖(∏ i : Fin n, (1+u i))-1‖≤2*s := by
  have hn : 0≤(∑ i, ‖u i‖) := Finset.sum_nonneg (fun i _ => norm_nonneg (u i))
  have hx : |(∑ i, ‖u i‖)|≤1 := by
    rw [abs_of_nonneg hn]
    exact hsum.trans hs
  calc
    _≤Real.exp (∑ i,‖u i‖)-1 := by
      simpa using Finset.norm_prod_one_add_sub_one_le (Finset.univ : Finset (Fin n)) u
    _≤|Real.exp (∑ i,‖u i‖)-1| := le_abs_self _
    _≤2*|(∑ i, ‖u i‖)| := Real.abs_exp_sub_one_le hx
    _≤2*s := by
      rw [abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- Perturbation of the SAME source-generated monic array at a separated
point, allowing coordinate collisions and all multiplicity copies. -/
theorem rootCompletionMonic_relative_bound {n : ℕ} (q : Fin n → ℚ×ℚ)
    (r : Fin n → ℂ) (z : ℂ) (eta gamma : ℝ) (heta : 0≤eta) (hgamma : 0<gamma)
    (hgap : ∀ i,gamma≤‖z-r i‖)
    (herror : ∀ i,‖rootRationalCoordinate (q i)-r i‖≤eta)
    (hcap : (n : ℝ)*eta/gamma≤1) :
    ‖(rootCompletionListPolynomial
        (rootCompletionMonicCoefficients (List.ofFn q))).eval z/
        (∏ i, (z-r i))-1‖≤2*((n : ℝ)*eta/gamma) := by
  let u : Fin n → ℂ := fun i => (r i-rootRationalCoordinate (q i))/(z-r i)
  have hnz (i : Fin n) : z-r i≠0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le hgamma (hgap i))
  have hfactor (i : Fin n) : (z-rootRationalCoordinate (q i))/(z-r i)=1+u i := by
    dsimp only [u]
    field_simp [hnz i]
    ring
  have hnorm (i : Fin n) : ‖u i‖≤eta/gamma := by
    dsimp only [u]
    rw [norm_div,norm_sub_rev (r i) (rootRationalCoordinate (q i))]
    apply (div_le_div_iff₀ (lt_of_lt_of_le hgamma (hgap i)) hgamma).mpr
    exact (mul_le_mul_of_nonneg_right (herror i) hgamma.le).trans
      (mul_le_mul_of_nonneg_left (hgap i) heta)
  have hsum : (∑ i, ‖u i‖)≤(n : ℝ)*eta/gamma := by
    calc
      _≤∑ _i : Fin n, (eta/gamma) := Finset.sum_le_sum (fun i _ => hnorm i)
      _=_ := by simp [mul_div_assoc]
  have hratio : (rootCompletionListPolynomial
        (rootCompletionMonicCoefficients (List.ofFn q))).eval z/(∏ i, (z-r i))=
      ∏ i, (1+u i) := by
    rw [rootCompletionMonicCoefficients_eval,List.map_ofFn,Fin.prod_ofFn,
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact hfactor i
  rw [hratio]
  exact rootCompletion_product_defect u _ hsum hcap

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
