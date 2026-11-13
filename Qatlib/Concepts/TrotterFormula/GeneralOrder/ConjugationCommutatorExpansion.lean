/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.CommutatorTaylorTools
import Qatlib.Concepts.TrotterFormula.GeneralOrder.NestedCommutatorScaling

/-!
# Exponential conjugation and iterated commutators

The operations `pfAdPower` and `pfConjExp` describe iterated commutation and conjugation by a
matrix exponential. Derivatives of the conjugation are conjugated iterated commutators, giving
factorial Taylor remainder bounds with an exponential factor in general and no such factor for
skew-Hermitian generators. For background, see [ChildsEtAl2021Trotter].

## Main statements

* `pfConjExp_iteratedDeriv`: derivative formula in terms of iterated commutators.
* `pf_conjugation_single_skew`: Taylor remainder bound for skew-Hermitian conjugation.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Set Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The result of applying `C ↦ pfComm X C` to `B` exactly `n` times. -/
def pfAdPower (X B : Matrix I I ℂ) (n : ℕ) : Matrix I I ℂ := (fun C=>pfComm X C)^[n] B

/-- The exponential conjugation `exp (t • X) * B * exp ((-t) • X)`. -/
def pfConjExp (X B : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp (t • X)*B*NormedSpace.exp ((-t) • X)

omit [DecidableEq I] in

/-- Iterating commutation zero times returns the original matrix. -/
@[simp] theorem pfAdPower_zero (X B : Matrix I I ℂ) : pfAdPower X B 0=B := rfl
omit [DecidableEq I] in

/-- One further commutator with `X` gives the successor iterated commutator. -/
@[simp] theorem pfAdPower_succ (X B : Matrix I I ℂ) (n : ℕ) :
    pfAdPower X B (n+1)=pfComm X (pfAdPower X B n) := Function.iterate_succ_apply' _ _ _

/-- The norm of `exp (t • X)` is at most `exp (|t| * ‖X‖)`. -/
theorem pf_matrix_exp_norm_le (X : Matrix I I ℂ) (t : ℝ) :
    ‖NormedSpace.exp (t • X)‖≤Real.exp (|t| *‖X‖) := by
  have hh := general_trotter_taylor_tail [X] t 0
  simpa [suzukiExponentialWord,suzukiMass] using! hh

/-- Exponential conjugation is infinitely differentiable in the real time parameter. -/
theorem pfConjExp_contDiff (X B : Matrix I I ℂ) : ContDiff ℝ ∞ (pfConjExp X B) := by
  have hn := (trotter_exp_contDiff X).comp contDiff_id.neg
  simpa only [pfConjExp,Function.comp_def] using!
      ((trotter_exp_contDiff X).mul contDiff_const).mul hn

/-- The derivative of exponential conjugation of `B` is the exponential conjugation of `pfComm X
B`. -/
theorem pfConjExp_hasDerivAt (X B : Matrix I I ℂ) (t : ℝ) :
    HasDerivAt (pfConjExp X B) (pfConjExp X (pfComm X B) t) t := by
  have hn : HasDerivAt (fun u : ℝ=>NormedSpace.exp ((-u) • X)) (-(X*NormedSpace.exp ((-t) • X))) t := by
    convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-t)).scomp t (hasDerivAt_id t).neg using 1
    simp
  convert! ((hasDerivAt_exp_smul_const X t).mul_const B).mul hn using 1
  simp only [pfConjExp,pfComm]
  noncomm_ring

/-- The `n`th derivative of exponential conjugation is the conjugation of `pfAdPower X B n`. -/
theorem pfConjExp_iteratedDeriv (X B : Matrix I I ℂ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (pfConjExp X B) t=pfConjExp X (pfAdPower X B n) t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    have he : iteratedDeriv n (pfConjExp X B)=pfConjExp X (pfAdPower X B n) := funext ih
    rw [iteratedDeriv_succ,he,(pfConjExp_hasDerivAt X (pfAdPower X B n) t).deriv,pfAdPower_succ]

/-- Exponential conjugation has norm at most `‖B‖ * exp (2 * |t| * ‖X‖)`. -/
theorem pfConjExp_norm_general (X B : Matrix I I ℂ) (t : ℝ) :
    ‖pfConjExp X B t‖≤‖B‖*Real.exp (2*|t| *‖X‖) := by
  calc _≤‖NormedSpace.exp (t • X)‖*‖B‖*‖NormedSpace.exp ((-t) • X)‖ :=
         (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
       _≤Real.exp (|t| *‖X‖)*‖B‖*Real.exp (|t| *‖X‖) := by
         gcongr
         · exact pf_matrix_exp_norm_le X t
         · simpa only [abs_neg] using! pf_matrix_exp_norm_le X (-t)
       _=‖B‖*Real.exp (2*|t| *‖X‖) := by rw [show 2*|t| *‖X‖=|t| *‖X‖+|t| *‖X‖ by ring,Real.exp_add];ring

/-- For skew-Hermitian `X`, exponential conjugation has norm at most `‖B‖`. -/
theorem pfConjExp_norm_skew (X B : Matrix I I ℂ) (t : ℝ) (hX : Xᴴ=-X) :
    ‖pfConjExp X B t‖≤‖B‖ := by
  calc _≤‖NormedSpace.exp (t • X)‖*‖B‖*‖NormedSpace.exp ((-t) • X)‖ :=
         (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
       _≤1*‖B‖*1 := by
         gcongr
         · exact l2_norm_unitary_le_one (general_trotter_exp_unitary X t hX)
         · exact l2_norm_unitary_le_one (general_trotter_exp_unitary X (-t) hX)
       _=‖B‖ := by ring

/-- Every real number between zero and `t` has absolute value at most `|t|`. -/
private theorem abs_le_of_mem_zero_uIcc (t u : ℝ) (hu : u∈uIcc 0 t) : |u|≤|t| := by
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht] at hu
    rw [abs_of_nonneg hu.1,abs_of_nonneg ht]
    exact hu.2
  · rw [uIcc_of_ge ht] at hu
    rw [abs_of_nonpos hu.2,abs_of_nonpos ht]
    linarith [hu.1]

/-- The Taylor remainder below degree `p` is bounded by `‖pfAdPower X B p‖ * |t| ^ p / p!` times
`exp (2 * |t| * ‖X‖)`. -/
theorem pf_conjugation_single_general (X B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    ‖pfConjExp X B t-pfTaylorBefore (pfConjExp X B) p t‖≤
      ‖pfAdPower X B p‖*|t| ^p/(p.factorial:ℝ)*Real.exp (2*|t| *‖X‖) := by
  have hh := pf_taylor_before_norm_bound (pfConjExp X B) (pfConjExp_contDiff X B) p t
    (‖pfAdPower X B p‖*Real.exp (2*|t| *‖X‖)) (by positivity) (by
      intro u hu
      rw [pfConjExp_iteratedDeriv]
      apply (pfConjExp_norm_general X (pfAdPower X B p) u).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_le_of_mem_zero_uIcc t u hu) (by norm_num))
          (norm_nonneg _))
  exact hh.trans_eq (by ring)

/-- For skew-Hermitian `X`, the Taylor remainder below degree `p` is bounded by `‖pfAdPower X B
p‖ * |t| ^ p / p!`. -/
theorem pf_conjugation_single_skew (X B : Matrix I I ℂ) (p : ℕ) (t : ℝ) (hX : Xᴴ=-X) :
    ‖pfConjExp X B t-pfTaylorBefore (pfConjExp X B) p t‖≤‖pfAdPower X B p‖*|t| ^p/(p.factorial:ℝ) := by
  apply pf_taylor_before_norm_bound _ (pfConjExp_contDiff X B) p t _ (norm_nonneg _)
  intro u _
  rw [pfConjExp_iteratedDeriv]
  exact pfConjExp_norm_skew X _ u hX
end Qatlib.Concepts.TrotterFormula.GeneralOrder
