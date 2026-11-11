/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterPrefixCounting

/-!
# Left generators of exponential words

This module defines `pfLeftGenerator` for a product of matrix exponentials and proves its
smoothness and derivative identity. The generator is expressed as a sum of prefix-conjugated
terms, giving the algebraic defect used in the error analysis of [ChildsEtAl2021Trotter].

The word is invertible at every real time, so its differential defect transported by the inverse
equals `pfLeftGenerator xs t - H`. Matching coefficients through any positive order also
identifies `H` with the sum of the word generators.

## Main statements

* `pf_word_hasDerivAt_left_generator`: expresses the derivative using the left generator.
* `pf_actual_left_defect`: identifies the transported differential defect.
* `pfLeftGenerator_prefix_sum`: expands the generator over prefixes.
* `pf_matched_generator_sum`: recovers the target generator from coefficient matching.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The left generator of an exponential product, recursively summing each head generator with
the conjugated generator of its tail. -/
def pfLeftGenerator : List (Matrix I I ℂ)→ℝ→Matrix I I ℂ
  | [],_ => 0
  | X::xs,t => X+pfConjExp X (pfLeftGenerator xs t) t

/-- The left-generator function is smooth in real time. -/
theorem pfLeftGenerator_contDiff (xs : List (Matrix I I ℂ)) : ContDiff ℝ ∞ (pfLeftGenerator xs) := by
  induction xs with
  | nil => exact contDiff_const
  | cons X xs ih =>
    have hn := (trotter_exp_contDiff X).comp contDiff_id.neg
    simpa only [pfLeftGenerator,pfConjExp,Function.comp_def] using!
      contDiff_const.add (((trotter_exp_contDiff X).mul ih).mul hn)

/-- The exponential word has derivative given by its left generator multiplied on the left of
the word. -/
theorem pf_word_hasDerivAt_left_generator (xs : List (Matrix I I ℂ)) (t : ℝ) :
    HasDerivAt (suzukiExponentialWord xs) (pfLeftGenerator xs t*suzukiExponentialWord xs t) t := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  induction xs with
  | nil => simpa only [suzukiExponentialWord,List.map_nil,List.prod_nil,pfLeftGenerator,zero_mul] using! hasDerivAt_const t (1 : Matrix I I ℂ)
  | cons X xs ih =>
    have hd := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul ih
    have hc : NormedSpace.exp ((-t) • X)*NormedSpace.exp (t • X)=1 := by
      rw [neg_smul,← NormedSpace.exp_add_of_commute ((Commute.refl (t • X)).neg_left),neg_add_cancel,NormedSpace.exp_zero]
    have hs :
        suzukiExponentialWord
        (X::xs)=(fun u=>NormedSpace.exp (u • X)*suzukiExponentialWord xs u) := rfl
    rw [hs]
    convert! hd using 1
    dsimp only [pfLeftGenerator,pfConjExp]
    calc (X+NormedSpace.exp (t • X)*pfLeftGenerator xs t*NormedSpace.exp ((-t) • X))*
          (NormedSpace.exp (t • X)*suzukiExponentialWord xs t)=
          (X*NormedSpace.exp (t • X))*suzukiExponentialWord xs t+
          NormedSpace.exp (t • X)*pfLeftGenerator xs t*
            (NormedSpace.exp ((-t) • X)*NormedSpace.exp (t • X))*suzukiExponentialWord xs t := by noncomm_ring
         _=(X*NormedSpace.exp (t • X))*suzukiExponentialWord xs t+
           NormedSpace.exp (t • X)*(pfLeftGenerator xs t*suzukiExponentialWord xs t) := by rw [hc];simp only [mul_one,mul_assoc]

/-- The degree-one coefficient of the exponential word equals the sum of its generators. -/
theorem pf_word_series_one (xs : List (Matrix I I ℂ)) : suzukiSeries xs 1=xs.sum := by
  induction xs with
  | nil => rfl
  | cons X xs ih => rw [suzukiSeries_cons_one,ih,List.sum_cons,add_comm]

/-- The exponential word is a unit at every real time. -/
theorem pf_word_isUnit (xs : List (Matrix I I ℂ)) (t : ℝ) : IsUnit (suzukiExponentialWord xs t) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  apply List.prod_isUnit
  intro Y hY
  obtain ⟨X,_hX,rfl⟩ := List.mem_map.mp hY
  exact NormedSpace.isUnit_exp (t • X)

/-- Right multiplication of the differential defect by the inverse word yields the
left-generator defect `pfLeftGenerator xs t - H`. -/
theorem pf_actual_left_defect (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (t : ℝ) :
    (deriv (suzukiExponentialWord xs) t-H*suzukiExponentialWord xs t)*
      Ring.inverse (suzukiExponentialWord xs t)=pfLeftGenerator xs t-H := by
  rw [(pf_word_hasDerivAt_left_generator xs t).deriv,← sub_mul,mul_assoc,
    Ring.mul_inverse_cancel _ (pf_word_isUnit xs t),mul_one]

/-- The left generator equals the sum of each generator conjugated by the word of its preceding
prefix. -/
theorem pfLeftGenerator_prefix_sum (xs : List (Matrix I I ℂ)) (t : ℝ) :
    pfLeftGenerator xs t=∑ j : Fin xs.length,pfConjWord (xs.take j.val) (xs.getD j.val 0) t := by
  induction xs with
  | nil => simp [pfLeftGenerator]
  | cons X xs ih =>
    rw [pfLeftGenerator]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,List.take_zero,List.take_succ_cons,
      List.getD_cons_zero,List.getD_cons_succ,pfConjWord]
    rw [ih]
    change X+(pfConjExpLinear X t) (∑ j : Fin xs.length,pfConjWord (xs.take j.val) (xs.getD j.val 0) t)=
      X+∑ j : Fin xs.length,(pfConjExpLinear X t) (pfConjWord (xs.take j.val) (xs.getD j.val 0) t)
    rw [map_sum]

/-- Matching exponential coefficients through a positive order forces the generator sum to equal
`H`. -/
theorem pf_matched_generator_sum (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ)
    (hp : 1≤p) (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n) : xs.sum=H := by
  have hh := hc 1 hp
  rw [pf_word_series_one] at hh
  simpa using! hh

end Qatlib.Concepts.TrotterFormula.GeneralOrder
