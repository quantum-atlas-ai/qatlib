/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorDuhamel
import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Representations of product-formula error

This module defines the left and right defects `pfWordDefectLeft` and `pfWordDefectRight` of a
matrix exponential word relative to a target generator. Prefix and suffix conjugation sums
express these defects explicitly.

The word has additive, time-ordered, and multiplicative representations, with
`pfWordMultiplicativeField` providing the conjugated defect for the last representation. These
identities formalize finite-dimensional product-formula error representations in the setting of
[ChildsEtAl2021Trotter].

## Main statements

* `pfWordDefectRight_suffix_sum`: the right defect as a suffix conjugation sum minus the
  conjugated target generator.
* `pfWordDefectLeft_prefix_sum`: the left defect as a prefix conjugation sum minus the target
  generator.
* `pf_word_additive_representation`: an integral representation of the approximation error.
* `pf_word_exponentiated_representation`: the word as a time-ordered evolution.
* `pf_word_multiplicative_representation`: factorization into exact evolution and time-ordered
  error evolution.

## References

* [Childs et al., 2021, Theorem 8][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.TrotterFormula.TimeOrdered
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The difference between the left generator `pfLeftGenerator xs τ` of an exponential word and
the target generator `H`. -/
def pfWordDefectLeft (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (τ : ℝ) :
    Matrix I I ℂ := pfLeftGenerator xs τ - H

/-- The left defect conjugated by the exponential word, namely `S⁻¹ * pfWordDefectLeft xs H τ *
S` for `S = suzukiExponentialWord xs τ`. -/
def pfWordDefectRight (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (τ : ℝ) :
    Matrix I I ℂ :=
  Ring.inverse (suzukiExponentialWord xs τ) *
    (pfWordDefectLeft xs H τ * suzukiExponentialWord xs τ)

/-- The left word defect conjugated by the exact evolution as `exp (-τ • H) * pfWordDefectLeft
xs H τ * exp (τ • H)`. -/
def pfWordMultiplicativeField (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (τ : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-τ) • H) * pfWordDefectLeft xs H τ * NormedSpace.exp (τ • H)

/-- Conjugating the left generator by its exponential word gives the sum of the generators
conjugated by the suffix words that follow them. -/
theorem pf_word_right_generator_suffix_sum (xs : List (Matrix I I ℂ)) (t : ℝ) :
    Ring.inverse (suzukiExponentialWord xs t) *
        (pfLeftGenerator xs t * suzukiExponentialWord xs t) =
      ∑ j : Fin xs.length,
        Ring.inverse (suzukiExponentialWord (xs.drop (j.val + 1)) t) *
          xs.getD j.val 0 * suzukiExponentialWord (xs.drop (j.val + 1)) t := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  induction xs with
  | nil => simp [suzukiExponentialWord, pfLeftGenerator]
  | cons X xs ih =>
    have hi : NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X) = 1 := by
      rw [neg_smul, ← NormedSpace.exp_add_of_commute ((Commute.refl (t • X)).neg_left),
        neg_add_cancel, NormedSpace.exp_zero]
    have hx : NormedSpace.exp ((-t) • X) * X * NormedSpace.exp (t • X) = X := by
      rw [((Commute.refl X).smul_left (-t)).exp_left.eq, mul_assoc, hi, mul_one]
    have hs :
        Ring.inverse (suzukiExponentialWord (X :: xs) t) *
            (pfLeftGenerator (X :: xs) t * suzukiExponentialWord (X :: xs) t) =
          Ring.inverse (suzukiExponentialWord xs t) * X * suzukiExponentialWord xs t +
            Ring.inverse (suzukiExponentialWord xs t) *
              (pfLeftGenerator xs t * suzukiExponentialWord xs t) := by
      simp only [suzukiExponentialWord, List.map_cons, List.prod_cons, pfLeftGenerator]
      rw [Ring.inverse_mul (Or.inl (NormedSpace.isUnit_exp (t • X))), Ring.inverse_exp]
      simp only [← neg_smul, pfConjExp]
      change Ring.inverse (suzukiExponentialWord xs t) * NormedSpace.exp ((-t) • X) *
          ((X + NormedSpace.exp (t • X) * pfLeftGenerator xs t *
            NormedSpace.exp ((-t) • X)) *
            (NormedSpace.exp (t • X) * suzukiExponentialWord xs t)) = _
      calc
        _ = Ring.inverse (suzukiExponentialWord xs t) *
              (NormedSpace.exp ((-t) • X) * X * NormedSpace.exp (t • X)) *
              suzukiExponentialWord xs t +
            Ring.inverse (suzukiExponentialWord xs t) *
              (NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X)) *
              pfLeftGenerator xs t *
              (NormedSpace.exp ((-t) • X) * NormedSpace.exp (t • X)) *
              suzukiExponentialWord xs t := by noncomm_ring
        _ = _ := by rw [hx, hi]; simp only [mul_one, mul_assoc, suzukiExponentialWord]
    rw [hs, ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, zero_add, List.getD_cons_zero,
      List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]

/-- The right word defect equals the sum of suffix-conjugated generators minus the target
generator conjugated by the full word. -/
theorem pfWordDefectRight_suffix_sum (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ) :
    pfWordDefectRight xs H t =
      (∑ j : Fin xs.length,
        Ring.inverse (suzukiExponentialWord (xs.drop (j.val + 1)) t) *
          xs.getD j.val 0 * suzukiExponentialWord (xs.drop (j.val + 1)) t) -
        Ring.inverse (suzukiExponentialWord xs t) * H * suzukiExponentialWord xs t := by
  rw [pfWordDefectRight, pfWordDefectLeft, sub_mul, mul_sub,
    pf_word_right_generator_suffix_sum, mul_assoc]

/-- The left word defect equals the sum of prefix-conjugated generators minus the target
generator `H`. -/
theorem pfWordDefectLeft_prefix_sum (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ) :
    pfWordDefectLeft xs H t =
      (∑ j : Fin xs.length, pfConjWord (xs.take j.val) (xs.getD j.val 0) t) - H := by
  rw [pfWordDefectLeft, pfLeftGenerator_prefix_sum]

/-- The difference between an exponential word and `exp (t • H)` equals the integral of exact
evolution times the word and its right defect. -/
theorem pf_word_additive_representation (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ) :
    suzukiExponentialWord xs t - NormedSpace.exp (t • H) =
      ∫ τ in 0..t, NormedSpace.exp ((t - τ) • H) *
        (suzukiExponentialWord xs τ * pfWordDefectRight xs H τ) := by
  have hr (τ : ℝ) : suzukiExponentialWord xs τ * pfWordDefectRight xs H τ =
      (pfLeftGenerator xs τ - H) * suzukiExponentialWord xs τ := by
    dsimp only [pfWordDefectRight, pfWordDefectLeft]
    rw [← mul_assoc, Ring.mul_inverse_cancel _ (pf_word_isUnit xs τ), one_mul]
  simpa only [hr] using! pf_word_duhamel xs H t

/-- An exponential word equals the time-ordered evolution with coefficient field `-(H +
pfWordDefectLeft xs H τ)` from zero to `t`. -/
theorem pf_word_exponentiated_representation (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ) :
    suzukiExponentialWord xs t =
      orderedEvolution (fun τ => -(H + pfWordDefectLeft xs H τ)) 0 t := by
  let A : ℝ → Matrix I I ℂ := fun τ => -(H + pfWordDefectLeft xs H τ)
  have hA : Continuous A :=
    (continuous_const.add ((pfLeftGenerator_contDiff xs).continuous.sub continuous_const)).neg
  have hd (τ : ℝ) : HasDerivAt (suzukiExponentialWord xs)
      (-(A τ * suzukiExponentialWord xs τ)) τ := by
    have hg : H + pfWordDefectLeft xs H τ = pfLeftGenerator xs τ := by
      dsimp only [pfWordDefectLeft]
      abel
    simpa only [A, hg, neg_mul, neg_neg] using!
      pf_word_hasDerivAt_left_generator xs τ
  have he := ordered_matrix_ode_unique A hA (suzukiExponentialWord xs)
    (orderedEvolution A 0) 0 (by simp [suzukiExponentialWord]) hd
    (orderedEvolution_hasDerivAt A hA 0)
  exact congrFun he t

/-- An exponential word factors as `exp (t • H)` times the time-ordered evolution generated by
the negative multiplicative defect field. -/
theorem pf_word_multiplicative_representation (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ) :
    suzukiExponentialWord xs t = NormedSpace.exp (t • H) *
      orderedEvolution (fun τ => -(pfWordMultiplicativeField xs H τ)) 0 t := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  let V : ℝ → Matrix I I ℂ := fun τ =>
    NormedSpace.exp ((-τ) • H) * suzukiExponentialWord xs τ
  let A : ℝ → Matrix I I ℂ := fun τ => -(pfWordMultiplicativeField xs H τ)
  have hA : Continuous A :=
    ((((trotter_exp_contDiff H).continuous.comp continuous_neg).mul
      ((pfLeftGenerator_contDiff xs).continuous.sub continuous_const)).mul
      (trotter_exp_contDiff H).continuous).neg
  have hi (τ : ℝ) : NormedSpace.exp (τ • H) * NormedSpace.exp ((-τ) • H) = 1 := by
    rw [neg_smul, ← NormedSpace.exp_add_of_commute ((Commute.refl (τ • H)).neg_right),
      add_neg_cancel, NormedSpace.exp_zero]
  have hd (τ : ℝ) : HasDerivAt V (-(A τ * V τ)) τ := by
    have hh := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) H (-τ)).scomp τ
      (hasDerivAt_id τ).neg).mul (pf_word_hasDerivAt_left_generator xs τ)
    convert! hh using 1
    dsimp only [V, A, pfWordMultiplicativeField, pfWordDefectLeft]
    simp only [Function.comp_def, neg_one_smul, neg_mul, neg_neg]
    calc
      _ = NormedSpace.exp ((-τ) • H) * (pfLeftGenerator xs τ - H) *
          (NormedSpace.exp (τ • H) * NormedSpace.exp ((-τ) • H)) *
          suzukiExponentialWord xs τ := by noncomm_ring
      _ = _ := by rw [hi]; noncomm_ring
  have he := ordered_matrix_ode_unique A hA V (orderedEvolution A 0) 0
    (by simp [V, suzukiExponentialWord]) hd (orderedEvolution_hasDerivAt A hA 0)
  rw [← congrFun he t]
  dsimp only [V]
  rw [← mul_assoc, hi, one_mul]

end Qatlib.Concepts.TrotterFormula.TimeOrdered
