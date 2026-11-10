/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHBalancedVisits
import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHHalfBudget

open Matrix
open scoped BigOperators MonoidAlgebra Classical Matrix.Norms.L2Operator
open BCHDynkin BCHWordLie BCHWordLog BCHCommBudget BCHBalancedVisits BCHMatrixBudget
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki

def halfLabels (Γ : ℕ) : List (Fin Γ) := List.finRange Γ ++ (List.finRange Γ).reverse

theorem halfLabels_balance (Γ : ℕ) :
    (∑ j : Fin (halfLabels Γ).length, (1 / 2 : ℚ) • letter ((halfLabels Γ).get j)) =
      ∑ i : Fin Γ, letter i := by
  have he := congrArg
    (fun w : List (Fin Γ) => (w.map (fun i => (1 / 2 : ℚ) • letter i)).sum)
    (List.ofFn_get (halfLabels Γ))
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def] at he
  rw [he, halfLabels, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse]
  have hcore : ((List.finRange Γ).map (fun i => (1 / 2 : ℚ) • letter i)).sum =
      (1 / 2 : ℚ) • ∑ i : Fin Γ, letter i := by
    rw [← List.ofFn_eq_map, List.sum_ofFn, Finset.smul_sum]
  rw [hcore, ← add_smul]
  norm_num

section Norm
variable {B : Type} [NormedRing B] [NormedAlgebra ℝ B] [Algebra ℚ B]

theorem alphaComm_half_labels {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) :
    alphaComm (fun j => (1 / 2 : ℚ) • X ((halfLabels Γ).get j)) n = alphaComm X n :=
  alphaComm_balanced X (halfLabels Γ).get (1 / 2) (by norm_num) (halfLabels_balance Γ) n

theorem alphaComm_two_visits {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) :
    alphaComm (fun j => X ((halfLabels Γ).get j)) n = (2 : ℝ) ^ n * alphaComm X n := by
  have h := alphaComm_half_labels X n
  have hs := alphaComm_smul (fun j => X ((halfLabels Γ).get j)) (1 / 2 : ℝ) n
  rw [show ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) by norm_num] at hs
  have hh : (1 / 2 : ℝ) ^ n * alphaComm (fun j => X ((halfLabels Γ).get j)) n =
      alphaComm X n := by
    rw [← hs]
    simpa only [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using! h
  calc
    _ = (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n *
        alphaComm (fun j => X ((halfLabels Γ).get j)) n) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ = _ := by rw [hh]

end Norm

section Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

theorem alphaComm_eq_frozen_ofFn {Γ : ℕ} (X : Fin Γ → Matrix I I ℂ) (n : ℕ) :
    alphaComm X n = pfCommAlphaSelf (List.ofFn X) n := by
  rw [← alphaComm_get_eq_frozen, alphaComm_get_ofFn]

theorem half_labels_eq_frozen (xs : List (Matrix I I ℂ)) :
    List.ofFn (fun j : Fin (halfLabels xs.length).length =>
      (1 / 2 : ℚ) • xs.get ((halfLabels xs.length).get j)) =
        recursiveSuzukiGenerators xs 0 := by
  have he := congrArg
    (List.map (fun i : Fin xs.length => (1 / 2 : ℚ) • xs.get i))
    (List.ofFn_get (halfLabels xs.length))
  simp only [List.map_ofFn, Function.comp_def] at he
  rw [he, halfLabels, List.map_append, List.map_reverse]
  have hq (A : Matrix I I ℂ) : (1 / 2 : ℚ) • A = (1 / 2 : ℝ) • A := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using!
      (Rat.cast_smul_eq_qsmul ℝ (1 / 2 : ℚ) A).symm
  simp_rw [hq]
  have hxs : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hscaled : ((List.finRange xs.length).map (fun i => (1 / 2 : ℝ) • xs.get i)) =
      xs.map (fun A => (1 / 2 : ℝ) • A) := by
    simpa only [List.map_map, Function.comp_def] using!
      congrArg (List.map (fun A => (1 / 2 : ℝ) • A)) hxs
  rw [hscaled]
  simp only [recursiveSuzukiGenerators, List.map_reverse]

theorem frozen_half_profile_eq (xs : List (Matrix I I ℂ)) (n : ℕ) :
    pfCommAlphaSelf (recursiveSuzukiGenerators xs 0) n = pfCommAlphaSelf xs n := by
  rw [← half_labels_eq_frozen, ← alphaComm_eq_frozen_ofFn, alphaComm_half_labels,
    alphaComm_get_eq_frozen]

theorem frozen_profile_smul (xs : List (Matrix I I ℂ)) (c : ℂ) (n : ℕ) :
    pfCommAlphaSelf (xs.map (fun A => c • A)) n = ‖c‖ ^ n * pfCommAlphaSelf xs n := by
  have he := congrArg (List.map (fun A => c • A)) (List.ofFn_get xs)
  simp only [List.map_ofFn, Function.comp_def] at he
  rw [← he, ← alphaComm_eq_frozen_ofFn, alphaComm_smul, alphaComm_get_eq_frozen]

theorem frozen_profile_neg_I (xs : List (Matrix I I ℂ)) (n : ℕ) :
    pfCommAlphaSelf (xs.map (fun A => (-Complex.I) • A)) n = pfCommAlphaSelf xs n := by
  simpa only [norm_neg, Complex.norm_I, one_pow, one_mul] using!
    frozen_profile_smul xs (-Complex.I) n

theorem norm_frozen_half_log_le (xs : List (Matrix I I ℂ)) (n : ℕ) (hn : 0 < n) :
    ‖BCHFormal.logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) n‖ ≤
        pfCommAlphaSelf xs n / (n : ℝ) ^ 2 := by
  have h := norm_existing_word_log_le (recursiveSuzukiGenerators xs 0) n hn
  rw [frozen_half_profile_eq] at h
  exact h

theorem frozen_half_log_one (xs : List (Matrix I I ℂ)) :
    BCHFormal.logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) 1 = xs.sum := by
  rw [BCHFormal.logCoefficient_one, SubdivisionPolynomial.wordSeries, PowerSeries.coeff_mk]
  simpa only [Nat.factorial_one, Nat.cast_one, inv_one, pow_one, one_smul] using!
    recursive_suzuki_all_even_order_coefficients I xs 0 1 (by decide)

theorem norm_unitary_half_log_le (xs : List (Matrix I I ℂ)) (n : ℕ) (hn : 0 < n) :
    ‖BCHFormal.logCoefficient (SubdivisionPolynomial.wordSeries
      (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0)) n‖ ≤
        pfCommAlphaSelf xs n / (n : ℝ) ^ 2 := by
  have h := norm_frozen_half_log_le (xs.map (fun A => (-Complex.I) • A)) n hn
  rw [frozen_profile_neg_I] at h
  exact h

theorem frozen_half_log_even (xs : List (Matrix I I ℂ)) (n : ℕ) (hn : Even n) :
    BCHFormal.logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) n = 0 :=
  BCHFormal.symmetric_logCoefficient_even _ (recursiveSuzukiGenerators_reverse xs 0) n hn

theorem frozen_half_log_skew (xs : List (Matrix I I ℂ))
    (hxs : ∀ A ∈ xs, Aᴴ = -A) (n : ℕ) :
    (BCHFormal.logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) n)ᴴ =
        -BCHFormal.logCoefficient
          (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) n :=
  BCHFormal.symmetric_logCoefficient_skew _ (recursiveSuzukiGenerators_reverse xs 0)
    (recursiveSuzukiGenerators_antiHermitian xs 0 hxs) n

theorem unitary_half_log_skew (xs : List (Matrix I I ℂ))
    (hxs : ∀ A ∈ xs, Aᴴ = A) (n : ℕ) :
    (BCHFormal.logCoefficient (SubdivisionPolynomial.wordSeries
      (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0)) n)ᴴ =
        -BCHFormal.logCoefficient (SubdivisionPolynomial.wordSeries
          (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0)) n := by
  apply frozen_half_log_skew
  intro A hA
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hA
  simp [Matrix.conjTranspose_smul, hxs H hH]

end Matrix

end Qatlib.Papers.CommutLCHS26.MainResults.BCHHalfBudget
