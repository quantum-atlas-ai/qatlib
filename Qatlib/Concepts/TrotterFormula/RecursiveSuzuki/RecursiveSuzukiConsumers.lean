/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.Basic

/-!
# Recursive Suzuki simulation and word perturbations

This module turns recursive Suzuki generator lists into segmented exponential words and proves
unitarity, exact word length, and an explicit exponential-tail error bound. The construction and
estimates use the product-formula setting of [Suzuki1990] and [ChildsEtAl2021Trotter].

For a unitary replacement word of the same length, a uniform entrywise error accumulates
linearly with length. Combining it with the simulation error gives an observable conjugation
bound for arbitrary matrices `O`.

## Main statements

* `recursive_suzuki_actual_simulation_and_cost`: unitarity, length, and simulation error for the
  actual word.
* `recursiveSuzuki_unitary_word_noise`: linear accumulation of error between equal-length
  unitary words.
* `recursive_suzuki_noisy_same_word_observable`: combined simulation and word error for
  observable conjugation.

## References

* [Suzuki, 1990][Suzuki1990]
* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The word formed by repeating `r` exponential segments of the level-`k` recursive Suzuki
generators at step size `t / r`. -/
noncomputable def recursiveSuzukiWord {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t : ℝ) (r : ℕ) : List (Matrix I I ℂ) :=
  (List.replicate r ((recursiveSuzukiGenerators hs k).map
    (fun X => NormedSpace.exp ((t/r) • X)))).flatten

/-- The explicit error budget `2r * exp (L * |t/r|) * (L * |t/r|)^(2k+3) / (2k+3)!`, where `L =
3^k * suzukiMass hs + ‖hs.sum‖`. -/
noncomputable def recursiveSuzukiError {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (t : ℝ) (r : ℕ) : ℝ :=
  let L := (3 : ℝ)^k*suzukiMass hs + ‖hs.sum‖
  2*r*Real.exp (L*|t/r|)*(L*|t/r|)^(2*k+3)/((2*k+3).factorial : ℝ)

/-- The sum of a list of anti-Hermitian generators is anti-Hermitian. -/
private theorem recursiveSuzuki_sum_antiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (hhs : ∀ X ∈ hs, Xᴴ = -X) : hs.sumᴴ = -hs.sum := by
  induction hs with
  | nil => simp
  | cons X xs ih =>
    simp only [List.sum_cons, Matrix.conjTranspose_add, hhs X (by simp),
      ih (by intro Y hY; exact hhs Y (by simp [hY])), neg_add]

/-- For anti-Hermitian generators and positive `r`, the recursive Suzuki word product is
unitary, its length is `r * (2 * hs.length * 5^k)`, and its error is at most
`recursiveSuzukiError hs k t r`; see [ChildsEtAl2021Trotter] for the product-formula
framework. -/
theorem recursive_suzuki_actual_simulation_and_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ),
      (∀ X ∈ hs, Xᴴ = -X) → 0 < r →
      let w := recursiveSuzukiWord hs k t r
      w.prod ∈ Matrix.unitaryGroup I ℂ ∧ w.length = r*(2*hs.length*5^k) ∧
        ‖w.prod - NormedSpace.exp (t • hs.sum)‖ ≤ recursiveSuzukiError hs k t r := by
  intro I _ _ hs k r t hhs hr
  obtain ⟨hu, hl, he⟩ := general_order_actual_word_error_and_cost I
    (recursiveSuzukiGenerators hs k) hs.sum (2*(k+1)) r t
    (recursiveSuzukiGenerators_antiHermitian hs k hhs)
    (recursiveSuzuki_sum_antiHermitian hs hhs) hr
    (recursive_suzuki_all_even_order_coefficients I hs k)
  obtain ⟨hlength, hmass⟩ := recursive_suzuki_length_and_mass I hs k
  have hp : 2*(k+1)+1 = 2*k+3 := by omega
  rw [hp] at he
  have hm : 0 ≤ suzukiMass (recursiveSuzukiGenerators hs k) := general_trotter_mass_nonneg _
  refine ⟨hu, ?_, he.trans ?_⟩
  · exact hl.trans (by rw [hlength])
  · unfold recursiveSuzukiError
    (try dsimp only)
    gcongr

/-- Every exponential entry in a recursive Suzuki word is unitary when the input generators are
anti-Hermitian. -/
private theorem recursiveSuzukiWord_unitary_entries {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ)
    (hhs : ∀ X ∈ hs, Xᴴ = -X) :
    ∀ U ∈ recursiveSuzukiWord hs k t r, U ∈ Matrix.unitaryGroup I ℂ := by
  intro U hU
  obtain ⟨xs, hxs, hU⟩ := List.mem_flatten.mp hU
  have hxs' := List.eq_of_mem_replicate hxs
  subst xs
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hU
  exact general_trotter_exp_unitary X (t/r) (recursiveSuzukiGenerators_antiHermitian hs k hhs X hX)

/-- Two equal-length unitary matrix words whose corresponding entries differ by at most a
nonnegative `δ` have product distance at most `V.length * δ`. -/
theorem recursiveSuzuki_unitary_word_noise {I : Type} [Fintype I] [DecidableEq I]
    (V W : List (Matrix I I ℂ)) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hlen : V.length = W.length)
    (hV : ∀ U ∈ V, U ∈ Matrix.unitaryGroup I ℂ)
    (hW : ∀ U ∈ W, U ∈ Matrix.unitaryGroup I ℂ)
    (hnoise : ∀ j : ℕ, j < V.length → ‖V.getD j 0-W.getD j 0‖ ≤ δ) :
    ‖V.prod-W.prod‖ ≤ (V.length : ℝ)*δ := by
  induction V generalizing W with
  | nil =>
    have hWnil : W = [] := List.length_eq_zero_iff.mp hlen.symm
    subst W
    simp
  | cons X xs ih =>
    cases W with
    | nil => simp at hlen
    | cons Y ys =>
      have hlen' : xs.length = ys.length := by simpa using! hlen
      have hVs : ∀ U ∈ xs, U ∈ Matrix.unitaryGroup I ℂ := by
        intro U hU; exact hV U (by simp [hU])
      have hWs : ∀ U ∈ ys, U ∈ Matrix.unitaryGroup I ℂ := by
        intro U hU; exact hW U (by simp [hU])
      have hh : ‖X-Y‖ ≤ δ := by simpa using! hnoise 0 (by simp)
      have ht : ‖xs.prod-ys.prod‖ ≤ (xs.length : ℝ)*δ :=
        ih ys hlen' hVs hWs (by
          intro j hj
          simpa using! hnoise (j+1) (by simpa using! hj))
      have hxn : ‖xs.prod‖ ≤ 1 :=
        l2_norm_unitary_le_one ((Matrix.unitaryGroup I ℂ).list_prod_mem hVs)
      have hyn : ‖Y‖ ≤ 1 := l2_norm_unitary_le_one (hW Y (by simp))
      simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hex : X*xs.prod-Y*ys.prod = (X-Y)*xs.prod+Y*(xs.prod-ys.prod) := by
        noncomm_ring
      rw [hex]
      calc
        _ ≤ ‖(X-Y)*xs.prod‖ + ‖Y*(xs.prod-ys.prod)‖ := norm_add_le _ _
        _ ≤ ‖X-Y‖*‖xs.prod‖ + ‖Y‖*‖xs.prod-ys.prod‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ δ+(xs.length : ℝ)*δ := by
          apply add_le_add
          · calc
              _ ≤ ‖X-Y‖*1 := mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
              _ ≤ δ := by simpa using! hh
          · calc
              _ ≤ 1*‖xs.prod-ys.prod‖ := mul_le_mul_of_nonneg_right hyn (norm_nonneg _)
              _ ≤ (xs.length : ℝ)*δ := by simpa using! ht
        _ = ((xs.length : ℝ)+1)*δ := by ring

/-- For a unitary replacement word of the same length with per-entry error at most `δ`, the
product error is at most the Suzuki budget plus `V.length * δ`, and conjugation error is at
most twice that total times `‖O‖`; the simulation component uses [ChildsEtAl2021Trotter]. -/
theorem recursive_suzuki_noisy_same_word_observable :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (hs : List (Matrix I I ℂ)) (k r : ℕ) (t δ : ℝ)
      (V : List (Matrix I I ℂ)) (O : Matrix I I ℂ),
      (∀ X ∈ hs, Xᴴ = -X) → 0 < r → 0 ≤ δ →
      V.length = (recursiveSuzukiWord hs k t r).length →
      (∀ U ∈ V, U ∈ Matrix.unitaryGroup I ℂ) →
      (∀ j : ℕ, j < V.length →
        ‖V.getD j 0 - (recursiveSuzukiWord hs k t r).getD j 0‖ ≤ δ) →
      let U := NormedSpace.exp (t • hs.sum)
      let η := recursiveSuzukiError hs k t r + (V.length : ℝ)*δ
      V.prod ∈ Matrix.unitaryGroup I ℂ ∧ ‖V.prod-U‖ ≤ η ∧
        ‖V.prodᴴ*O*V.prod - Uᴴ*O*U‖ ≤ 2*‖O‖*η := by
  intro I _ _ hs k r t δ V O hhs hr hδ hlen hV hn
  obtain ⟨_, _, he⟩ := recursive_suzuki_actual_simulation_and_cost I hs k r t hhs hr
  have hw := recursiveSuzuki_unitary_word_noise V (recursiveSuzukiWord hs k t r) δ
    hδ hlen hV (recursiveSuzukiWord_unitary_entries hs k r t hhs) hn
  have hVu : V.prod ∈ Matrix.unitaryGroup I ℂ := (Matrix.unitaryGroup I ℂ).list_prod_mem hV
  have hUu : NormedSpace.exp (t • hs.sum) ∈ Matrix.unitaryGroup I ℂ :=
    general_trotter_exp_unitary hs.sum t (recursiveSuzuki_sum_antiHermitian hs hhs)
  have herr : ‖V.prod-NormedSpace.exp (t • hs.sum)‖ ≤
      recursiveSuzukiError hs k t r+(V.length : ℝ)*δ := by
    calc
      _ ≤ ‖V.prod-(recursiveSuzukiWord hs k t r).prod‖ +
          ‖(recursiveSuzukiWord hs k t r).prod-NormedSpace.exp (t • hs.sum)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (V.length : ℝ)*δ+recursiveSuzukiError hs k t r := add_le_add hw he
      _ = _ := by ring
  refine ⟨hVu, herr, ?_⟩
  exact (suzuki_unitary_observable_error _ _ O hUu hVu).trans
    (mul_le_mul_of_nonneg_left herr (by positivity))

end Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
