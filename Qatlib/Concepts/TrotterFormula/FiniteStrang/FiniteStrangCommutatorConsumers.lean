/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutator
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrderConsumers

/-!
# Strang segmentation, gate costs, and observables

This module carries the Strang error estimate through repeated segments while counting the gates
and their indexed prices in `finiteStrangWord`. The explicit choice `finiteStrangSegments` gives
a requested positive accuracy and a corresponding error bound for conjugating an observable. For
background, see [ChildsEtAl2021Trotter].

## Main statements

* `finite_strang_same_word_error_and_tariffs`: unitarity, gate counts, prices, and global error
  for one word.
* `finite_strang_selected_accuracy_and_observable`: explicit segmentation and observable error.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.FiniteStrang
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The positive segment count given by the ceiling of `√(|t| ^ 3 * finiteStrangConstant H /
ε)`, with minimum one. -/
def finiteStrangSegments {D m : ℕ} (H : Fin m → Operator D) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.sqrt (|t|^3*finiteStrangConstant H/ε)))

/-- A tagged word whose matrix components are unitary has a unitary interpretation. -/
private theorem fs_word_unitary {D : ℕ} (xs : List (Operator D × ℕ))
    (h : ∀ x ∈ xs, x.1 ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    pfInterpret xs ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  induction xs with
  | nil => exact (Matrix.unitaryGroup _ _).one_mem
  | cons x xs ih =>
    change xs.foldl (fun V y => y.1*V) (x.1*1) ∈ _
    rw [pfInterpret_start, mul_one]
    exact (Matrix.unitaryGroup _ _).mul_mem
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))) (h x List.mem_cons_self)

/-- The interpreted `r`-segment Strang word is the `r`th power of a single segment of duration
`t / r`. -/
private theorem fs_word_repeat {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) (r : ℕ) :
    pfInterpret (finiteStrangWord H t r) =
      (pfInterpret (finiteStrangWord H (t/r) 1))^r := by
  have he : t/(2*(r : ℝ)) = (t/r)/2 := by ring
  simp only [finiteStrangWord, Nat.cast_one, mul_one, List.replicate_one,
    List.flatten_cons, List.flatten_nil, List.append_nil, he]
  exact pfInterpret_repeat _ _

/-- The Strang word has `2 * m * r` gates, each term appears `2 * r` times, and its total price
is `2 * r` times the sum of term prices. -/
private theorem fs_word_ledger {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) (r : ℕ)
    (price : ℕ → ℕ) :
    (finiteStrangWord H t r).length = 2*m*r ∧
    (∀ j : Fin m, ((finiteStrangWord H t r).map Prod.snd).count j.val = 2*r) ∧
    ((finiteStrangWord H t r).map (fun x => price x.2)).sum =
      2*r*(∑ j : Fin m, price j.val) := by
  let step := (List.finRange m ++ (List.finRange m).reverse).map
    (fun j => (HamiltonianEvolution (H j) (t/(2*r)), j.val))
  have hc (j : Fin m) : (step.map Prod.snd).count j.val = 2 := by
    simp only [step, List.map_append, List.map_reverse, List.map_map, Function.comp_def]
    rw [List.count_append, List.count_reverse,
      List.count_map_of_injective _ Fin.val Fin.val_injective, List.count_finRange]
  have hp : (step.map (fun x => price x.2)).sum = 2*(∑ j : Fin m, price j.val) := by
    simp [step, ← List.ofFn_eq_map, List.sum_ofFn]
    omega
  change ((List.replicate r step).flatten).length = _ ∧
    (∀ j : Fin m, (((List.replicate r step).flatten).map Prod.snd).count j.val = _) ∧
    (((List.replicate r step).flatten).map (fun x => price x.2)).sum = _
  refine ⟨?_, ?_, ?_⟩
  · simp [step, List.length_flatten, List.map_replicate, Nat.mul_comm, Nat.mul_left_comm]
    ring
  · intro j
    simp only [List.map_flatten, List.map_replicate, List.count_flatten,
      List.map_replicate, hc, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
    omega
  · simp only [List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate, hp, nsmul_eq_mul, Nat.cast_id]
    ring

/-- For Hermitian terms and positive segment count, the Strang word is unitary with explicit
length, per-term counts, total price, and error bounded by `|t| ^ 3 * finiteStrangConstant H
/ r ^ 2` [ChildsEtAl2021Trotter]. -/
theorem finite_strang_same_word_error_and_tariffs :
    ∀ (D m r : ℕ) (H : Fin m → Operator D) (t : ℝ) (price : ℕ → ℕ),
      (∀ j, (H j).IsHermitian) → 0 < r →
      let w := finiteStrangWord H t r
      pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ w.length = 2*m*r ∧
      (∀ j : Fin m, (w.map Prod.snd).count j.val = 2*r) ∧
      (w.map (fun x => price x.2)).sum = 2*r*(∑ j : Fin m, price j.val) ∧
      ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) t‖ ≤
        |t|^3*finiteStrangConstant H/(r : ℝ)^2 := by
  intro D m r H t price hH hr
  (try dsimp only)
  have hu (s : ℝ) (q : ℕ) : pfInterpret (finiteStrangWord H s q) ∈
      Matrix.unitaryGroup (Fin D) ℂ := by
    apply fs_word_unitary
    intro x hx
    obtain ⟨ys, hys, hx⟩ := List.mem_flatten.mp hx
    have hy := List.eq_of_mem_replicate hys
    rw [hy] at hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hamiltonianEvolution_unitary (hH j) _
  obtain ⟨hlen, hcount, hprice⟩ := fs_word_ledger H t r price
  refine ⟨hu t r, hlen, hcount, hprice, ?_⟩
  have hsum : (∑ j, H j).IsHermitian := by
    change (∑ j, H j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (hH j).eq
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have he : (HamiltonianEvolution (∑ j, H j) (t/r))^r =
      HamiltonianEvolution (∑ j, H j) t := by
    rw [pf_evolution_pow]
    congr 1
    field_simp
  rw [fs_word_repeat, ← he]
  have h := pf_unitary_power_error (pfInterpret (finiteStrangWord H (t/r) 1))
    (HamiltonianEvolution (∑ j, H j) (t/r)) (hu (t/r) 1)
    (hamiltonianEvolution_unitary hsum (t/r)) r
  refine h.trans ((mul_le_mul_of_nonneg_left
    (finite_strang_tight_nested_commutator D m H (t/r) hH) (Nat.cast_nonneg r)).trans_eq ?_)
  rw [abs_div, abs_of_pos (by exact_mod_cast hr : 0 < (r : ℝ))]
  field_simp

/-- The finite Strang nested commutator coefficient is nonnegative. -/
private theorem fs_constant_nonneg {D m : ℕ} (H : Fin m → Operator D) :
    0 ≤ finiteStrangConstant H := by
  unfold finiteStrangConstant
  positivity

/-- For positive `ε`, the selected segment count gives a unitary Strang word with error at most
`ε` and observable conjugation error at most `2 * ‖O‖ * ε` [ChildsEtAl2021Trotter]. -/
theorem finite_strang_selected_accuracy_and_observable :
    ∀ (D m : ℕ) (H : Fin m → Operator D) (t ε : ℝ) (O : Operator D),
      (∀ j, (H j).IsHermitian) → 0 < ε →
      let r := finiteStrangSegments H t ε
      let w := finiteStrangWord H t r
      0 < r ∧ w.length = 2*m*r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
      ‖pfInterpret w-HamiltonianEvolution (∑ j, H j) t‖ ≤ ε ∧
      ‖(pfInterpret w)ᴴ*O*pfInterpret w -
        (HamiltonianEvolution (∑ j, H j) t)ᴴ*O*HamiltonianEvolution (∑ j, H j) t‖ ≤
          2*‖O‖*ε := by
  intro D m H t ε O hH hε
  let r := finiteStrangSegments H t ε
  let a := |t|^3*finiteStrangConstant H/ε
  have ha : 0 ≤ a := by
    have hc := fs_constant_nonneg H
    dsimp [a]
    positivity
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hroot : Real.sqrt a ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 (Nat.ceil (Real.sqrt a)))
  have hsq : a ≤ (r : ℝ)^2 := by
    nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
  have hbudget : |t|^3*finiteStrangConstant H/(r : ℝ)^2 ≤ ε := by
    apply (div_le_iff₀ (sq_pos_of_pos hrR)).mpr
    have hb := (div_le_iff₀ hε).mp hsq
    nlinarith
  obtain ⟨hu, hlen, _, _, herr⟩ :=
    finite_strang_same_word_error_and_tariffs D m r H t (fun _ => 0) hH hr
  have haccuracy := herr.trans hbudget
  refine ⟨hr, hlen, hu, haccuracy, ?_⟩
  have hsum : (∑ j, H j).IsHermitian := by
    change (∑ j, H j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => (hH j).eq
  exact (suzuki_unitary_observable_error _ _ O (hamiltonianEvolution_unitary hsum t) hu).trans
    (mul_le_mul_of_nonneg_left haccuracy (by positivity))

end Qatlib.Concepts.TrotterFormula.FiniteStrang
