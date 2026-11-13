/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.LchsRep.ImaginaryTimeProduct
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula

/-!
# Finite-family imaginary-time product formulas

This module constructs labelled first-order imaginary-time words for finite matrix families and
bounds their error by a sum of pairwise commutator norms. For positive-semidefinite terms and
nonnegative time, each segment and the complete run are contractions, as in the
commutator-scaling framework of [ChildsEtAl2021Trotter].

The word ledger records length, occurrences of each label, and arbitrary label prices. Pairwise
commuting terms give exact evolution for every positive segment count.

## Main statements

* `imaginary_family_psd_lie_segment_error`: the one-segment commutator error estimate.
* `imaginary_family_actual_word_error_and_tariffs`: contraction, word accounting, and segmented
  error.
* `imaginary_family_commuting_exact`: exactness for commuting terms.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.LchsSimulation.LchsRep

namespace Qatlib.Concepts.TrotterFormula.ImaginaryTime
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The sum of norms of pairwise commutators over index pairs `j < k`. -/
noncomputable def imaginaryCommutatorSum {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) : ℝ :=
  ∑ j : Fin m, ∑ k : Fin m, if j < k then ‖pfComm (H j) (H k)‖ else 0

/-- The labelled imaginary-time word obtained by repeating the ordered family of exponentials
`r` times with step size `t / r`. -/
noncomputable def imaginaryFamilyWord {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) (t : ℝ) (r : ℕ) : List (Matrix I I ℂ × ℕ) :=
  (List.replicate r (List.ofFn (fun j : Fin m =>
    (NormedSpace.exp (-(t / (r : ℝ)) • H j), j.val)))).flatten

/-- The list-order product of the matrix entries in `imaginaryFamilyWord H t r`. -/
noncomputable def imaginaryFamilyRun {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) (t : ℝ) (r : ℕ) : Matrix I I ℂ :=
  ((imaginaryFamilyWord H t r).map Prod.fst).prod

/-- The segment count `max 1 ⌈t² * imaginaryCommutatorSum H / (2 * ε)⌉`. -/
noncomputable def finiteImaginarySegments {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → Matrix I I ℂ) (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (t ^ 2 * imaginaryCommutatorSum H / (2 * ε)))

/-- The commutator sum splits into interactions with the first term and the commutator sum of
the remaining family. -/
private theorem imaginary_pair_sum_succ {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin (m+1) → Matrix I I ℂ) :
    imaginaryCommutatorSum H = (∑ j : Fin m, ‖pfComm (H 0) (H j.succ)‖) +
      imaginaryCommutatorSum (fun j : Fin m => H j.succ) := by
  simp [imaginaryCommutatorSum, Fin.sum_univ_succ]

/-- The norm of the commutator with a finite sum is bounded by the sum of the individual
commutator norms. -/
private theorem imaginary_comm_sum_bound {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin m → Matrix I I ℂ) (A : Matrix I I ℂ) :
    ‖pfComm A (∑ j, H j)‖ ≤ ∑ j, ‖pfComm A (H j)‖ := by
  have he : pfComm A (∑ j, H j) = ∑ j, pfComm A (H j) := by
    simp only [pfComm, Matrix.mul_sum, Matrix.sum_mul, Finset.sum_sub_distrib]
  rw [he]
  exact norm_sum_le _ _

/-- A product of negative-time exponentials of positive-semidefinite matrices has norm at most
one when the step size is nonnegative. -/
private theorem imaginary_segment_contraction {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin m → Matrix I I ℂ) (s : ℝ)
    (hH : ∀ j, (H j).PosSemidef) (hs : 0 ≤ s) :
    ‖(List.ofFn (fun j => NormedSpace.exp (-s • H j))).prod‖ ≤ 1 := by
  apply l2_norm_list_prod_le_one
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact imaginary_exp_psd_contraction (H j) (hH j) s hs

/-- For positive-semidefinite terms and `s ≥ 0`, the one-segment imaginary-time error is at most
`s² / 2` times `imaginaryCommutatorSum H`; this is a finite first-order instance of the
framework in [ChildsEtAl2021Trotter]. -/
theorem imaginary_family_psd_lie_segment_error :
  ∀ {I : Type} [Fintype I] [DecidableEq I] {m : ℕ} (H : Fin m → Matrix I I ℂ) (s : ℝ),
    (∀ j : Fin m, (H j).PosSemidef) → 0 ≤ s →
    ‖(List.ofFn (fun j : Fin m => NormedSpace.exp (-s • H j))).prod -
        NormedSpace.exp (-s • ∑ j : Fin m, H j)‖ ≤
      s ^ 2 / 2 * imaginaryCommutatorSum H := by
  intro I _ _ m H s hH hs
  induction m with
  | zero => simp [imaginaryCommutatorSum]
  | succ m ih =>
    let tail : Fin m → Matrix I I ℂ := fun j => H j.succ
    let B : Matrix I I ℂ := ∑ j, tail j
    have hB : B.PosSemidef := Matrix.posSemidef_sum _ (fun j _ => hH j.succ)
    have hi := ih tail (fun j => hH j.succ)
    have hLie : ‖NormedSpace.exp (-s • H 0)*NormedSpace.exp (-s • B)-
        NormedSpace.exp (-s • (H 0+B))‖ ≤ s^2/2*‖pfComm (H 0) B‖ :=
      (imaginary_psd_lie_segment_error (H 0) B (hH 0) hB s hs).trans_eq (by
        unfold pfComm
        ring)
    have hC := imaginary_comm_sum_bound tail (H 0)
    have he : (List.ofFn (fun j => NormedSpace.exp (-s • H j))).prod -
        NormedSpace.exp (-s • ∑ j, H j) =
      NormedSpace.exp (-s • H 0)*
        ((List.ofFn (fun j => NormedSpace.exp (-s • tail j))).prod-NormedSpace.exp (-s • B)) +
        (NormedSpace.exp (-s • H 0)*NormedSpace.exp (-s • B)-
          NormedSpace.exp (-s • (H 0+B))) := by
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      dsimp [tail, B]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖NormedSpace.exp (-s • H 0)*
          ((List.ofFn (fun j => NormedSpace.exp (-s • tail j))).prod-NormedSpace.exp (-s • B))‖ +
          ‖NormedSpace.exp (-s • H 0)*NormedSpace.exp (-s • B)-
            NormedSpace.exp (-s • (H 0+B))‖ := norm_add_le _ _
      _ ≤ ‖(List.ofFn (fun j => NormedSpace.exp (-s • tail j))).prod-NormedSpace.exp (-s • B)‖ +
          ‖NormedSpace.exp (-s • H 0)*NormedSpace.exp (-s • B)-
            NormedSpace.exp (-s • (H 0+B))‖ := by
        apply add_le_add _ le_rfl
        exact (norm_mul_le _ _).trans
          ((mul_le_mul_of_nonneg_right (imaginary_exp_psd_contraction (H 0) (hH 0) s hs)
            (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ s^2/2*imaginaryCommutatorSum tail + s^2/2*‖pfComm (H 0) B‖ := add_le_add hi hLie
      _ ≤ s^2/2*imaginaryCommutatorSum tail + s^2/2*(∑ j, ‖pfComm (H 0) (tail j)‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (by positivity))
      _ = _ := by rw [imaginary_pair_sum_succ]; dsimp [tail]; ring

/-- The imaginary-time family run is the `r`th power of its one-segment product at step size `t
/ r`. -/
private theorem imaginary_family_run_power {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin m → Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    imaginaryFamilyRun H t r =
      ((List.ofFn (fun j => NormedSpace.exp (-(t/(r : ℝ)) • H j))).prod)^r := by
  simp [imaginaryFamilyRun, imaginaryFamilyWord, List.map_flatten, List.map_replicate,
    List.map_ofFn, List.prod_flatten, List.prod_replicate, Function.comp_def]

/-- The imaginary-time word has length `m * r`, contains each family label exactly `r` times,
and has total price `r` times the sum of label prices. -/
private theorem imaginary_family_word_ledger {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (H : Fin m → Matrix I I ℂ) (t : ℝ) (r : ℕ) (price : ℕ → ℕ) :
    (imaginaryFamilyWord H t r).length = m*r ∧
    (∀ j : Fin m, ((imaginaryFamilyWord H t r).map Prod.snd).count j.val = r) ∧
    ((imaginaryFamilyWord H t r).map (fun x => price x.2)).sum = r*∑ j : Fin m, price j.val := by
  let step := List.ofFn (fun j : Fin m => (NormedSpace.exp (-(t/(r : ℝ)) • H j), j.val))
  have hc (j : Fin m) : (step.map Prod.snd).count j.val = 1 := by
    simp only [step, List.map_ofFn, Function.comp_def]
    rw [List.ofFn_eq_map, List.count_map_of_injective _ Fin.val Fin.val_injective,
      List.count_finRange]
  have hp : (step.map (fun x => price x.2)).sum = ∑ j : Fin m, price j.val := by
    simp [step, List.map_ofFn, List.sum_ofFn]
  change ((List.replicate r step).flatten).length = _ ∧
    (∀ j : Fin m, (((List.replicate r step).flatten).map Prod.snd).count j.val = _) ∧
    (((List.replicate r step).flatten).map (fun x => price x.2)).sum = _
  refine ⟨?_, ?_, ?_⟩
  · simp [step, List.length_flatten, List.map_replicate, Nat.mul_comm]
  · intro j
    simp only [List.map_flatten, List.map_replicate, List.count_flatten,
      List.map_replicate, hc, List.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one]
  · simp only [List.map_flatten, List.map_replicate, List.sum_flatten,
      List.sum_replicate, hp, nsmul_eq_mul, Nat.cast_id]

/-- For positive-semidefinite terms, nonnegative time, and positive `r`, the run is contractive,
satisfies the word ledger, and has error at most `t² * imaginaryCommutatorSum H / (2 * r)`,
in the setting of [ChildsEtAl2021Trotter]. -/
theorem imaginary_family_actual_word_error_and_tariffs :
  ∀ {I : Type} [Fintype I] [DecidableEq I] {m : ℕ} (H : Fin m → Matrix I I ℂ)
    (t : ℝ) (r : ℕ) (price : ℕ → ℕ),
    (∀ j : Fin m, (H j).PosSemidef) → 0 ≤ t → 0 < r →
    ‖imaginaryFamilyRun H t r‖ ≤ 1 ∧
    (imaginaryFamilyWord H t r).length = m * r ∧
    (∀ j : Fin m, ((imaginaryFamilyWord H t r).map Prod.snd).count j.val = r) ∧
    ((imaginaryFamilyWord H t r).map (fun x => price x.2)).sum =
      r * ∑ j : Fin m, price j.val ∧
    ‖imaginaryFamilyRun H t r - NormedSpace.exp (-t • ∑ j : Fin m, H j)‖ ≤
      t ^ 2 * imaginaryCommutatorSum H / (2 * (r : ℝ)) := by
  intro I _ _ m H t r price hH ht hr
  let s := t/(r : ℝ)
  let U := (List.ofFn (fun j => NormedSpace.exp (-s • H j))).prod
  let V := NormedSpace.exp (-s • ∑ j, H j)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hs : 0 ≤ s := div_nonneg ht hrR.le
  have hsum : (∑ j, H j).PosSemidef := Matrix.posSemidef_sum _ (fun j _ => hH j)
  have hU : ‖U‖ ≤ 1 := imaginary_segment_contraction H s hH hs
  have hV : ‖V‖ ≤ 1 := imaginary_exp_psd_contraction _ hsum s hs
  have hVpow : V^r = NormedSpace.exp (-t • ∑ j, H j) := by
    rw [imaginary_exp_power]
    congr 1
    dsimp [s]
    rw [mul_div_cancel₀ _ hrR.ne']
  obtain ⟨hlen, hcount, hprice⟩ := imaginary_family_word_ledger H t r price
  refine ⟨?_, hlen, hcount, hprice, ?_⟩
  · rw [imaginary_family_run_power]
    exact imaginary_contraction_pow_norm U hU r
  · rw [imaginary_family_run_power, ← hVpow]
    apply (imaginary_contraction_power_error U V hU hV r).trans
    have he := mul_le_mul_of_nonneg_left (imaginary_family_psd_lie_segment_error H s hH hs)
      (Nat.cast_nonneg r)
    apply he.trans_eq
    dsimp [s]
    field_simp

/-- For pairwise commuting positive-semidefinite terms, nonnegative time, and positive `r`, the
imaginary-time family run equals the exponential of the negative scaled sum; see
[ChildsEtAl2021Trotter] for the commutator-scaling setting. -/
theorem imaginary_family_commuting_exact :
  ∀ {I : Type} [Fintype I] [DecidableEq I] {m : ℕ} (H : Fin m → Matrix I I ℂ)
    (t : ℝ) (r : ℕ),
    (∀ j : Fin m, (H j).PosSemidef) → 0 ≤ t → 0 < r →
    (∀ j k : Fin m, H j * H k = H k * H j) →
    imaginaryFamilyRun H t r = NormedSpace.exp (-t • ∑ j : Fin m, H j) := by
  intro I _ _ m H t r hH ht hr hcomm
  have hz : imaginaryCommutatorSum H = 0 := by
    unfold imaginaryCommutatorSum
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    simp [pfComm, hcomm j k]
  have h := (imaginary_family_actual_word_error_and_tariffs H t r (fun _ => 0) hH ht hr).2.2.2.2
  rw [hz, mul_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end Qatlib.Concepts.TrotterFormula.ImaginaryTime
