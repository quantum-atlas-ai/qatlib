/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Matrix sum instances and a concentration criterion

This module defines the binomial matrices, matrix sums, and finite solution sets used for Lemma
5 of [BaconChildsVanDam2005]. The solution count has mean one, and a second-moment hypothesis
implies that at least one quarter of instances have one or two solutions.

## Main statements

* `solutions_sum_card`: Solution sets partition the space of coefficient vectors.
* `mean_eq_one`: The total solution count equals the number of instances.
* `concentration_one_two`: A mean-one natural-valued function with the stated second-moment
  bound takes values one or two on at least one quarter of its domain.

## References

* [Bacon et al., 2005][BaconChildsVanDam2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.MatrixSumCount

open scoped Classical BigOperators

variable (p r : ℕ)

/-- The binomial coefficient formed from the canonical natural representative of `b`, reduced to
`ZMod p`. -/
def binomMod (b : ZMod p) (l : ℕ) : ZMod p :=
  ((b.val).choose l : ZMod p)

/-- The upper triangular matrix whose `(i, j)` entry is `binomMod p b (j - i + 1)` when `i ≤ j`
and zero otherwise. -/
def matEntry (b : ZMod p) (i j : Fin r) : ZMod p :=
  if (i : ℕ) ≤ (j : ℕ) then binomMod p b ((j : ℕ) - (i : ℕ) + 1) else 0

/-- The product of the binomial matrix `matEntry p r b` with a vector over `ZMod p`. -/
def matVec (b : ZMod p) (v : Fin r → ZMod p) : Fin r → ZMod p :=
  fun i => ∑ j : Fin r, matEntry p r b i j * v j

/-- The sum, over the coefficient coordinates, of the corresponding binomial matrix actions on
the input vectors. -/
def matSum (x : Fin r → Fin r → ZMod p) (b : Fin r → ZMod p) : Fin r → ZMod p :=
  fun i => ∑ j : Fin r, matVec p r (b j) (x j) i

/-- The finite set of coefficient vectors `b` for which the matrix sum of `x` equals the target
`w`. -/
def solutions [NeZero p] (x : Fin r → Fin r → ZMod p) (w : Fin r → ZMod p) :
    Finset (Fin r → ZMod p) :=
  Finset.univ.filter (fun b => matSum p r x b = w)

/-- The binomial matrix action with parameter zero sends every vector to zero. -/
lemma matVec_zero (v : Fin r → ZMod p) : matVec p r (0 : ZMod p) v = 0 := by
  funext i
  simp only [matVec]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : (i : ℕ) ≤ (j : ℕ)
  · rw [matEntry, if_pos h, binomMod]
    have hl : 0 < (j : ℕ) - (i : ℕ) + 1 := by omega
    have hz : (0 : ZMod p).val = 0 := ZMod.val_zero
    rw [hz, Nat.choose_eq_zero_of_lt hl]
    simp
  · rw [matEntry, if_neg h]
    simp

/-- Summing the cardinalities of the solution sets over all targets gives the number of
coefficient vectors [BaconChildsVanDam2005]. -/
lemma solutions_sum_card [NeZero p] (x : Fin r → Fin r → ZMod p) :
    ∑ w, (solutions p r x w).card = Fintype.card (Fin r → ZMod p) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin r → ZMod p)))
    (t := (Finset.univ : Finset (Fin r → ZMod p)))
    (f := fun b => matSum p r x b) (fun a _ => by simp)
  rw [Finset.card_univ] at h
  simpa [solutions] using h.symm

/-- The sum of solution counts over all input-target pairs equals the number of such pairs, so
the uniform mean solution count is one [BaconChildsVanDam2005]. -/
theorem mean_eq_one [NeZero p] :
    (∑ xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p),
        ((solutions p r xw.1 xw.2).card : ℝ))
      = (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) := by
  calc (∑ xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p),
        ((solutions p r xw.1 xw.2).card : ℝ))
      = ∑ x : Fin r → Fin r → ZMod p, ∑ w : Fin r → ZMod p,
          ((solutions p r x w).card : ℝ) := Fintype.sum_prod_type' (f := fun x w => ((solutions p r x w).card : ℝ))
    _ = ∑ _x : Fin r → Fin r → ZMod p, (Fintype.card (Fin r → ZMod p) : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Nat.cast_sum, solutions_sum_card p r x]
    _ = (Fintype.card (Fin r → Fin r → ZMod p) : ℝ) *
          (Fintype.card (Fin r → ZMod p) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) := by
        rw [Fintype.card_prod, Nat.cast_mul]

/-- A natural-valued function with mean one and second moment at most `2 - δ`, where `0 ≤ δ ≤
1`, takes the value one or two on at least one quarter of a finite domain
[BaconChildsVanDam2005]. -/
theorem concentration_one_two {S : Type*} [Fintype S] (η : S → ℕ) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmean : (∑ s, (η s : ℝ)) = (Fintype.card S : ℝ))
    (hsec : (∑ s, (η s : ℝ) ^ 2) ≤ (2 - δ) * (Fintype.card S : ℝ)) :
    4 * ((Finset.univ.filter (fun s => η s = 1 ∨ η s = 2)).card : ℝ) ≥
      (Fintype.card S : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card S) with h0 | hpos
  · have hc : (Fintype.card S : ℝ) = 0 := by simp [h0]
    rw [hc]
    positivity
  set N : ℝ := (Fintype.card S : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  set supp := Finset.univ.filter (fun s => η s ≠ 0) with hsupp
  have hexp : (∑ s, ((η s : ℝ) - 1) ^ 2) = (∑ s, (η s : ℝ) ^ 2) - N := by
    have hpt : ∀ s : S, ((η s : ℝ) - 1) ^ 2 = (η s : ℝ) ^ 2 - 2 * (η s : ℝ) + 1 := by
      intro s; ring
    calc (∑ s, ((η s : ℝ) - 1) ^ 2)
        = ∑ s, ((η s : ℝ) ^ 2 - 2 * (η s : ℝ) + 1) :=
          Finset.sum_congr rfl (fun s _ => hpt s)
      _ = (∑ s, (η s : ℝ) ^ 2) - 2 * (∑ s, (η s : ℝ)) + (∑ _s : S, (1 : ℝ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ s, (η s : ℝ) ^ 2) - 2 * N + N := by
            rw [hmean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp [hN]
      _ = (∑ s, (η s : ℝ) ^ 2) - N := by ring
  set tail := Finset.univ.filter (fun s => 3 ≤ η s) with htail
  have htail_bound : 4 * (tail.card : ℝ) ≤ (∑ s, ((η s : ℝ) - 1) ^ 2) := by
    have h4 : ∀ s ∈ tail, (4 : ℝ) ≤ ((η s : ℝ) - 1) ^ 2 := by
      intro s hs
      simp only [htail, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have h3 : (3 : ℝ) ≤ (η s : ℝ) := by exact_mod_cast hs
      nlinarith
    calc 4 * (tail.card : ℝ) = ∑ _s ∈ tail, (4 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ s ∈ tail, ((η s : ℝ) - 1) ^ 2 := Finset.sum_le_sum h4
      _ ≤ ∑ s, ((η s : ℝ) - 1) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun s _ _ => sq_nonneg _)
  have hPZ : N ^ 2 ≤ (supp.card : ℝ) * (∑ s, (η s : ℝ) ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := supp) (f := fun s => (η s : ℝ))
    have hsum_supp : (∑ s ∈ supp, (η s : ℝ)) = ∑ s, (η s : ℝ) := by
      rw [hsupp, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : η s = 0 <;> simp [h]
    have hsq_supp : (∑ s ∈ supp, (η s : ℝ) ^ 2) = ∑ s, (η s : ℝ) ^ 2 := by
      rw [hsupp, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : η s = 0 <;> simp [h]
    rw [hsum_supp, hsq_supp, hmean] at h
    exact h
  set zero := Finset.univ.filter (fun s => η s = 0) with hzero
  have hsupp_card : (supp.card : ℝ) = N - (zero.card : ℝ) := by
    have hdisj : Disjoint supp zero := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      simp only [hsupp, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp only [hzero, Finset.mem_filter, Finset.mem_univ, true_and] at hs'
      exact hs hs'
    have hunion : supp ∪ zero = Finset.univ := by
      ext s
      simp only [hsupp, hzero, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hc : supp.card + zero.card = Fintype.card S := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    have hcR : (supp.card : ℝ) + (zero.card : ℝ) = N := by
      rw [hN]; exact_mod_cast hc
    linarith
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hpos
  have hzero_le : (zero.card : ℝ) ≤ N * (1 - δ) / (2 - δ) := by
    have h2d : (0 : ℝ) < 2 - δ := by linarith
    have hPZ' : N ^ 2 ≤ (N - (zero.card : ℝ)) * (∑ s, (η s : ℝ) ^ 2) := by
      rw [← hsupp_card]; exact hPZ
    have hsec' : (∑ s, (η s : ℝ) ^ 2) ≤ (2 - δ) * N := by simpa [hN] using hsec
    have hchain : N ^ 2 ≤ (N - (zero.card : ℝ)) * (2 - δ) * N := by
      calc N ^ 2 ≤ (N - (zero.card : ℝ)) * (∑ s, (η s : ℝ) ^ 2) := hPZ'
        _ ≤ (N - (zero.card : ℝ)) * ((2 - δ) * N) := by
            apply mul_le_mul_of_nonneg_left hsec'
            have : (0:ℝ) ≤ N - (zero.card:ℝ) := by rw [← hsupp_card]; positivity
            exact this
        _ = (N - (zero.card : ℝ)) * (2 - δ) * N := by ring
    have hdiv : N ≤ (N - (zero.card : ℝ)) * (2 - δ) := by
      have hchain' : N * N ≤ ((N - (zero.card : ℝ)) * (2 - δ)) * N := by nlinarith [hchain]
      exact le_of_mul_le_mul_right hchain' hNpos
    have hz2 : (zero.card : ℝ) * (2 - δ) ≤ N * (1 - δ) := by nlinarith [hdiv]
    exact (le_div_iff₀ h2d).mpr hz2
  have hA3 : (tail.card : ℝ) ≤ (1 - δ) * N / 4 := by
    have h1 : (∑ s, ((η s : ℝ) - 1) ^ 2) ≤ (1 - δ) * N := by
      rw [hexp]; nlinarith [hsec, hN]
    nlinarith [htail_bound, h1]
  have hA0 : (zero.card : ℝ) ≤ N / 2 := by
    have h2d : (0:ℝ) < 2 - δ := by linarith
    have hstep : N * (1 - δ) / (2 - δ) ≤ N / 2 := by
      rw [div_le_iff₀ h2d]
      nlinarith [hN0, hδ0, hδ1]
    linarith [hzero_le, hstep]
  have hcover : zero ∪ tail ∪ (Finset.univ.filter (fun s => ¬ (η s = 0) ∧ ¬ (3 ≤ η s)))
      = Finset.univ := by
    ext s
    simp only [hzero, htail, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hmid : (Finset.univ.filter (fun s => ¬ (η s = 0) ∧ ¬ (3 ≤ η s)))
      = Finset.univ.filter (fun s => η s = 1 ∨ η s = 2) := by
    apply Finset.filter_congr
    intro s _
    omega
  have hdz : Disjoint zero tail := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [hzero, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [htail, Finset.mem_filter, Finset.mem_univ, true_and] at hs'
    omega
  have hdzt : Disjoint (zero ∪ tail)
      (Finset.univ.filter (fun s => ¬ (η s = 0) ∧ ¬ (3 ≤ η s))) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_union, hzero, htail, Finset.mem_filter, Finset.mem_univ,
      true_and] at hs hs'
    omega
  have hcard : (zero ∪ tail ∪ (Finset.univ.filter (fun s => ¬ (η s = 0) ∧ ¬ (3 ≤ η s)))).card
      = zero.card + tail.card +
        (Finset.univ.filter (fun s => ¬ (η s = 0) ∧ ¬ (3 ≤ η s))).card := by
    rw [Finset.card_union_of_disjoint hdzt, Finset.card_union_of_disjoint hdz]
  rw [hcover, Finset.card_univ, hmid] at hcard
  have hcardR : (Fintype.card S : ℝ) = (zero.card : ℝ) + (tail.card : ℝ) +
      ((Finset.univ.filter (fun s => η s = 1 ∨ η s = 2)).card : ℝ) := by
    have h := hcard
    exact_mod_cast h
  have hfinal : 4 * ((Finset.univ.filter (fun s => η s = 1 ∨ η s = 2)).card : ℝ) ≥ N := by
    nlinarith [hcardR, hA0, hA3, hN0, hδ0]
  simpa [hN] using hfinal

/-- A second-moment bound of the stated form implies that at least one quarter of matrix sum
instances have one or two solutions. This isolates the concentration step in Lemma 5 of
[BaconChildsVanDam2005]. -/
theorem lemma5_of_second_moment [NeZero p] (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsec : (∑ xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p),
        (((solutions p r xw.1 xw.2).card : ℝ)) ^ 2)
      ≤ (2 - δ) * (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ)) :
    4 * ((Finset.univ.filter (fun xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p) =>
        (solutions p r xw.1 xw.2).card = 1 ∨ (solutions p r xw.1 xw.2).card = 2)).card : ℝ)
      ≥ (Fintype.card ((Fin r → Fin r → ZMod p) × (Fin r → ZMod p)) : ℝ) :=
  concentration_one_two (fun xw : (Fin r → Fin r → ZMod p) × (Fin r → ZMod p) =>
    (solutions p r xw.1 xw.2).card) δ hδ0 hδ1 (mean_eq_one p r) hsec

end Qatlib.Papers.SemidirectHSP05.MainResults.MatrixSumCount
