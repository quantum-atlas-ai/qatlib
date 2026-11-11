/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Zify
import Qatlib.Papers.CertQuery09.MainResults.Source.SpectralBound
import Qatlib.Papers.CertQuery09.MainResults.Source.QueryLowerSum
import Qatlib.Papers.CertQuery09.MainResults.Source.TwoLevelAdversary

/-!
# Product adversary matrices for two-level certification

This module constructs a product adjacency matrix by changing exactly one component of a tuple
of two-level representatives. Its operator norm grows linearly with the number of components,
while each query-filtered row sum remains bounded by `d`, yielding the explicit product lower
bound used in the certification analysis of [AmbainisEtAl2009].

## Main statements

* `gammaProd_opNorm`: computes the product matrix norm.
* `two_level_prod_adv_ratio_ge`: bounds the explicit adversary ratio below by `t * (d - 1)`.
* `two_level_prod_advValue_ge`: transfers this bound to the adversary value under boundedness of
  the ratio set.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CertQuery09.MainResults.Source

variable {d : ℕ}

/-- Adjacency of tuples that are representative-adjacent in one component and equal in every
other component. -/
def prodAdj (t : ℕ) (X Y : Fin t → TwoLevelRep d) : Prop :=
  ∃ j : Fin t, repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l

/-- The component witnessing product adjacency is unique. -/
theorem prodAdj_witness_unique {t : ℕ} {X Y : Fin t → TwoLevelRep d} {j j' : Fin t}
    (hj : repAdj (X j) (Y j) ∧ ∀ l, l ≠ j → X l = Y l)
    (hj' : repAdj (X j') (Y j') ∧ ∀ l, l ≠ j' → X l = Y l) : j = j' := by
  by_contra hne
  have hX : X j' = Y j' := hj.2 j' (fun h => hne h.symm)
  exact hj'.1.1 (congrArg repRow hX)

/-- Product adjacency is symmetric. -/
theorem prodAdj_comm {t : ℕ} {X Y : Fin t → TwoLevelRep d}
    (h : prodAdj (d := d) t X Y) : prodAdj t Y X := by
  obtain ⟨j, hadj, hagree⟩ := h
  exact ⟨j, repAdj_comm hadj, fun l hl => (hagree l hl).symm⟩

/-- The real zero-one adjacency matrix of the product relation on tuples of two-level
representatives. -/
def gammaProd (t : ℕ) : Matrix (Fin t → TwoLevelRep d) (Fin t → TwoLevelRep d) ℝ := by
  classical exact fun X Y => if prodAdj t X Y then 1 else 0

/-- The product adjacency matrix is symmetric. -/
theorem gammaProd_symm (t : ℕ) :
    ∀ X Y, gammaProd (d := d) t X Y = gammaProd t Y X := by
  classical
  intro X Y
  unfold gammaProd
  by_cases h : prodAdj (d := d) t X Y
  · rw [if_pos h, if_pos (prodAdj_comm h)]
  · rw [if_neg h, if_neg (fun h' => h (prodAdj_comm h'))]

/-- Every entry of the product adjacency matrix is nonnegative. -/
theorem gammaProd_nonneg (t : ℕ) : ∀ X Y, 0 ≤ gammaProd (d := d) t X Y := by
  classical
  intro X Y
  unfold gammaProd
  split <;> norm_num

/-- The product adjacency matrix vanishes between tuples with the same componentwise output. -/
theorem gammaProd_eq_zero (t : ℕ) :
    ∀ X Y, sumFun (repFun (d := d)) t X = sumFun (repFun (d := d)) t Y →
      gammaProd (d := d) t X Y = 0 := by
  classical
  intro X Y h
  unfold gammaProd
  rw [if_neg]
  intro hadj
  obtain ⟨j, hadj, _⟩ := hadj
  have hf := congrFun h j
  simp only [sumFun] at hf
  exact hadj.1 hf

/-- Each product adjacency entry is the sum of the indicators for its possible single-component
witnesses. -/
theorem gammaProd_eq_indicator_sum (t : ℕ) (X Y : Fin t → TwoLevelRep d) :
    gammaProd (d := d) t X Y
      = ∑ j : Fin t,
          (if repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l then (1 : ℝ) else 0) := by
  classical
  unfold gammaProd
  by_cases h : prodAdj (d := d) t X Y
  · have hsum : ∑ j : Fin t,
          (if repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l then (1 : ℝ) else 0) = 1 := by
      obtain ⟨j0, hj0⟩ := h
      rw [Finset.sum_eq_single j0]
      · exact if_pos hj0
      · intro j _ hj
        exact if_neg (fun hc => hj (prodAdj_witness_unique hc hj0))
      · intro hmem
        exact absurd (Finset.mem_univ j0) hmem
    rw [if_pos h, hsum]
  · have hsum : ∑ j : Fin t,
          (if repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      exact if_neg (fun hc => h ⟨j, hc⟩)
    rw [if_neg h, hsum]

/-- The number of product neighbors witnessed by a fixed component equals the number of
representative neighbors of that component. -/
theorem filter_witness_card (t : ℕ) (X : Fin t → TwoLevelRep d) (j : Fin t) :
    (Finset.univ.filter (fun Y : Fin t → TwoLevelRep d =>
        repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l)).card
      = (Finset.univ.filter (fun q : TwoLevelRep d => repAdj (X j) q)).card := by
  classical
  refine Finset.card_bij (fun Y _ => Y j) ?_ ?_ ?_
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
    exact hY.1
  · intro Y hY Y' hY' heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY hY'
    funext l
    by_cases hl : l = j
    · subst hl; exact heq
    · rw [← hY.2 l hl, ← hY'.2 l hl]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨fun l => if l = j then q else X l, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa using hq, fun l hl => by simp [hl]⟩
    · simp

/-- The real-valued cardinality of a filtered finite universe equals the sum of its zero-one
indicator function. -/
theorem card_filter_cast {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ) = ∑ x, (if P x then (1 : ℝ) else 0) := by
  rw [← Finset.sum_boole (p := P) (s := (Finset.univ : Finset ι))]

/-- For `d ≥ 1`, every row sum of the product adjacency matrix is `t * (d * (d - 1))`. -/
theorem gammaProd_row_sum (t : ℕ) (hd : 1 ≤ d) (X : Fin t → TwoLevelRep d) :
    ∑ Y, gammaProd (d := d) t X Y = ((t * (d * (d - 1)) : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_congr rfl fun Y _ => gammaProd_eq_indicator_sum t X Y, Finset.sum_comm]
  have hper : ∀ j : Fin t,
      ∑ Y : Fin t → TwoLevelRep d,
        (if repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l then (1 : ℝ) else 0)
      = ((d - 1) * d : ℝ) := by
    intro j
    have hcard := filter_witness_card t X j
    have hsum := card_filter_cast
      (fun Y : Fin t → TwoLevelRep d =>
        repAdj (X j) (Y j) ∧ ∀ l : Fin t, l ≠ j → X l = Y l)
    rw [← hsum, hcard, card_neighbours (X j)]
    rw [Nat.cast_mul, Nat.cast_sub hd, Nat.cast_one]
  rw [Finset.sum_congr rfl fun j _ => hper j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hd, Nat.cast_one]
  ring

/-- For `d ≥ 1` and positive `t`, the Euclidean operator norm of the product adjacency matrix is
`t * (d * (d - 1))`. -/
theorem gammaProd_opNorm (t : ℕ) (hd : 1 ≤ d) (_ht : 0 < t) :
    ‖gammaProd (d := d) t‖ = ((t * (d * (d - 1)) : ℕ) : ℝ) := by
  haveI : Nonempty (Fin t → TwoLevelRep d) :=
    ⟨fun _ => ⟨(⟨0, hd⟩, fun _ => ⟨0, hd⟩), rfl⟩⟩
  exact l2_opNorm_eq_of_regular (gammaProd (d := d) t) (gammaProd_nonneg t)
    (gammaProd_symm t) (gammaProd_row_sum t hd)

/-- The query-filtered product adjacency entry is one exactly when the tuples are
product-adjacent and differ at the queried input bit, and is zero otherwise. -/
theorem hadamard_gammaProd (hn : 0 < d * d) (t : ℕ)
    (X Y : Fin t → TwoLevelRep d) (i : Fin (d * d * t)) :
    (gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hn) i) X Y
      = if prodAdj (d := d) t X Y ∧
            sumBit (repBits d) t hn X i ≠ sumBit (repBits d) t hn Y i
        then (1 : ℝ) else 0 := by
  classical
  unfold gammaProd diffMatrix
  by_cases h1 : prodAdj (d := d) t X Y <;>
    by_cases h2 : sumBit (repBits d) t hn X i = sumBit (repBits d) t hn Y i <;>
    simp [h1, h2]

/-- Every row sum of a query-filtered product adjacency matrix is at most `d`. -/
theorem hadamard_gammaProd_row_sum_le (hn : 0 < d * d) (t : ℕ)
    (X : Fin t → TwoLevelRep d) (i : Fin (d * d * t)) :
    ∑ Y, (gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hn) i) X Y
      ≤ (d : ℝ) := by
  classical
  set b : Fin t := ⟨i.1 / (d * d), Nat.div_lt_of_lt_mul i.2⟩ with hb
  set ip : Fin (d * d) := ⟨i.1 % (d * d), Nat.mod_lt _ hn⟩ with hip
  set rc : Fin d × Fin d := finProdFinEquiv.symm ip with hrc
  have hbit : ∀ Y : Fin t → TwoLevelRep d,
      sumBit (repBits d) t hn Y i = repBits d (Y b) ip := by
    intro Y
    simp only [sumBit, hb, hip]

  set S : Finset (Fin t → TwoLevelRep d) :=
    Finset.univ.filter (fun Y =>
      repAdj (X b) (Y b) ∧ ∀ l : Fin t, l ≠ b → X l = Y l) with hS
  set T : Finset (TwoLevelRep d) :=
    Finset.univ.filter (fun q => repAdj (X b) q ∧ repBits d (X b) ip ≠ repBits d q ip) with hT

  have hsum : ∑ Y, (gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hn) i) X Y
      = ((Finset.univ.filter (fun Y : Fin t → TwoLevelRep d =>
          prodAdj (d := d) t X Y ∧
            sumBit (repBits d) t hn X i ≠ sumBit (repBits d) t hn Y i)).card : ℝ) := by
    rw [card_filter_cast
      (fun Y : Fin t → TwoLevelRep d =>
        prodAdj (d := d) t X Y ∧
          sumBit (repBits d) t hn X i ≠ sumBit (repBits d) t hn Y i)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [hadamard_gammaProd hn t X Y i]

  have hinj : (Finset.univ.filter (fun Y : Fin t → TwoLevelRep d =>
        prodAdj (d := d) t X Y ∧
          sumBit (repBits d) t hn X i ≠ sumBit (repBits d) t hn Y i)).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun Y => Y b) ?_ ?_
    · intro Y hY
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hY
      obtain ⟨hprod, hdiff⟩ := hY
      obtain ⟨j, hadj, hagree⟩ := hprod
      have hjb : j = b := by
        by_contra hne
        apply hdiff
        have hXb : X b = Y b := hagree b (fun h => hne h.symm)
        rw [hbit X, hbit Y, hXb]
      subst hjb
      simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj, by rw [← hbit X, ← hbit Y]; exact hdiff⟩
    · intro Y hY Y' hY' heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hY hY'
      obtain ⟨hprod, hdiff⟩ := hY
      obtain ⟨hprod', hdiff'⟩ := hY'
      obtain ⟨j, _, hagree⟩ := hprod
      obtain ⟨j', _, hagree'⟩ := hprod'
      have hjb : j = b := by
        by_contra hne
        exfalso
        apply hdiff
        have hXb : X b = Y b := hagree b (fun h => hne h.symm)
        rw [hbit X, hbit Y, hXb]
      have hjb' : j' = b := by
        by_contra hne
        exfalso
        apply hdiff'
        have hXb : X b = Y' b := hagree' b (fun h => hne h.symm)
        rw [hbit X, hbit Y', hXb]
      subst hjb
      subst hjb'
      funext l
      by_cases hl : l = b
      · subst hl; exact heq
      · rw [← hagree l hl, ← hagree' l hl]

  have hTcard : T.card ≤ d := by
    rw [hT]
    have : (Finset.univ.filter (fun q : TwoLevelRep d =>
          repAdj (X b) q ∧ repBits d (X b) ip ≠ repBits d q ip)).card
        ≤ (Finset.univ.filter (fun q : TwoLevelRep d =>
          repAdj (X b) q ∧ repMat (X b) rc.1 rc.2 ≠ repMat q rc.1 rc.2)).card := by
      refine Finset.card_le_card ?_
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      refine ⟨hq.1, ?_⟩
      intro heq
      have hip' : finProdFinEquiv rc = ip := by
        rw [hrc]; exact Equiv.apply_symm_apply finProdFinEquiv ip
      exact hq.2 (by rw [← hip', repBits_finProdFinEquiv, repBits_finProdFinEquiv, heq])
    exact le_trans this (filter_diff_card_le (X b) rc.1 rc.2)
  calc ∑ Y, (gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hn) i) X Y
      = ((Finset.univ.filter (fun Y : Fin t → TwoLevelRep d =>
          prodAdj (d := d) t X Y ∧
            sumBit (repBits d) t hn X i ≠ sumBit (repBits d) t hn Y i)).card : ℝ) := hsum
    _ ≤ (T.card : ℝ) := by exact_mod_cast hinj
    _ ≤ (d : ℝ) := by exact_mod_cast hTcard

/-- For positive block and total input lengths, the adversary denominator of the product
adjacency matrix is at most `d`. -/
theorem gammaProd_advDenom_le (t : ℕ) (hdd : 0 < d * d) (HN : 0 < d * d * t) :
    advDenom (sumBit (repBits d) t hdd) HN (gammaProd (d := d) t) ≤ (d : ℝ) := by
  classical
  unfold advDenom
  refine Finset.sup'_le _ _ fun i _ => ?_
  refine l2_opNorm_le_of_row_sum_le (r := (d : ℝ)) _ (fun X Y => ?_) (fun X Y => ?_)
    (Nat.cast_nonneg d) (fun X => hadamard_gammaProd_row_sum_le hdd t X i)
  · exact mul_nonneg (gammaProd_nonneg t X Y)
      (by unfold diffMatrix; split <;> norm_num)
  · exact hadamard_symm (gammaProd (d := d) t)
      (diffMatrix (sumBit (repBits d) t hdd) i)
      (gammaProd_symm t) (fun x y => diffMatrix_symm _ _ x y) X Y

/-- The two-level representative with distinguished row zero and all stored positions zero,
defined when `d ≥ 1`. -/
def baseRep (d : ℕ) (hd : 1 ≤ d) : TwoLevelRep d :=
  ⟨(⟨0, hd⟩, fun _ => ⟨0, hd⟩), rfl⟩

/-- For `d ≥ 2` and positive tuple length, the product adjacency matrix is nonzero. -/
theorem gammaProd_ne_zero {t : ℕ} (hd : 2 ≤ d) (ht : 0 < t) :
    gammaProd (d := d) t ≠ 0 := by
  classical
  let p0 : TwoLevelRep d := ⟨(⟨0, by omega⟩, fun _ => ⟨0, by omega⟩), rfl⟩
  let j1 : Fin d := ⟨1, by omega⟩
  have hj1 : j1 ≠ repRow p0 := by
    intro h
    have h0 : (repRow p0).val = 0 := rfl
    have h1 : j1.val = 1 := rfl
    rw [h] at h1
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  let q : TwoLevelRep d := repRebuild p0 j1 ⟨0, by omega⟩
  let j0 : Fin t := ⟨0, ht⟩
  let X : Fin t → TwoLevelRep d := fun _ => p0
  let Y : Fin t → TwoLevelRep d := fun l => if l = j0 then q else p0
  have hq : repAdj p0 q := repRebuild_adj p0 j1 ⟨0, by omega⟩ hj1
  have hprod : prodAdj (d := d) t X Y := by
    refine ⟨j0, ?_, ?_⟩
    · show repAdj (X j0) (Y j0)
      rw [show X j0 = p0 from rfl, show Y j0 = q from by simp [Y]]
      exact hq
    · intro l hl
      show X l = Y l
      simp only [X, Y, hl, if_false]
  intro h
  have h1 := congrFun (congrFun h X) Y
  unfold gammaProd at h1
  rw [if_pos hprod] at h1
  exact one_ne_zero h1

/-- Querying the concatenated input at offset `j * (d * d) + ip` returns bit `ip` of component
`j`. -/
theorem sumBit_eq_of_block (hn : 0 < d * d) (t : ℕ) (X : Fin t → TwoLevelRep d)
    (j : Fin t) (ip : Fin (d * d)) :
    sumBit (repBits d) t hn X
        ⟨j.1 * (d * d) + ip.1, by
          have hj := j.2; have hi := ip.2
          have : (d * d) * (j.1 + 1) ≤ (d * d) * t :=
            Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hj)
          nlinarith [this]⟩
      = repBits d (X j) ip := by
  simp only [sumBit]
  have hdiv : (j.1 * (d * d) + ip.1) / (d * d) = j.1 := by
    rw [Nat.mul_comm j.1 (d * d), Nat.mul_add_div hn, Nat.div_eq_of_lt ip.2, Nat.add_zero]
  have hmod : (j.1 * (d * d) + ip.1) % (d * d) = ip.1 := by
    rw [Nat.mul_comm j.1 (d * d), Nat.mul_add_mod, Nat.mod_eq_of_lt ip.2]
  refine congrArg₂ (repBits d) ?_ ?_
  · exact congrArg X (Fin.ext hdiv)
  · exact Fin.ext hmod

/-- For `d ≥ 2` and positive tuple length, the product adjacency matrix has a strictly positive
adversary denominator. -/
theorem gammaProd_advDenom_pos {t : ℕ} (hd : 2 ≤ d) (hdd : 0 < d * d) (ht : 0 < t)
    (HN : 0 < d * d * t) :
    0 < advDenom (sumBit (repBits d) t hdd) HN (gammaProd (d := d) t) := by
  classical
  let p0 : TwoLevelRep d := ⟨(⟨0, by omega⟩, fun _ => ⟨0, by omega⟩), rfl⟩
  let j1 : Fin d := ⟨1, by omega⟩
  have hj1 : j1 ≠ repRow p0 := by
    intro h
    have h0 : (repRow p0).val = 0 := rfl
    have h1 : j1.val = 1 := rfl
    rw [h] at h1; rw [h0] at h1
    exact absurd h1 (by norm_num)
  let q : TwoLevelRep d := repRebuild p0 j1 ⟨0, by omega⟩
  have hq : repAdj p0 q := repRebuild_adj p0 j1 ⟨0, by omega⟩ hj1
  let c : Fin d := repPos q (repRow p0)
  let ip : Fin (d * d) := finProdFinEquiv (repRow p0, c)
  let j0 : Fin t := ⟨0, ht⟩
  let X : Fin t → TwoLevelRep d := fun _ => p0
  let Y : Fin t → TwoLevelRep d := fun l => if l = j0 then q else p0
  have hprod : prodAdj (d := d) t X Y := by
    refine ⟨j0, ?_, ?_⟩
    · show repAdj (X j0) (Y j0)
      rw [show X j0 = p0 from rfl, show Y j0 = q from by simp [Y]]
      exact hq
    · intro l hl; show X l = Y l; simp only [X, Y, hl, if_false]
  let i : Fin (d * d * t) :=
    ⟨j0.1 * (d * d) + ip.1, by
      have hj := j0.2; have hi := ip.2
      have : (d * d) * (j0.1 + 1) ≤ (d * d) * t :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hj)
      nlinarith [this]⟩
  have hbits_p : sumBit (repBits d) t hdd X i = true := by
    have h := sumBit_eq_of_block hdd t X j0 ip
    rw [h]
    show repBits d (X j0) ip = true
    rw [show X j0 = p0 from rfl]
    show repBits d p0 ip = true
    unfold repBits repBitsPair
    simp [ip, repMat, c]
  have hbits_q : sumBit (repBits d) t hdd Y i = false := by
    have h := sumBit_eq_of_block hdd t Y j0 ip
    rw [h]
    show repBits d (Y j0) ip = false
    rw [show Y j0 = q from by simp [Y]]
    show repBits d q (finProdFinEquiv (repRow p0, repPos q (repRow p0))) = false
    rw [repBits_finProdFinEquiv]
    simp [repMat, hq.1]
  have hentry : (gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hdd) i) X Y = 1 := by
    rw [hadamard_gammaProd hdd t X Y i]
    have hne : sumBit (repBits d) t hdd X i ≠ sumBit (repBits d) t hdd Y i := by
      rw [hbits_p, hbits_q]; simp
    simp [hprod, hne]
  have hne0 : (gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hdd) i) ≠ 0 := by
    intro h
    have h1 := congrFun (congrFun h X) Y
    simp only [hentry] at h1
    exact one_ne_zero h1
  have hpos_norm : 0 < ‖gammaProd (d := d) t ⊙ diffMatrix (sumBit (repBits d) t hdd) i‖ := by
    rw [norm_pos_iff]
    exact hne0
  unfold advDenom
  rw [Finset.lt_sup'_iff ⟨⟨0, HN⟩, Finset.mem_univ _⟩]
  exact ⟨i, Finset.mem_univ _, hpos_norm⟩

/-- For `d ≥ 2` and positive tuple length `t`, the product adjacency matrix's adversary ratio is
at least `t * (d - 1)`. -/
theorem two_level_prod_adv_ratio_ge {t : ℕ} (hd : 2 ≤ d) (ht : 0 < t)
    (hdd : 0 < d * d) (HN : 0 < d * d * t) :
    (t : ℝ) * ((d : ℝ) - 1)
      ≤ ‖gammaProd (d := d) t‖ /
          advDenom (sumBit (repBits d) t hdd) HN (gammaProd (d := d) t) := by
  have hden := gammaProd_advDenom_pos (d := d) hd hdd ht HN
  rw [le_div_iff₀ hden]
  have hle := gammaProd_advDenom_le (d := d) t hdd HN
  have hop := gammaProd_opNorm (d := d) t (by omega) ht
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (le_trans (by norm_num) hd)
  calc (t : ℝ) * ((d : ℝ) - 1) * advDenom (sumBit (repBits d) t hdd) HN (gammaProd (d := d) t)
      ≤ (t : ℝ) * ((d : ℝ) - 1) * (d : ℝ) := by
          apply mul_le_mul_of_nonneg_left hle
          positivity
    _ = ((t * (d * (d - 1)) : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)]
          push_cast
          ring
    _ = ‖gammaProd (d := d) t‖ := hop.symm

/-- For `d ≥ 2` and positive tuple length `t`, boundedness above of the product adversary-ratio
set implies that its adversary value is at least `t * (d - 1)`. This is the explicit
two-level product lower bound used in the certification analysis of [AmbainisEtAl2009]. -/
theorem two_level_prod_advValue_ge {t : ℕ} (hd : 2 ≤ d) (ht : 0 < t)
    (hdd : 0 < d * d) (HN : 0 < d * d * t)
    (hbdd : BddAbove (advRatios (sumBit (repBits d) t hdd) HN (sumFun (repFun (d := d)) t))) :
    (t : ℝ) * ((d : ℝ) - 1)
      ≤ advValue (sumBit (repBits d) t hdd) HN (sumFun (repFun (d := d)) t) := by
  have hmem : ‖gammaProd (d := d) t‖ /
      advDenom (sumBit (repBits d) t hdd) HN (gammaProd (d := d) t)
      ∈ advRatios (sumBit (repBits d) t hdd) HN (sumFun (repFun (d := d)) t) :=
    ⟨gammaProd (d := d) t,
      ⟨gammaProd_ne_zero (d := d) hd ht, gammaProd_symm t, gammaProd_nonneg t, gammaProd_eq_zero t⟩,
      rfl⟩
  exact le_trans (two_level_prod_adv_ratio_ge (d := d) hd ht hdd HN) (le_csSup hbdd hmem)

end Qatlib.Papers.CertQuery09.MainResults.Source
