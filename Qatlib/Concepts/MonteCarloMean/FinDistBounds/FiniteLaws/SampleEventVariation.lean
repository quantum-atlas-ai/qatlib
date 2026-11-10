/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteDistributionVariation
import Mathlib.Data.Fin.Tuple.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.SampleEventVariation

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open FiniteInformationDivergence
open scoped BigOperators

variable {X : Type} [Fintype X]

theorem product_l1 {Y : Type} [Fintype Y] (p q : FinDist X) (r s : FinDist Y) :
    (∑ x, ∑ y, |p.prob x * r.prob y - q.prob x * s.prob y|) ≤
      (∑ x, |p.prob x - q.prob x|) + ∑ y, |r.prob y - s.prob y| := by
  calc
    _ ≤ ∑ x, ∑ y, (|p.prob x - q.prob x| * r.prob y +
        q.prob x * |r.prob y - s.prob y|) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have he : p.prob x * r.prob y - q.prob x * s.prob y =
          (p.prob x - q.prob x) * r.prob y + q.prob x * (r.prob y - s.prob y) := by ring
      rw [he]
      simpa only [abs_mul, abs_of_nonneg (r.nonneg y), abs_of_nonneg (q.nonneg x)] using
        abs_add_le ((p.prob x - q.prob x) * r.prob y)
          (q.prob x * (r.prob y - s.prob y))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, r.sum_one, mul_one]
      rw [← Finset.sum_mul, q.sum_one, one_mul]

theorem record_l1_succ (p q : FinDist X) (n : ℕ) :
    (∑ w : Fin (n + 1) → X, |p.probOf w - q.probOf w|) =
      ∑ x : X, ∑ w : Fin n → X,
        |p.prob x * p.probOf w - q.prob x * q.probOf w| := by
  symm
  calc
    _ = ∑ z : X × (Fin n → X),
        |p.prob z.1 * p.probOf z.2 - q.prob z.1 * q.probOf z.2| :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => X))
      intro z
      simp [FinDist.probOf, Fin.prod_univ_succ, Fin.consEquiv]

variable [DecidableEq X]

theorem record_l1 (p q : FinDist X) (n : ℕ) :
    (∑ w : Fin n → X, |p.probOf w - q.probOf w|) ≤
      (n : ℝ) * ∑ x, |p.prob x - q.prob x| := by
  induction n with
  | zero => simp [FinDist.probOf]
  | succ n ih =>
    rw [record_l1_succ]
    have h := product_l1 p q (records p n) (records q n)
    change (∑ x, ∑ w : Fin n → X,
      |p.prob x * p.probOf w - q.prob x * q.probOf w|) ≤ _ at h
    have h' := h.trans (add_le_add_right ih _)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h'

theorem record_tv (p q : FinDist X) (n : ℕ) :
    tv (records p n) (records q n) ≤ (n : ℝ) * tv p q := by
  have h := div_le_div_of_nonneg_right (record_l1 p q n) (by norm_num : (0 : ℝ) ≤ 2)
  change (∑ w : Fin n → X, |p.probOf w - q.probOf w|) / 2 ≤
    (n : ℝ) * ((∑ x, |p.prob x - q.prob x|) / 2)
  simpa only [mul_div_assoc] using h

theorem event_distance (p q : FinDist X) (n : ℕ)
    (E : (Fin n → X) → Prop) [DecidablePred E] :
    |p.probEvent E - q.probEvent E| ≤ (n : ℝ) * tv p q := by
  have h := FiniteDistributionVariation.event_distance (records p n) (records q n)
    (Finset.univ.filter E)
  exact h.trans (record_tv p q n)

theorem risk_transfer (p q : FinDist X) (n : ℕ)
    (E : (Fin n → X) → Prop) [DecidablePred E] (risk eps : ℝ)
    (hrisk : q.probEvent E ≤ risk) (happrox : tv p q ≤ eps) :
    p.probEvent E ≤ risk + (n : ℝ) * eps := by
  have he := (le_abs_self (p.probEvent E - q.probEvent E)).trans (event_distance p q n E)
  have hm := mul_le_mul_of_nonneg_left happrox (Nat.cast_nonneg n)
  linarith

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.SampleEventVariation
