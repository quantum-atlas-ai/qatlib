/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

/-!
# Classical needle search bounds

This module specializes deterministic query trees to equality testing for an unknown target
using `needleOracle`. A tree using at most `M` actual queries can correctly recover at most `M +
1` possible targets.

The counting bound yields upper bounds on uniform success probability for deterministic trees
and finite randomized mixtures, giving a classical search benchmark for the quantum search
setting of [Grover1997].

## Main statements

* `bounded_needle_recovery_card`: at most `M + 1` targets are recoverable within `M` queries.
* `actual_needle_exact_lower`: exact recovery requires at least the number of targets minus one
  queries.
* `randomized_needle_success_upper`: the corresponding success bound for randomized mixtures.

## References

* [Grover, 1997][Grover1997]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

/-- The Boolean equality oracle that returns true exactly when the queried address equals the
target. -/
def needleOracle {I : Type} [DecidableEq I] (target address : I) : Bool :=
  decide (address = target)

/-- A classical needle search tree recovers at most `M + 1` targets correctly if each successful
run uses at most `M` queries. -/
theorem bounded_needle_recovery_card {I : Type} [DecidableEq I]
    (tree : QueryTree I Bool I) :
    ∀ (S : Finset I) (M : ℕ),
      (∀ y ∈ S, (run (needleOracle y) tree).1 = y) →
      (∀ y ∈ S, (run (needleOracle y) tree).2 ≤ M) → S.card ≤ M + 1 := by
  classical
  induction tree with
  | leaf value =>
    intro S M hcorrect _
    have hs : S ⊆ {value} := by
      intro y hy
      simpa only [run, Finset.mem_singleton] using (hcorrect y hy).symm
    have hc : S.card ≤ 1 := by simpa using Finset.card_le_card hs
    omega
  | ask q next ih =>
    intro S M hcorrect hcost
    cases M with
    | zero =>
      have hs : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hc := hcost y hy
        simp [run] at hc
      simp [hs]
    | succ M =>
      have ha (y : I) (hy : y ∈ S.erase q) : needleOracle y q = false := by
        have h := (Finset.mem_erase.mp hy).1
        simp [needleOracle, Ne.symm h]
      have hc : (S.erase q).card ≤ M + 1 := by
        apply ih false (S.erase q) M
        · intro y hy
          simpa only [run, ha y hy] using hcorrect y (Finset.mem_of_mem_erase hy)
        · intro y hy
          have h := hcost y (Finset.mem_of_mem_erase hy)
          simp only [run, ha y hy] at h
          omega
      have he : S.card ≤ (S.erase q).card + 1 := by
        by_cases hq : q ∈ S
        · exact (Finset.card_erase_add_one hq).ge
        · simp [Finset.erase_eq_of_notMem hq]
      omega

/-- Exact classical recovery of every target with at most `M` actual queries requires the number
of targets to be at most `M + 1`. -/
theorem actual_needle_exact_lower {I : Type} [Fintype I] [DecidableEq I]
    (tree : QueryTree I Bool I) (M : ℕ)
    (hcorrect : ∀ y, (run (needleOracle y) tree).1 = y)
    (hcost : ∀ y, (run (needleOracle y) tree).2 ≤ M) :
    Fintype.card I ≤ M + 1 := by
  simpa using bounded_needle_recovery_card tree Finset.univ M
    (fun y _ => hcorrect y) (fun y _ => hcost y)

/-- The fraction of targets recovered correctly by a classical needle search tree under the
uniform distribution. -/
noncomputable def needleSuccess {I : Type} [Fintype I] [DecidableEq I]
    (tree : QueryTree I Bool I) : ℝ :=
  ((Finset.univ.filter (fun y => (run (needleOracle y) tree).1 = y)).card : ℝ) /
    Fintype.card I

/-- A classical needle search tree using at most `M` queries on every target has uniform success
probability at most `(M + 1) / Fintype.card I`. -/
theorem actual_needle_success_upper {I : Type} [Fintype I] [DecidableEq I]
    (tree : QueryTree I Bool I) (M : ℕ)
    (hcost : ∀ y, (run (needleOracle y) tree).2 ≤ M) :
    needleSuccess tree ≤ ((M : ℝ) + 1) / Fintype.card I := by
  classical
  have hc := bounded_needle_recovery_card tree
    (Finset.univ.filter (fun y => (run (needleOracle y) tree).1 = y)) M
    (fun y hy => (Finset.mem_filter.mp hy).2) (fun y _ => hcost y)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

/-- A finite probability mixture of classical needle search trees, each using at most `M`
queries, has uniform success probability at most `(M + 1) / Fintype.card I`. -/
theorem randomized_needle_success_upper {I S : Type} [Fintype I] [DecidableEq I]
    [Fintype S] (weight : S → ℝ) (tree : S → QueryTree I Bool I) (M : ℕ)
    (hw : ∀ s, 0 ≤ weight s) (hmass : ∑ s, weight s = 1)
    (hcost : ∀ s y, (run (needleOracle y) (tree s)).2 ≤ M) :
    ∑ s, weight s * needleSuccess (tree s) ≤ ((M : ℝ) + 1) / Fintype.card I := by
  calc
    _ ≤ ∑ s, weight s * (((M : ℝ) + 1) / Fintype.card I) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (actual_needle_success_upper (tree s) M (hcost s)) (hw s)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
