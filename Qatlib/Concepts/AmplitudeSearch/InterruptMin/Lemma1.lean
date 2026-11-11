/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.VisitLaw

/-!
# The minimum-search rank visit contract

This module defines `Lemma1`, collecting normalization and rank-visit statements for the BBHT
law associated with a sorted table. It records reciprocal-rank visit probabilities for distinct
values and upper bounds that allow ties.

The contract packages the visit analysis underlying minimum finding [DurrHoyer1996].

## Main statements

* `Lemma1`: The minimum-search rank-visit contract: normalization of run laws, reciprocal-rank
  visit formulas for distinct values, and nonnegative reciprocal-rank upper bounds when ties are
  allowed [DurrHoyer1996].

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

universe u

/-- The minimum-search rank-visit contract: normalization of run laws, reciprocal-rank visit
formulas for distinct values, and nonnegative reciprocal-rank upper bounds when ties are
allowed [DurrHoyer1996]. -/
def Lemma1 : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (α : Type u) [LinearOrder α] (T : Fin N → α),
    let ranked := SortedRankedTable.ofTable T
    let law := sourceBBHTLaw ranked.indexOfRank hN
    HasSum (law.initialMass ranked.skip) 1 ∧
    (∀ y : Fin N, HasSum (law.runMass ranked.skip
      (ranked.skip.next (ranked.indexOfRank.symm y))) 1) ∧
    (Function.Injective T →
      (∀ (t r : ℕ) (htN : t < N),
        rankMarked ranked.indexOfRank t =
          Finset.univ.filter (fun i => T i < T (ranked.indexOfRank ⟨t,htN⟩)) ∧
        HasSum (fun xs : List (SearchTrace N) =>
          if r ∈ law.rankTrace xs then law.runMass ranked.skip t xs else 0)
          (if 1 ≤ r ∧ r ≤ t then 1/(r : ℝ) else 0)) ∧
      (∀ r : ℕ, HasSum (fun x : Fin N × List (SearchTrace N) =>
        if r ∈ law.initialRankTrace x then law.initialMass ranked.skip x else 0)
        (if 1 ≤ r ∧ r ≤ N then 1/(r : ℝ) else 0))) ∧
    (∀ (y : Fin N) (r : ℕ),
      let t := ranked.skip.next (ranked.indexOfRank.symm y)
      rankMarked ranked.indexOfRank t = Finset.univ.filter (fun i => T i < T y) ∧
      ∃ q : ℝ, HasSum (fun xs : List (SearchTrace N) =>
        if r ∈ law.rankTrace xs then law.runMass ranked.skip t xs else 0) q ∧
        0 ≤ q ∧ q ≤ (if 1 ≤ r ∧ r ≤ t then 1/(r : ℝ) else 0)) ∧
    (∀ r : ℕ, ∃ q : ℝ, HasSum (fun x : Fin N × List (SearchTrace N) =>
      if r ∈ law.initialRankTrace x then law.initialMass ranked.skip x else 0) q ∧
      0 ≤ q ∧ q ≤ (if 1 ≤ r ∧ r ≤ N then 1/(r : ℝ) else 0))

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
