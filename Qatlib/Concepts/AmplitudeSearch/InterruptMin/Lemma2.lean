/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall
import Qatlib.Concepts.AmplitudeSearch.Amplification.TableRun

/-!
# The minimum-search source-clock contract

This module defines `Lemma2`, combining normalization of uniformly initialized BBHT traces with
correctness of every positive-mass checked output. It also records an expected source-clock
bound of `(45 / 4) * √N + (7 / 10) * (binaryLog N)²`.

The contract captures the expected-time analysis of quantum minimum finding [DurrHoyer1996].

## Main statements

* `Lemma2`: The contract asserting normalized minimum-search trace masses, global minimality of
  positive-mass final checked indices, and the stated square-root-plus-logarithmic expected
  source-clock bound [DurrHoyer1996].

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

/-- The contract asserting normalized minimum-search trace masses, global minimality of
positive-mass final checked indices, and the stated square-root-plus-logarithmic expected
source-clock bound [DurrHoyer1996]. -/
def Lemma2 : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α),
    let ranked := SortedRankedTable.ofTable T
    let law := sourceBBHTLaw ranked.indexOfRank hN
    HasSum (law.initialMass ranked.skip) 1 ∧
    (∀ x : Fin N × List (SearchTrace N), 0 < law.initialMass ranked.skip x →
      ∀ i : Fin N, T (finalCheckedIndex T (ranked.indexOfRank x.1)
        (tableClockedTrace ranked law x.2)) ≤ T i) ∧
    ∃ q : ℝ, HasSum (fun x : Fin N × List (SearchTrace N) =>
      law.initialMass ranked.skip x * law.runClock x.2) q ∧
      0 ≤ q ∧ q ≤ (45 / 4 : ℝ) * Real.sqrt N + (7 / 10 : ℝ) * (binaryLog N) ^ 2

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
