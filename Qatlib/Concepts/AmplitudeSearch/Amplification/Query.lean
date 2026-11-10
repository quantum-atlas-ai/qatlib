/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.QueryClock
import Qatlib.Concepts.AmplitudeSearch.Amplification.CompletionLaw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
noncomputable def queryCompletion {N : ℕ} (e : Fin N ≃ Fin N) (skip : RankSkip N)
    (t budget : ℕ) : ℝ :=
  (queryBBHTLaw e).completionMass skip (TerminalBooleanQueries (ExponentialSizes N)) t budget

theorem queryCompletion_law {N : ℕ} (e : Fin N ≃ Fin N) (skip : RankSkip N)
    (t : ℕ) (htN : t < N) (budget : ℕ) :
    HasSum (fun xs : List (SearchTrace N) => if runQueries xs ≤ budget then
      (queryBBHTLaw e).runMass skip t xs else 0) (queryCompletion e skip t budget) ∧
      0 ≤ queryCompletion e skip t budget ∧ queryCompletion e skip t budget ≤ 1 :=
  (queryBBHTLaw e).completion_law skip (TerminalBooleanQueries (ExponentialSizes N)) t htN budget

theorem queryCompletion_zero {N : ℕ} (e : Fin N ≃ Fin N) (skip : RankSkip N)
    (hN : 0 < N) (budget : ℕ) : queryCompletion e skip 0 budget = 1 :=
  (queryBBHTLaw e).completion_zero skip (TerminalBooleanQueries (ExponentialSizes N)) hN budget

theorem queryCompletion_step {N : ℕ} (e : Fin N ≃ Fin N) (skip : RankSkip N)
    (t : ℕ) (ht : 0 < t) (htN : t < N) (budget : ℕ) :
    HasSum (fun x : SearchTrace N =>
      if TerminalBooleanQueries (ExponentialSizes N) x ≤ budget then
        (queryBBHTLaw e).mass t x * queryCompletion e skip
          (skip.next ((queryBBHTLaw e).outputRank x))
          (budget - TerminalBooleanQueries (ExponentialSizes N) x) else 0)
      (queryCompletion e skip t budget) :=
  (queryBBHTLaw e).completion_step skip (TerminalBooleanQueries (ExponentialSizes N)) t ht htN budget

end Qatlib.Concepts.AmplitudeSearch.Amplification
