/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WalkSpatial08.MainResults.RunCorrectness

@[expose] public section

/-!
# Examine and move counts for controlled lattice search

Section III charges one query and one nearest-neighbor move per iteration.
Section II.A prepares the initial distribution in a separate pass along each
axis. The count uses the existing scalar success model.
-/

set_option autoImplicit false

namespace Qatlib.Papers.WalkSpatial08.MainResults

open Qatlib.Papers.WalkSpatial08.MainResults

/-- Each controlled iteration charges one query and one move. The setup charges only moves. -/
def iterationCount (iterations setup : ℕ) : TimeAccount :=
  ⟨2 * iterations + setup, iterations, iterations + setup, by omega⟩

/-- The balanced schedule's existing total and success bound admit a query and move split. -/
theorem balanced_count :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ alg : LatticeBudgetSchedule n,
        alg.account.steps = controlledWalkTimeSteps n ∧
        alg.account.queries = alg.iterations ∧
        alg.account.moves = alg.iterations + alg.setup ∧
        c ≤ modelSuccessWeight n alg.iterations := by
  obtain ⟨c, hc, N₀, hschedule⟩ := balanced_schedule_bound
  refine ⟨c, hc, N₀, fun n hn => ?_⟩
  obtain ⟨alg, htotal, hsuccess⟩ := hschedule n hn
  let counted : LatticeBudgetSchedule n :=
    { iterations := alg.iterations
      setup := alg.setup
      account := iterationCount alg.iterations alg.setup
      steps_eq := rfl }
  exact ⟨counted, alg.steps_eq.symm.trans htotal, rfl, rfl, hsuccess⟩

/-- On a lattice of side length `n ≥ 16`, the two axes of source preparation add
`2 * n` moves to the balanced model schedule. -/
theorem source_count {n : ℕ} (hn : 16 ≤ n) :
    let iterations := Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n)))
    let account := iterationCount iterations (2 * n)
    account.steps = 2 * iterations + 2 * n ∧ account.queries = iterations ∧
      account.moves = iterations + 2 * n ∧
      1 / 66 ≤ modelSuccessWeight n iterations :=
  ⟨rfl, rfl, rfl, modelSuccessWeight_ge hn⟩

end Qatlib.Papers.WalkSpatial08.MainResults
