/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.PathBudget
import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.AllocationBound

/-!
# Recorded erasure runs and survival

The distribution `recordedRun` samples complete policy histories, including continuations after
a complete erasure, and `survives` tests the masks along the resulting path. Pushing the history
distribution through this test recovers `execute`, transferring the exponential survival bound
to recorded runs [BhartiHaugTanggara2026].

## Main statements

* `recordedRun_survival`: The history survival pushforward equals the operational survival law.
* `recorded_survival_le_exp`: Recorded survival obeys the same exponential budget bound.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators
namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- The distribution of complete policy histories obtained by sampling every random choice,
erasure mask, and observation along the path. -/
noncomputable def recordedRun {R : Type*} (p : ℝ≥0) (hp : p ≤ 1) {S C : ℕ} :
    (policy : ErasurePolicy R S C) → PMF (History policy)
  | .done => PMF.pure PUnit.unit
  | .random draw next => draw.bind (fun r => (recordedRun p hp (next r)).map (fun h => ⟨r,h⟩))
  | .noise width observe next =>
      (erasureMask width.val p hp).bind (fun mask => (observe mask).bind (fun r =>
        (recordedRun p hp (next mask r)).map (fun h => ⟨mask,r,h⟩)))

/-- The Boolean test that every noise mask along a complete policy history avoids complete
erasure. -/
noncomputable def survives {R : Type*} {S C : ℕ} (policy : ErasurePolicy R S C) :
    History policy → Bool :=
  match policy with
  | .done => fun _ => true
  | .random _ next => fun h => survives (next h.1) h.2
  | .noise _ _ next => fun h =>
      if h.1 = (fun _ => true) then false else survives (next h.1 h.2.1) h.2.2

/-- Mapping the complete-history distribution through `survives` gives exactly the Boolean
distribution `execute`. -/
theorem recordedRun_survival {R : Type*} (p : ℝ≥0) (hp : p ≤ 1) {S C : ℕ}
    (policy : ErasurePolicy R S C) :
    (recordedRun p hp policy).map (survives policy) = execute p hp policy := by
  induction policy with
  | done => simp [recordedRun, survives, execute, PMF.pure_map]
  | random draw next ih =>
    simp only [recordedRun, PMF.map_bind, PMF.map_comp, survives, Function.comp_def, ih, execute]
  | @noise steps budget width observe next ih =>
    classical
    simp only [recordedRun, PMF.map_bind, PMF.map_comp]
    congr 1
    funext mask
    by_cases hmask : mask = (fun _ => true)
    · simp only [survives, hmask, if_true, Function.comp_def]
      change ((observe (fun _ => true)).bind (fun r =>
        (recordedRun p hp (next mask r)).map (Function.const _ false))) = PMF.pure false
      simp only [PMF.map_const, PMF.bind_const]
    · simp only [survives, hmask, if_false, Function.comp_def, ih]

/-- For `0 < p < 1` and a positive number of steps, the real probability that a recorded history
survives is at most exp(-S p^(C/S)). -/
theorem recorded_survival_le_exp {R : Type*} (p : ℝ≥0) (hp : 0 < p) (hp1 : p < 1)
    {S C : ℕ} (hS : 0 < S) (policy : ErasurePolicy R S C) :
    (((recordedRun p hp1.le policy).map (survives policy)) true).toReal ≤
      Real.exp (-(S : ℝ) * (p : ℝ) ^ ((C : ℝ)/(S : ℝ))) := by
  rw [recordedRun_survival]
  exact execute_survival_le_exp p hp hp1 hS policy

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
