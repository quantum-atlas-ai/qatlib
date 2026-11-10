/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.TimeDependentSegmentSplitStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.CoherentSim.TimeDependent

private theorem evolution_partition {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (hA : Continuous A) (s : ℕ → ℝ) (n : ℕ) :
    ((List.ofFn (fun k : Fin n => orderedEvolution A (s k.val) (s (k.val + 1)))).reverse).prod =
      orderedEvolution A (s 0) (s n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.prod_cons, Fin.val_last, Fin.val_castSucc]
    rw [ih, orderedEvolution_cocycle A hA]

theorem timeDependentSegmentSplit : TimeDependentSegmentSplit := by
  intro I _ _ H t r hH _ hr
  have hn : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he := evolution_partition (fun u => Complex.I • H u) (by fun_prop)
    (fun k => (k : ℝ) * t / r) r
  simpa [hn] using! he.symm

end Qatlib.Concepts.CoherentSim.TimeDependent
