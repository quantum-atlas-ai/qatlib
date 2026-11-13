/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.TimeDependentSegmentSplitStat

/-!
# Splitting ordered evolution into time segments

This module proves `timeDependentSegmentSplit`, expressing evolution over a time interval as the
reverse list product of evolutions over equal subintervals. The auxiliary result
`evolution_partition` derives the corresponding identity for an arbitrary sequence of endpoints
from the cocycle law.

The mathematical context is discussed in [BerryEtAl2015Taylor].

## Main statements

* `evolution_partition`: The ordered product identity for a sequence of endpoints.
* `timeDependentSegmentSplit`: The equal segment decomposition of continuous ordered evolution.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.CoherentSim.TimeDependent

/-- For a continuous generator, the reverse list product of consecutive evolutions from `s k` to
`s (k + 1)` equals the evolution from `s 0` to `s n`. -/
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

/-- For continuous `H`, nonnegative `t` and positive `r`, evolution from zero to `t` equals the
reverse list product of its `r` equal time segments [BerryEtAl2015Taylor]. -/
theorem timeDependentSegmentSplit : TimeDependentSegmentSplit := by
  intro I _ _ H t r hH _ hr
  have hn : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he := evolution_partition (fun u => Complex.I • H u) (by fun_prop)
    (fun k => (k : ℝ) * t / r) r
  simpa [hn] using! he.symm

end Qatlib.Concepts.CoherentSim.TimeDependent
