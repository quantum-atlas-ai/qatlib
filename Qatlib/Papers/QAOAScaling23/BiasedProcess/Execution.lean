/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree

/-!
# Finite-branch execution of rank descent

This module defines stochastic descent rows, execution traces, and the recursively sampled
process `descend`. Every next rank is smaller than the current positive rank, so descent ends at
zero while recording charges, oracle failures, and sampled outcomes for the analysis associated
with [ShaydulinEtAl2024].

## Main statements

* `descend`: The finite-branch descent tree that stops at rank zero and samples a row to move to
  a strictly smaller rank otherwise.
* `descend_minimum`: Every trace of descent has final output rank zero.
* `descend_states_le`: Every rank visited during descent from `r` is at most `r`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch

/-- A finite probability law of outcomes carrying a next rank below `r + 1`, a natural charge,
and an oracle bad flag. -/
structure Row (r : ℕ) where
  outcomes : ℕ
  law : PMF (Fin outcomes)
  next : Fin outcomes → Fin (r+1)
  charge : Fin outcomes → ℕ
  bad : Fin outcomes → Bool

/-- A descent trace recording visited ranks, charges, the accumulated oracle bad flag, final
output, individual bad flags, and sampled indices. -/
structure Trace where
  states : List ℕ
  charges : List ℕ
  oracleBad : Bool
  output : ℕ
  badRows : List Bool
  samples : List ℕ

/-- Prepend a visited rank, charge, bad flag, and sampled index to a trace, combining the new
bad flag with the accumulated one. -/
def prepend (r cost : ℕ) (bad : Bool) (sample : ℕ) (tr : Trace) : Trace :=
  ⟨r::tr.states,cost::tr.charges,bad||tr.oracleBad,tr.output,bad::tr.badRows,sample::tr.samples⟩

/-- The finite-branch descent tree that stops at rank zero and samples a row to move to a
strictly smaller rank otherwise. -/
def descend (rows : (r : ℕ) → Row r) : (r : ℕ) → Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace
  | 0 => .pure ⟨[0],[],false,0,[],[]⟩
  | r+1 => .sample (rows r).outcomes (rows r).law (fun a =>
      (descend rows ((rows r).next a).val).map (prepend (r+1) ((rows r).charge a) ((rows r).bad a) a.val))
termination_by r => r

/-- The descent tree initialized by sampling the starting rank from `p`. -/
def initialized {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r) : Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree Trace :=
  .sample L p (fun i => descend rows i.val)

/-- The total paid charge of a trace, obtained by summing its recorded charges. -/
def paid (tr : Trace) : ℕ := tr.charges.sum

/-- The number of occurrences of rank `j` in a trace's state list, viewed as a real number. -/
def visits (j : ℕ) (tr : Trace) : ℝ := ((tr.states.count j : ℕ) : ℝ)

/-- Every trace of descent has final output rank zero. -/
theorem descend_minimum (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).All (fun tr => tr.output=0) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.All]
    | succ r =>
      rw [descend]
      change ∀ a, ((descend rows ((rows r).next a).val).map _).All _
      intro a
      rw [Tree.all_map]
      exact ih ((rows r).next a).val ((rows r).next a).isLt

/-- Every rank visited during descent from `r` is at most `r`. -/
theorem descend_states_le (rows : (r : ℕ) → Row r) (r : ℕ) :
    (descend rows r).All (fun tr => ∀ j ∈ tr.states, j≤r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [descend,Tree.All]
    | succ r =>
      rw [descend]
      change ∀ a, ((descend rows ((rows r).next a).val).map _).All _
      intro a
      rw [Tree.all_map]
      apply Tree.all_mono _ (ih _ ((rows r).next a).isLt)
      intro tr htr j hj
      rcases List.mem_cons.1 hj with hj|hj
      · exact hj.le
      · exact (htr j hj).trans (Nat.le_of_lt ((rows r).next a).isLt)
end Qatlib.Papers.QAOAScaling23.BiasedProcess
