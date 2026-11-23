/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle
import Mathlib.Tactic.Linarith

public section

/-!
# Fixed-error query budgets for learning-graph algorithms

[Belovs2012], Theorems 7–8 of the [fixed preprint](https://arxiv.org/abs/1205.1534v2).
The allowed error is a parameter of the counted-circuit budget. For a Boolean
function with both outputs, any run with error strictly below one half uses at
least one query. This sanity check uses the phase-query circuit and POVM laws;
it does not construct either of the paper's sublinear algorithms.
-/

open Matrix
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.LearnGraphDis12.MainResults

/-- A single counted phase-query circuit solves the Boolean word problem within
the prescribed error and query budget. -/
@[expose] def QueryCostAtMostWithError {n q : ℕ} [NeZero q]
    (f : (Fin n → Fin q) → Bool) (ε budget : ℝ) : Prop :=
  ∃ (m : ℕ) (C : Circuit ((Fin n × Fin q) × Fin m))
    (ψ : QState ((Fin n × Fin q) × Fin m))
    (out : Bool → Matrix ((Fin n × Fin q) × Fin m) ((Fin n × Fin q) × Fin m) ℂ),
    IsBoundedErrorRun id f C ψ out ε ∧ (QueryCount C : ℝ) ≤ budget

/-- A bounded-error run on opposite Boolean labels needs a query. With no oracle
steps its final state is the same on both inputs, and a binary POVM assigns
total probability one to its two labels. -/
theorem query_count_pos_of_opposite_outputs {n q m : ℕ} [NeZero q]
    {f : (Fin n → Fin q) → Bool} {x y : Fin n → Fin q}
    (hx : f x = false) (hy : f y = true)
    {C : Circuit ((Fin n × Fin q) × Fin m)} {ψ : QState ((Fin n × Fin q) × Fin m)}
    {out : Bool → Matrix ((Fin n × Fin q) × Fin m) ((Fin n × Fin q) × Fin m) ℂ}
    {ε : ℝ} (hε : ε < 1 / 2) (hrun : IsBoundedErrorRun id f C ψ out ε) :
    0 < QueryCount C := by
  obtain ⟨hC, hψ, hout, _, _, hsuccess⟩ := hrun
  by_contra! hcount
  have hzero := Nat.eq_zero_of_le_zero hcount
  let φ := Run (phaseOracle (W := Fin m) x) C ψ
  have hnorm : Normalized φ := by
    let : DecidableEq (Fin m) := Classical.decEq _
    exact hC.normalized_run (phaseOracle_unitary (W := Fin m) x) hψ
  have heq : Run (phaseOracle (W := Fin m) y) C ψ = φ :=
    run_eq_of_queryCount_eq_zero _ _ C hzero ψ
  have hfalse : 1 - ε ≤ povmProb out false φ := by simpa only [hx, id_eq] using hsuccess x
  have htrue : 1 - ε ≤ povmProb out true φ := by simpa only [hy, id_eq, heq] using hsuccess y
  have hsum : povmProb out false φ + povmProb out true φ = 1 := by
    let : DecidableEq ((Fin n × Fin q) × Fin m) := Classical.decEq _
    have hmeasure : out false + out true = 1 := by
      simpa only [Fintype.sum_bool, add_comm] using hout.2
    have hinner := (normalized_iff_inner_self φ).mp hnorm
    unfold povmProb
    rw [← Complex.add_re]
    have hadd : Inner φ (out false *ᵥ φ) + Inner φ (out true *ᵥ φ) = Inner φ φ := by
      calc
        _ = Inner φ ((out false + out true) *ᵥ φ) := by
          simp only [Matrix.add_mulVec, Qatlib.Foundations.PureStateMath.Inner, dotProduct_add]
        _ = _ := by rw [hmeasure, Matrix.one_mulVec]
    rw [hadd, hinner, Complex.one_re]
  linarith

/-- Every fixed-error budget below the fair-guessing threshold is at least one
query when the function has both a negative and a positive input. -/
theorem one_le_query_budget_of_opposite_outputs {n q : ℕ} [NeZero q]
    {f : (Fin n → Fin q) → Bool} {x y : Fin n → Fin q}
    (hx : f x = false) (hy : f y = true) {ε budget : ℝ} (hε : ε < 1 / 2)
    (hbudget : QueryCostAtMostWithError f ε budget) : 1 ≤ budget := by
  obtain ⟨m, C, ψ, out, hrun, hcost⟩ := hbudget
  have hcount := query_count_pos_of_opposite_outputs hx hy hε hrun
  have hone : (1 : ℝ) ≤ QueryCount C := by exact_mod_cast hcount
  exact hone.trans hcost

end Qatlib.Papers.LearnGraphDis12.MainResults
