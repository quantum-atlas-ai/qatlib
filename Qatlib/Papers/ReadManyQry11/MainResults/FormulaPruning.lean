/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ReadManyQry11.MainResults.SourceModel

@[expose] public section


/-!
The legacy formula-pruning record and its literal existential theorem. Query cost is a free field and the output is chosen pointwise with full knowledge of the formula value. The proof gives no source algorithm or oracle-cost credit.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.ReadManyQry11.MainResults

open scoped BigOperators Real

namespace Qatlib.Papers.ReadManyQry11.MainResults

/-- The legacy pruning record has a free cost field and pointwise existential
outputs. It does not describe a query-emitting quantum computation. -/
structure PruningAlgorithm (n : ℕ) where
  /-- The number of queries made by the algorithm. -/
  queries : ℝ
  /-- The formula-size bound on the returned formula. -/
  sizeBound : ℝ
  /-- The pruning guarantee: on every input the returned formula has the same value and
  respects the size bound. -/
  correct : ∀ (f : Formula n) (x : Fin n → Bool), ∃ f' : Formula n,
    f'.eval x = f.eval x ∧ (f'.size : ℝ) ≤ sizeBound

/-- The legacy pruning interface permits a free omniscient choice of a literal.
This proves its literal contract without a query algorithm or source cost credit. -/
theorem lemma2_formula_pruning :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n G : ℕ) (f : Formula n), 1 ≤ G → 2 ≤ n → f.gateCount = G →
        ∃ A : PruningAlgorithm n,
          A.queries ≤ c₁ * pruningBound n G ∧
          A.sizeBound ≤ c₂ * ((n : ℝ) * Real.sqrt (G : ℝ)) := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  intro n G f hG hn hf
  let i : Fin n := ⟨0, by omega⟩
  have hs : ∀ (g : Formula n) (x : Fin n → Bool), ∃ g' : Formula n,
      g'.eval x = g.eval x ∧ (g'.size : ℝ) ≤ 1 := by
    intro g x
    by_cases h : x i = g.eval x
    · exact ⟨Formula.leaf i, h, by simp⟩
    · refine ⟨Formula.not (Formula.leaf i), ?_, by simp⟩
      cases hx : x i <;> cases hg : g.eval x <;> simp_all [Formula.eval]
  refine ⟨{ queries := 0, sizeBound := 1, correct := hs }, ?_, ?_⟩
  · dsimp
    unfold pruningBound
    positivity
  · dsimp
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hg' : (1 : ℝ) ≤ Real.sqrt (G : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast hG
    nlinarith

end Qatlib.Papers.ReadManyQry11.MainResults
