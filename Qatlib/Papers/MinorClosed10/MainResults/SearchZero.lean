/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.SearchModel
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ConstantCost
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # The actual historical zero-marked promise has a zero-query program

This is the given-K promise model, not a certification algorithm for an
unknown marked count. Its zero-cost claim is proved by a genuine legal
source word, without relying on infinity-to-real conversion.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.MinorClosed10.MainResults.SearchZero
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.LowerBoundTools.ConstantCost
open SearchModel

/-- Every promised zero-marked input has the same empty marked set, computed by a real zero-query word. -/
theorem zeroCost (N : ℕ) : searchCost N 0 = 0 := by
  have he : sourceFunctionQ
      (fun (f : SearchInput N 0) (i : Fin N) => if f.1 i then (1 : Fin 2) else 0)
      (fun (f : SearchInput N 0) => Finset.univ.filter (fun i => f.1 i = true)) = 0 :=
    zeroCalls _ (∅ : Finset (Fin N)) _ (fun f => Finset.card_eq_zero.mp f.2)
  change (sourceFunctionQ _ _).toReal = 0
  rw [he]
  rfl

/-- The entire original zero-count cost bound holds with constant one in the historical promise model. -/
theorem zeroBudget (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ searchCost N 0 ≤ C*Real.sqrt (N : ℝ) := by
  refine ⟨1, by norm_num, ?_⟩
  rw [zeroCost, one_mul]
  exact Real.sqrt_nonneg _

end Qatlib.Papers.MinorClosed10.MainResults.SearchZero
