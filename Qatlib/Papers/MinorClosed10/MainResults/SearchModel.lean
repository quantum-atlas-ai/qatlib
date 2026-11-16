/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Actual historical promise-search costs and their quantifier boundary

Fixed source: Childs--Kothari, arXiv:1011.1443v2. The historical cost
expressions are preserved. A constant chosen after fixed N and K is only
a pointwise real inequality, not the source's uniform quantum algorithm.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.MinorClosed10.MainResults.SearchModel
open Qatlib.Papers.MinorClosed10.MainResults
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

/-- The actual historical promise family consists of Boolean strings with a prescribed marked count. -/
abbrev SearchInput (N K : ℕ) : Type :=
  {f : Fin N → Bool // (Finset.univ.filter (fun i => f i = true)).card = K}

/-- The old real-valued cost of outputting the entire marked set on the prescribed promise family. -/
def searchCost (N K : ℕ) : ℝ := by
  classical
  exact (sourceFunctionQ
    (fun (f : SearchInput N K) (i : Fin N) => if f.1 i then (1 : Fin 2) else 0)
    (fun (f : SearchInput N K) => Finset.univ.filter (fun i => f.1 i = true))).toReal

/-- The genuine historical edge-count promise has one of the two displayed gap inequalities. -/
abbrev ThresholdInput (n : ℕ) (ε : ℝ) (f : ℕ → ℕ) : Type :=
  {G : SimpleGraph (Fin n) //
    ((1+ε)*(f n : ℝ) ≤ (G.edgeFinset.card : ℝ)) ∨
    ((G.edgeFinset.card : ℝ) ≤ (1-ε)*(f n : ℝ))}

/-- The historical threshold cost uses the actual fixed two-thirds source success convention, without a delta argument. -/
def thresholdCost (n : ℕ) (ε : ℝ) (f : ℕ → ℕ) : ℝ := by
  classical
  exact (sourceFunctionQ
    (fun (G : ThresholdInput n ε f) (i : Fin (n*n)) => graphInput n G.1 i)
    (fun (G : ThresholdInput n ε f) =>
      decide ((1+ε)*(f n : ℝ) ≤ (G.1.edgeFinset.card : ℝ)))).toReal

/-- Every actual historical real threshold cost is nonnegative, regardless of whether its extended cost is finite. -/
theorem thresholdNonneg (n : ℕ) (ε : ℝ) (f : ℕ → ℕ) : 0 ≤ thresholdCost n ε f :=
  ENNReal.toReal_nonneg

/-- Any real value admits a positive multiple bound at one fixed positive scale. -/
private theorem pointBudget (q r : ℝ) (hr : 0 < r) : ∃ C : ℝ, 0 < C ∧ q ≤ C*r := by
  refine ⟨(|q|+1)/r, by positivity, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hr)]
  linarith [le_abs_self q]

/-- The entire old positive-count target follows pointwise, with a constant allowed to depend on N and K; no uniform algorithm is certified. -/
theorem positiveBudget (N K : ℕ) (hK : 0 < K) (hKN : K ≤ N) :
    ∃ C : ℝ, 0 < C ∧ searchCost N K ≤ C*Real.sqrt ((N : ℝ)*(K : ℝ)) := by
  apply pointBudget
  apply Real.sqrt_pos.mpr
  exact mul_pos (Nat.cast_pos.mpr (hK.trans_le hKN)) (Nat.cast_pos.mpr hK)

end Qatlib.Papers.MinorClosed10.MainResults.SearchModel
