/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GndStatePrep20.MainResults.SourceModel

@[expose] public section

/-!
# The four grid-index updates of Algorithm 1

Two equal threshold answers continue the search on one side of the
midpoint. Two unequal answers return a bracket of width at most three.
A bracket of width at most three stays fixed, representing the stopping
rule while indexing the search by all natural numbers.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GndStatePrep20.MainResults

/-- Width of the bracket in grid spacings. -/
def gridWidth (bracket : ℕ × ℕ) : ℕ := bracket.2 - bracket.1

/-- Apply the source Algorithm 1 update for the two threshold answers,
or keep the bracket when the calculation has stopped. -/
def gridUpdate (bracket : ℕ × ℕ) (outcomes : Bool × Bool) : ℕ × ℕ :=
  if gridWidth bracket ≤ 3 then bracket
  else
    let k := (bracket.1 + bracket.2) / 2
    match outcomes with
    | (true, true) => (bracket.1, k + 1)
    | (false, false) => (k, bracket.2)
    | (false, true) => (k - 1, k + 2)
    | (true, false) => (k, k + 1)

/-- The four Table 2 cases all satisfy the affine width bound while
the bracket is active. -/
theorem grid_update_width_le (bracket : ℕ × ℕ) (outcomes : Bool × Bool)
    (hactive : 3 < gridWidth bracket) :
    gridWidth (gridUpdate bracket outcomes) ≤ gridWidth bracket / 2 + 1 := by
  obtain ⟨L, U⟩ := bracket
  obtain ⟨a, b⟩ := outcomes
  rw [gridUpdate, ite_eq_right (not_le.mpr hactive)]
  cases a <;> cases b <;> dsimp [gridWidth] at hactive ⊢ <;> omega

/-- Each update keeps its ordered bracket inside the previous endpoints. -/
theorem grid_update_stays_inside (bracket : ℕ × ℕ) (outcomes : Bool × Bool)
    (hordered : bracket.1 ≤ bracket.2) :
    bracket.1 ≤ (gridUpdate bracket outcomes).1 ∧
      (gridUpdate bracket outcomes).1 ≤ (gridUpdate bracket outcomes).2 ∧
      (gridUpdate bracket outcomes).2 ≤ bracket.2 := by
  obtain ⟨L, U⟩ := bracket
  obtain ⟨a, b⟩ := outcomes
  by_cases hstop : gridWidth (L,U) ≤ 3
  · rw [gridUpdate, ite_eq_left hstop]
    exact ⟨le_rfl, hordered, le_rfl⟩
  · rw [gridUpdate, ite_eq_right hstop]
    cases a <;> cases b <;> dsimp [gridWidth] at hstop ⊢ <;> omega

/-- The grid bracket after a prescribed stream of answer pairs. Ending
branches have width at most three and subsequent updates leave them fixed. -/
def gridBracket (G : ℕ) (answers : ℕ → Bool × Bool) : ℕ → ℕ × ℕ
  | 0 => (0, G)
  | l + 1 => gridUpdate (gridBracket G answers l) (answers l)

/-- The source initialization and the four updates keep both endpoints
ordered at every round. -/
theorem grid_bracket_order (G : ℕ) (answers : ℕ → Bool × Bool) (l : ℕ) :
    (gridBracket G answers l).1 ≤ (gridBracket G answers l).2 := by
  induction l with
  | zero => exact Nat.zero_le G
  | succ j ih =>
    exact (grid_update_stays_inside (gridBracket G answers j) (answers j) ih).2.1

/-- After a number of rounds whose power of two reaches `G - 2`,
Algorithm 1 has reduced the bracket width to at most three. -/
theorem algorithm1_grid_width_le_three (G : ℕ) (answers : ℕ → Bool × Bool)
    (l : ℕ) (hbudget : G - 2 ≤ 2 ^ l) :
    gridWidth (gridBracket G answers l) ≤ 3 := by
  have hbound (j : ℕ) : 3 < gridWidth (gridBracket G answers j) →
      gridWidth (gridBracket G answers j) ≤ 2 + (G - 2) / 2 ^ j := by
    induction j with
    | zero =>
      intro _
      simp [gridBracket, gridWidth]
      omega
    | succ j ih =>
      intro hwide
      have hprevious : 3 < gridWidth (gridBracket G answers j) := by
        by_contra! hstop
        rw [gridBracket, gridUpdate, ite_eq_left hstop] at hwide
        omega
      have hstep := grid_update_width_le (gridBracket G answers j) (answers j) hprevious
      have hhalf := Nat.div_le_div_right (ih hprevious) (c := 2)
      rw [gridBracket]
      calc
        _ ≤ gridWidth (gridBracket G answers j) / 2 + 1 := hstep
        _ ≤ 2 + ((G - 2) / 2 ^ j) / 2 := by omega
        _ = _ := by rw [Nat.div_div_eq_div_mul, pow_succ]
  by_contra! hwide
  have hcap := Nat.div_le_div_right hbudget (c := 2 ^ l)
  rw [Nat.div_self (by positivity : 0 < 2 ^ l)] at hcap
  have h := hbound l hwide
  omega

end Qatlib.Papers.GndStatePrep20.MainResults
