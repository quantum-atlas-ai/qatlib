/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.ClawMatching
public import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
public import Mathlib.Tactic.FinCases

@[expose] public section


/-! # The complete three vertex-cover formulas from Proposition 4.1

Fixed source: arXiv1011.1443v2, page 18. The historical path and claw
constructors are used directly. The immutable original proposition is
proved with no cover-number equality or matching-size premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.MinorClosed10.MainResults.VertexFormulas
open Qatlib.Papers.MinorClosed10.MainResults
open PathCover ClawCover ClawMatching

/-- The actual three-branch paper graph has exactly the adjacency relation of the generic subdivided star. -/
theorem clawBridge (d1 d2 d3 : ℕ) :
    ClawGraph d1 d2 d3 = starG (![d1,d2,d3] : Fin 3 → ℕ) := by
  apply SimpleGraph.ext
  funext a b
  rcases a with u | ⟨i,j⟩ <;> rcases b with v | ⟨k,l⟩ <;> rfl

/-- The genuine paper path, including the zero-edge path, has the stated vertex-cover number. -/
theorem pathFormula (k : ℕ) : vc (PathGraph k) = (((k+1)/2 : ℕ) : ℕ∞) :=
  pathNumber k

/-- All three even branch lengths give exactly half their total as the true minimum cover size. -/
theorem evenFormula (d1 d2 d3 : ℕ) (h1 : Even d1) (h2 : Even d2) (h3 : Even d3) :
    vc (ClawGraph d1 d2 d3) = (((d1+d2+d3)/2 : ℕ) : ℕ∞) := by
  let d : Fin 3 → ℕ := ![d1,d2,d3]
  have hd : ∀ i, Even (d i) := by
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  have h := evenNumber d hd
  have he : (∑ i, d i/2 : ℕ) = (d1+d2+d3)/2 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, d, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero]
    obtain ⟨a,ha⟩ := h1
    obtain ⟨b,hb⟩ := h2
    obtain ⟨c,hc⟩ := h3
    omega
  rw [he] at h
  change (ClawGraph d1 d2 d3).vertexCoverNum = _
  rw [clawBridge]
  exact h

/-- At least one odd branch supplies the additional centre matching edge required by the printed formula. -/
theorem oddFormula (d1 d2 d3 : ℕ) (h : Odd d1 ∨ Odd d2 ∨ Odd d3) :
    vc (ClawGraph d1 d2 d3) = ((1+d1/2+d2/2+d3/2 : ℕ) : ℕ∞) := by
  let d : Fin 3 → ℕ := ![d1,d2,d3]
  have hs : ∃ s : Fin 3, Odd (d s) := by
    rcases h with h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  obtain ⟨s,hs⟩ := hs
  have he := oddNumber d s hs
  have hc : 1+(∑ i, d i/2 : ℕ) = 1+d1/2+d2/2+d3/2 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, d, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero]
    omega
  rw [hc] at he
  change (ClawGraph d1 d2 d3).vertexCoverNum = _
  rw [clawBridge]
  exact he

/-- The full original Proposition 4.1 target, with all three universal formulas and their original domains. -/
theorem proposition41 :
    (∀ k : ℕ, vc (PathGraph k) = (((k+1)/2 : ℕ) : ℕ∞)) ∧
    (∀ d1 d2 d3 : ℕ, Even d1 → Even d2 → Even d3 →
      vc (ClawGraph d1 d2 d3) = (((d1+d2+d3)/2 : ℕ) : ℕ∞)) ∧
    (∀ d1 d2 d3 : ℕ, (Odd d1 ∨ Odd d2 ∨ Odd d3) →
      vc (ClawGraph d1 d2 d3) = ((1+d1/2+d2/2+d3/2 : ℕ) : ℕ∞)) :=
  ⟨pathFormula,evenFormula,oddFormula⟩

end Qatlib.Papers.MinorClosed10.MainResults.VertexFormulas
