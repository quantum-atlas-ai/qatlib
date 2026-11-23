/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOASupremacy16.LocalGadget.Source
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Repeated local clause gadgets and their effective diagonal cost

Eqs. (44) and (45) of [FarhiHarrow2016] implement a postselected Hadamard step by a diagonal
phase with entries `1, i, 1, -i` on the four two-bit inputs. The paper accounts for these phases
as six copies of the `01` clause together with two copies of the `11` clause, while the largest
effective integer cost is six; the effective cost is therefore not the total printed clause count
eight.

This module makes that accounting explicit for the diagonal phases `gadgetDiag` and integer costs
`gadgetCost` of the local gadget. It proves that the cost is the sum of the `01` and `11` clause
multiplicities, that the maximal effective cost is six while the printed clause count is eight,
and that a list of gadget layers has diagonal word equal to a single exponential
`exp (-(π/4) * totalCost * I)`. For `k` repeated layers the total effective cost is at most
`6 * k`, with the uniform constant six outside the quantifiers, and the bound is attained by a
family of `01` layers.

The surrounding Hadamard and postselection word, the fresh-ancilla layout, and any global gate
count are not formalized here; only the diagonal cost accounting is.

## Main statements

* `Qatlib.Papers.QAOASupremacy16.ClauseGates.gadgetDiag_eq_exp_clauseCopies`
  identifies the diagonal entries with the phase from six `01` copies and two `11` copies.
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.repeatedDiag_eq_exp`
  combines the diagonal phases into one exponential at the total cost.
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.exists_uniform_repeated_gadget_cost`
  gives a positive uniform per-layer bound.
* `Qatlib.Papers.QAOASupremacy16.ClauseGates.repeatedFinCost_zeroOne_attained`
  shows that `01` layers attain the bound.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAOASupremacy16.ClauseGates

open Qatlib.Papers.QAOASupremacy16.LocalGadget
open scoped BigOperators

/-- The multiplicity of the `01` clause in the Eq. (44) accounting. -/
def clauseCopiesZeroOne (a j : Bool) : ℕ :=
  if a = false ∧ j = true then 6 else 0

/-- The multiplicity of the `11` clause in the Eq. (44) accounting. -/
def clauseCopiesOneOne (a j : Bool) : ℕ :=
  if a = true ∧ j = true then 2 else 0

/-- The total number of printed clause copies in the single-gadget accounting of Eq. (44):
six copies of `01` and two copies of `11`. -/
def printedClauseCopies : ℕ :=
  6 + 2

/-- The effective integer cost is the sum of the `01` and `11` clause multiplicities. -/
theorem gadgetCost_eq_clauseCopies (a j : Bool) :
    gadgetCost a j = clauseCopiesZeroOne a j + clauseCopiesOneOne a j := by
  cases a <;> cases j <;> rfl

/-- The diagonal entry in Eq. (44) is the phase from the repeated clauses of Eq. (45). -/
theorem gadgetDiag_eq_exp_clauseCopies (a j : Bool) :
    gadgetDiag a j =
      Complex.exp (-((Real.pi / 4) *
        ((clauseCopiesZeroOne a j + clauseCopiesOneOne a j : ℕ) : ℝ)) * Complex.I) := by
  rw [gadgetDiag_eq_exp, gadgetCost_eq_clauseCopies]

/-- The printed clause count is eight. -/
theorem printedClauseCopies_eq_eight : printedClauseCopies = 8 := rfl

/-- Every effective cost is at most six. -/
theorem gadgetCost_le_six (a j : Bool) : gadgetCost a j ≤ 6 := by
  cases a <;> cases j <;> decide

/-- The maximal effective cost six is attained by the `01` input. -/
theorem gadgetCost_exists_six : ∃ a j : Bool, gadgetCost a j = 6 :=
  ⟨false, true, rfl⟩

/-- The maximal effective cost is strictly smaller than the printed clause count eight. -/
theorem gadgetCost_lt_printedClauseCopies (a j : Bool) :
    gadgetCost a j < printedClauseCopies := by
  rw [printedClauseCopies_eq_eight]
  have := gadgetCost_le_six a j
  omega

/-- The total effective cost of a list of gadget layers. -/
def repeatedCost (layers : List (Bool × Bool)) : ℕ :=
  (layers.map fun p => gadgetCost p.1 p.2).sum

/-- The product of the diagonal phases of a list of gadget layers. -/
noncomputable def repeatedDiag (layers : List (Bool × Bool)) : ℂ :=
  (layers.map fun p => gadgetDiag p.1 p.2).prod

/-- A repeated diagonal gadget word is a single exponential at the total effective cost. -/
theorem repeatedDiag_eq_exp (layers : List (Bool × Bool)) :
    repeatedDiag layers
      = Complex.exp (-((Real.pi / 4) * (repeatedCost layers : ℝ)) * Complex.I) := by
  induction layers with
  | nil => simp [repeatedDiag, repeatedCost]
  | cons p ps ih =>
      have hcost : repeatedCost (p :: ps) = gadgetCost p.1 p.2 + repeatedCost ps := rfl
      calc repeatedDiag (p :: ps)
          = gadgetDiag p.1 p.2 * repeatedDiag ps := by simp [repeatedDiag]
        _ = gadgetDiag p.1 p.2 *
              Complex.exp (-((Real.pi / 4) * (repeatedCost ps : ℝ)) * Complex.I) := by
            rw [ih]
        _ = Complex.exp (-((Real.pi / 4) * (gadgetCost p.1 p.2 : ℝ)) * Complex.I) *
              Complex.exp (-((Real.pi / 4) * (repeatedCost ps : ℝ)) * Complex.I) := by
            rw [gadgetDiag_eq_exp]
        _ = Complex.exp
              (-((Real.pi / 4) * ((gadgetCost p.1 p.2 + repeatedCost ps : ℕ) : ℝ)) *
                Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
        _ = Complex.exp (-((Real.pi / 4) * (repeatedCost (p :: ps) : ℝ)) * Complex.I) := by
            rw [hcost]

/-- The total effective cost of `k` ordered gadget layers is at most `6 * k`. -/
theorem repeatedFinCost_le (k : ℕ) (layers : Fin k → Bool × Bool) :
    (∑ i, gadgetCost (layers i).1 (layers i).2) ≤ 6 * k := by
  calc (∑ i, gadgetCost (layers i).1 (layers i).2) ≤ ∑ _i : Fin k, 6 :=
        Finset.sum_le_sum fun i _ => gadgetCost_le_six _ _
    _ = k * 6 := by simp
    _ = 6 * k := by omega

/-- The uniform constant six for repeated local gadget layers, outside the quantifiers. -/
theorem exists_uniform_repeated_gadget_cost :
    ∃ K : ℕ, 0 < K ∧ ∀ (k : ℕ), 0 < k → ∀ layers : Fin k → Bool × Bool,
      (∑ i, gadgetCost (layers i).1 (layers i).2) ≤ K * k :=
  ⟨6, by norm_num, fun k _ layers => repeatedFinCost_le k layers⟩

/-- Repeating the `01` layer attains the bound `6 * k`, so the constant six is optimal for this
family. -/
theorem repeatedFinCost_zeroOne_attained (k : ℕ) :
    (∑ _i : Fin k, gadgetCost (false, true).1 (false, true).2) = 6 * k := by
  simp [gadgetCost]
  omega

end Qatlib.Papers.QAOASupremacy16.ClauseGates
