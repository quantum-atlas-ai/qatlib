/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.FibonacciRepresentation

/-!
# The two-element four-strand SS basis

`ssFourIndex` reads the middle bit of an element of `SSBasis 4`. The two explicit strings
`ssFourStar` and `ssFourP` show that this map is bijective, giving `ssBasisFourEquivBool` and
the two-element cardinality needed for the base-sector analysis. See [ShorJordan2008].

## Main statements

* `ssBasisFourEquivBool`: The equivalence between `SSBasis 4` and `Bool` given by the middle
  bit.
* `card_ssBasis_four`: The type `SSBasis 4` has exactly two elements.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Density

open Definitions

/-- The middle bit, at position two, of a string in `SSBasis 4`. -/
def ssFourIndex (s : SSBasis 4) : Bool := s.1 2

/-- The SS string (true, false, true, false, true). -/
def ssFourStar : SSBasis 4 := ⟨![true, false, true, false, true], by
  refine ⟨by decide, by decide, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The SS string (true, false, false, false, true). -/
def ssFourP : SSBasis 4 := ⟨![true, false, false, false, true], by
  refine ⟨by decide, by decide, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The middle bit of `ssFourStar` is true. -/
theorem ssFourIndex_star : ssFourIndex ssFourStar = true := by decide

/-- The middle bit of `ssFourP` is false. -/
theorem ssFourIndex_p : ssFourIndex ssFourP = false := by decide

/-- An element of `SSBasis 4` is determined by its middle bit; see [ShorJordan2008]. -/
theorem ssFourIndex_injective : Function.Injective ssFourIndex := by
  intro s t h
  have h0s : s.1 0 = true := by simpa using s.2.1
  have h4s : s.1 4 = true := by simpa using s.2.2.1
  have h0t : t.1 0 = true := by simpa using t.2.1
  have h4t : t.1 4 = true := by simpa using t.2.2.1
  have h1s : s.1 1 = false := by
    have hh := s.2.2.2 (0 : Fin 5) (1 : Fin 5) (by decide)
    have h0' : s.1 (0 : Fin 5) = true := h0s
    simp only [h0', true_and, Bool.not_eq_true] at hh
    exact hh
  have h3s : s.1 3 = false := by
    have hh := s.2.2.2 (3 : Fin 5) (4 : Fin 5) (by decide)
    have h4' : s.1 (4 : Fin 5) = true := h4s
    simp only [h4', and_true, Bool.not_eq_true] at hh
    exact hh
  have h1t : t.1 1 = false := by
    have hh := t.2.2.2 (0 : Fin 5) (1 : Fin 5) (by decide)
    have h0' : t.1 (0 : Fin 5) = true := h0t
    simp only [h0', true_and, Bool.not_eq_true] at hh
    exact hh
  have h3t : t.1 3 = false := by
    have hh := t.2.2.2 (3 : Fin 5) (4 : Fin 5) (by decide)
    have h4' : t.1 (4 : Fin 5) = true := h4t
    simp only [h4', and_true, Bool.not_eq_true] at hh
    exact hh
  apply Subtype.ext
  funext i
  have h2 : s.1 2 = t.1 2 := h
  fin_cases i <;> simp [h0s, h1s, h2, h3s, h4s, h0t, h1t, h3t, h4t]

/-- Every Boolean value occurs as the middle bit of an element of `SSBasis 4`. -/
theorem ssFourIndex_surjective : Function.Surjective ssFourIndex := by
  intro b
  cases b
  · exact ⟨ssFourP, ssFourIndex_p⟩
  · exact ⟨ssFourStar, ssFourIndex_star⟩

/-- The equivalence between `SSBasis 4` and `Bool` given by the middle bit; see
[ShorJordan2008]. -/
def ssBasisFourEquivBool : SSBasis 4 ≃ Bool :=
  Equiv.ofBijective ssFourIndex ⟨ssFourIndex_injective, ssFourIndex_surjective⟩

/-- The type `SSBasis 4` has exactly two elements; see [ShorJordan2008]. -/
theorem card_ssBasis_four : Fintype.card (SSBasis 4) = 2 := by
  rw [Fintype.card_congr ssBasisFourEquivBool, Fintype.card_bool]

end Qatlib.Papers.JonesPolyShor07.MainResults.Density
