/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.FibonacciRepresentation
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Density

open Definitions

def ssFourIndex (s : SSBasis 4) : Bool := s.1 2

def ssFourStar : SSBasis 4 := ⟨![true, false, true, false, true], by
  refine ⟨by decide, by decide, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all⟩

def ssFourP : SSBasis 4 := ⟨![true, false, false, false, true], by
  refine ⟨by decide, by decide, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all⟩

theorem ssFourIndex_star : ssFourIndex ssFourStar = true := by decide

theorem ssFourIndex_p : ssFourIndex ssFourP = false := by decide

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

theorem ssFourIndex_surjective : Function.Surjective ssFourIndex := by
  intro b
  cases b
  · exact ⟨ssFourP, ssFourIndex_p⟩
  · exact ⟨ssFourStar, ssFourIndex_star⟩

def ssBasisFourEquivBool : SSBasis 4 ≃ Bool :=
  Equiv.ofBijective ssFourIndex ⟨ssFourIndex_injective, ssFourIndex_surjective⟩

theorem card_ssBasis_four : Fintype.card (SSBasis 4) = 2 := by
  rw [Fintype.card_congr ssBasisFourEquivBool, Fintype.card_bool]

end Qatlib.Papers.JonesPolyShor07.MainResults.Density
