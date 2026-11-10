/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Density.Proposition2
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Density

open Definitions

theorem subsingleton_ssBasis_three : Subsingleton (SSBasis 3) := by
  constructor
  intro s t
  have hs : s.1 = ![true, false, false, true] := by
    have h0 : s.1 0 = true := by simpa using s.2.1
    have h3 : s.1 3 = true := by simpa using s.2.2.1
    have h1 : s.1 1 = false := by
      have hh := s.2.2.2 (0 : Fin 4) (1 : Fin 4) (by decide)
      have h0' : s.1 (0 : Fin 4) = true := h0
      simp only [h0', true_and, Bool.not_eq_true] at hh
      exact hh
    have h2 : s.1 2 = false := by
      have hh := s.2.2.2 (2 : Fin 4) (3 : Fin 4) (by decide)
      have h3' : s.1 (3 : Fin 4) = true := h3
      simp only [h3', and_true, Bool.not_eq_true] at hh
      exact hh
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  have ht : t.1 = ![true, false, false, true] := by
    have h0 : t.1 0 = true := by simpa using t.2.1
    have h3 : t.1 3 = true := by simpa using t.2.2.1
    have h1 : t.1 1 = false := by
      have hh := t.2.2.2 (0 : Fin 4) (1 : Fin 4) (by decide)
      have h0' : t.1 (0 : Fin 4) = true := h0
      simp only [h0', true_and, Bool.not_eq_true] at hh
      exact hh
    have h2 : t.1 2 = false := by
      have hh := t.2.2.2 (2 : Fin 4) (3 : Fin 4) (by decide)
      have h3' : t.1 (3 : Fin 4) = true := h3
      simp only [h3', and_true, Bool.not_eq_true] at hh
      exact hh
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  exact Subtype.ext (hs.trans ht.symm)

theorem proposition3_base : PhaseDenseOn (SSBasis 3) (Set.range (rhoSS 3)) := by
  haveI := subsingleton_ssBasis_three
  exact phaseDenseOn_of_subsingleton _

end Qatlib.Papers.JonesPolyShor07.MainResults.Density
