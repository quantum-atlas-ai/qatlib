/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Density.Proposition2

/-!
# Density up to phase in the three-strand SS sector

The module proves that `SSBasis 3` is a subsingleton. Applying the general subsingleton result
for `PhaseDenseOn` yields `proposition3_base` for the generator matrices `rhoSS 3`. See
[ShorJordan2008].

## Main statements

* `subsingleton_ssBasis_three`: Any two elements of `SSBasis 3` are equal.
* `proposition3_base`: The three-strand SS generator matrices are dense up to phase in the sense
  of `PhaseDenseOn`.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Density

open Definitions

/-- Any two elements of `SSBasis 3` are equal; see [ShorJordan2008]. -/
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

/-- The three-strand SS generator matrices are dense up to phase in the sense of `PhaseDenseOn`;
see [ShorJordan2008]. -/
theorem proposition3_base : PhaseDenseOn (SSBasis 3) (Set.range (rhoSS 3)) := by
  haveI := subsingleton_ssBasis_three
  exact phaseDenseOn_of_subsingleton _

end Qatlib.Papers.JonesPolyShor07.MainResults.Density
