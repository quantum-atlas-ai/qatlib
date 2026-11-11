/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverStat
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4MarkedMassQuan
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainQuan

/-!
# Quantitative expander walk detection

This module proves `SzegedyTheorem4ExpanderGrover` from the chain-gap detection results. A
positive gap at most one, a nonempty marked set, and a unitary implementing frame preparation
give average detection probability at least `1 / 32` over the prescribed times.

The theorem includes bounds on all three detection-program counts and on the integer search
horizon, making the square-root walk-detection scale explicit [Szegedy2004].

## Main statements

* `szegedyTheorem4ExpanderGrover`: detection probability and resource bounds.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.WalkSearch.WalkDetector
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Th4Expander
open Matrix
open scoped BigOperators

/-- Establish the expander detection contract: under the stated gap and preparation assumptions,
the average detection probability is at least `1 / 32`, with explicit program counts and
search length at most `1000 * sqrt (n / δ) + 1` [Szegedy2004]. -/
theorem szegedyTheorem4ExpanderGrover : SzegedyTheorem4ExpanderGrover := by
  classical
  intro n d adj f δ j U hn hδ hδ1 hgap hmarked hU hprepare
  letI : Nonempty (Fin n) := ⟨j⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hε : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hroot : 0 < Real.sqrt ((n : ℝ) / δ) := Real.sqrt_pos.mpr (div_pos hnR hδ)
  have hL : 0 < expanderSearchLength n δ :=
    Nat.ceil_pos.mpr (mul_pos (by norm_num) hroot)
  have hprod : Real.sqrt (δ * (1 / (n : ℝ))) * Real.sqrt ((n : ℝ) / δ) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have he : δ * (1 / (n : ℝ)) * ((n : ℝ) / δ) = 1 := by
      field_simp
    rw [he, Real.sqrt_one]
  have hscale : 1000 / Real.sqrt (δ * (1 / (n : ℝ))) ≤
      (expanderSearchLength n δ : ℝ) := by
    calc
      1000 / Real.sqrt (δ * (1 / (n : ℝ))) =
          1000 * Real.sqrt ((n : ℝ) / δ) := by
        apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hδ hε)))).mpr
        nlinarith [hprod]
      _ ≤ (expanderSearchLength n δ : ℝ) := Nat.le_ceil _
  have hdet := corrected_szegedy_actual_random_power_detection (Fin n)
    (expanderStep n d adj) (Finset.univ.filter (fun i => f i = true))
    δ (1 / (n : ℝ)) (expanderSearchLength n δ) j U hδ hδ1 hgap hε
    (szegedyTheorem4MarkedMass n f hn hmarked) hL hscale hU hprepare
  exact ⟨hdet.1, hdet.2, (Nat.ceil_lt_add_one (by positivity)).le⟩

end Qatlib.Concepts.WalkSearch.Th4Expander
