/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Qatlib.Papers.GrpCommTest05.MainResults.CouplingSpectralGap

/-!
# Hamming distance under synchronized updates

`hamming` counts the coordinates at which two index tuples differ, and `diffSet` records those
coordinates. Updating the same coordinate to the same value in both tuples cannot increase the
distance and decreases it by exactly one when the coordinate originally differed.

The module also records the elementary probability factor for a decreasing step and derives a
scalar spectral gap bound from the stated coupling time and exponential estimates. See
[MagniezNayak2005].

## Main statements

* `hamming_update_of_ne`: If coordinate `i` originally differs, a synchronized update reduces
  the Hamming distance by exactly one.
* `spectralGap_ge_of_coupling_time`: Given the stated positive parameters, coupling time bound
  `T ≤ 2*l*log l`, and exponential bound on `lam`, the gap `1 - lam` is at least `1/(8*exp
  1*l*log l)`.

## References

* [Magniez and Nayak, 2005][MagniezNayak2005]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Finset Real

variable {l k : ℕ}

/-- The number of coordinates on which `u` and `v` differ. -/
def hamming (u v : Fin l → Fin k) : ℕ :=
  (univ.filter (fun i => u i ≠ v i)).card

/-- The finite set of coordinates on which `u` and `v` differ. -/
def diffSet (u v : Fin l → Fin k) : Finset (Fin l) :=
  univ.filter (fun i => u i ≠ v i)

/-- The cardinality of `diffSet u v` equals their Hamming distance. -/
theorem card_diffSet (u v : Fin l → Fin k) : (diffSet u v).card = hamming u v := rfl

/-- Updating coordinate `i` to `j` in both tuples erases `i` from their difference set. -/
theorem diffSet_update {u v : Fin l → Fin k} {i : Fin l} {j : Fin k} :
    diffSet (Function.update u i j) (Function.update v i j) = (diffSet u v).erase i := by
  ext m
  by_cases hm : m = i
  · subst hm
    simp [diffSet, Function.update_self]
  · simp [diffSet, Function.update, hm]

/-- A synchronized update cannot increase Hamming distance. -/
theorem hamming_update_le (u v : Fin l → Fin k) (i : Fin l) (j : Fin k) :
    hamming (Function.update u i j) (Function.update v i j) ≤ hamming u v := by
  rw [← card_diffSet, diffSet_update, ← card_diffSet]
  exact Finset.card_le_card (Finset.erase_subset _ _)

/-- If coordinate `i` originally differs, a synchronized update reduces the Hamming distance by
exactly one. See [MagniezNayak2005]. -/
theorem hamming_update_of_ne {u v : Fin l → Fin k} {i : Fin l} {j : Fin k}
    (hi : u i ≠ v i) :
    hamming (Function.update u i j) (Function.update v i j) + 1 = hamming u v := by
  rw [← card_diffSet, diffSet_update, ← card_diffSet]
  have hmem : i ∈ diffSet u v := by simp [diffSet, hi]
  rw [Finset.card_erase_of_mem hmem]
  have hpos : 0 < (diffSet u v).card := Finset.card_pos.mpr ⟨i, hmem⟩
  omega

/-- For positive `l`, the rational expression `(d/l) * (1/2)` equals `d/(2*l)`. -/
theorem decrease_prob (d l : ℕ) (hl : 0 < l) :
    ((d : ℚ) / (l : ℚ)) * (1 / 2) = (d : ℚ) / (2 * l) := by
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  field_simp

/-- Given the stated positive parameters, coupling time bound `T ≤ 2*l*log l`, and exponential
bound on `lam`, the gap `1 - lam` is at least `1/(8*exp 1*l*log l)`. See [MagniezNayak2005]. -/
theorem spectralGap_ge_of_coupling_time {lam T l : ℝ} (hl : 0 < l) (hlog : 0 < Real.log l)
    (hT : 0 < T) (hTl : T ≤ 2 * l * Real.log l)
    (hT1 : 1 ≤ 2 * Real.exp 1 * T)
    (hlam : lam ≤ Real.exp (-(1 / (2 * Real.exp 1 * T)))) :
    1 / (8 * Real.exp 1 * l * Real.log l) ≤ 1 - lam := by
  have hgap := spectralGap_ge_of_exp_bound hT hT1 hlam
  have hden : (0 : ℝ) < 2 * Real.exp 1 * T := by positivity
  have hden' : (0 : ℝ) < 4 * Real.exp 1 * l * Real.log l := by positivity
  have hle : 4 * Real.exp 1 * T ≤ 8 * Real.exp 1 * l * Real.log l := by
    nlinarith [Real.exp_pos 1, hl, hlog, hTl]
  have hden4 : (0 : ℝ) < 4 * Real.exp 1 * T := by positivity
  have hinv : 1 / (8 * Real.exp 1 * l * Real.log l) ≤ 1 / (4 * Real.exp 1 * T) :=
    one_div_le_one_div_of_le hden4 hle
  linarith

end Qatlib.Papers.GrpCommTest05.MainResults
