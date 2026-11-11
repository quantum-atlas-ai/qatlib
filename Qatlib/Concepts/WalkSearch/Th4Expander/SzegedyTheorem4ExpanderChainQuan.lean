/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.WalkSearch.TwoLevelLower

/-!
# Regular-graph transition and frame support

This module proves `SzegedyTheorem4ExpanderChain` for the kernel `expanderStep`. Positive
regular degree gives row normalization, adjacency symmetry gives kernel symmetry, and nonzero
frame amplitudes occur only on adjacent pairs with the specified first vertex.

These properties supply the classical kernel and preparation support used in the walk-search
construction [Szegedy2004].

## Main statements

* `szegedyTheorem4ExpanderChain`: transition, symmetry, and support properties.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Th4Expander
open Matrix
open scoped BigOperators

/-- Establish that a symmetric regular adjacency relation with positive size and degree gives a
symmetric transition matrix whose Szegedy frame has the required edge support [Szegedy2004]. -/
theorem szegedyTheorem4ExpanderChain : SzegedyTheorem4ExpanderChain := by
  classical
  intro n d adj _ hd hsym hreg
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j
    unfold expanderStep
    split <;> positivity
  · intro i
    change (∑ j : Fin n, if adj i j then (d : ℝ)⁻¹ else 0) = 1
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hreg]
    exact mul_inv_cancel₀ (by exact_mod_cast hd.ne')
  · intro i j
    simp only [expanderStep, hsym i j]
  · intro i p hne
    have hcol : (SzegedyIsometry (expanderStep n d adj) *ᵥ Ket i) p =
        SzegedyIsometry (expanderStep n d adj) p i := by
      simp [Matrix.mulVec, dotProduct, Ket, mul_ite]
    rw [hcol] at hne
    by_cases hfirst : p.1 = i
    · refine ⟨hfirst, ?_⟩
      by_contra hadj
      apply hne
      simp [SzegedyIsometry, hfirst, expanderStep, hadj]
    · exact (hne (by simp [SzegedyIsometry, hfirst])).elim

end Qatlib.Concepts.WalkSearch.Th4Expander
