/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.TensorRegisters.CohGraph.GraphState

/-!
# Coherent graph overlap and disagreement probability

This module identifies the real overlap defect of two coherent graph states with the fraction of
inputs on which their functions disagree. `graph_defect_le_bad` bounds this defect using a
specified exceptional set, and `graph_defect_uniform` expresses it as a uniform probability. For
background, see [NielsenChuang2010].

## Main statements

* `graph_overlap_defect`: overlap defect equals the disagreement fraction.
* `graph_defect_uniform`: uniform probability interpretation of the defect.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.TensorRegisters.CohGraph

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] [Nonempty I]

/-- One minus the real inner product of two graph states equals their functions' disagreement
count divided by the input cardinality. -/
theorem graph_overlap_defect (f g : I → O) :
    1 - (inner ℂ (graphState f) (graphState g)).re =
      ((Finset.univ.filter (fun i => f i ≠ g i)).card : ℝ) / (Fintype.card I : ℝ) := by
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => f i = g i)
  have hN : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [graph_inner_quotient]
  have hr : (((Finset.univ.filter (fun i => f i = g i)).card : ℂ) /
      (Fintype.card I : ℂ)).re =
      ((Finset.univ.filter (fun i => f i = g i)).card : ℝ)/(Fintype.card I : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rw [hr]
  simp only [Finset.card_univ] at hc
  field_simp
  have hcast : ((Finset.univ.filter (fun i => f i = g i)).card : ℝ) +
      ((Finset.univ.filter (fun i => f i ≠ g i)).card : ℝ) = Fintype.card I := by
    exact_mod_cast hc
  linarith

/-- If two functions agree outside `bad`, their graph overlap defect is at most the relative
cardinality of `bad`. -/
theorem graph_defect_le_bad (f g : I → O) (bad : Finset I)
    (hgood : ∀ i, i ∉ bad → f i = g i) :
    1 - (inner ℂ (graphState f) (graphState g)).re ≤
      (bad.card : ℝ) / (Fintype.card I : ℝ) := by
  rw [graph_overlap_defect]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs : Finset.univ.filter (fun i => f i ≠ g i) ⊆ bad := by
    intro i hi
    by_contra hb
    exact (Finset.mem_filter.mp hi).2 (hgood i hb)
  exact_mod_cast Finset.card_le_card hs

/-- The graph overlap defect equals the real probability of disagreement under the uniform
distribution on inputs. -/
theorem graph_defect_uniform (f g : I → O) :
    1 - (inner ℂ (graphState f) (graphState g)).re =
      ((PMF.uniformOfFintype' I).toOuterMeasure {i | f i ≠ g i}).toReal := by
  rw [graph_overlap_defect, PMF.toOuterMeasure_uniformOfFintype'_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_subtype, Set.mem_setOf_eq]

end Qatlib.Concepts.TensorRegisters.CohGraph
