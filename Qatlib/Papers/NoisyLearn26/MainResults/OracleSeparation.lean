/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels

/-!
# Inclusions of oracle-relative learning classes

Proves the inclusions `NISQ ⊆ NBQP ⊆ BQP` for the algorithm predicates defined in
`InterfaceModels`. An assumed promise pair belonging to `BQP` and excluded from `NBQP` yields
`ClassStrict`. See [CotlerGongKannan2025] for the surrounding analysis.

## Main statements

* `nbqp_subset_bqp`: Every promise pair in the defined class `NBQP O` also belongs to `BQP O`.
* `nisq_subset_nbqp`: Every promise pair in the defined class `NISQ O` also belongs to `NBQP O`.
* `nbqp_bqp_separation_of_hard_promise`: A promise pair in `BQP O` and outside `NBQP O`
  witnesses strict containment of the defined classes.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation

open Qatlib.Papers.NoisyLearn26.MainResults

/-- Every promise pair in the defined class `NBQP O` also belongs to `BQP O`. -/
theorem nbqp_subset_bqp (O : Oracle) (yes no : Prop) : NBQP O yes no → BQP O yes no := by
  rintro ⟨A, ⟨_hpos, _hlt, hpoly⟩, hsolve⟩
  exact ⟨A, hpoly, hsolve⟩

/-- Every promise pair in the defined class `NISQ O` also belongs to `NBQP O`
[CotlerGongKannan2025]. -/
theorem nisq_subset_nbqp (O : Oracle) (yes no : Prop) : NISQ O yes no → NBQP O yes no := by
  rintro ⟨A, ⟨hpos, hlt, hpoly, _hplog⟩, hsolve⟩
  exact ⟨A, ⟨hpos, hlt, hpoly⟩, hsolve⟩

/-- A promise pair in `BQP O` and outside `NBQP O` witnesses strict containment of the defined
classes [CotlerGongKannan2025]. -/
theorem nbqp_bqp_separation_of_hard_promise (O : Oracle) {yes no : Prop}
    (h : BQP O yes no ∧ ¬ NBQP O yes no) : ClassStrict (NBQP O) (BQP O) :=
  ⟨fun y n hc => nbqp_subset_bqp O y n hc, ⟨yes, no, h.1, h.2⟩⟩

end Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation
