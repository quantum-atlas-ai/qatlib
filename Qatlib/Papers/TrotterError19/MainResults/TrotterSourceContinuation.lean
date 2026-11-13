/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterError19.MainResults.TrotterSourceContinuationDefs

/-!
# A single parallel layer for disjoint supports

This module supplies the disjoint-support scheduling case of the Trotter source continuation.
Pairwise disjoint term supports can all be assigned to the unique layer of `Fin 1`. See
[ChildsEtAl2021Trotter].

## Main statements

* `clause52_disjoint_single_layer`: Validity of the constant single-layer schedule.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false

namespace Qatlib.Papers.TrotterError19.MainResults

open Qatlib
open Finset
open scoped BigOperators

/-- Pairwise disjoint supports form a valid parallel schedule when every term is assigned to the
unique layer of `Fin 1`. -/
theorem clause52_disjoint_single_layer {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S)
    (h : ∀ i j : ι, i ≠ j → Disjoint (supp i) (supp j)) :
    IsParallelSchedule supp (fun _ => (0 : Fin 1)) := by
  intro i j _
  by_cases hij : i = j
  · exact Or.inl hij
  · exact Or.inr (h i j hij)

end Qatlib.Papers.TrotterError19.MainResults
