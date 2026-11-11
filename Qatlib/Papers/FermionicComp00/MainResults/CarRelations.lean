/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Canonical anticommutation relations

`source_car_relations` collects the mixed, annihilation, and creation anticommutation relations
for the Jordan-Wigner matrices on an `m`-mode register.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `source_car_relations`: packages the three canonical anticommutation identities.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermionicComp00.MainResults.CarRelations

/-- The creation and annihilation matrices satisfy the canonical anticommutation relations:
mixed anticommutators are the Kronecker delta times the identity, and same-type
anticommutators vanish. [BravyiKitaev2002] -/
theorem source_car_relations (m : ℕ) :
    (∀ j k : Fin m,
        annihilation j * creation k + creation k * annihilation j
          = (if j = k then (1 : Matrix (Reg m) (Reg m) ℂ) else 0)) ∧
    (∀ j k : Fin m,
        annihilation j * annihilation k + annihilation k * annihilation j = 0) ∧
    (∀ j k : Fin m,
        creation j * creation k + creation k * creation j = 0) := by
  obtain ⟨hcar, -⟩ := g1 m
  refine ⟨?_, ?_, ?_⟩
  · intro j k; exact (hcar j k).1
  · intro j k; exact (hcar j k).2.1
  · intro j k; exact (hcar j k).2.2

end Qatlib.Papers.FermionicComp00.MainResults.CarRelations
