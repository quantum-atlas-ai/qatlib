/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Mathlib.Algebra.Algebra.Subalgebra.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermionicComp00.MainResults.CarRelations

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
