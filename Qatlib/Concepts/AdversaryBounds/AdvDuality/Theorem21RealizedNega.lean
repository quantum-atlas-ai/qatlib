/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessNega
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Matrix.Norms.L2Operator

theorem theorem21Realized : Theorem21Realized := by
  intro W _ _ C psi E eps hC hpsi he0 he1 hs
  obtain ⟨hG, hz, hfilter, hnorm⟩ := theorem21RealizedWitness
  have h := negative_adversary_actual_bounded_error_circuit_lower_bound
    (Fin 20) W 6 kushilevitzInputW kushilevitzGammaW kushilevitzFunW C psi E eps
    hG hz hC hpsi he0 he1 hs
  have hsqrt : Real.sqrt (eps * (1 - eps)) ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [sq_nonneg (eps - 1 / 2)]
  have hfactor : 0 ≤ 1 - 2 * Real.sqrt (eps * (1 - eps)) := by linarith
  have hleft := mul_le_mul_of_nonneg_left hnorm hfactor
  have hright := mul_le_mul_of_nonneg_left hfilter
    (by positivity : 0 ≤ (2 : ℝ) * QueryCount C)
  nlinarith

end Qatlib.Concepts.AdversaryBounds.AdvDuality
