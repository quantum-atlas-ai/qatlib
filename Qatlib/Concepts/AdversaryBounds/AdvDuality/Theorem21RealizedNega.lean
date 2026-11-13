/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessNega

/-!
# Circuit lower bound from the Kushilevitz witness

`theorem21Realized` applies the explicit witness `kushilevitzGammaW` to unitary query circuits
with a normalized initial state and bounded classification error on the twenty selected inputs.
It yields the lower bound `(2 + 3 * sqrt 5 / 5) * (1 - 2 * sqrt (eps * (1 - eps))) / 2` on the
query count.

The argument combines the witness norm lower bound and filter bound with the negative adversary
circuit inequality, realizing the witness from Theorem 21 of [HoyerLeeSpalek2007].

## Main statements

* `theorem21Realized`: proves the bounded-error circuit query lower bound from the explicit
  witness.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped Matrix.Norms.L2Operator

/-- Every unitary query circuit with a normalized initial state and error at most `eps`, where
`0 ≤ eps ≤ 1 / 2`, on the twenty witness inputs has query count at least `(2 + 3 * sqrt 5 /
5) * (1 - 2 * sqrt (eps * (1 - eps))) / 2`. This realizes the witness underlying [Hoyer,
Lee, and Spalek, Theorem 21][HoyerLeeSpalek2007]. -/
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
