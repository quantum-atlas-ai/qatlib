/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs

/-!
# Second-quantized Hubbard resource bounds

This module bounds the resource ledger for second-quantized Hubbard simulation with a linearly
bounded set of interacting pairs. It obtains an explicit quadratic bound for a chain and records
the occupation-number and adjoint identities for the fermionic operators.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `second_quantized_hubbard_cost`: For `m ≥ 1` and at most `c * m` interacting pairs, the
  Hubbard cost is at most `(1 + 9 * c) * m ^ 2`.
* `chain_hubbard_quadratic`: For `m ≥ 1`, the second-quantized Hubbard cost on a chain is at
  most `10 * m ^ 2`.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Foundations.PureStateMath

/-- The absolute difference between the numerical indices of two modes. -/
def interveningCount (m : ℕ) (i j : Fin m) : ℕ :=
  if i.val ≤ j.val then j.val - i.val else i.val - j.val

/-- The distance between two indices in `Fin m` is at most `m`. -/
theorem interveningCount_le (m : ℕ) (i j : Fin m) : interveningCount m i j ≤ m := by
  unfold interveningCount
  split
  · have h := j.isLt; omega
  · have h := i.isLt; omega

/-- The second-quantized potential-pass cost is exactly `m`. -/
theorem potential_pass_cost (m : ℕ) : secondQuantPotentialCost m = m := rfl

/-- The second-quantized pair cost is exactly `m + 8`. -/
theorem pair_cost (m : ℕ) : secondQuantPairCost m = m + 8 := rfl

/-- The chain's interaction-pair set has at most `m` elements. -/
theorem chain_neighbours_card (m : ℕ) : (chainPairs m).card ≤ m :=
  chainPairs_card m

/-- For `m ≥ 1` and at most `c * m` interacting pairs, the Hubbard cost is at most `(1 + 9 * c)
* m ^ 2`. -/
theorem second_quantized_hubbard_cost {m c : ℕ} (hm : 1 ≤ m)
    (pairs : Finset (Fin m × Fin m)) (hcard : pairs.card ≤ c * m) :
    secondQuantHubbardCost m pairs ≤ (1 + 9 * c) * m ^ 2 :=
  secondQuantHubbardCost_bound hm pairs hcard

/-- For `m ≥ 1`, the second-quantized Hubbard cost on a chain is at most `10 * m ^ 2`.
[AbramsLloyd1997] -/
theorem chain_hubbard_quadratic (m : ℕ) (hm : 1 ≤ m) :
    secondQuantHubbardCost m (chainPairs m) ≤ 10 * m ^ 2 :=
  chain_hubbard_cost_bound m hm

/-- The diagonal entry of the number operator is one when mode `i` is occupied and zero
otherwise. -/
theorem numberOp_diagonal_action {m : ℕ} (i : Fin m) (x : Reg m) :
    numberOp i x x = if x i then 1 else 0 := by
  rw [num_apply]
  simp

/-- The creation matrix is the conjugate transpose of the corresponding annihilation matrix. -/
theorem creation_eq_adjoint {m : ℕ} (i : Fin m) :
    creation i = (annihilation i)ᴴ :=
  creation_eq_conjTranspose i

end Qatlib.Papers.ManyBodyFermi97.MainResults
