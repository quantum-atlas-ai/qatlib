/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries.PowerAccumulation

/-!
# Symmetric Trotter steps and exact evolution powers

This module defines the increasing and decreasing ordered products `orderedProd` and
`reverseProd`, and combines them in `trotterStep`. The identity `timeEvolution_pow_nat`
identifies repeated exact evolution with evolution for the accumulated time, providing the
comparison operator for Trotter power estimates. The mathematical context is
[AharonovTaShma2007].

## Main statements

* `trotterStep`: The symmetric product of the individual Hamiltonian evolutions, first in
  increasing order and then in decreasing order, with time parameter `δ` for each factor.
* `timeEvolution_pow_nat`: The `N`th power of evolution for time `t` equals evolution for time
  `N * t`.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries

open Qatlib.Papers.AdiabStateGen03.MainResults

/-- The product of operators indexed by `Fin M`, taken in increasing index order. -/
def orderedProd {n M : ℕ} (f : Fin M → Op n) : Op n :=
  (List.finRange M).foldr (fun m acc => f m * acc) (1 : Op n)

/-- The product of operators indexed by `Fin M`, taken in decreasing index order. -/
def reverseProd {n M : ℕ} (f : Fin M → Op n) : Op n :=
  (List.finRange M).reverse.foldr (fun m acc => f m * acc) (1 : Op n)

/-- The symmetric product of the individual Hamiltonian evolutions, first in increasing order
and then in decreasing order, with time parameter `δ` for each factor. -/
def trotterStep {n M : ℕ} (Hs : Fin M → Ham n) (δ : ℝ) : Op n :=
  orderedProd (fun m => timeEvolution (Hs m) δ) * reverseProd (fun m => timeEvolution (Hs m) δ)

/-- The `N`th power of evolution for time `t` equals evolution for time `N * t`
[AharonovTaShma2007]. -/
theorem timeEvolution_pow_nat {n : ℕ} (H : Ham n) (t : ℝ) (N : ℕ) :
    timeEvolution H t ^ N = timeEvolution H ((N : ℝ) * t) := by

  haveI : NormedAlgebra ℚ (Op n) := NormedAlgebra.restrictScalars ℚ ℂ (Op n)
  unfold timeEvolution
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ N, smul_smul]
  congr 1
  ring

end Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries
