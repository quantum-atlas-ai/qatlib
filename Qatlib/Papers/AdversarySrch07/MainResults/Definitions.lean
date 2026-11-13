/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Definitions for ordered-search adversary bounds

Defines the central-binomial sequence `xi`, its truncated correlations `AM`, and the cyclic
ordered-search inputs used in [ChildsLee2008]. The matrices `ospDelta` record the coordinatewise
input differences.

The quantities `ospAdvNonneg` and `ospAdvNeg` specify the nonnegative and unrestricted spectral
adversary bounds, using the matrix operator norm constraints for each query coordinate.

## Main statements

* `xi`: Defines `choose (2 * i) i / 4 ^ i`.
* `AM`: Defines the finite shifted correlation of `xi`.
* `ospAdvNonneg`: Defines the supremum over feasible real nonnegative Hermitian adversary
  matrices.
* `ospAdvNeg`: Defines the unrestricted source adversary value.

## References

* [Childs and Lee, 2008][ChildsLee2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.AdversarySrch07.MainResults

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

/-- The normalized central-binomial sequence `Nat.centralBinom i / 4 ^ i`, valued in the reals. -/
noncomputable def xi (i : ℕ) : ℝ := (Nat.centralBinom i : ℝ) / 4 ^ i

/-- The truncated correlation `∑ i < m - j, xi i * xi (i + j)`. -/
noncomputable def AM (m j : ℕ) : ℝ := ∑ i ∈ Finset.range (m - j), xi i * xi (i + j)

/-- The cyclic ordered-search input family, with bit one when `(x + j) mod (2 * N) < N` and bit
zero otherwise. -/
def ospInput (N : ℕ) : Fin (2 * N) → Fin (2 * N) → Fin 2 :=
  fun x j => if (x.val + j.val) % (2 * N) < N then 1 else 0

/-- The coordinate-indexed source alphabet difference matrices of the cyclic ordered-search
inputs. -/
def ospDelta (N : ℕ) : Fin (2 * N) → Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  sourceAlphabetDelta (ospInput N)

/-- The supremum of operator norms over Hermitian, real-valued, entrywise nonnegative,
zero-diagonal matrices whose Hadamard products with every `ospDelta` have norm at most one. -/
noncomputable def ospAdvNonneg (N : ℕ) : ℝ≥0∞ :=
  ⨆ Γ : { Γ : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ //
      Γ.IsHermitian ∧
      (∀ x y, (Γ x y).im = 0) ∧
      (∀ x y, x = y → Γ x y = 0) ∧
      (∀ x y, 0 ≤ (Γ x y).re) ∧
      (∀ j : Fin (2 * N), ‖Γ ⊙ ospDelta N j‖ ≤ 1) },
    ENNReal.ofReal ‖Γ.1‖

/-- The unrestricted source adversary value for `ospDelta N` and the identity output labeling. -/
noncomputable def ospAdvNeg (N : ℕ) : ℝ≥0∞ :=
  sourceAdversary (ospDelta N) (id : Fin (2 * N) → Fin (2 * N))

end Qatlib.Papers.AdversarySrch07.MainResults
