/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Numerical interface for HSP complexity certificates

This module introduces `bitLength` and the cubic expressions `polyBound`, `polyBoundCyclic`, and
`polyBoundFamily` used to state complexity estimates associated with [CosmePortugal2007]. The
structure `HSPAlgorithm` stores a natural query count and a rational success value; its fields
carry no correctness or probability-range conditions.

## Main statements

- `bitLength` fixes the logarithmic size convention, including the value one at zero.
* `polyBound`, `polyBoundCyclic`, and `polyBoundFamily` define the numerical bounds for the
  semidirect, cyclic, and finite-family settings.
- `HSPAlgorithm` packages the two numerical fields used by later certificates.

## References

* [Cosme and Portugal, 2007][CosmePortugal2007]
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

/-- The size convention `Nat.log 2 n + 1`, equal to the binary digit length for positive `n` and
to one for `n = 0`. -/
def bitLength (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The numerical cubic bound `100 * ((r + 2) * bitLength p) ^ 3` used for the
semidirect-product parameters. -/
def polyBound (r p : ℕ) : ℕ := 100 * ((r + 2) * bitLength p) ^ 3

/-- The numerical cubic bound `100 * (bitLength n) ^ 3` used for a cyclic-factor size parameter. -/
def polyBoundCyclic (n : ℕ) : ℕ := 100 * (bitLength n) ^ 3

/-- The cubic bound with coefficient one hundred on the sum of `(r + 2) * bitLength p` and the
bit lengths of the finitely indexed parameters `q i`. -/
def polyBoundFamily {ι : Type*} [Fintype ι] (r p : ℕ) (q : ι → ℕ) : ℕ :=
  100 * ((r + 2) * bitLength p + Finset.univ.sum (fun i => bitLength (q i))) ^ 3

/-- A record of a natural query count and a rational success value, indexed by a group `G`. The
structure imposes no correctness or probability-range conditions on these fields. -/
structure HSPAlgorithm (G : Type*) [Group G] where

  queryCount : ℕ

  successProb : ℚ

end Qatlib.Papers.SemidirectHSP07.MainResults
