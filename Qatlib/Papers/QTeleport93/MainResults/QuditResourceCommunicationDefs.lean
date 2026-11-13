/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportation

/-!
# Qudit message width, branch count, and guess mass

`Clause11MessageWidth`, `Clause11BranchCount`, and `Clause11GuessMass` name the bit width,
outcome count, and reciprocal outcome count used in the qudit resource and communication
results. For positive `n`, these are the standard quantities for the qudit teleportation
protocol associated with [BennettEtAl1993Teleportation].

## Main statements

* `Clause11MessageWidth` is twice the ceiling base two logarithm of the dimension.
* `Clause11BranchCount` is the square of the dimension.
* `Clause11GuessMass` is the reciprocal of the branch count, interpreted in the real numbers.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QTeleport93.MainResults

/-- The fixed message width `2 * Nat.clog 2 n` for encoding the two qudit outcome coordinates. -/
def Clause11MessageWidth (n : ℕ) : ℕ := 2 * Nat.clog 2 n

/-- The number `n * n` of qudit teleportation outcome pairs. -/
def Clause11BranchCount (n : ℕ) : ℕ := n * n

/-- The real reciprocal of the branch count, equal to `1 / n^2` in positive dimension. -/
noncomputable def Clause11GuessMass (n : ℕ) : ℝ := 1 / ((Clause11BranchCount n : ℕ) : ℝ)

end Qatlib.Papers.QTeleport93.MainResults
