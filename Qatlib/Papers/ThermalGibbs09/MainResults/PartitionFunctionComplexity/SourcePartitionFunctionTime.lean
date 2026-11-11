/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalGibbs09.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — Main result: partition function in time

`O( sqrt(D/Z(β)) · β^5 E_max^5 / ε^2 )`

Poulin--Wocjan, fixed arXiv:0905.2199, p. 4 (the paragraph after eq. (7),
describing the estimate of the ratios `F_k` and the evaluation of `Z(β)`).

Claim `c002`: with quantum counting estimating each partition-function ratio
`F_k`, the partition function can be evaluated to relative accuracy `ε` with
constant success probability in total time

`O( sqrt(D / Z(β)) · β^5 E_max^5 / ε^2 )`,

i.e. inverse-quadratic in `ε` and proportional to the thermalization time.

## Formalization boundary

As for `c001`, the concrete sequential quantum-counting circuit is not rebuilt
in Lean, so this file supplies only the `PartitionFunctionEstimator` interface
(runtime `T`, relative-accuracy guarantee `|Ẑ - Z(β)| ≤ ε Z(β)`).  The
`ε^{-2}` factor is the standard quantum-counting repetition cost; the
`β^5 E_max^5` factor is inherited from the thermalization time in `c001` (see
p. 4: "O(T_th(β) β^4 E_max^4 / ε^2)" before substituting the `T_th` bound).
The runtime bound itself is recorded in prose only; the finite-arithmetic
correctness half is in `SourcePartitionFunctionRatio`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionComplexity

open Qatlib.Papers.ThermalGibbs09.MainResults

/-- A certified partition-function estimator at inverse temperature `β`:
runtime `T` (counted in uses of the state-preparation/amplification circuit),
an estimate `Zhat`, and relative accuracy `ε`. -/
structure PartitionFunctionEstimator (D : ℕ) (H : Matrix (Fin D) (Fin D) ℂ) (β ε : ℝ) where
  /-- Runtime of the estimation procedure. -/
  T : ℝ
  /-- The runtime is nonnegative. -/
  T_nonneg : 0 ≤ T
  /-- The estimated value of the partition function. -/
  Zhat : ℝ
  /-- Relative accuracy of the estimate. -/
  relative_accuracy : |Zhat - partitionFunction β H| ≤ ε * partitionFunction β H

/- **arXiv:0905.2199, p. 4 (main result, partition function).** The paper's
guarantee: there is an absolute constant `C > 0` such that, for every
`D`-dimensional Hamiltonian `H` with `‖H‖ ≤ E_max`, every inverse temperature
`β ≥ 0` and every accuracy `0 < ε`, some partition-function estimator
evaluates `Z(β)` to relative accuracy `ε` in time

`T ≤ C · sqrt(D / Z(β)) · (β^5 E_max^5 / ε^2)`.

## Status: unformalised algorithmic content

The runtime bound depends on the concrete quantum-counting circuit: each
ratio `F_k = Z(β_{k+1})/Z(β_k)` is read out by phase estimation to accuracy
`ℓε`, `ℓ = Θ(1/δ)` sequential ratios are multiplied with `Z(β_0) = D`, and
quantum counting costs `O(1/ε^2)` repetitions on top of the state-preparation
(thermalization) time `T_th(β)`, giving `T = O(T_th(β) · β^4 E_max^4 / ε^2)`.
No such circuit is built in the repository, and the
`PartitionFunctionEstimator` certificate does not constrain `T` against an
actual procedure, so the bound cannot be honestly asserted (a trivially
satisfiable `∃` with `T = 0` would restate the conclusion and is deliberately
avoided).

The correctness half of the surrounding argument *is* formalised in the
sibling file `SourcePartitionFunctionRatio` (`prod_ratio_telescope`,
`prod_relative_error_bound`, `ratio_product_error_exp`): the ratio product
telescopes to `Z(β_n)/Z(β_0)` and its relative error is controlled by
`1 + x ≤ eˣ`. -/


end Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionComplexity
