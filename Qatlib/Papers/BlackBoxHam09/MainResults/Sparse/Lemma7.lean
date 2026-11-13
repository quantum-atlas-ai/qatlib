/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs

/-!
# Lemma 7 perturbation error bounds

This module bounds the diagonal perturbation expression `sandwich` using `lemma7_sandwich_bound`
and its amplified form `lemma7_simulation_error`. It also provides the triangle bound
`lemma7_error_composition` for `simulationError` and a monotonicity step for an existing scalar
perturbation bound.

These estimates accompany the error analysis of Lemma 7 in [BerryChilds2012].

## Main statements

* `lemma7_simulation_error` bounds the amplified perturbation expression.
* `lemma7_error_composition` adds errors through an intermediate matrix.

## References

* [Berry and Childs, 2012][BerryChilds2012]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Sparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

/-- For `0 < ε ≤ 1`, `maxAbs x ≤ ε`, positive `Λ1`, and nonnegative time, the scaled sandwich
norm multiplied by `t * Λ1 / ε` is at most `3 * spectralNorm H * t * ε`. See [Berry and
Childs, Lemma 7][BerryChilds2012]. -/
theorem lemma7_simulation_error
    (H : Ham ι) (x : ι → ℝ) {ε Λ1 t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : maxAbs x ≤ ε) (hΛ1 : 0 < Λ1) (ht : 0 ≤ t) :
    (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖ ≤ 3 * spectralNorm H * t * ε :=
  lemma7_error_amplification H x ε Λ1 t hε hε1 hx hΛ1 ht

/-- For nonnegative `ε` and positive `Λ1`, bound the scaled sandwich norm by `(ε * spectralNorm
H / Λ1) * (2 * maxAbs x + (maxAbs x) ^ 2)`. See [Berry and Childs, Lemma
7][BerryChilds2012]. -/
theorem lemma7_sandwich_bound
    (H : Ham ι) (x : ι → ℝ) {ε Λ1 : ℝ} (hε : 0 ≤ ε) (hΛ1 : 0 < Λ1) :
    ‖(ε / Λ1) • sandwich H x‖ ≤
      (ε * spectralNorm H / Λ1) * (2 * maxAbs x + (maxAbs x) ^ 2) :=
  sandwich_norm_le H x ε Λ1 hε hΛ1

/-- Compose two `simulationError` bounds through an intermediate matrix, adding their error
tolerances. See [Berry and Childs, Lemma 7][BerryChilds2012]. -/
theorem lemma7_error_composition (K M E : Matrix ι ι ℂ) (δ1 δ2 : ℝ)
    (h1 : simulationError K M ≤ δ1) (h2 : simulationError M E ≤ δ2) :
    simulationError K E ≤ δ1 + δ2 := by
  have h := simulationError_triangle K M E
  linarith

/-- Given the perturbation bound with right side `3 * spectralNorm H * t * ε1`, enlarge its
right side to use any `ε2 ≥ ε1` under the stated sign conditions. See [Berry and Childs,
Lemma 7][BerryChilds2012]. -/
theorem lemma7_bound_mono {H : Ham ι} {x : ι → ℝ} {ε1 ε2 Λ1 t : ℝ}
    (hε : ε1 ≤ ε2) (hε1 : 0 < ε1) (ht : 0 ≤ t) (hH : 0 ≤ spectralNorm H)
    (h1 : (t * Λ1 / ε1) * ‖(ε1 / Λ1) • sandwich H x‖ ≤ 3 * spectralNorm H * t * ε1) :
    (t * Λ1 / ε1) * ‖(ε1 / Λ1) • sandwich H x‖ ≤ 3 * spectralNorm H * t * ε2 := by
  have hc : 0 ≤ 3 * spectralNorm H * t := by positivity
  calc (t * Λ1 / ε1) * ‖(ε1 / Λ1) • sandwich H x‖ ≤ 3 * spectralNorm H * t * ε1 := h1
    _ ≤ 3 * spectralNorm H * t * ε2 := by gcongr

end Qatlib.Papers.BlackBoxHam09.MainResults.Sparse
