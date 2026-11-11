/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — divergence of two KdV solitons

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026), Section 3, pp. 18–20.

The paper compares the two single-soliton solutions of Eq. (97), p. 18, with velocities
`c = 1` and `c = 1 + δ`:

* c011 = Lemma 13, Eq. (99), p. 18 — the initial distance is `O(δ)`;
* c012 = Lemma 14, Eq. (111), p. 19 — at time `2/δ` the distance is `Ω(1)`.

The state distance is the Euclidean distance of the normalized fields, as in Eq. (21),
p. 9, and Eqs. (96)–(98), p. 18.  Lemmas 13 and 14 are not formalized (their proofs
need the closed-form `sech⁴` integrals and the overlap asymptotics of Eqs. (100)–(118));
their statements are preserved in this branch's history.  This file retains the
single-soliton vocabulary (`soliton`, `solitonUnit`, `solitonPerturbed`,
`normalizedFieldDistance`) used to state them.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory Filter
open Qatlib.Foundations.PureStateMath

open scoped BigOperators Topology

/-! ## The single-soliton solutions of Eq. (96)–(97), p. 18 -/

/-- `sech² z = 1 / cosh² z`. -/
def sechSq (z : ℝ) : ℝ := 1 / (Real.cosh z) ^ 2

/-- The single-soliton solution of Eq. (96), p. 18:
`φ(x,t) = -(c/2) sech²(√c/2 · (x - c t + a))`, with offset `a = 0` as in Eq. (97). -/
def soliton (c : ℝ) (x t : ℝ) : ℝ :=
  -(c / 2) * sechSq (Real.sqrt c / 2 * (x - c * t))

/-- The soliton of Eq. (97) with velocity `c = 1`. -/
def solitonUnit : ℝ → ℝ → ℝ := fun x t => soliton 1 x t

/-- The soliton of Eq. (97) with velocity `c = 1 + δ`. -/
def solitonPerturbed (δ : ℝ) : ℝ → ℝ → ℝ := fun x t => soliton (1 + δ) x t

/-! ## Field norms and normalized field distance -/

/-- Squared `L²` norm of a space-time field on `ℝ`. -/
def fieldL2Sq (φ : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, (φ x t) ^ 2

/-- `L²` inner product of two space-time fields on `ℝ`. -/
def fieldInner (φ φ' : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, φ x t * φ' x t

/-- Normalized distance of two fields at time `t`: normalize both fields and take the
pure-state Euclidean distance of Eq. (21), p. 9, `sqrt(2 - 2|⟨φ̂,φ̂'⟩|)`. -/
def normalizedFieldDistance (φ φ' : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (2 - 2 * |fieldInner φ φ' t| / Real.sqrt (fieldL2Sq φ t * fieldL2Sq φ' t))

end Qatlib.Papers.FluidDynamics26.MainResults
