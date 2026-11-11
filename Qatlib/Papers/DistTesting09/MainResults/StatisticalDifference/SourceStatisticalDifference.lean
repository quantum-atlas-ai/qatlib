/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistTesting09.MainResults.Defs
import Qatlib.Papers.DistTesting09.MainResults.StatisticalDifference


set_option backward.isDefEq.respectTransparency false

/-!
# DistTesting09 — Statistical difference (Sections 2–3)

Fixed source: arXiv:0907.3920v1, *Quantum algorithms for testing properties of
distributions* (Bravyi, Harrow, Hassidim), 22 Jul 2009.

Contents:

* Theorem 5 (`theorem5_estprob`), p. 5, Eqs. (3)–(4): the quantum counting
  primitive `EstProb(p, A, M)` makes `M` queries and outputs `p̃_A` with
  `Pr[|p̃_A − p_A| ≤ δ] ≥ 1 − ω` whenever `M ≥ c√p_A/(ωδ)` and
  `M ≥ c/(ω√δ)`; if `p_A = 0` then `p̃_A = 0` with certainty;
* Lemma 1 (`lemma1_estdist`), p. 6, Eq. (7): `EstDist(p, q, ε, τ)` outputs `x̃`
  with `Pr[|x̃ − E(x)| < ε] ≥ 1 − τ`, `E(x) = ½‖p − q‖₁`;
* Proposition 1 (`prop1_ratio_lipschitz`), p. 7, Eq. (13):
  `|f(p,q) − f(p̃,q̃)| ≤ 5δ` for `f(p,q) = (p−q)/(p+q)` and `δ ≤ 1/5`;
* Theorem 1 (`theorem1_statistical_difference`), p. 3: statistical difference
  is testable in `O(N^{1/2})` queries.

The probability space is the finite product law of the library
(`FinDist.probEvent (L := n)` with the midpoint distribution `r = (p+q)/2`),
so Lemma 1's concentration estimate (Eq. (8)) is a genuine statement about the
sampling step. The quantum oracle model (`EstProb`, swap registers) is
abstracted: Theorem 5 is stated as the guarantee (3)–(4) on the output law, and
Lemma 1 is stated conditionally on the per-sample estimate accuracy (Eq. (14)).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.DistTesting09.MainResults.Defs

open Qatlib.Papers.DistTesting09.MainResults.StatisticalDifference

namespace Qatlib.Papers.DistTesting09.MainResults.StatisticalDifference

variable {N : ℕ}

/-! ### The auxiliary distribution `r = (p+q)/2` and the variable `x_i` (Section 3) -/

/-- The mass of the outputs of a finite estimator that lie within `δ` of
`target`: `Pr[|p̃ − target| ≤ δ]`. -/
def estMass {K : ℕ} (law : FinDist (Fin K)) (val : Fin K → ℝ) (target δ : ℝ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => |val r - target| ≤ δ), law.prob r

end Qatlib.Papers.DistTesting09.MainResults.StatisticalDifference
