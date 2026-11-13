/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpStep2SampledOracle
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 11 (source restatement)

Brandão–Svore, *Quantum Speed-ups for Semidefinite Programming*, fixed
arXiv:1609.05537v5 (PDF SHA-256
746714c3d97424df74d7f5956107687f73c6501403e35af757421328dfb030b7).
Lemma 11 is printed on pp. 13–14, Eqs. (40)–(41); its proof runs through
Eqs. (42)–(49), with the Chernoff + union bound on p. 14.

The lemma states: if `ORACLE(ρ)` does not fail, then with probability larger
than `1 − exp(−log^ξ(nm))` Algorithm 10 outputs `y` with

* `∑ bᵢ yᵢ ≤ α(1 + 2R(κ+ν))` (Eq. (40)), and
* `∑ yᵢ tr(Aᵢρ) ≥ tr(Cρ) − 2α(κ+ν)` (Eq. (41)).

The scalar good-event bridge is the library theorem
`Qatlib.Concepts.SdpMmwSolver.OracleError.sdpStep2SampledOracleOnGoodEvent`:
from the grid bound `κN ≤ α` and the two empirical deviations it derives exactly
Eqs. (40)–(41) for `y = κN · q`.  The present module restates that conclusion in
the paper's own `α(1+2R(κ+ν))` / `2α(κ+ν)` notation.

Scope note: the probabilistic clause `1 − exp(−log^ξ(nm))` and the Chernoff +
union bound over the grid `k ≤ γ` are outside the scope of this file. The
probability space for the `M` independent draws from `q_{ρ,k}` is not modeled.
The *unconditional* statement `SdpStep2SampledOracle` is refuted separately
(`not_sdpStep2SampledOracle`), so the good-event hypotheses are explicit here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma11Oracle

open Qatlib.Concepts.SdpMmwSolver.OracleError

/-- Lemma 11, Eq. (40)–(41), good-event scalar bridge.  On the concentration event of
the source proof (the two empirical deviations `hcost`/`hexpect` together with the
acceptance inequalities), the Algorithm-10 output `y = κN · q` satisfies the two source
bounds

`∑ bᵢ yᵢ ≤ α(1 + 2R(κ+ν))` and `∑ yᵢ eᵢ ≥ c − 2α(κ+ν)`,

where `eᵢ = tr(Aᵢρ)` and `c = tr(Cρ)`.  This is exactly the library theorem
`sdpStep2SampledOracleOnGoodEvent`, rewritten through the definitions of
`sdpSampledWidthBudget` and `sdpSampledSeparationSlack`. -/
theorem lemma11_goodEvent (m M N : ℕ) (b e q : Fin m → ℝ) (idx : Fin M → Fin m)
    (c α R κ ν : ℝ)
    (hscale : 0 < κ * (N : ℝ)) (hgrid : κ * (N : ℝ) ≤ α)
    (hR : 0 ≤ R) (htol : 0 ≤ κ + ν)
    (hcost : (∑ i, q i * b i) ≤ (∑ j, b (idx j)) / (M : ℝ) + R * (κ + ν))
    (hexpect : (∑ j, e (idx j)) / (M : ℝ) - (κ + ν) ≤ ∑ i, q i * e i)
    (hacceptCost : (∑ j, b (idx j)) / (M : ℝ) ≤
      α / (κ * (N : ℝ)) + R * (κ + ν))
    (hacceptExpect : c / (κ * (N : ℝ)) - (κ + ν) ≤
      (∑ j, e (idx j)) / (M : ℝ)) :
    (∑ i, b i * (κ * (N : ℝ) * q i)) ≤ α * (1 + 2 * R * (κ + ν)) ∧
      c - 2 * α * (κ + ν) ≤ ∑ i, (κ * (N : ℝ) * q i) * e i := by
  have h := sdpStep2SampledOracleOnGoodEvent m M N b e q idx c α R κ ν
    hscale hgrid hR htol hcost hexpect hacceptCost hacceptExpect
  simpa only [sdpSampledWidthBudget, sdpSampledSeparationSlack] using h

end Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma11Oracle
