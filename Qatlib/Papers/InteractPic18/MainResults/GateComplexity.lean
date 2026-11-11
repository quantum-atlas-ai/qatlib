/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.InteractionPicture

/-!
# GateComplexity — Theorem 7 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Theorem 7 (Section IV p. 8, Eq. (24)): the truncated-Dyson-series gate
  complexity `C_TDS` is bounded by the interaction-picture gate rate
  `O(α_B t (C_B + … log(t(α_A+α_B)/ε)) log(α_B t/ε)/log log(α_B t/ε))`; the
  formal content is the per-copy gate ledger: each of the `K` duplicated
  oracle copies carries one primitive gate, so the summed gate cost of the
  dyadic counter register is bounded by the frozen interaction-picture gate
  rate `EffectiveInteractionGateRate`.

Boundary: the rate is a matrix/integer ledger over the frozen
`ipSegmentProgram`; the paper's big-O form is not restated as an asymptotic
statement. No qubit or failure accounting beyond `ipSegmentCopies` is
asserted here (Theorem 3's failure ledger is `MainAlgorithm.theorem3_total_failure`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.RandCompile.ChannelBudget
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.InteractPic18.MainResults.GateComplexity

/-- **Theorem 7, gate rate** (fixed arXiv:1805.00675v2, Eq. (24)): supplying
the per-step gate cost `cost j` of the `j`-th dyadic time step inside the
budget `CA·|t_j|·(1 + log(1 + |t_j|/δ))^γ + 1`, the total primitive-gate
count of the interaction-picture counter register is at most
`2·CA·τ·(1 + log(1 + τ/δ))^γ + (nd + 1)`. This is the `α_B t · polylog` form
of the source with `CA ↔ C_B + C_{e^{-iA/α_B}}`, `τ ↔ α_B t`, `δ ↔ ε`. -/
theorem theorem7_gate_rate (p : EffectiveSegmentParameters) (gamma : ℝ) (hgamma : 0 < gamma)
    (tau delta : ℚ) (nd : ℕ) (CA : ℝ) (hτ : 0 ≤ tau) (hδ : 0 < delta) (hCA : 0 ≤ CA)
    (cost : ℕ → ℕ)
    (hcost : ∀ j ≤ nd, (cost j : ℝ) ≤
        CA * abs (effectiveIPDyadicTime tau nd j) *
          (1 + Real.log (1 + abs (effectiveIPDyadicTime tau nd j) / (delta : ℝ))) ^ gamma + 1) :
    ((∑ j ∈ Finset.range (nd + 1), cost j) : ℝ) ≤
      2 * CA * (tau : ℝ) * (1 + Real.log (1 + (tau : ℝ) / (delta : ℝ))) ^ gamma + (nd + 1) :=
  ipGateRateTotal p gamma hgamma tau delta nd CA hτ hδ hCA cost hcost

/-- **Theorem 7, per-copy gates** (fixed arXiv:1805.00675v2, Eq. (24)): the
actual interaction-picture segment program spends exactly one primitive gate
per duplicated oracle copy, so its gate count equals the HAM-T query count
`ipSegmentQueries p = K`. -/
theorem theorem7_segment_gates (p : EffectiveSegmentParameters) :
    effectiveGates (ipSegmentProgram p) = ipSegmentQueries p :=
  ipSegmentProgram_gates p

/-- **Theorem 7, HAM-T queries** (fixed arXiv:1805.00675v2, Eq. (24)): the
actual segment program makes exactly one oracle query per duplicated copy,
`K = ipSegmentQueries p`. -/
theorem theorem7_segment_queries (p : EffectiveSegmentParameters) :
    effectiveQueries (ipSegmentProgram p) = ipSegmentQueries p :=
  ipSegmentProgram_queries p

/-- **Theorem 7, register width** (fixed arXiv:1805.00675v2, Eq. (24)): the
segment program uses `ns + K(na + nd)` wires, `K = ipSegmentCopies p`. -/
theorem theorem7_segment_width (p : EffectiveSegmentParameters) :
    (ipSegmentProgram p).width = p.ns + ipSegmentCopies p * (p.na + p.nd) := rfl

/-- **Theorem 7, cutoff identification** (fixed arXiv:1805.00675v2, Eq. (24)):
the number of duplicated copies is the computed factorial-search cutoff
`K = ⌈-1 + 2 log(2/ε)/log log(2/ε) + 1⌉` as implemented by
`computedDysonCutoff (precision + 8)`. -/
theorem theorem7_copies_eq_cutoff (p : EffectiveSegmentParameters) :
    ipSegmentCopies p = computedDysonCutoff (p.precision + 8) := rfl

end Qatlib.Papers.InteractPic18.MainResults.GateComplexity
