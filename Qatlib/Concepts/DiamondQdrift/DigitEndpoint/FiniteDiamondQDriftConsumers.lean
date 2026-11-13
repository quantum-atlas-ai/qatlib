/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore

/-!
# A weighted Pauli qDRIFT example

This module specializes finite coin qDRIFT to the noncommuting Hamiltonian `pauliX + 2 •
pauliZ`. It computes one sampling probability and bounds the actual map in finite diamond
distance for `|t| ≤ 1`, illustrating the randomized simulation setting of [Campbell2019].

## Main statements

* `fair_qdrift_xz_actual_finite_diamond_consumer`: the explicit sampling law and simulation
  error.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal
set_option autoImplicit false

/-- For weights one and two on Pauli X and Z, the second outcome probability is `(2 / 3) * (1 -
(1 / 4) ^ R)` and the actual finite diamond error is at most `2⁻ˢ / 2` when `|t| ≤ 1`
[Campbell2019]. -/
theorem fair_qdrift_xz_actual_finite_diamond_consumer : ∀ (s : ℕ) (t : ℝ), |t| ≤ 1 →
  let w := (![1,2] : Fin 2 → ℕ)
  let K := fun j : Fin 2 => if j=0 then pauliX else pauliZ
  let n := fairQdriftSteps 3 1 s
  let R := fairQdriftFuel n s
  (fairQdriftLaw w 0 R).prob 1 = (2/3)*(1-(1/4:ℝ)^R) ∧
  finiteDiamondDistance (fairQdriftActualMap w 0 n R K t)
    (conjBranch (HamiltonianEvolution (pauliX+2 • pauliZ) t)) ≤
      ENNReal.ofReal (((2:ℝ)⁻¹)^s/2) := by
  intro s t ht
  (try dsimp only)
  refine ⟨(fair_bit_qdrift_noncommuting_weighted_consumer s 0 t 0 ht).1, ?_⟩
  apply finiteDiamondDistance_le_of_uniform _ _ (((2 : ℝ)⁻¹)^s) (by positivity)
  intro r X
  rw [fairQdriftActualMap_reference, tensorLeft_conjBranch]
  exact (fair_bit_qdrift_noncommuting_weighted_consumer s r t X ht).2

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
