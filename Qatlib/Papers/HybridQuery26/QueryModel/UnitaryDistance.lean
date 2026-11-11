/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpaceExtensions
import Qatlib.Papers.HybridQuery26.QueryModel.TranscriptPotential

set_option backward.isDefEq.respectTransparency false

/-!
# Oracle switching and the hybrid block bound (HybridQuery26 Lemma 2)

Source: Ambainis–Gilyén–Kokainis, *Tight bounds for hybrid quantum-classical query
algorithms*, arXiv:2610.06803v1, §4 "Proofs of Theorems 1 and 2", Lemma 2:

`‖|ψ₀⟩ − |ψ₁⟩‖ ≤ r ‖U₀ − U₁‖ ≤ r ε`

for an `r`-query quantum algorithm whose non-query operations do not depend on the oracle.

This module does **not** re-prove Lemma 2 from scratch: the hybrid argument over oracle
replacements is the existing Dev theorem
`QuantumAlgorithmDev.Concepts.QueryComplexity.DegreeMethod.unitaryHybridDistance_fixed`,
which states exactly `‖Run O C ψ − Run O' C ψ‖ ≤ QueryCount C * ‖O − O'‖` for unitary
oracles and a unitary circuit.  Here that result is restated in the paper's notation
(`ε` for the oracle gap, `r` for the block's query bound) and composed with Lemma 1
(`one_block_progress_le_query`) to give the per-block increment bound `(r ε)²` that the
proof of Theorem 1 consumes.

Boundary: the oracle switching is the paper's standard hybrid argument; the module does
not model controlled oracle access separately (`QueryCount` counts oracle applications),
and it does not assemble the transcript tree or the averaging over histories.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.HybridQuery26.QueryModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix

/-- **Lemma 2 in the paper's notation.** For unitary oracles `O, O'` with
`‖O − O'‖ ≤ ε` and a circuit with at most `r` oracle queries, the two final states are
within `r ε` in Hilbert distance.  The distance bound itself is the existing
`unitaryHybridDistance_fixed`; this statement only re-bounds it by the oracle gap `ε`. -/
theorem lemma2_state_distance {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]
    (O O' : Matrix K K ℂ) (C : Circuit K) (ψ : QState K) (r : ℕ) (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup K ℂ) (hO' : O' ∈ Matrix.unitaryGroup K ℂ)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (hcount : QueryCount C ≤ r)
    (hgap : oracleDistance O O' ≤ ε) :
    ‖toEuclidean_fromVec (Run O C ψ) - toEuclidean_fromVec (Run O' C ψ)‖
      ≤ (r : ℝ) * ε := by
  have hbase := unitaryHybridDistance_fixed O O' C ψ r hO hO' hC hψ hcount
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  calc ‖toEuclidean_fromVec (Run O C ψ) - toEuclidean_fromVec (Run O' C ψ)‖
      ≤ (r : ℝ) * oracleDistance O O' := hbase
    _ ≤ (r : ℝ) * ε := by
        exact mul_le_mul_of_nonneg_left hgap hr

/-- **The per-block increment bound of Theorem 1's proof.** A block that starts from the
normalised state `|ψ⟩`, applies at most `r` queries to unitary oracles `O, O'` and then
measures obeys
`M_{t+1}(h) − M_t(h) ≤ (r ε)²`, combining Lemma 2 (`lemma2_state_distance`) with
Lemma 1 (`one_block_progress_le_query`). -/
theorem hybrid_block_progress_le {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]
    (O O' : Matrix K K ℂ) (C : Circuit K) (ψ : QState K) (a : ℝ) (r : ℕ) (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup K ℂ) (hO' : O' ∈ Matrix.unitaryGroup K ℂ)
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcount : QueryCount C ≤ r) (hgap : oracleDistance O O' ≤ ε) (hε : 0 ≤ ε) :
    conditionalProgress a (BornProb (Run O C ψ)) (BornProb (Run O' C ψ)) - (2 * a - 1) ^ 2
      ≤ ((r : ℝ) * ε) ^ 2 := by
  have hψ0 : Normalized (Run O C ψ) := normalized_run O hO C hC hψ
  have hψ1 : Normalized (Run O' C ψ) := normalized_run O' hO' C hC hψ
  have hdist := lemma2_state_distance O O' C ψ r ε hO hO' hC hψ hcount hgap
  exact one_block_progress_le_query a ha0 ha1 (Run O C ψ) (Run O' C ψ) hψ0 hψ1
    (r : ℝ) ε hε (Nat.cast_nonneg r) hdist

end Qatlib.Papers.HybridQuery26.QueryModel
