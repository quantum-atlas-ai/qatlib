/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
public import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1Simulation
public import Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1TaylorTruncationLowc
public import Qatlib.Papers.Qubitization19.LCUConsumers.SourceLCU
public import Qatlib.Papers.Qubitization19.MainResults.SourceDefinitions

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Papers.Qubitization19
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Matrix.Norms.L2Operator

open Qatlib.Papers.Qubitization19.LCUConsumers

open Qatlib.Papers.Qubitization19.MainResults

namespace Qatlib.Papers.Qubitization19.MainResults

section

/-- Fixed arXiv:1610.06546v3, Theorem 1 (p.3): the full-spectrum operator core
of the two-word Taylor program. This is exactly the frozen contract
`Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation`,
whose proof is `Qatlib.Concepts.SignalPrimitive.MainResults.theorem1Simulation`:
for every Hermitian standard-form encoding at scale `α`, times `t` and errors
`ε ∈ (0,1)`, two explicit adjoint words query the encoding `2n` / `2n+1` times,
charge `2n+1` / `2n+2` phase macros, and their `4·even − i·4·odd` corner
combination is within `ε` of `exp(-i t H)` in the L² operator norm. -/
theorem theorem1_operator_core :
    Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation :=
  Qatlib.Concepts.SignalPrimitive.MainResults.theorem1Simulation

/-- Fixed arXiv:1610.06546v3, Theorem 1 proof (Eqs. (32)–(33), PDF p.14–15):
the Taylor truncation step. For every `τ` and `0 < ε` there is a cutoff `n`
with `2|τ| ≤ n+1`, tail `exponentialTaylorError τ n ≤ ε`, and explicit budget
`n ≤ 4|τ| + 8·log(8/min(ε,1)) + 8`. This is the frozen `Theorem1TaylorTruncation`
proved by `Qatlib.Concepts.SignalPrimitive.MainResults.theorem1TaylorTruncation`. -/
theorem theorem1_taylor_truncation :
    Qatlib.Concepts.SignalPrimitive.MainResults.Theorem1TaylorTruncation :=
  Qatlib.Concepts.SignalPrimitive.MainResults.theorem1TaylorTruncation

/-- The paper's degree criterion `Q = min{q ∈ ℤ⁺ : ε ≥ 4|t|^q/(q!·2^q)}`
(Eq. (1), PDF p.3), stated as a minimality predicate to avoid choosing a
noncomputable witness. -/
def IsPaperCutoffQ (t ε : ℝ) (Q : ℕ) : Prop :=
  0 < Q ∧
    ε ≥ 4 * |t| ^ Q / ((Nat.factorial Q : ℝ) * 2 ^ Q) ∧
    ∀ q : ℕ, 0 < q → q < Q →
      ¬ ε ≥ 4 * |t| ^ q / ((Nat.factorial q : ℝ) * 2 ^ q)

/-- Fixed arXiv:1610.06546v3, Theorem 1 (p.3), Eq. (1): the full cost statement.
For a standard-form encoding of a Hermitian `H` with `‖H‖ ≤ α` on a system of
dimension `N = card I` and ancilla dimension `d = card J`, and for every time `t`
and error `ε ∈ (0,1)`, there is a paper cutoff `Q` (the minimum in Eq. (1)) and
two words `wc`, `ws` whose combined query ledger is at most `4Q+1` and gate
ledger at most `4Q+3`, whose register uses one flag bit beyond `Bool × (J × I)`
(the `+2` qubits of the theorem are the ancilla and system registers plus the
flag), and whose `4·even − i·4·odd` corner approximates `exp(-i t H)` to `ε`.

The failure-probability `O(ε)` and `O(Q log d)` basic-gate synthesis are not
modelled by the frozen matrix substrate; see the file docstring.
This is a statement-only specification; no proof is asserted here. -/
def CostSpec : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (α t ε : ℝ),
      H.IsHermitian → 0 < α → ‖H‖ ≤ α → 0 < ε → ε < 1 →
      ProjectedUnitaryEncoding (((α⁻¹ : ℝ) : ℂ) • H) V
        (encodingFiber j₀) (encodingFiber j₀) →
      ∃ (Q : ℕ), IsPaperCutoffQ (t * α) ε Q ∧
        ∃ (wc ws : List (AdjointStep (Bool × (J × I)))),
          adjointQueryCount wc + adjointQueryCount ws ≤ 4 * Q + 1 ∧
          adjointGateCount wc + adjointGateCount ws ≤ 4 * Q + 3 ∧
          Fintype.card (Bool × (J × I)) = 2 * Fintype.card J * Fintype.card I ∧
          ‖((4 : ℂ) • compress (averageFrame (encodingFiber j₀))
                (evaluate (parallelOracle V) wc)
                (averageFrame (encodingFiber j₀))
              - Complex.I • ((4 : ℂ) • compress (averageFrame (encodingFiber j₀))
                (evaluate (parallelOracle V) ws)
                (averageFrame (encodingFiber j₀)))
              - NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))‖ ≤ ε

end

end Qatlib.Papers.Qubitization19.MainResults
