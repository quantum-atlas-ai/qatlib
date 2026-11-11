/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — the paper's model layer

Berry--Cleve--Gharibian, *Gate-efficient discrete simulations of continuous-time
quantum query algorithms*, fixed arXiv:1211.4637v2 (5 April 2013).
PDF SHA-256 `aef583fed3675ee75a251ed7438ab99cb4c16b34697dd8f4293f3d39d07d471d`
(local copy `prove/assets/1211.4637.pdf`).

This module fixes the model used by the paper-layer statements:

* `ContinuousTimeQueryAlgorithm` — a continuous-time query algorithm running for
  time `T` under a driving Hamiltonian `H(t)`, with an output law on a finite
  outcome type (the paper's bounded-error task semantics).
* `DiscreteQueryAlgorithm` — a discrete-query algorithm with the paper's three
  resource counters (queries, 1- and 2-qubit gates, qubits of space) and an output law.
* `Simulates` — total-variation closeness of two output laws, the paper's
  "constant error" simulation relation.
* `ApproxImplementable` — Definition from §3 (text between Eq. (1) and
  Theorem 3.2, p.2–3): the driving Hamiltonian is implementable within precision
  `ε'` using `G` gates, measured in the completely bounded norm.  The
  completely-bounded distance is the frozen
  `QuantumAlgorithm.Papers.RandCompiler19.ChannelBudget.finiteDiamondDistance`;
  the ideal propagator is the frozen Volterra solution `sourceVolterraMatrix`.
* `averageTraceDistance` — Eq. (43), the error `D_av` of §5.

Model boundary (also recorded in each theorem docstring):

* The gate count `G` of an implementation is a *granted* resource: the paper
  assumes a concrete gate decomposition of the time-evolution unitary, and this
  model records its gate count as the `gates` field of `ApproxImplementable`
  rather than re-deriving 1- and 2-qubit gate synthesis from a matrix.
* The output law `p` of a continuous-time algorithm is taken as the algorithm's
  task output; `Simulates` compares laws, which is the paper's notion of
  simulating the algorithm with constant error.  The internal unitary semantics
  of the driving Hamiltonian enters through `ApproxImplementable`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Papers.GateEffSim12.MainResults.SourceModel

/-! ## Channels and diamond distance -/

/-- The conjugation channel `ρ ↦ U ρ U†` of a matrix `U`. -/
def conjChannel {d : ℕ} (U : Operator d) : Operator d →ₗ[ℂ] Operator d where
  toFun ρ := U * ρ * Uᴴ
  map_add' a b := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, RingHom.id_apply]

/-- The completely bounded distance between two conjugation channels, i.e. the
paper's precision measure for "approximately implementable". -/
def cbDistance {d : ℕ} (U V : Operator d) : ℝ≥0∞ :=
  finiteDiamondDistance (conjChannel U) (conjChannel V)

/-! ## The two algorithm models -/

/-- A continuous-time query algorithm of arXiv:1211.4637v2 §3: it runs for time
`time` under the driving Hamiltonian `driving`, and outputs a distribution `p`.
The oracle Hamiltonian is the paper's fixed diagonal `HQ` and is not part of the
driving family; the model keeps only the algorithm's data used by Theorem 3.2. -/
structure ContinuousTimeQueryAlgorithm (X Ω : Type) [Fintype X] [Fintype Ω] (d : ℕ) where
  /-- The driving Hamiltonian `H(t)` of the paper (independent of the oracle). -/
  driving : ℝ → Operator d
  /-- Each `H(t)` is Hermitian, as required for Hamiltonian evolution. -/
  hermitian : ∀ t, (driving t).IsHermitian
  /-- Total evolution time `T` (the paper's query time). -/
  time : ℝ
  time_pos : 0 < time
  /-- Output probability of outcome `o` on input `x`. -/
  p : X → Ω → ℝ
  p_nonneg : ∀ x o, 0 ≤ p x o
  p_sum : ∀ x, ∑ o, p x o = 1

/-- A discrete-query quantum algorithm with the three resource counters of
Theorem 3.2: oracle queries, 1- and 2-qubit gates, and qubits of space. -/
structure DiscreteQueryAlgorithm (X Ω : Type) [Fintype X] [Fintype Ω] where
  queryCount : ℕ
  gateCount : ℕ
  space : ℕ
  p : X → Ω → ℝ
  p_nonneg : ∀ x o, 0 ≤ p x o
  p_sum : ∀ x, ∑ o, p x o = 1

/-- `B` simulates `A` within error `δ`: the output laws are `2δ`-close in total
variation on every input.  This is the paper's "simulated with constant error". -/
def Simulates {X Ω : Type} [Fintype X] [Fintype Ω] {d : ℕ}
    (A : ContinuousTimeQueryAlgorithm X Ω d) (B : DiscreteQueryAlgorithm X Ω)
    (δ : ℝ) : Prop :=
  ∀ x, ∑ o, |A.p x o - B.p x o| ≤ 2 * δ

/-! ## Approximate implementability (§3) -/

/-- The driving Hamiltonian `K` is **approximately implementable within precision
`ε'` using `G` gates** in the sense of §3 of arXiv:1211.4637v2 (text before
Theorem 3.2, p.2–3): there is a family of unitaries `U ts tf`, produced by at most
`G` elementary gates, whose channels are within completely bounded distance `ε'`
of the exact propagator of `K` from `ts` to `tf`, for every `0 ≤ ts ≤ tf ≤ T`.
The exact propagator is the frozen Volterra solution `sourceVolterraMatrix`. -/
def ApproxImplementable {d : ℕ} (K : ℝ → Operator d) (T ε' : ℝ) (G : ℕ) : Prop :=
  ∃ (U : ℝ → ℝ → Operator d) (gates : ℕ),
    gates ≤ G ∧
      ∀ ts tf : ℝ, ts ∈ Set.Icc 0 T → tf ∈ Set.Icc 0 T → ts ≤ tf →
        U ts tf ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
          cbDistance (U ts tf) (sourceVolterraMatrix K (tf - ts)) ≤ ENNReal.ofReal ε'

/-! ## The error measure of §5 (Eq. (43)) -/

/-- Eq. (43) of arXiv:1211.4637v2 (p.19): the error
`D_av = Σ_b ‖p_u(b) ρ_u(b) − p_c(b) ρ_c(b)‖_tr` between the uncompressed and
compressed measurement schemes, with outcome type `Ω` and target dimension `W`. -/
def averageTraceDistance (Ω : Type) [Fintype Ω] (W : ℕ)
    (pu pc : Ω → ℝ) (ρu ρc : Ω → Operator W) : ℝ :=
  ∑ b, Matrix.traceNorm (pu b • ρu b - pc b • ρc b)

end Qatlib.Papers.GateEffSim12.MainResults.SourceModel
