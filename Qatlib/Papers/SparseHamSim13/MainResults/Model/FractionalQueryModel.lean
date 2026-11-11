/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.SparseHamSim13.MainResults.Model.SparseSimModel
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Fractional-query and continuous-query model vocabulary

Fixed source: arXiv:1312.1414 (Berry, Childs, Cleve, Kothari, Somma, *Exponential
improvement in precision for simulating sparse Hamiltonians*), Section 3,
Definitions of the continuous-query and fractional-query models, pp. 6–8.

The paper compares three computational models:

* the **discrete-query** model, already encoded by `AdjointStep`/`evaluate` in
  `Model.SparseSimModel` (`Concepts.CoherentSim.CoherentOAA`);
* the **fractional-query** model: the algorithm may apply `e^{i x A}` for a
  Hermitian generator `A` and real `x`, at cost `|x| · ‖A‖max` (the paper's
  `cost(A) ≤ 1` normalisation);
* the **continuous-query** model: the algorithm queries a time-dependent
  Hamiltonian along a timeline, at cost equal to the total elapsed time.

`FracStep wires` is one step of a counted fractional word; `evalFracWord`
evaluates it as a matrix; `fracQueryCount` counts fractional queries and
`fracCost` sums the fractional costs.  `ContinuousProgram` is a list of
Hamiltonian segments with durations.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped Matrix.Norms.L2Operator Classical BigOperators

namespace Qatlib.Papers.SparseHamSim13.MainResults

/-- Max-entry norm `‖A‖max = ⨆ i j, ‖A i j‖` of a matrix on `Reg k`
(arXiv:1312.1414 §2). -/
noncomputable def matMaxEntry {k : ℕ} (A : Matrix (Reg k) (Reg k) ℂ) : ℝ :=
  ⨆ (i : Reg k) (j : Reg k), ‖A i j‖

/-! ## Fractional-query words -/

/-- One step of a counted fractional-query word (arXiv:1312.1414 §3): either a
fixed unitary gate on the full register, or a fractional query `e^{i x A}` of
the Hermitian generator `A` with fractional exponent `x`. -/
inductive FracStep (wires : ℕ) where
  | gate (U : Matrix (Reg wires) (Reg wires) ℂ)
  | query (A : Matrix (Reg wires) (Reg wires) ℂ) (x : ℝ)

/-- Matrix semantics of one fractional step: the fractional query `e^{i x A}`
of arXiv:1312.1414 §3 (the paper writes `e^{i A x}`; the sign convention is
absorbed in `A`). -/
noncomputable def FracStep.eval {wires : ℕ} : FracStep wires → Matrix (Reg wires) (Reg wires) ℂ
  | .gate U => U
  | .query A x => NormedSpace.exp ((Complex.I * (x : ℂ)) • A)

/-- Matrix semantics of a counted fractional word (product in program order). -/
noncomputable def evalFracWord {wires : ℕ} (ws : List (FracStep wires)) :
    Matrix (Reg wires) (Reg wires) ℂ :=
  (ws.map FracStep.eval).prod

/-- Number of fractional queries in a word. -/
def fracQueryCount {wires : ℕ} : List (FracStep wires) → ℕ
  | [] => 0
  | .gate _ :: t => fracQueryCount t
  | .query _ _ :: t => fracQueryCount t + 1

/-- Number of fixed gates in a word. -/
def fracGateCount {wires : ℕ} : List (FracStep wires) → ℕ
  | [] => 0
  | .gate _ :: t => fracGateCount t + 1
  | .query _ _ :: t => fracGateCount t

/-- Total fractional-query cost, `Σ |x| · ‖A‖max`, the paper's `cost(A)`
normalisation of arXiv:1312.1414 §3 (with `‖A‖max` the max-entry norm). -/
noncomputable def fracCost {wires : ℕ} : List (FracStep wires) → ℝ
  | [] => 0
  | .gate _ :: t => fracCost t
  | .query A x :: t => |x| * matMaxEntry A + fracCost t

/-- Every fixed gate of a fractional word is unitary. -/
def WellFormedFracWord {wires : ℕ} (ws : List (FracStep wires)) : Prop :=
  ∀ U, FracStep.gate U ∈ ws → IsUnitary U

/-! ## Continuous-query programs -/

/-- A continuous-query program (arXiv:1312.1414 §3): a finite list of
Hamiltonian segments, each given by a Hermitian generator and a duration. -/
structure ContinuousProgram (n : ℕ) where
  /-- The time-ordered Hamiltonian segments `(H_j, Δ_j)`. -/
  segments : List (Matrix (Reg n) (Reg n) ℂ × ℝ)
  /-- Each segment generator is Hermitian. -/
  hermitian : ∀ p ∈ segments, p.1.IsHermitian
  /-- Each duration is nonnegative. -/
  duration_nonneg : ∀ p ∈ segments, 0 ≤ p.2

/-- Total time `T` of a continuous-query program. -/
def ContinuousProgram.totalTime {n : ℕ} (P : ContinuousProgram n) : ℝ :=
  (P.segments.map (·.2)).sum

/-- Max-entry norm bound `h̄` of a continuous-query program: the largest
`‖H_j‖max` over its segments (and `0` for the empty program). -/
noncomputable def ContinuousProgram.maxEntry {n : ℕ} (P : ContinuousProgram n) : ℝ :=
  (P.segments.map (fun p : Matrix (Reg n) (Reg n) ℂ × ℝ => matMaxEntry p.1)).foldr max 0

/-- Number of continuous queries (segments) of a program. -/
def ContinuousProgram.queryCount {n : ℕ} (P : ContinuousProgram n) : ℕ :=
  P.segments.length

/-- Matrix semantics of a continuous program: the time-ordered product of the
segment evolutions `e^{-i H_j Δ_j}`. -/
noncomputable def ContinuousProgram.eval {n : ℕ} (P : ContinuousProgram n) :
    Matrix (Reg n) (Reg n) ℂ :=
  (P.segments.map (fun p => HamiltonianEvolution p.1 p.2)).prod

/-! ## Zero-ancilla tensoring of states -/

/-- The all-zero computational basis record. -/
def zeroReg (k : ℕ) : Reg k := fun _ => false

/-- Tensor `|0^a⟩ ⊗ φ` for a state `φ` on `b` wires, written as the finite sum
over the computational basis of the data register. -/
noncomputable def zeroAncillaTensor {a b : ℕ} (φ : QState (Reg b)) : QState (Reg (a + b)) :=
  ∑ y : Reg b, φ y • Ket (simCat (zeroReg a) y)

end Qatlib.Papers.SparseHamSim13.MainResults
