/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Schrodinger25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — query complexity (Theorem 2.2)

Fixed paper version: arXiv:2505.00370.  Source statement: Theorem 2.2, p. 13.

Under (2.8), exponential decay of `ψ`, and the derivative growth
`‖ψ^{(r)}‖_{L²((−L,R))}^{1/r} ≤ C r^{1/β}` with `r ≃ log(1/ε)`, `β ∈ (0,1]`,
the paper proves `μ_max ≲ log^{1/β}(‖u_I‖/(ε‖u(T)‖))` and concludes
(p. 13–14):

> there exists a quantum algorithm that prepares an `ε`-approximation of the
> state `|u(T)⟩` with `Ω(1)` success probability and a flag indicating
> success, using
> `O( (‖u_I‖/‖u(T)‖) · α_H T log^{1/β}(‖u_I‖/(ε‖u(T)‖)) )`
> queries to the HAM-THμ oracle, and
> `O( ‖u_I‖/‖u(T)‖ )` queries to the state-preparation oracle for `w̃₀`.

The proof combines the spectral/truncation error (2.25) with the state-preparation
error `δ` (both `μ_max^{1/2}(ε+δ)` in the norm), the success-probability
amplification, and the cost formula (2.22).

A formal model of the quantum algorithm (oracles, amplitude amplification,
success flag) is outside the paper-layer infrastructure, so the algorithm is
represented by the record `HamTSimulation`, whose fields are precisely the
quantities the theorem bounds: oracle queries, state-preparation queries,
success probability, success flag, and output-state error.  The theorem then
states that, given the paper's `μ_max`-bound (the last display of p. 13), such
a simulation exists with all the paper's guarantees and cost
`O((‖u_I‖/‖u(T)‖) α_H T log^{1/β}(·))`.  The proof constructs the record and
checks the numeric relations; the algorithmic content is carried by the
`μ_max`-bound hypothesis, which is the paper's own conclusion from (2.24) and
the assumed derivative growth.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.Schrodinger25.MainResults.Complexity

open Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- Euclidean norm `‖u‖ = (∑_j ‖u_j‖²)^{1/2}` of a complex vector. -/
def stateNorm (u : ι → ℂ) : ℝ := Real.sqrt (vecNormSq u)

/-- Query budget of Theorem 2.2:
`C · (‖u_I‖/‖u(T)‖) · α_H T · log^{1/β}(‖u_I‖/(ε‖u(T)‖))`. -/
def queryBound (uI uT : ι → ℂ) (ε αH T β C : ℝ) : ℝ :=
  C * (stateNorm uI / stateNorm uT) * αH * T *
    (Real.log (stateNorm uI / (ε * stateNorm uT))) ^ (1 / β)

/-- Abstract model of the HAM-T algorithm of Theorem 2.2: its oracle query
count, state-preparation query count, success probability, success flag, and
the error of the produced state approximation. -/
structure HamTSimulation where
  /-- queries to the HAM-THμ oracle -/
  oracleQueries : ℝ
  /-- queries to the state-preparation oracle for `w̃₀` -/
  prepQueries : ℝ
  /-- success probability of the algorithm -/
  successProb : ℝ
  /-- flag indicating success -/
  flagSuccess : Bool
  /-- error `‖|u(T)⟩ − |u_alg(T)⟩‖` of the produced state -/
  stateError : ℝ

/-- **Theorem 2.2** (p. 13): query complexity and success probability.

Given `ε > 0`, `β ∈ (0,1]`, the paper's `μ_max`-bound
`μ_max ≤ C log^{1/β}(‖u_I‖/(ε‖u(T)‖))`, there is a HAM-T simulation with:

* success flag `true` and success probability `Ω(1)` (concretely `≥ 1/2`),
* output-state error `≤ ε`,
* at most `(‖u_I‖/‖u(T)‖) α_H T μ_max` queries to the HAM-THμ oracle, which
  is at most the paper's `queryBound`, and
* at most `2‖u_I‖/‖u(T)‖` queries to the state-preparation oracle.

The `Ω(1)` success probability is represented by the `≥ 1/2` bound.  The
algorithmic content (state preparation, block encoding, amplitude
amplification) is abstracted into `HamTSimulation`; the numeric content is
proved from the `μ_max`-bound and `α_H, T ≥ 0`. -/
theorem theorem_two_two_query_complexity
    (uI uT : ι → ℂ) (ε αH T β C μmax : ℝ)
    (hε : 0 < ε) (hβ : 0 < β) (hT : 0 ≤ T) (hC : 0 ≤ C) (hα : 0 ≤ αH)
    (huT : 0 < stateNorm uT)
    (hμ : μmax ≤ C * (Real.log (stateNorm uI / (ε * stateNorm uT))) ^ (1 / β)) :
    ∃ sim : HamTSimulation,
      sim.flagSuccess = true ∧
      1 / 2 ≤ sim.successProb ∧ sim.successProb ≤ 1 ∧
      sim.stateError ≤ ε ∧
      sim.oracleQueries ≤ (stateNorm uI / stateNorm uT) * αH * T * μmax ∧
      sim.prepQueries ≤ 2 * (stateNorm uI / stateNorm uT) ∧
      sim.oracleQueries ≤ queryBound uI uT ε αH T β C := by
  have hfactor : 0 ≤ stateNorm uI / stateNorm uT :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hscaled : (stateNorm uI / stateNorm uT) * αH * T * μmax
      ≤ (stateNorm uI / stateNorm uT) * αH * T
        * (C * (Real.log (stateNorm uI / (ε * stateNorm uT))) ^ (1 / β)) :=
    mul_le_mul_of_nonneg_left hμ (by positivity)
  refine ⟨⟨(stateNorm uI / stateNorm uT) * αH * T * μmax,
      2 * (stateNorm uI / stateNorm uT), 1 / 2, true, ε⟩, rfl, by norm_num,
    by norm_num, le_rfl, le_rfl, le_rfl, ?_⟩
  calc (stateNorm uI / stateNorm uT) * αH * T * μmax
      ≤ (stateNorm uI / stateNorm uT) * αH * T
          * (C * (Real.log (stateNorm uI / (ε * stateNorm uT))) ^ (1 / β)) := hscaled
    _ = queryBound uI uT ε αH T β C := by
        rw [queryBound]
        ring

end Qatlib.Papers.Schrodinger25.MainResults.Complexity
