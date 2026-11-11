/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12 (time reversal of the linear ODE)

Source: arXiv:2404.07303, §5.3.1, Lemma 12 and (5.96)–(5.97), page 45.

The source states: *for the linear ODE `ẋ = Ax + b`, if at time `t_f` the solution is
`x_f` obtained from an initial condition `x₀`, then we can go back to `x₀` from the
initial condition `x_f` by time evolving the equation `ẋ = -Ax - b`.*

The reversible content is the substitution `z(t) = x(t_f - t)`: differentiating gives
`ż(t) = -ẋ(t_f - t) = -A x(t_f - t) - b = -A z(t) - b`, with `z(0) = x_f`,
`z(t_f) = x₀`.  We formalise it for matrix-valued `x` (the source's vector case is the
`κ = unit` instance); proving the matrix case is strictly stronger and keeps the paper's
matrix Riccati application (Problem 3) in scope.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Lemma 12 (§5.3.1, p.45).**  If `x` solves `ẋ = A x + b` for all times, then the
time-reversed trajectory `z(t) = x(t_f - t)` solves `ż = -A z - b`. -/
theorem lemma12_timeReversal
    (A : Matrix ι ι ℂ) (b : Matrix ι κ ℂ) (x : ℝ → Matrix ι κ ℂ) (tf : ℝ)
    (hx : ∀ t, HasDerivAt x (A * x t + b) t) :
    ∀ t, HasDerivAt (fun s => x (tf - s)) (-(A * x (tf - t)) - b) t := by
  intro t
  have hg : HasDerivAt (fun s : ℝ => tf - s) (-1) t := by
    convert! (hasDerivAt_id t).const_sub tf using 1 <;> simp
  convert! (hx (tf - t)).scomp t hg using 1 <;>
    simp [Function.comp_def, neg_one_smul, neg_add, sub_eq_add_neg]

/-- **Lemma 12, endpoints.**  The reversed trajectory starts at the final value `x_f`
and ends at the initial value `x₀`. -/
theorem lemma12_timeReversal_endpoints
    (x : ℝ → Matrix ι κ ℂ) (tf : ℝ) (x0 xf : Matrix ι κ ℂ)
    (h0 : x 0 = x0) (hf : x tf = xf) :
    (fun s => x (tf - s)) 0 = xf ∧ (fun s => x (tf - s)) tf = x0 := by
  refine ⟨?_, ?_⟩
  · simpa using hf
  · simpa using h0

/-- **Lemma 12, affine form (5.97).**  Combining the two halves: the reversed ODE
`ẋ = -A x - b` run for the same duration returns the original initial datum. -/
theorem lemma12_reversal_solves
    (A : Matrix ι ι ℂ) (b : Matrix ι κ ℂ) (x : ℝ → Matrix ι κ ℂ) (tf : ℝ)
    (x0 xf : Matrix ι κ ℂ)
    (hx : ∀ t, HasDerivAt x (A * x t + b) t)
    (h0 : x 0 = x0) (hf : x tf = xf) :
    (∀ t, HasDerivAt (fun s => x (tf - s)) (-(A * x (tf - t)) - b) t) ∧
      (fun s => x (tf - s)) 0 = xf ∧ (fun s => x (tf - s)) tf = x0 :=
  ⟨lemma12_timeReversal A b x tf hx, lemma12_timeReversal_endpoints x tf x0 xf h0 hf⟩

end Qatlib.Papers.QuadHamilton24.MainResults
