/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonMarkovSim24.MainResults.DQMEModel
import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false

/-!
# c004 — Trace preservation of the DQME-SQ reduced density operator

Paper: arXiv:2401.17255v4, Appendix B, Eq. (B1), (B2), pp. 11.

Claim (c004): the reduced density operator is `ρ_S(t) = ⟨0|ρ̃(t)` (Eq. (B1)),
which under the DQME-SQ obeys Eq. (B2),
`ρ̇_S = -i[H_S, ρ_S] - i Σ_k ζ_k [Q̂, ρ̄^{(1)}_k]`.
Every term on the right-hand side is a commutator, hence traceless, so
`tr ρ_S(t)` is conserved at all times and the DQME-SQ can be propagated by any
classical propagator without renormalizing the RDT at each step.

The formalization separates the two logical ingredients of Appendix B:

* `trace_rhs_eq_zero`: the trace of the Eq. (B2) right-hand side vanishes
  identically, because `tr(AB - BA) = 0` for all operators (`trace_commutator_eq_zero`).
* `trace_preserved`: whenever the scalar function `t ↦ tr ρ_S(t)` has derivative
  equal to `tr` of the Eq. (B2) right-hand side (the standard linearity of the
  trace applied to the DQME-SQ equation), it is constant in time.

Together these give the paper's conclusion: no per-step renormalization of the
RDT is needed for exact propagation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonMarkovSim24.MainResults

variable {ι : Type*} [Fintype ι]

/-- The right-hand side of Eq. (B2) of Appendix B, read with the first-order
auxiliary operator `ρ̄^{(1)}_k = ⟨0_k^+|ρ̃`:
`-i[H_S, ρ_S] - i Σ_k ζ_k [Q̂_k, ρ̄^{(1)}_k]`. -/
def traceRHS {d : ℕ} (H ρS : Op d) (Q : ι → Op d) (r : ι → Op d) (ζ : ι → ℂ) : Op d :=
  (-Complex.I) • (H * ρS - ρS * H)
    - Complex.I • (∑ k, ζ k • (Q k * r k - r k * Q k))

/-- The trace of any commutator vanishes, `tr(AB - BA) = 0`.  This is the
"trace of any commutator is zero" step of Appendix B. -/
theorem trace_commutator_eq_zero {d : ℕ} (A B : Op d) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

/-- **Eq. (B2) is traceless.**  The trace of the right-hand side of Eq. (B2)
vanishes identically: the Hamiltonian commutator and every dissipaton
commutator `[Q̂_k, ρ̄^{(1)}_k]` are traceless.  This is the algebraic content of
Appendix B's "Eq. (B2) preserves the trace of `ρ_S(t)` at any time t". -/
theorem trace_rhs_eq_zero {d : ℕ} (H : Op d) (ρS : Op d) (Q r : ι → Op d)
    (ζ : ι → ℂ) :
    Matrix.trace (traceRHS H ρS Q r ζ) = 0 := by
  unfold traceRHS
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  have hH : Matrix.trace (H * ρS) - Matrix.trace (ρS * H) = 0 := by
    rw [Matrix.trace_mul_comm H ρS, sub_self]
  have hsum :
      (∑ k, ζ k * (Matrix.trace (Q k * r k) - Matrix.trace (r k * Q k))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.trace_mul_comm (Q k) (r k), sub_self, mul_zero]
  rw [hH, hsum]
  ring

/-- **c004: trace preservation.**  If the reduced density operator `ρ_S` obeys
the DQME-SQ trace equation of Eq. (B2) — formalized as: the scalar trace
`t ↦ tr ρ_S(t)` has derivative equal to the trace of the Eq. (B2) right-hand
side — then `tr ρ_S(t)` is constant in time:
`tr ρ_S(t) = tr ρ_S(0)` for every `t`.

This is the paper's conclusion that the DQME-SQ preserves the trace at all
times and therefore needs no renormalization when solved by a classical
propagator.  The hypothesis `hode` is exactly the Eq. (B2) differential
identity after applying the linear trace, not an extra physical assumption. -/
theorem trace_preserved {d : ℕ} (H : Op d) (Q : ι → Op d) (ζ : ι → ℂ)
    (ρS : ℝ → Op d) (r : ℝ → ι → Op d)
    (hode : ∀ t, HasDerivAt (fun s => Matrix.trace (ρS s))
        (Matrix.trace (traceRHS H (ρS t) Q (r t) ζ)) t) :
    ∀ t, Matrix.trace (ρS t) = Matrix.trace (ρS 0) := by
  have hderiv : ∀ t, HasDerivAt (fun s => Matrix.trace (ρS s)) 0 t := by
    intro t
    have h := hode t
    rw [trace_rhs_eq_zero H (ρS t) Q (r t) ζ] at h
    exact h
  have hdiff : Differentiable ℝ (fun s => Matrix.trace (ρS s)) :=
    fun t => (hderiv t).differentiableAt
  intro t
  exact is_const_of_deriv_eq_zero hdiff (fun s => (hderiv s).deriv) t 0

end Qatlib.Papers.NonMarkovSim24.MainResults
