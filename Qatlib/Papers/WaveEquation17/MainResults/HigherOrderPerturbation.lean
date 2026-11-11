/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WaveEquation17.MainResults.PerturbationCore

set_option backward.isDefEq.respectTransparency false

/-!
# WaveEquation17.MainResults.HigherOrderPerturbation

Fixed arXiv:1711.05394v4, Theorem 4, equations (113)--(151).

The appendix relaxes the commutation hypothesis of Theorem 2: the perturbation is
`λ ∑ⱼ (∂^k/∂xⱼ^k)²`, whose Hamiltonian `H1` need not commute with `H0`.  The source
introduces the auxiliary block `θ` in (115)--(121), then proves that the relevant
block operators `H_j^{(k)}` are self-adjoint and commute with `H0` (135)--(136), that
`Hθ S0(0) = 0` by (125), and hence obtains (142):

`‖H1 S0(t)‖ ≤ √(∑ⱼ ‖H_j^{(k)} S0(0)‖²)`.

Once this bound is available, the rest of the proof is identical to Theorem 2:
(143)--(149) is the same Cauchy--Schwarz and integration argument, and (151) is the
`φ`-component estimate.

The module therefore proves the analytic inequality (149)/(151) from the source's
operator-norm bound (142), and records (142) as the named hypothesis `hC`.  The
internal derivation of (142) from the `θ`-block commutation is not repeated here.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate

namespace Qatlib.Papers.WaveEquation17.MainResults

/-- Theorem 4, equations (113)--(149): for a higher-order perturbation whose operator
norm along the unperturbed flow is bounded by `C`, the state difference obeys the same
`√(2tε ‖S(0)‖ C)` estimate as Theorem 2.  This is (149) before substituting (142). -/
theorem theorem4_perturbation_norm_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H0 H1 : E →L[ℂ] E)
    (hH0 : IsSelfAdjointCLM H0) (hH1 : IsSelfAdjointCLM H1)
    {Sε S0 : ℝ → E} {ε C t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε
      (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • H1 (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • (H0 (S0 τ))) τ)
    (hinit : Sε 0 = S0 0)
    (hC : ∀ τ, 0 ≤ τ → ‖H1 (S0 τ)‖ ≤ C)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖Sε t - S0 t‖ ≤ Real.sqrt (2 * t * ε * ‖Sε 0‖ * C) :=
  perturbation_norm_bound hH0 hH1 hSε hS0 hinit hC hε ht

/-- Theorem 4, source form (113): the operator-norm factor (142) is
`√(∑ⱼ ‖H_j^{(k)} S0(0)‖²)`, and the resulting bound is
`√(2tε ‖S(0)‖ √(∑ⱼ ‖H_j^{(k)} S0(0)‖²))`, which equals the paper's
`√(2tε) [‖S(0)‖² ∑ⱼ ‖H_j^{(k)} S0(0)‖²]^{1/4}`.

The hypothesis `hC` is exactly the source's inequality (142).  The block operators
`Hj` are the `H_j^{(k)}` of (135); in the paper they act on `S0(0)` as the derivatives
`∂^k φ(0)` and `∂^k ψ_l(0)`, so the sum is the one displayed in (113). -/
theorem theorem4_higher_order_perturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H0 H1 : E →L[ℂ] E) (d : ℕ) (Hj : Fin d → E →L[ℂ] E)
    (hH0 : IsSelfAdjointCLM H0) (hH1 : IsSelfAdjointCLM H1)
    {Sε S0 : ℝ → E} {ε t : ℝ}
    (hSε : ∀ τ, HasDerivAt Sε
      (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • H1 (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • (H0 (S0 τ))) τ)
    (hinit : Sε 0 = S0 0)
    (hC : ∀ τ, 0 ≤ τ →
      ‖H1 (S0 τ)‖ ≤ Real.sqrt (∑ j : Fin d, ‖Hj j (S0 0)‖ ^ 2))
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖Sε t - S0 t‖ ≤
      Real.sqrt (2 * t * ε * ‖Sε 0‖) *
        Real.sqrt (Real.sqrt (∑ j : Fin d, ‖Hj j (S0 0)‖ ^ 2)) := by
  have hmain := theorem4_perturbation_norm_bound H0 H1 hH0 hH1 hSε hS0 hinit hC hε ht
  have hsum : 0 ≤ ∑ j : Fin d, ‖Hj j (S0 0)‖ ^ 2 := by positivity
  have hstep : Real.sqrt (2 * t * ε * ‖Sε 0‖ *
        Real.sqrt (∑ j : Fin d, ‖Hj j (S0 0)‖ ^ 2)) =
      Real.sqrt (2 * t * ε * ‖Sε 0‖) *
        Real.sqrt (Real.sqrt (∑ j : Fin d, ‖Hj j (S0 0)‖ ^ 2)) := by
    rw [Real.sqrt_mul (by positivity)]
  rwa [hstep] at hmain

end Qatlib.Papers.WaveEquation17.MainResults
