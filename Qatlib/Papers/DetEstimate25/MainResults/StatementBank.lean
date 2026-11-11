/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DetEstimate25.MainResults.ErrorBudget

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"A quantum algorithm for estimating the determinant"
(arXiv:2504.11049, 2025).

Two cores are proved in this block (see `ErrorBudget`):

- c002 (Eq. (2)): `logdet_relerr_le`, the systematic-plus-statistical
  relative-error budget of the log-determinant estimator, at B-.
- c003 (Eq. (4)): `spectralsum_relerr_le`, the identical budget for a
  general spectral sum with Lipschitz systematic error, at B-.

The remaining claim c001 (Eq. (1), the total step count
`#_LgD ≃ O(κ (log κ)² s² ε⁻³ log n log²(s²/ε))`) is recorded here as
faithful `Prop` shapes:

- `lgdStepBound`: the Eq. (1) cost bound itself.
- `qsStepBound`: the per-sample quantum-step cost Eq. (3) of one
  phase-estimation sample (sparse Hamiltonian simulation, paper
  refs. [12–14, 25–30]) — an external input for this paper.
- `c001_assembly`: the paper's accounting rule combining the
  per-sample cost, the Monte-Carlo count `N_mc = (2Δ/(|μ|ε))²`, the
  QPE precision `2^m ≥ 4κ/(|μ|ε)` and the variance proxy
  `Δ ≤ log κ` (proved as `SpectrumStats.delta_le`) into Eq. (1).

The obstacle for c001 is substantive: the oracle-model runtime
accounting of phase estimation on an `s`-sparse matrix — the
Hamiltonian-simulation cost `N_qs` of refs. [12–14, 25–30] — is an
external theorem of the simulation literature, absent from Mathlib
and both repositories, and is therefore recorded as an explicit
hypothesis rather than derived.

No axiom beyond the three standard ones, no `admit`. -/
set_option autoImplicit false

namespace Qatlib.Papers.DetEstimate25.MainResults

/-! ## Shared shapes -/

/-- Eq. (1) total-cost bound: the number of computational steps of
the full log-determinant estimator is at most
`C κ (log κ)² s² ε⁻³ log n log²(s²/ε)` for a constant `C`. -/
def lgdStepBound (T kappa s n : ℝ) (eps : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ T ≤ C * kappa * (Real.log kappa) ^ 2 * s ^ 2 / eps ^ 3
      * Real.log n * (Real.log (s ^ 2 / eps)) ^ 2

/-- Eq. (3) per-sample cost (external input, sparse Hamiltonian
simulation [12–14, 25–30]): one phase-estimation sample of the
rescaled spectrum costs at most
`C κ (log κ)² s² ε⁻¹ log²(s²/ε)` quantum steps. -/
def qsStepBound (Nqs kappa s : ℝ) (eps : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ Nqs ≤ C * kappa * (Real.log kappa) ^ 2 * s ^ 2 / eps
      * (Real.log (s ^ 2 / eps)) ^ 2

/-! ## Claim statement -/

/-- **c001 (Eq. (1)), complexity-assembly shape**: with the external
per-sample cost `qsStepBound Nqs`, the Monte-Carlo count
`Nmc = (2Δ/(|μ|ε))²` and the QPE resolution `2^m ≥ 4κ/(|μ|ε)` that
make the Eq. (2) budget at most `ε`, and the variance proxy
`Δ ≤ log κ` of `SpectrumStats.delta_le`, the total cost
`Nqs * Nmc * m` obeys the Eq. (1) bound `lgdStepBound`. -/
def c001_assembly (Nqs Nmc m delta mu : ℝ) (kappa s n : ℝ) (eps : ℝ) : Prop :=
  0 < eps ∧ 1 ≤ kappa
    ∧ qsStepBound Nqs kappa s eps
    ∧ Nmc = (2 * delta / (abs mu * eps)) ^ 2
    ∧ 4 * kappa / (abs mu * eps) ≤ 2 ^ m
    ∧ delta ≤ Real.log kappa
    ∧ lgdStepBound (Nqs * Nmc * m) kappa s n eps

end Qatlib.Papers.DetEstimate25.MainResults
