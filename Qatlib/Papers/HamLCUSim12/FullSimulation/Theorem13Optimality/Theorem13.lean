/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 13 (Appendix A) — optimality of the linear-combination failure

Fixed source: arXiv:1202.5822v1, Theorem 13, Appendix A, pp.15-17.
Any protocol implementing `V = Σ_q C_q U_q` with a circuit of the form of Figure 3
must fail with probability at least `4κ/(κ+1)²`.

The paper's derivation (Eqs. (A2)-(A8)) bounds the success probability of any such
protocol by
`1 − P_− = Σ_j |K C_j U_j ψ|² ≤ ((Σ⁺ − Σ⁻)/(Σ⁺ + Σ⁻))² = ((κ−1)/(κ+1))²`
with `Σ±` the positive/negative coefficient masses and `κ = Σ⁺/Σ⁻` (Eq. (A8)).
The algebraic content of Eqs. (A7)-(A8) is proved here in full:
`theorem13_success_mass_identity` (the second equality) and
`theorem13_failure_lower_bound` (the implication `P_− ≥ 4κ/(κ+1)²`).
The circuit-level bound (A6) itself — that every Figure-3 protocol's success amplitude
is at most `(Σ⁺−Σ⁻)/(Σ⁺+Σ⁻)` — rests on the Cauchy-Schwarz step (A6) and the
orthogonality argument (A9), which require a formal circuit model; it enters the
present statement as the explicit hypothesis `hp` on the success probability.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamLCUSim12.FullSimulation.Theorem13Optimality

/-- Fixed arXiv:1202.5822v1, Eq. (A7)-(A8): the squared success bound
`((Σ⁺−Σ⁻)/(Σ⁺+Σ⁻))²` of Appendix A equals `((κ−1)/(κ+1))²` with `κ = Σ⁺/Σ⁻`. -/
theorem theorem13_success_mass_identity (Sp Sm : ℝ) (hSm : 0 < Sm) :
    ((Sp - Sm) / (Sp + Sm)) ^ 2
      = ((Sp / Sm - 1) / (Sp / Sm + 1)) ^ 2 := by
  have hSmne : Sm ≠ 0 := ne_of_gt hSm
  have hsub : Sp - Sm = (Sp / Sm - 1) * Sm := by
    rw [sub_mul, div_mul_cancel₀ Sp hSmne, one_mul]
  have hadd : Sp + Sm = (Sp / Sm + 1) * Sm := by
    rw [add_mul, div_mul_cancel₀ Sp hSmne, one_mul]
  rw [hsub, hadd, mul_div_mul_right _ _ hSmne]

/-- Fixed arXiv:1202.5822v1, Eq. (A8): for `κ > 0`, the failure probability
`P_− = 1 − pSuccess` is at least `4κ/(κ+1)²` whenever the success probability is at
most `((κ−1)/(κ+1))²`. -/
theorem theorem13_optimal_failure (κ pSuccess : ℝ) (hκ : 0 < κ)
    (hp : pSuccess ≤ ((κ - 1) / (κ + 1)) ^ 2) :
    4 * κ / (κ + 1) ^ 2 ≤ 1 - pSuccess := by
  have hne : κ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hkey : 1 - ((κ - 1) / (κ + 1)) ^ 2 = 4 * κ / (κ + 1) ^ 2 := by
    field_simp [hne]
    ring
  linarith

/-- Fixed arXiv:1202.5822v1, Theorem 13 / Eq. (A8): a protocol of Figure 3 whose
success probability is at most `((Σ⁺−Σ⁻)/(Σ⁺+Σ⁻))²` (the Appendix-A Cauchy-Schwarz
bound (A6)) fails with probability at least `4κ/(κ+1)²`, `κ = Σ⁺/Σ⁻`. -/
theorem theorem13_failure_lower_bound (Sp Sm pSuccess : ℝ) (hSm : 0 < Sm) (hSp : 0 < Sp)
    (hp : pSuccess ≤ ((Sp - Sm) / (Sp + Sm)) ^ 2) :
    4 * (Sp / Sm) / (Sp / Sm + 1) ^ 2 ≤ 1 - pSuccess := by
  have h1 : pSuccess ≤ ((Sp / Sm - 1) / (Sp / Sm + 1)) ^ 2 := by
    rw [theorem13_success_mass_identity Sp Sm hSm] at hp
    exact hp
  exact theorem13_optimal_failure (Sp / Sm) pSuccess (div_pos hSp hSm) h1

end Qatlib.Papers.HamLCUSim12.FullSimulation.Theorem13Optimality
