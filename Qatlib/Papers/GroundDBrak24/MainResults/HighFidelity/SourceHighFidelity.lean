/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults.HighFidelity — energy below mid-gap implies fidelity ≥ 50% (c005)

Fixed source: arXiv:2408.03987, Sec. III, Eq. (32).

The paper defines a *high-fidelity* ground-state preparation by the energy
expectation lying below the middle of the spectral gap,

  `⟨H_0⟩_ψ ≤ (E_0 + E_1) / 2`,                                              (32)

and observes that "all such states will have the actual fidelity `F ≥ 50%`".
This is a spectral-decomposition fact: writing the state's spectral weights,
the ground-state weight is `F = |⟨E_0|ψ⟩|²` and the residual weight `1 - F`
sits on levels of energy at least the first excited energy `E_1`. The energy
expectation is therefore `F·E_0 + (1 - F)·Eres` with `E_1 ≤ Eres`, and the
mid-gap inequality forces `F ≥ 1/2` because the gap is strict (`E_0 < E_1`).

The scalar parametrisation below is exactly this spectral decomposition; the
only spectral input is the residual bound `E_1 ≤ Eres`. Complete proof.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GroundDBrak24.MainResults.HighFidelity

/-- c005, Eq. (32): if a state has ground-state weight `F` (squared overlap with
the ground state), its residual spectral weight `1 - F` carries energy at least
the first excited energy `E_1` (i.e. `E_1 ≤ Eres`), the spectral gap is strict
`E_0 < E_1`, and the energy expectation `F·E_0 + (1 - F)·Eres` is at or below
the middle of the gap `(E_0 + E_1)/2`, then the actual fidelity `F ≥ 50%`.

The expression `F·E_0 + (1 - F)·Eres` is the spectral decomposition of
`⟨H_0⟩_ψ`, with `F = |⟨E_0|ψ⟩|²`; the bound `E_1 ≤ Eres` is the only spectral
input. This is the paper's "all such states will have the actual fidelity
`F ≥ 50%`". -/
theorem fidelity_ge_half_of_energy_le_midgap
    (E0 E1 Eres F : ℝ)
    (hgap : E0 < E1)
    (hres : E1 ≤ Eres)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (henergy : F * E0 + (1 - F) * Eres ≤ (E0 + E1) / 2) :
    (1 : ℝ) / 2 ≤ F := by
  -- The residual weight `1 - F` is nonnegative, so raising the residual energy
  -- from `E_1` to `Eres` only increases the expectation.
  have hnonneg : 0 ≤ 1 - F := by linarith
  have hresterm : 0 ≤ (1 - F) * (Eres - E1) :=
    mul_nonneg hnonneg (by linarith)
  -- `E_1 - F·(E_1 - E_0) = F·E_0 + (1 - F)·E_1 ≤ F·E_0 + (1 - F)·Eres`.
  have h1 : E1 - F * (E1 - E0) ≤ F * E0 + (1 - F) * Eres := by
    nlinarith [hresterm]
  -- The mid-gap bound is `(E_0 + E_1)/2 = E_1 - (E_1 - E_0)/2`.
  have h2 : E1 - (E1 - E0) / 2 = (E0 + E1) / 2 := by ring
  have h3 : E1 - F * (E1 - E0) ≤ E1 - (E1 - E0) / 2 := by
    rw [h2]
    linarith [h1, henergy]
  have hg : 0 < E1 - E0 := by linarith
  -- Divide the rearranged inequality by the positive gap `E_1 - E_0`.
  nlinarith [h3, hg]

end Qatlib.Papers.GroundDBrak24.MainResults.HighFidelity
