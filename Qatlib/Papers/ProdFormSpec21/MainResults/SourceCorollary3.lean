/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProdFormSpec21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 3 (optimal choice of `T`) — paper-layer Lean

Source: *Spectral Analysis of Product Formulas for Quantum Simulation*,
arXiv:2102.12655v2, **Corollary 3**, p.7, Eq (42)–(44); proof in Appendix F
(p.14, Eq (48) and the displayed bound `ε'_tot ≤ O((1/(Tlam³))(D + 3C₁T/(2M))²)`).

In the setting of Proposition 1, with circuit depth `M` fixed, Appendix F shows

  `ε'_tot ≤ (1/(Tlam³)) · (D + 3C₁ T/(2M))²`,

where `D = ‖Hi − Hf‖`, `C₁ = ‖[Hi,Hf]‖`, and `lam` is the lower bound of the
spectral gap.  Corollary 3 states that under `(8C₀ + 12D)D ≤ 3C₁` this upper
bound is minimal at `T_c = 2MD/(3C₁)`, with value `ε_opt = O(DC₁/(Mlam³))`, and
that achieving a fixed error `ε` fixes the ratio `T_c/M` and requires circuit
depth `O(NDC₁/(lam³ε))` (`N` the width).

We model the *shape* `(D + 3C₁T/(2M))²/T` of the Appendix-F bound exactly
(scaling in `M`, `T`, `D`, `C₁`); the `1/lam³` factor is carried separately since
it does not affect the minimisation.  The optimisation statements below are
proved outright by algebra.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

open Real

/-- The Appendix-F shape `Φ(T) = (D + 3C₁T/(2M))² / T` of the `ε'_tot` upper
bound at fixed circuit depth `M` (paper p.14), without the overall `1/lam³`
factor (kept separate in `errorBound`). -/
noncomputable def depthBound (D C1 M T : ℝ) : ℝ := (D + 3 * C1 * T / (2 * M)) ^ 2 / T

/-- The full Appendix-F upper bound `ε'_tot ≤ Φ(T)/lam³`. -/
noncomputable def errorBound (D C1 M lam T : ℝ) : ℝ := depthBound D C1 M T / lam ^ 3

/-- Appendix F, p.14, Eq (48): the critical time `T_c = 2MD/(3C₁)`. -/
noncomputable def criticalT (D C1 M : ℝ) : ℝ := 2 * M * D / (3 * C1)

/-- **Corollary 3, Eq (42) — the minimiser.**  For `D,C₁,M > 0`, the point
`T_c = 2MD/(3C₁)` minimises the Appendix-F bound shape `Φ(T)` over all `T > 0`.

Proof (Appendix F): writing `Φ(T) = D²/T + 3C₁D/M + 9C₁²T/(4M²)`, the difference
is the exact square `Φ(T) − Φ(T_c) = D²(T−T_c)²/(T_c²·T) ≥ 0`. -/
theorem corollary3_optimal_T (D C1 M : ℝ) (hD : 0 < D) (hC1 : 0 < C1) (hM : 0 < M)
    (T : ℝ) (hT : 0 < T) :
    depthBound D C1 M (criticalT D C1 M) ≤ depthBound D C1 M T := by
  have hTc : 0 < criticalT D C1 M := by
    unfold criticalT; positivity
  have hsq : 0 ≤ D ^ 2 * (T - criticalT D C1 M) ^ 2 / (criticalT D C1 M ^ 2 * T) := by
    have : 0 < criticalT D C1 M ^ 2 * T := by positivity
    positivity
  have hdiff :
      depthBound D C1 M T - depthBound D C1 M (criticalT D C1 M)
        = D ^ 2 * (T - criticalT D C1 M) ^ 2 / (criticalT D C1 M ^ 2 * T) := by
    unfold depthBound criticalT
    field_simp [hD.ne', hC1.ne', hM.ne', hT.ne', hTc.ne']
    ring
  linarith

/-- **Corollary 3, Eq (43) — the optimal error.**  At `T_c` the Appendix-F bound
takes the value `6C₁D/M`; with the overall gap factor the error is
`6C₁D/(Mlam³) = O(DC₁/(Mlam³))`. -/
theorem corollary3_opt_value (D C1 M : ℝ) (hD : 0 < D) (hC1 : 0 < C1) (hM : 0 < M) :
    depthBound D C1 M (criticalT D C1 M) = 6 * C1 * D / M := by
  have hTc : 0 < criticalT D C1 M := by unfold criticalT; positivity
  unfold depthBound criticalT
  field_simp [hD.ne', hC1.ne', hM.ne', hTc.ne']
  ring

/-- **Corollary 3, Eq (43) — the error at the optimum**, including the spectral-gap
factor `1/lam³`: `ε_opt = 6C₁D/(Mlam³) = O(DC₁/(Mlam³))`. -/
theorem corollary3_opt_error (D C1 M lam : ℝ) (hD : 0 < D) (hC1 : 0 < C1)
    (hM : 0 < M) (hlam : 0 < lam) :
    errorBound D C1 M lam (criticalT D C1 M) = 6 * C1 * D / (M * lam ^ 3) := by
  unfold errorBound
  rw [corollary3_opt_value D C1 M hD hC1 hM]
  field_simp [hM.ne', hlam.ne']

/-- **Corollary 3, Eq (42) — the fixed ratio.**  The optimum keeps the ratio
`T_c/M = 2D/(3C₁)` independent of the depth. -/
theorem corollary3_Tc_ratio (D C1 M : ℝ) (hC1 : 0 < C1) (hM : 0 < M) :
    criticalT D C1 M / M = 2 * D / (3 * C1) := by
  unfold criticalT
  field_simp [hC1.ne', hM.ne']

/-- **Corollary 3, Eq (44) — depth to achieve a target error.**  Keeping the ratio
`T_c/M = 2D/(3C₁)` fixed, a circuit depth `M = 6C₁D/(lam³ε)` attains the error `ε`;
since the circuit depth is `N·M` for width `N`, this is `O(NDC₁/(lam³ε))`.

The statement below is the exact algebraic identity at that `M`. -/
theorem corollary3_depth_to_error (D C1 lam ε : ℝ) (hD : 0 < D) (hC1 : 0 < C1)
    (hlam : 0 < lam) (hε : 0 < ε) :
    errorBound D C1 (6 * C1 * D / (lam ^ 3 * ε)) lam
        (criticalT D C1 (6 * C1 * D / (lam ^ 3 * ε))) = ε := by
  have hMpos : 0 < 6 * C1 * D / (lam ^ 3 * ε) := by positivity
  rw [corollary3_opt_error D C1 (6 * C1 * D / (lam ^ 3 * ε)) lam hD hC1 hMpos hlam]
  field_simp [hMpos.ne', hlam.ne']

/-- **Corollary 3 — width times depth.**  For a circuit of width `N`, the depth
`N·M` that reaches error `ε` is `N · 6C₁D/(lam³ε)`. -/
theorem corollary3_circuit_depth (N D C1 lam ε : ℝ) (hD : 0 < D) (hC1 : 0 < C1)
    (hlam : 0 < lam) (hε : 0 < ε) :
    N * (6 * C1 * D / (lam ^ 3 * ε)) = 6 * N * D * C1 / (lam ^ 3 * ε) := by
  field_simp [hlam.ne']

end Qatlib.Papers.ProdFormSpec21.MainResults
