/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# HeatEquation20 — Theorem 1 (p. 6, eq. (12)) and Corollary 2 (p. 7, eq. (22))

Fixed source: arXiv:2004.06516v2, pp. 6–7.

The paper's Theorem 1 bounds the `ℓ∞` error of the FTCS discretisation (11) of
the heat equation by

`ζ α d T / L^d · (α d Δt / 2 + Δx²/12)`     (12)

under the stability condition `Δt ≤ Δx²/(2dα)`.  Its proof combines

* the discretisation error bounds (8)–(9) into the one-step bound (15)–(17),
* stochasticity (14) of the FTCS operator, giving `ℓ∞`-contraction, and
* the induction (18)–(21) over the `m = T/Δt` time steps.

The formal statement below assumes the per-step bound (17) (the Taylor
remainder input, which the paper derives on p. 6 from (8)–(9) and the smoothness
bound (10)) and proves the contraction and the accumulation here.  Corollary 2
is then verified completely: the displayed `Δt`, `Δx` do satisfy
`Δt = Δx²/(2dα)`, make (12) equal to `ε/L^d`, and give the displayed `m`, `n`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators

/-- **Theorem 1** (arXiv:2004.06516v2, p. 6, eq. (12)).  Let `w` be the FTCS
iterate (13) started at `u 0`, and let `u` be the exact solution sampled on the
grid.  Assume the per-step truncation bound (17), the stability condition
`Δt ≤ Δx²/(2dα)`, and `m Δt = T`.  Then the `ℓ∞` error after `m` steps is at
most `ζ α d T / L^d · (α d Δt / 2 + Δx²/12)`.

The per-step bound (17) is the Taylor-remainder input derived in the paper from
(8)–(9); it is stated as a hypothesis.  Stochasticity (14) and the induction
(18)–(21) are proved below (`ftcsStep_linfty_le`, `error_accumulation`). -/
theorem theorem1_error_bound
    {d n m : ℕ} [NeZero n] (hd : 0 < d)
    (α Δt Δx L ζ T : ℝ) (hα : 0 < α) (hL : 0 < L) (hζ : 0 ≤ ζ)
    (hΔx : 0 < Δx) (hΔt : 0 ≤ Δt)
    (hstab : 2 * (d : ℝ) * (α * Δt / Δx ^ 2) ≤ 1)
    (u w : ℕ → Grid d n → ℝ) (h0 : w 0 = u 0)
    (hstep : ∀ k, w (k + 1) = ftcsStep (α * Δt / Δx ^ 2) (w k))
    (htaylor : ∀ k, ‖u (k + 1) - ftcsStep (α * Δt / Δx ^ 2) (u k)‖
      ≤ ζ * α * (d : ℝ) * Δt / L ^ d * (α * (d : ℝ) * Δt / 2 + Δx ^ 2 / 12))
    (hT : (m : ℝ) * Δt = T) :
    ‖w m - u m‖ ≤ ζ * α * (d : ℝ) * T / L ^ d
      * (α * (d : ℝ) * Δt / 2 + Δx ^ 2 / 12) := by
  have hη0 : 0 ≤ α * Δt / Δx ^ 2 := by positivity
  have hcontr : ∀ v : Grid d n → ℝ, ‖ftcsStepLM (α * Δt / Δx ^ 2) v‖ ≤ ‖v‖ := by
    intro v
    rw [ftcsStepLM_apply]
    exact ftcsStep_linfty_le hd _ hη0 hstab v
  have hacc := error_accumulation (ftcsStepLM (α * Δt / Δx ^ 2)) hcontr u w h0
    (fun k => by rw [hstep k, ftcsStepLM_apply])
    (ζ * α * (d : ℝ) * Δt / L ^ d * (α * (d : ℝ) * Δt / 2 + Δx ^ 2 / 12))
    (fun k => by rw [ftcsStepLM_apply]; exact htaylor k) m
  refine hacc.trans_eq ?_
  rw [← hT]
  ring

/-! ## Corollary 2 (p. 7, eq. (22)) -/

/-- The time step `Δt = 3ε / (2 d² α² ζ T)` of Corollary 2, eq. (22). -/
def cor2DeltaT (d : ℕ) (α ζ T ε : ℝ) : ℝ :=
  3 * ε / (2 * (d : ℝ) ^ 2 * α ^ 2 * ζ * T)

/-- The space step `Δx = √(3ε / (d α ζ T))` of Corollary 2, eq. (22). -/
def cor2DeltaX (d : ℕ) (α ζ T ε : ℝ) : ℝ :=
  Real.sqrt (3 * ε / ((d : ℝ) * α * ζ * T))

/-- The number of time steps `m = 2 T² d² α² ζ / (3ε)` of Corollary 2. -/
def cor2M (d : ℕ) (α ζ T ε : ℝ) : ℝ :=
  2 * T ^ 2 * (d : ℝ) ^ 2 * α ^ 2 * ζ / (3 * ε)

/-- **Corollary 2** (arXiv:2004.06516v2, p. 7, eq. (22)).  The displayed choice
`Δt = 3ε/(2d²α²ζT)`, `Δx = √(3ε/(dαζT))` satisfies `Δt = Δx²/(2dα)` (so
Theorem 1 applies), makes the error bound (12) equal to `ε/L^d`, and gives
`m Δt = T`, `n Δx = L` for the displayed `m`, `n`. -/
theorem corollary2_parameter_choice
    (d : ℕ) (hd : 0 < d) (L α ζ T ε : ℝ)
    (hL : 0 < L) (hα : 0 < α) (hζ : 0 < ζ) (hT : 0 < T) (hε : 0 < ε) :
    cor2DeltaT d α ζ T ε = cor2DeltaX d α ζ T ε ^ 2 / (2 * (d : ℝ) * α) ∧
      ζ * α * (d : ℝ) * T / L ^ d
          * (α * (d : ℝ) * cor2DeltaT d α ζ T ε / 2 + cor2DeltaX d α ζ T ε ^ 2 / 12)
        = ε / L ^ d ∧
      cor2M d α ζ T ε * cor2DeltaT d α ζ T ε = T ∧
      L * Real.sqrt ((d : ℝ) * α * ζ * T / (3 * ε)) * cor2DeltaX d α ζ T ε = L := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hden1 : 0 < (d : ℝ) ^ 2 * α ^ 2 * ζ * T := by positivity
  have hden2 : 0 < (d : ℝ) * α * ζ * T := by positivity
  have hsq : cor2DeltaX d α ζ T ε ^ 2 = 3 * ε / ((d : ℝ) * α * ζ * T) := by
    unfold cor2DeltaX
    exact Real.sq_sqrt (by positivity)
  have hsqrt_mul : Real.sqrt ((d : ℝ) * α * ζ * T / (3 * ε)) * cor2DeltaX d α ζ T ε = 1 := by
    unfold cor2DeltaX
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (d : ℝ) * α * ζ * T / (3 * ε) * (3 * ε / ((d : ℝ) * α * ζ * T)) = 1 by
      field_simp <;> ring]
    exact Real.sqrt_one
  have hLd : L ^ d ≠ 0 := pow_ne_zero d hL.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cor2DeltaT
    rw [hsq]
    field_simp <;> ring
  · unfold cor2DeltaT
    rw [hsq]
    field_simp <;> ring
  · unfold cor2M cor2DeltaT
    field_simp <;> ring
  · rw [mul_assoc, hsqrt_mul, mul_one]

end Qatlib.Papers.HeatEquation20.MainResults
