/-
Copyright (c) 2026 qatlas-lean-org. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Mathlib.Basic.Complex.Basic

@[expose] public section


/-!
# FermiHubbard20 — linear damping law support (§III, Eq. (4))

Source: arXiv:2010.07965 (quantum simulation of the Fermi-Hubbard model),
Section III, Eq. (4) and Fig. 3.

This module preserves the closed algebraic declarations of the original
development of this material: the exactness of the error-mitigation rescaling
(`rescaling_recovers_numeric`), the algebraic form of the observed
`U`-independence of the damping slope (`damping_slope_u_independent`), and
the damping-ratio record `dampingRatioAt` of Eq. (4).

The empirical linear damping law itself (`linear_damping_law`) is a
model-contract deferral of this development: its existential over
unconstrained measurement sequences is vacuously satisfiable, and a faithful
statement would have to fix the Fig. 3 dataset as hypotheses.
-/

set_option autoImplicit false

namespace Qatlib.Papers.FermiHubbard20.MainResults.DampingLaw

/-- **Correctness of the error-mitigation rescaling (arXiv:2010.07965 Eq. (4),
§III).**

Let `nbar` be the half-filling density, `xexp` the device-measured and `xnum`
the numerically exact occupation deviation from `nbar`, and let `r` be the
damping ratio `r = (xexp - nbar) / (xnum - nbar)`.  If the deviations are both
non-zero, then rescaling the measured deviation by `1/r` and adding it back to
`nbar` returns exactly the numerical deviation `xnum`.  This is precisely the
relation used to "damp" the experimental data in Eq. (4). -/
theorem rescaling_recovers_numeric {nbar xexp xnum r : ℂ}
    (hxe : xexp - nbar ≠ 0) (_hn : xnum - nbar ≠ 0)
    (hr : r = (xexp - nbar) / (xnum - nbar)) :
    nbar + (xexp - nbar) / r = xnum := by
  subst hr
  have hx : (xexp - nbar) / ((xexp - nbar) / (xnum - nbar)) = xnum - nbar := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ (xnum - nbar) hxe]
  rw [hx]
  ring

/-- **Damping slope is independent of the interaction strength**
(arXiv:2010.07965 §III, Fig. 3).

If the damping ratios at step `η` for two interaction strengths `u = 0` and
`u ≠ 0` are `b₀ - a η` and `b₁ - a η` with the same slope `a`, their
difference is the constant `b₀ - b₁`, independent of `η`.  This is the
algebraic form of the observation that the slope `a` is common to all `U` and
only the intercept shifts weakly. -/
theorem damping_slope_u_independent (a b0 b1 : ℝ) (η : ℕ) :
    (b0 - a * (η : ℝ)) - (b1 - a * (η : ℝ)) = b0 - b1 := by
  ring

/-- The damping ratio at step `η` of Eq. (4), built from the numerical
(`xnum`), experimental (`xexp`) and half-filling (`nbar`) occupation-deviation
sequences. -/
noncomputable def dampingRatioAt (xexp xnum nbar : ℕ → ℂ) (η : ℕ) : ℂ :=
  (xexp η - nbar η) / (xnum η - nbar η)

end Qatlib.Papers.FermiHubbard20.MainResults.DampingLaw
