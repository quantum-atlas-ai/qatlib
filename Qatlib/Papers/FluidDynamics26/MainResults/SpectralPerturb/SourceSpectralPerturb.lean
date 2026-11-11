/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — existence of unstable Kelvin–Helmholtz modes

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026), Theorem 16, Eqs. (126)–(131), p. 22.

c014 = Theorem 16: for a perturbation wavenumber `1 ≤ k < m` there are Fourier
coefficients `{c_j}` and a growth rate `γ` such that

1. `γ > 0` for `k < k_cutoff = sqrt((sqrt 177 - 9)/6) · m` (Eq. (126));
2. `γ_l < γ < γ_u` with the explicit rates of Eqs. (128)–(129);
3. the perturbation `ψ` and its pressure `pt` are smooth;
4. the coefficients can be normalized so that `‖vt‖_{L²} = ℵ` and `‖pt‖_{L²} = q ℵ`.

The Fourier recurrence solved by the coefficients is Eq. (124), p. 22, and the
definitions of `kCutoff`, `gammaU`, `gammaL`, `fourierRecurrence` are in the source
model.  Theorem 16 itself is not formalized (its proof is the spectral analysis of the
infinite Jacobi recurrence of Eq. (124)); its statement is preserved in this branch's
history.  This file retains the proved positivity of the cutoff (`kCutoff_pos`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory
open Qatlib.Foundations.PureStateMath

open scoped BigOperators

/-! ## Positivity of the cutoff wavenumber -/

/-- Eq. (126), p. 22: the cutoff `k_cutoff = sqrt((sqrt 177 - 9)/6) · m` is positive for
`m > 0`.  (`sqrt 177 > 9` since `177 > 81`.) -/
theorem kCutoff_pos {m : ℝ} (hm : 0 < m) : 0 < kCutoff m := by
  unfold kCutoff
  have h177 : (9 : ℝ) < Real.sqrt 177 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 177), Real.sqrt_nonneg 177]
  have hpos : 0 < (Real.sqrt 177 - 9) / 6 := by linarith
  exact mul_pos (Real.sqrt_pos.2 hpos) hm

end Qatlib.Papers.FluidDynamics26.MainResults
