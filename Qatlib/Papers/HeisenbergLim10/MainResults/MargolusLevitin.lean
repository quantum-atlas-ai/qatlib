/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Heisenberg limit versus the Margolus–Levitin bound, Eq. (10)

Source: Zwierz, Pérez-Delgado, Kok, *General optimality of the Heisenberg limit
for quantum metrology*, fixed arXiv:1004.3944 (2010), p. 4.

Eq. (6) bounds the speed of the Wootters statistical distance by
`ds/dφ ≤ |⟨H⟩|`.  Separating variables,

```
∫_0^φ dφ' ≥ (1/|⟨H⟩|) ∫_0^{π/2} ds  ⇒  φ ≥ (π/2) / |⟨H⟩|,
```

which identifies the Heisenberg limit with the Margolus–Levitin bound on the
speed of dynamical evolution whenever `H` is the Hamiltonian.

This module proves the separation-of-variables step rigorously: if `s` runs
from `0` at phase `0` to `π/2` at phase `φ` and its derivative is bounded by the
resource count `H` all along `[0, φ]`, then `φ ≥ π/(2H)`.  The proof is the
fundamental theorem of calculus together with monotonicity of the interval
integral.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HeisenbergLim10.MainResults

open MeasureTheory

/-- Fixed arXiv:1004.3944, Eq. (10), p. 4.  Separation of variables for the
Wootters distance speed bound Eq. (6).

If the statistical distance `s` accumulates from `s 0 = 0` at phase `0` to
`s φ = π/2` at the final phase `φ`, with derivative `s' = ds/dφ ≤ H` on
`[0, φ]` (where `H = |⟨H⟩| > 0` is the resource count), then
`φ ≥ (π/2) / H`, i.e. the Margolus–Levitin time bound.

The integral estimate is the paper's
`∫_0^φ dφ' ≥ (1/|⟨H⟩|) ∫_0^{π/2} ds`: the accumulated distance `π/2` is at most
`H` per unit of phase. -/
theorem margolus_levitin_phase_bound
    (s s' : ℝ → ℝ) (φ H : ℝ) (hH : 0 < H) (hφ : 0 ≤ φ)
    (hs0 : s 0 = 0) (hsφ : s φ = Real.pi / 2)
    (hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) φ, HasDerivAt s (s' x) x)
    (hint : IntervalIntegrable s' volume 0 φ)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) φ, s' x ≤ H) :
    Real.pi / (2 * H) ≤ φ := by
  -- Fundamental theorem of calculus: the accumulated distance is the integral
  -- of the speed.
  have hFTC : ∫ x in (0 : ℝ)..φ, s' x = s φ - s 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- Monotonicity of the interval integral against the constant speed bound.
  have hintH : IntervalIntegrable (fun _ : ℝ => H) volume 0 φ :=
    intervalIntegrable_const
  have hmono : ∫ x in (0 : ℝ)..φ, s' x ≤ ∫ x in (0 : ℝ)..φ, (H : ℝ) :=
    intervalIntegral.integral_mono_on hφ hint hintH hbound
  have hconst : ∫ x in (0 : ℝ)..φ, (H : ℝ) = H * φ := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  -- Total distance `π/2` is at most `H φ`.
  have hacc : Real.pi / 2 ≤ H * φ := by
    calc
      Real.pi / 2 = s φ - s 0 := by rw [hsφ, hs0]; ring
      _ = ∫ x in (0 : ℝ)..φ, s' x := hFTC.symm
      _ ≤ ∫ x in (0 : ℝ)..φ, (H : ℝ) := hmono
      _ = H * φ := hconst
  -- Divide by the positive resource count.
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Qatlib.Papers.HeisenbergLim10.MainResults
