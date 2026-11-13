/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Rabi first-order deficit coefficient (source Theorem 2, Eq. (C16)--(C19))

Source: Ali Hamed Moosavian and Stephen Jordan, *Faster quantum algorithm to simulate
Fermionic Quantum Field Theory*, fixed version arXiv:1711.04006v3 (23 Oct 2019),
Section IV B (Theorem 2, Eq. (29)--(30)) and Appendix C.

Theorem 2 of the source bounds the overlap of the driven two-level state with the excited
state: for `H = -(Δ/2) Z + λ cos(ωt) X` started in `|0⟩` and `λ ≪ ω`, after `t = π/λ`

  `|⟨1|ψ(π/λ)⟩| ≥ 1 - (1/√3)(λ/ω)^2 - O((λ/ω)^4)`.

Appendix C derives this by writing the exact Floquet solution in terms of Bessel functions
`J_0, J_1` (Eq. (C2)--(C6)), expanding the overlap in powers of `λ/ω` (Eq. (C17)), and then
observing that, with `κ = sin(πω/λ)` bounded by `-1 ≤ κ ≤ 1` (Eq. (C16)), the first-order
deficit is

  `1 - |⟨1|ψ(π/λ)⟩| = |cos²(πω/λ)/2 + i sin(πω/λ) cos(πω/λ)| (λ/ω)^2 + O((λ/ω)^4)`  (C18)

whose coefficient has maximum `1/√3` over the admissible range of `κ` (C19); the maximum is
attained at `κ² = 1/3`.

This module formalises the quantitative core of that reduction: the exact algebraic identity
by which the squared modulus of the Eq. (C18) coefficient is `(1-κ²)(1+3κ²)/4`, its uniform
bound `1/3`, its sharpness at `κ² = 1/3`, and the resulting uniform `1/√3` bound on the
`(λ/ω)^2` term, rounded into the shape of Eq. (30) with an explicit higher-order remainder.

Boundary: the Floquet/Bessel solution of Appendix C (Eq. (C1)--(C17)) is not formalised here;
no Bessel functions occur in Mathlib at this pin, so the passage from the driven
Schrödinger equation to the Eq. (C17) expansion remains open. The shared library provides a power-series Bessel function and a Jacobi--Anger expansion
(`Qatlib.Papers.QSingValue19.PhaseExistence.Lc17AuxBessel.lcBesselJ` and
`...lcBesselJacobiAnger`), which covers the shape of Eq. (C14), but the Floquet quasi-energies
and quasi-modes of Eq. (C3)--(C13) are absent there, so the expansion (C15)--(C18) is not
reached. The source hypotheses `0 < ω` and `λ ≪ ω` enter only through that omitted step, so
the statements below carry no frequency restriction; everything below is unconditional.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.FermionQFT17.MainResults.RabiFirstOrder

/-- Source Eq. (C18): the squared modulus of the first-order coefficient
`cos²(πω/λ)/2 + i sin(πω/λ) cos(πω/λ)` of `(λ/ω)²` in the Rabi overlap deficit,
written in terms of the phase parameter `κ = sin(πω/λ)` of Eq. (C16) using
`cos²(πω/λ) = 1 - κ²`. -/
def firstOrderDeficitSq (κ : ℝ) : ℝ := ((1 - κ ^ 2) / 2) ^ 2 + κ ^ 2 * (1 - κ ^ 2)

/-- Source Eq. (C18): the squared coefficient modulus factors as `(1-κ²)(1+3κ²)/4`, which is
the form used to maximise it over the admissible range `-1 ≤ κ ≤ 1` of Eq. (C16). -/
theorem firstOrderDeficitSq_eq (κ : ℝ) :
    firstOrderDeficitSq κ = (1 - κ ^ 2) * (1 + 3 * κ ^ 2) / 4 := by
  unfold firstOrderDeficitSq
  ring

/-- The Eq. (C18) coefficient modulus is nonnegative on the admissible range `κ² ≤ 1` of
Eq. (C16), so that the overlap deficit `1 - |⟨1|ψ(π/λ)⟩|` is an actual modulus. -/
theorem firstOrderDeficitSq_nonneg {κ : ℝ} (hκ : κ ^ 2 ≤ 1) : 0 ≤ firstOrderDeficitSq κ := by
  rw [firstOrderDeficitSq_eq]
  have h₁ : 0 ≤ 1 - κ ^ 2 := by linarith
  have h₂ : 0 ≤ 1 + 3 * κ ^ 2 := by positivity
  positivity

/-- Source Eq. (C18)--(C19): the squared first-order coefficient of the Rabi deficit is at
most `1/3` for every `κ`, with equality exactly when `κ² = 1/3`; equivalently the deficit
from `1/3` is `(3κ²-1)²/3`. -/
theorem firstOrderDeficitSq_le_one_third (κ : ℝ) : firstOrderDeficitSq κ ≤ 1 / 3 := by
  rw [firstOrderDeficitSq_eq]
  nlinarith [sq_nonneg (3 * κ ^ 2 - 1)]

/-- Source Eq. (C19): the bound `1/3` on the squared coefficient is sharp; it is attained at
`κ = 1/√3`, which is an admissible value of `sin(πω/λ)`, so the `1/√3` constant of
Theorem 2 cannot be improved at this order. -/
theorem firstOrderDeficitSq_attained :
    firstOrderDeficitSq (1 / Real.sqrt 3) = 1 / 3 := by
  have hsq : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [firstOrderDeficitSq_eq, hsq]
  norm_num

/-- Reconnaissance identity used by Eq. (C19): the `1/√3` constant is the square root of
`1/3`. -/
theorem sqrt_one_third : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

/-- Source Eq. (C18)--(C19): the first-order coefficient modulus of the Rabi deficit is
bounded by `1/√3` for every phase, and in particular over the admissible range `κ² ≤ 1` of
Eq. (C16). -/
theorem firstOrderDeficit_sqrt_le (κ : ℝ) :
    Real.sqrt (firstOrderDeficitSq κ) ≤ 1 / Real.sqrt 3 := by
  rw [← sqrt_one_third]
  exact Real.sqrt_le_sqrt (firstOrderDeficitSq_le_one_third κ)

/-- Source Eq. (C16)--(C19) with the phase written as `κ = sin(πω/λ)`: the modulus of the
first-order coefficient is bounded by `1/√3` for every driving frequency ratio, using only
`|sin| ≤ 1` from Eq. (C16). -/
theorem firstOrderDeficit_sqrt_sin_le (θ : ℝ) :
    Real.sqrt (firstOrderDeficitSq (Real.sin θ)) ≤ 1 / Real.sqrt 3 :=
  firstOrderDeficit_sqrt_le (Real.sin θ)

/-- Source Eq. (C18)--(C19): the `(λ/ω)²` term of the Rabi deficit obeys the `1/√3` bound of
Eq. (30) for every phase `κ`. -/
theorem rabi_firstOrder_deficit_bound (lam ω κ : ℝ) :
    Real.sqrt (firstOrderDeficitSq κ) * (lam / ω) ^ 2 ≤ (1 / Real.sqrt 3) * (lam / ω) ^ 2 :=
  mul_le_mul_of_nonneg_right (firstOrderDeficit_sqrt_le κ) (sq_nonneg _)

/-- Source Theorem 2, Eq. (30): with `κ = sin(πω/λ)` the `(λ/ω)²` contribution to the
excited-state overlap deficit is at most `(1/√3)(λ/ω)²` for every phase, i.e. uniformly in
the driving frequency. -/
theorem rabi_firstOrder_deficit_bound_sin (lam ω θ : ℝ) :
    Real.sqrt (firstOrderDeficitSq (Real.sin θ)) * (lam / ω) ^ 2 ≤
      (1 / Real.sqrt 3) * (lam / ω) ^ 2 :=
  rabi_firstOrder_deficit_bound lam ω (Real.sin θ)

/-- Source Eq. (C18)--(C19): `1/√3` is the exact value of the maximum of the first-order
deficit coefficient over `κ`, not merely an upper bound. -/
theorem firstOrderDeficit_sqrt_max :
    (∀ κ : ℝ, Real.sqrt (firstOrderDeficitSq κ) ≤ 1 / Real.sqrt 3) ∧
      ∃ κ : ℝ, κ ^ 2 = 1 / 3 ∧ Real.sqrt (firstOrderDeficitSq κ) = 1 / Real.sqrt 3 := by
  refine ⟨firstOrderDeficit_sqrt_le, 1 / Real.sqrt 3, ?_, ?_⟩
  · rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · rw [firstOrderDeficitSq_attained, sqrt_one_third]

/-- Source Theorem 2, Eq. (30), in the form used in Section IV C: suppose the deficit
`1 - o` of the excited-state overlap `o = |⟨1|ψ(π/λ)⟩|` is no larger than the first-order
term `√(firstOrderDeficitSq κ) (λ/ω)²` plus a higher-order remainder `R` standing for the
`O((λ/ω)^4)` term of Eq. (C17)--(C18); then `o` obeys the Eq. (30) lower bound with the
explicit remainder `R`. -/
theorem rabi_excited_overlap_bound {o R lam ω κ : ℝ}
    (hdef : 1 - o ≤ Real.sqrt (firstOrderDeficitSq κ) * (lam / ω) ^ 2 + R) :
    1 - (1 / Real.sqrt 3) * (lam / ω) ^ 2 - R ≤ o := by
  have hcoef := rabi_firstOrder_deficit_bound lam ω κ
  linarith

end Qatlib.Papers.FermionQFT17.MainResults.RabiFirstOrder
