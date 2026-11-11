/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase.PhaseAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# The concrete reflection / phase-oracle walk (arXiv:2208.07544v1, §3.1, §3.3--3.4)

Fixed arXiv version: `2208.07544v1`. Source locations: Definitions 3.1--3.2,
Equations (12)--(17), (23)--(29), Fact 3.10, Fact 3.13, and Proposition 3.15
(pp. 10--15).

The code for a real random variable `y` on the finite outcome set `ι` is modelled
by a probability mass `p` and the values `y i`.  In the computational (outcome)
basis the states of Notation 3.9 are

`|z⟩ = ∑_i z_i √(p_i) |i⟩`,

the phase oracle `ROT_y` multiplies the `i`-th amplitude by the unit phase
`(1 - i y_i)/(1 + i y_i)` (equal to the paper's `e^{i α_i}` with
`α_i = -2 arctan y_i`, by the tangent half-angle formula), and the reflection
`REFL_p = 2|1⟩⟨1| - 1` sends `z_i` to `2 E_p[z] - z_i`.

Proved here: Fact 3.13 (inner products and norms of `|1⟩` and `|1+iy⟩`) and
Proposition 3.15, `(1-U)/2 |1+iy⟩ = i µ |1⟩`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Notation 3.9, Equation (23): `|z⟩ = ∑_i z_i √(p_i) |i⟩` in the outcome basis. -/
noncomputable def ket (p : ι → ℝ) (z : ι → ℂ) : QState ι :=
  fun i => z i * (Real.sqrt (p i) : ℂ)

/-- Equation (28): `µ = E_p[y]`. -/
noncomputable def mean (p y : ι → ℝ) : ℝ := ∑ i, p i * y i

/-- Equation (28): `s² = E_p[y²]`. -/
noncomputable def secondMoment (p y : ι → ℝ) : ℝ := ∑ i, p i * (y i) ^ 2

/-- The constant random variable `1` (Equation (24)). -/
def oneVar : ι → ℂ := fun _ => 1

/-- Equation (29): the complex random variable `1 + i y`. -/
noncomputable def onePlusIy (y : ι → ℝ) : ι → ℂ := fun i => 1 + Complex.I * (y i : ℂ)

/-- The complex random variable `1 - i y`, the phase-oracle image of `1 + i y`. -/
noncomputable def oneMinusIy (y : ι → ℝ) : ι → ℂ := fun i => 1 - Complex.I * (y i : ℂ)

/-- Definition 3.2, Equation (16): the phase oracle `ROT_y` multiplies the `i`-th
amplitude by `e^{i α_i} = (1 - i y_i)/(1 + i y_i)`. -/
noncomputable def roty (y : ι → ℝ) (z : ι → ℂ) : ι → ℂ :=
  fun i => ((1 - Complex.I * (y i : ℂ)) / (1 + Complex.I * (y i : ℂ))) * z i

/-- Definition 3.1, Equation (26): `REFL_p = 2|1⟩⟨1| - 1` acts on the coefficient
vector as `z_i ↦ 2 E_p[z] - z_i`. -/
noncomputable def refl (p : ι → ℝ) (z : ι → ℂ) : ι → ℂ :=
  fun i => 2 * (∑ j, (p j : ℂ) * z j) - z i

/-- Equation (14): `U = REFL_p · ROT_y`. -/
noncomputable def walkU (p y : ι → ℝ) (z : ι → ℂ) : ι → ℂ :=
  refl p (roty y z)

/-- Halving a difference of coefficient vectors, the action of `(1-U)/2`. -/
noncomputable def halfSub (a b : ι → ℂ) : ι → ℂ := fun i => (a i - b i) / 2

/-- The phase `(1 - i y_i)/(1 + i y_i)` is well defined: the denominator is nonzero. -/
theorem one_add_I_mul_ne_zero (t : ℝ) : (1 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.one_re,
    Complex.ofReal_re] at hre

/-- `ROT_y` sends `1 + i y` to `1 - i y` (Equation (17)). -/
theorem roty_onePlusIy (y : ι → ℝ) (i : ι) :
    roty y (onePlusIy y) i = oneMinusIy y i := by
  unfold roty onePlusIy oneMinusIy
  rw [div_mul_eq_mul_div]
  field_simp [one_add_I_mul_ne_zero (y i)]

/-- The reflection barycenter of `1 - i y`: `E_p[1 - i y] = 1 - i µ`. -/
theorem sum_oneMinusIy (p y : ι → ℝ) (hsum : ∑ i, p i = 1) :
    ∑ i, (p i : ℂ) * oneMinusIy y i = 1 - Complex.I * (mean p y : ℂ) := by
  have hterm : ∀ i, (p i : ℂ) * oneMinusIy y i =
      (p i : ℂ) - Complex.I * ((p i * y i : ℝ) : ℂ) := by
    intro i
    unfold oneMinusIy
    push_cast
    ring
  calc
    ∑ i, (p i : ℂ) * oneMinusIy y i
        = ∑ i, ((p i : ℂ) - Complex.I * ((p i * y i : ℝ) : ℂ)) := by
          exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, (p i : ℂ)) - Complex.I * ((∑ i, p i * y i : ℝ) : ℂ) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
            ← Complex.ofReal_sum, ← Complex.ofReal_sum]
    _ = 1 - Complex.I * (mean p y : ℂ) := by
          rw [mean, ← Complex.ofReal_sum, hsum]
          push_cast
          ring

/-- Equation (26)--(27): `REFL_p` sends `1 - i y` to `1 + i (y - 2µ)`. -/
theorem refl_oneMinusIy (p y : ι → ℝ) (hsum : ∑ i, p i = 1) (i : ι) :
    refl p (oneMinusIy y) i =
      onePlusIy y i - 2 * Complex.I * (mean p y : ℂ) := by
  unfold refl onePlusIy
  rw [sum_oneMinusIy p y hsum]
  unfold oneMinusIy
  ring

/-- The action of `U = REFL_p · ROT_y` on `|1 + i y⟩` (Equations (30)--(32)). -/
theorem walkU_onePlusIy (p y : ι → ℝ) (hsum : ∑ i, p i = 1) (i : ι) :
    walkU p y (onePlusIy y) i =
      onePlusIy y i - 2 * Complex.I * (mean p y : ℂ) := by
  unfold walkU refl
  simp only [roty_onePlusIy]
  exact refl_oneMinusIy p y hsum i

/-- Proposition 3.15 (p. 15): `(1-U)/2 |1+iy⟩ = i µ |1⟩`.
This is the concrete rank-one identity at the heart of §3.4. -/
theorem prop3_15 (p y : ι → ℝ) (hsum : ∑ i, p i = 1) :
    halfSub (ket p (onePlusIy y)) (ket p (walkU p y (onePlusIy y))) =
      fun i => Complex.I * (mean p y : ℂ) * ket p oneVar i := by
  funext i
  unfold halfSub ket oneVar
  rw [walkU_onePlusIy p y hsum i]
  ring

/-- A norm identity for the outcome-basis state vectors: `∑ ‖z_i √p_i‖²
= ∑ ‖z_i‖² p_i`. -/
theorem normSq_ket (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (z : ι → ℂ) :
    ∑ i, ‖ket p z i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 * p i := by
  apply Finset.sum_congr rfl
  intro i _
  unfold ket
  rw [norm_mul, mul_pow]
  have hsqrt : ‖(Real.sqrt (p i) : ℂ)‖ ^ 2 = p i := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt (hp i)
  rw [hsqrt]

/-- The squared modulus of `1 + i t` is `1 + t²`. -/
theorem normSq_onePlusIy_real (t : ℝ) : ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- Fact 3.13 (p. 14): `⟨1+iy|1+iy⟩ = 1 + s²`. -/
theorem fact3_13_normSq (p y : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ∑ i, ‖ket p (onePlusIy y) i‖ ^ 2 = 1 + secondMoment p y := by
  rw [normSq_ket p hp]
  have hterm : ∀ i, ‖onePlusIy y i‖ ^ 2 * p i = p i + p i * (y i) ^ 2 := by
    intro i
    unfold onePlusIy
    rw [normSq_onePlusIy_real]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hsum]
  rfl

/-- The general inner product of two outcome-basis states (Fact 3.10): with
`⟨z| = ∑ conj(z_i)√p_i ⟨i|`, one has
`⟨w|z⟩ = ∑ p_i conj(w_i) z_i`. -/
theorem inner_ket (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (w z : ι → ℂ) :
    Inner (ket p w) (ket p z) = ∑ i, (p i : ℂ) * (starRingEnd ℂ) (w i) * z i := by
  rw [inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold ket
  have hsq : (Real.sqrt (p i) : ℂ) * (Real.sqrt (p i) : ℂ) = (p i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]
  simp only [map_mul, Complex.conj_ofReal]
  calc
    (starRingEnd ℂ) (w i) * (Real.sqrt (p i) : ℂ) *
        (z i * (Real.sqrt (p i) : ℂ))
        = (starRingEnd ℂ) (w i) * z i *
            ((Real.sqrt (p i) : ℂ) * (Real.sqrt (p i) : ℂ)) := by ring
    _ = (starRingEnd ℂ) (w i) * z i * (p i : ℂ) := by rw [hsq]
    _ = (p i : ℂ) * (starRingEnd ℂ) (w i) * z i := by ring

/-- Fact 3.13 (p. 14): `⟨1|1+iy⟩ = 1 + i µ`. -/
theorem fact3_13_inner (p y : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    Inner (ket p oneVar) (ket p (onePlusIy y)) = 1 + Complex.I * (mean p y : ℂ) := by
  rw [inner_ket p hp]
  have hterm : ∀ i, (p i : ℂ) * (starRingEnd ℂ) (oneVar i) * onePlusIy y i =
      (p i : ℂ) * onePlusIy y i := by
    intro i
    unfold oneVar
    simp
  simp_rw [hterm]
  have := sum_oneMinusIy p y hsum
  -- `sum_oneMinusIy` has a minus sign; derive the plus sign directly.
  have hterm' : ∀ i, (p i : ℂ) * onePlusIy y i =
      (p i : ℂ) + Complex.I * ((p i * y i : ℝ) : ℂ) := by
    intro i
    unfold onePlusIy
    push_cast
    ring
  calc
    ∑ i, (p i : ℂ) * onePlusIy y i
        = ∑ i, ((p i : ℂ) + Complex.I * ((p i * y i : ℝ) : ℂ)) := by
          exact Finset.sum_congr rfl (fun i _ => hterm' i)
    _ = (∑ i, (p i : ℂ)) + Complex.I * (∑ i, ((p i * y i : ℝ) : ℂ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 1 + Complex.I * (mean p y : ℂ) := by
          rw [mean, ← Complex.ofReal_sum, hsum]
          push_cast
          ring

end Qatlib.Papers.QMonteCarlo22.MainResults.Eigenphase
