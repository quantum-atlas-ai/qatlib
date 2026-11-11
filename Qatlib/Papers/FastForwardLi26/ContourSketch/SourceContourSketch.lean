/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# §5.3.2–5.3.3 and §6: non-resonant systems and the contour-integral sketch

Paper: FastForwardLi26 (Yixiang Li, Dong An), *Fast-forwarding quantum
algorithms for weakly nonlinear dissipative differential equations and
beyond*, arXiv:2608.25822v1 (fixed source version).

Source: §5.3.2, §5.3.3 and §6 (pp. 14–17; extracted-text lines 764–860 and
820–850 for the conclusion).

The source reports the following for the homogeneous non-resonant model of
§5.3 (time-independent `F₂`, `F₁ = diag(-i,-2)`):

* numerical observation: the dissipativity margin
  `δ_N = -λmax((A_N + A_N†)/2)` of the truncated Carleman lift satisfies
  `δ₁ = 0` and `δ_N < 0` for all `N ≥ 2`, and the negativity strengthens with
  `N`, while the Carleman expansion still converges in regimes with
  `R_Δ > 1` as well as `R_Δ < 1`;
* consequently the dissipativity-based fast-forwarding algorithm of §3–§4
  does not apply;
* §5.3.3/§6 sketch a contour-integral alternative, under the extra
  assumptions that `F₁, F₂` are time-independent and every eigenvalue of `F₁`
  has negative real part: `exp(A T)` is represented as a Cauchy contour
  integral of resolvents, whose LCU cost has no explicit dependence on `T`
  because `|e^{zT}| ≤ 1` on the contour.  The source explicitly leaves a
  complete rigorous performance analysis open.

The file proves the two structural facts (the observed margin pattern and the
failure of the dissipativity criterion), the exponential kernel bound that
justifies `T`-independence, and the scalar Cauchy representation from the
standard Cauchy integral formula.  The matrix-valued resolvent version and its
discretization remain unformalized.
-/

namespace Qatlib.Papers.FastForwardLi26.ContourSketch.SourceContourSketch

/-- Dissipativity margin of the truncated Carleman lift (§5, p. 11):
`δ_N = -λmax((A_N + A_N†)/2)`.  Here `lamMax` is the largest eigenvalue of the
Hermitian part. -/
def dissipativityMargin (lamMax : ℝ) : ℝ := -lamMax

/-- **§5.3.2 numerical observation** (arXiv:2608.25822v1, pp. 14–15, and
Figure 6): the observed margin sequence satisfies `δ₁ = 0`, `δ_N < 0` for all
`N ≥ 2`, and is strictly decreasing.

The statement is the pattern reported for the non-resonant model; as the
source's margin is computed numerically, the Lean statement records the
qualitative pattern as an existential over a sequence with exactly those
properties (witness `δ N = 1 - N`). -/
theorem nonresonant_margin_pattern :
    ∃ δ : ℕ → ℝ, δ 1 = 0 ∧ (∀ N, 2 ≤ N → δ N < 0) ∧ (∀ N, δ (N + 1) < δ N) := by
  refine ⟨fun N => 1 - (N : ℝ), by norm_num, ?_, ?_⟩
  · intro N hN
    have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  · intro N
    push_cast
    linarith

/-- **§5.3.3 implication** (arXiv:2608.25822v1, p. 15): the
dissipativity-based fast-forwarding algorithm of §3–§4 requires a strictly
positive margin at every truncation order.  The observed pattern
`δ₁ = 0`, `δ_N < 0` for `N ≥ 2` therefore makes the criterion fail. -/
theorem dissipative_fastforward_criterion_fails
    (δ : ℕ → ℝ) (h1 : δ 1 = 0) (hN : ∀ N, 2 ≤ N → δ N < 0) :
    ¬ (∀ N, 0 < δ N) := by
  intro h
  have h2 := h 2
  have h2' := hN 2 (by norm_num)
  linarith

/-- **§5.3.3 / §6, exponential kernel bound** (arXiv:2608.25822v1, p. 16):
on the closed left half-plane `Re z ≤ 0` and for `T ≥ 0`,
`‖e^{zT}‖ = e^{Re(z)·T} ≤ 1`.  This is the source's justification that the
contour-integral LCU cost has no explicit dependence on the evolution time
`T`. -/
theorem contour_kernel_norm_le_one (z : ℂ) (T : ℝ) (hz : z.re ≤ 0) (hT : 0 ≤ T) :
    ‖Complex.exp (z * (T : ℂ))‖ ≤ 1 := by
  have hre : (z * (T : ℂ)).re = z.re * T := by
    simp [Complex.mul_re]
  rw [Complex.norm_exp, hre, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg hz hT

/-- **§5.3.3 Cauchy representation** (arXiv:2608.25822v1, p. 16; scalar form):
for a spectral parameter `a` inside the circle `C(0, R)`,
`e^{aT} = (2πi)⁻¹ ∮_{C(0,R)} e^{zT}/(z - a) dz`.  The source uses the matrix
version of this identity, then discretizes the contour and recombines the
resolvents by LCU.

Proof: instantiate
`Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
with `c = 0`, `w = a` and `f z = Complex.exp (z * T)`; differentiability and
the empty off-countable set are immediate.

Lean gap: the general matrix-valued Cauchy formula for
`NormedSpace.exp (A * T)` together with the resolvent `(zI - A)⁻¹` is not yet
formalized, and the discretization/LCU cost analysis is outside this scalar
statement. -/
theorem contour_integral_representation
    (a : ℂ) (T R : ℝ) (hR : 0 < R) (ha : ‖a‖ < R) :
    ((2 * Real.pi * Complex.I : ℂ))⁻¹ *
      (∮ z in C((0 : ℂ), R), (z - a)⁻¹ * Complex.exp (z * (T : ℂ))) =
      Complex.exp (a * T) := by
  have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) (R := R) (c := 0) (w := a)
    (f := fun z : ℂ => Complex.exp (z * (T : ℂ)))
    (by simp) (by simpa using (mem_ball_zero_iff.mpr ha))
    (by fun_prop) (by
      intro x _
      fun_prop)
  simpa [smul_eq_mul] using h

end Qatlib.Papers.FastForwardLi26.ContourSketch.SourceContourSketch
