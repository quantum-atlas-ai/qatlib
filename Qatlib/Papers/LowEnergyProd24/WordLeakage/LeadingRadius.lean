/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowEnergyProd24.WordLeakage.ActualLeakage
public import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.NestedLeakage
public import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalWord
public import Qatlib.Papers.LowEnergyProd24.ProductError.LieCoefficients

@[expose] public section

/-!
# The leading leakage coefficient of the geometric majorant

Fixed paper version: arXiv:2402.10362v1 (K. Hejazi, M. Shokrian Zini, J. M. Arrazola,
11 pages), [arXiv:2402.10362v1](https://arxiv.org/abs/2402.10362v1).

Source: p. 3, Eq. (6), the leakage radius `α = (λ / (p + 1)) Σ_{m, {m_i}} |f| ℓ_p` with `λ =
1 / (2 J k d)`, and p. 8-9, Eq. (32), where the nested-commutator majorant
`Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.sourceEll` replaces the paper's `ℓ_p`.

`Qatlib.Papers.LowEnergyProd24.WordLeakage.stepExponent` is the exponent of the geometric
leakage majorant actually proved in the paper namespace, with growth coefficient
`Qatlib.Papers.LowEnergyProd24.WordLeakage.growthCoefficient`.  This module relates its leading
`s ^ (p + 1)` coefficient to the leading coefficient of the source majorant: the dimensionless
ratio of the two is the explicit elementary factor
`2 ^ (p + 1) (timeBudget stages) ^ (p + 1) / (p! e ^ (p + 1) (1 - 2 J k d (timeBudget
stages) s))`, so under the small-step condition the geometric exponent dominates a positive
multiple of `s ^ (p + 1) · sourceEll L k d J p / (p + 1)`.

Boundary: this is a constant-factor comparison of the two source coefficients, not the equality
of Eq. (6) with the geometric majorant.  The paper's leading coefficient is the sum
`Σ_{m, {m_i}} |f| ℓ_p` of stage-coefficient magnitudes, whereas `sourceEll L k d J p` bounds each
nested commutator by the same `L (p!) (J k d e) ^ p e J`; the ratio proved below therefore
carries the factorial and `2 ^ p e ^ p` bookkeeping of those two independent majorants and is not
claimed to be a sharp comparison.  The hypothesis `0 < timeBudget stages` is necessary: if every
stage weight vanishes, the word is the identity, `stepExponent` vanishes, while `sourceEll` stays
positive for positive `L`, so no positive multiple can be dominated.  `L`, `J`, `k`, `d` and `p`
are those of the source statements; the small-step hypothesis is the one used by the leakage
bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.LowEnergyProd24.WordLeakage

open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Papers.LowEnergyProd24.WordLeakage

variable {N R M k d : ℕ} {J : ℝ}

/-- The leading `s ^ (p + 1)` coefficient of the geometric leakage majorant, divided by the
leading coefficient `sourceEll L k d J p / (p + 1)` of the source majorant, is the explicit factor
`2 ^ (p + 1) T ^ (p + 1) / (p! e ^ (p + 1) (1 - 2 J k d T s))` with `T = timeBudget
stages`.  Equivalently, the geometric exponent equals that factor times the source leading term. -/
theorem stepExponent_eq_leading_radius_factor (L : ℕ) {stages : List (ℝ × Fin M)}
    (hJ : 0 < J) (hT : 0 < timeBudget stages) (p : ℕ) (s : ℝ)
    (hsmall : 2*J*k*d*timeBudget stages*s < 1) :
    stepExponent L k d J stages p s =
      2^(p+1)*(timeBudget stages)^(p+1)/
          ((p.factorial : ℝ)*Real.exp 1^(p+1)*(1-2*J*k*d*timeBudget stages*s))*
        (s^(p+1)*sourceEll L k d J p/(p+1)) := by
  have hden : (0 : ℝ) < 1 - 2*J*k*d*timeBudget stages*s := by linarith
  have hTne : timeBudget stages ≠ 0 := ne_of_gt hT
  have hJne : J ≠ 0 := ne_of_gt hJ
  have hfac : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hexp : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have h1 : (2*J*k*d*timeBudget stages)^p =
      2^p*(J*k*d)^p*(timeBudget stages)^p := by
    rw [show (2:ℝ)*J*k*d*timeBudget stages = ((2:ℝ)*J*k*d)*timeBudget stages by ring, mul_pow,
      show (2:ℝ)*J*k*d = (2:ℝ)*(J*k*d) by ring, mul_pow]
  have h2 : (J*k*d*Real.exp 1)^p = (J*k*d)^p*(Real.exp 1)^p := by
    rw [show J*k*d*Real.exp 1 = (J*k*d)*Real.exp 1 by ring, mul_pow]
  simp only [stepExponent, growthCoefficient, sourceEll, h1, h2]
  field_simp
  ring

/-- The paper's leading leakage radius is dominated by the geometric exponent: for positive `J`
and positive total step time, some explicit positive constant `K` satisfies
`K s ^ (p + 1) sourceEll L k d J p / (p + 1) ≤ stepExponent L k d J stages p s` under the
small-step condition. -/
theorem leading_radius_upper (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (L : ℕ) (stages : List (ℝ × Fin M)) (p : ℕ) (_hp0 : 0 < p)
    (hT : 0 < timeBudget stages) (_horder : lowerOrderCancellation h stages p)
    (s : ℝ) (_hs : 0 ≤ s) (hsmall : 2*J*k*d*timeBudget stages*s < 1) :
    ∃ K : ℝ, 0 < K ∧
      K*s^(p+1)*sourceEll L k d J p/(p+1) ≤ stepExponent L k d J stages p s := by
  have hden : (0 : ℝ) < 1 - 2*J*k*d*timeBudget stages*s := by linarith
  refine ⟨2^(p+1)*(timeBudget stages)^(p+1)/
    ((p.factorial : ℝ)*Real.exp 1^(p+1)*(1-2*J*k*d*timeBudget stages*s)), ?_, ?_⟩
  · apply div_pos (by positivity) (by positivity)
  · rw [stepExponent_eq_leading_radius_factor L hJ hT p s hsmall]
    exact le_of_eq (by ring)

end Qatlib.Papers.LowEnergyProd24.WordLeakage
