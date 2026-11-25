/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.StressImpulse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The quantum-stress divergence in Madelung variables

[Musser2019Superfoil], equation (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
The quantum-stress term for density `ρ = A²` is expressed in terms of the
amplitude and its Cartesian derivatives. Its divergence is a multiple of the
gradient of the quantum-pressure ratio `ΔA / A`. The computation takes
place at positive density and uses commutation of the third partials.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open scoped Topology

/-- The coordinate line through a point in the direction of the indicated
Cartesian basis vector. The point itself is at parameter zero. -/
def axisLine (x : ℝ × ℝ) (j : Fin 2) (s : ℝ) : ℝ × ℝ :=
  if j = 0 then (x.1 + s, x.2) else (x.1, x.2 + s)

/-- Every coordinate line passes through its base point at parameter zero. -/
@[simp]
theorem axisLine_zero (x : ℝ × ℝ) (j : Fin 2) : axisLine x j 0 = x := by
  unfold axisLine
  split <;> simp

/-- A Cartesian coordinate line differentiates to its coordinate unit vector. -/
theorem hasDerivAt_axisLine (x : ℝ × ℝ) (j : Fin 2) (s : ℝ) :
    HasDerivAt (axisLine x j) (if j = 0 then (1, 0) else (0, 1)) s := by
  fin_cases j
  · change HasDerivAt (axisLine x (0 : Fin 2)) (1, 0) s
    have heq : axisLine x 0 = fun r => (x.1 + r, x.2) := by
      funext r
      simp [axisLine]
    rw [heq]
    simpa using (((hasDerivAt_id s).const_add x.1).prodMk (hasDerivAt_const s x.2))
  · change HasDerivAt (axisLine x (1 : Fin 2)) (0, 1) s
    have heq : axisLine x 1 = fun r => (x.1, x.2 + r) := by
      funext r
      simp [axisLine]
    rw [heq]
    simpa using ((hasDerivAt_const s x.1).prodMk ((hasDerivAt_id s).const_add x.2))

/-- At a point in an open fluid region, short coordinate segments stay in the region. -/
theorem eventually_mem_axisLine {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {x : ℝ × ℝ} (hx : x ∈ U) (j : Fin 2) :
    ∀ᶠ s in 𝓝 (0 : ℝ), axisLine x j s ∈ U := by
  have ht := (hasDerivAt_axisLine x j 0).continuousAt
  change Filter.Tendsto (axisLine x j) (𝓝 0) (𝓝 (axisLine x j 0)) at ht
  rw [axisLine_zero] at ht
  exact ht.eventually (hU.mem_nhds hx)

/-- The quantum-stress density corresponding to amplitude `A` and density
`A²`, in terms of the first and second amplitude partials. -/
def amplitudeQuantumStress (A : ℝ × ℝ → ℝ)
    (dA : ℝ × ℝ → Fin 2 → ℝ) (ddA : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    (x : ℝ × ℝ) (j k : Fin 2) : ℝ :=
  2 * (A x * ddA x j k - dA x j * dA x k)

/-- At positive density the amplitude formula is exactly the density times
the mixed Cartesian derivative of `log ρ`, as in the stress tensor of
equation (5). The first amplitude derivative in direction `k` is
certified on a neighborhood along the outer differentiation direction. -/
theorem amplitudeQuantumStress_eq_logDensity_partial
    (A : ℝ × ℝ → ℝ) (dA : ℝ × ℝ → Fin 2 → ℝ)
    (ddA : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (j k : Fin 2)
    (hpos : 0 < A x)
    (hA : HasDerivAt (fun s => A (axisLine x j s)) (dA x j) 0)
    (hD : HasDerivAt (fun s => dA (axisLine x j s) k) (ddA x j k) 0)
    (hnear : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < A (axisLine x j s) ∧ HasDerivAt
      (fun r => A (axisLine (axisLine x j s) k r)) (dA (axisLine x j s) k) 0) :
    amplitudeQuantumStress A dA ddA x j k = A x ^ 2 *
      deriv (fun s => deriv (fun r => Real.log (A (axisLine (axisLine x j s) k r) ^ 2)) 0) 0 := by
  have he : (fun s => deriv (fun r => Real.log (A (axisLine (axisLine x j s) k r) ^ 2)) 0)
      =ᶠ[𝓝 (0 : ℝ)] fun s => (2 * dA (axisLine x j s) k) / A (axisLine x j s) := by
    filter_upwards [hnear] with s hs
    have h := (hs.2.fun_pow 2).log (pow_ne_zero 2 (by simpa using hs.1.ne'))
    rw [h.deriv]
    simp only [axisLine_zero]
    field_simp [hs.1.ne']
    ring
  rw [he.deriv_eq]
  have h := (hD.const_mul 2).fun_div hA (by simpa using hpos.ne')
  rw [h.deriv]
  simp only [axisLine_zero, amplitudeQuantumStress]
  field_simp [hpos.ne']

/-- For amplitude `A` with the indicated derivatives, the divergence of
the quantum-stress density in column `k` is `2 A² ∂ₖ(ΔA/A)`. The two
third-derivative certificates identify `∂ⱼ∂ⱼ∂ₖA` and `∂ₖ∂ⱼ∂ⱼA`. -/
theorem amplitudeQuantumStress_divergence (A : ℝ × ℝ → ℝ)
    (dA : ℝ × ℝ → Fin 2 → ℝ) (ddA : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    (x : ℝ × ℝ) (k : Fin 2) (dLapTerms : Fin 2 → ℝ) (hpos : 0 < A x)
    (hA : ∀ j, HasDerivAt (fun s => A (axisLine x j s)) (dA x j) 0)
    (hD : ∀ j i, HasDerivAt (fun s => dA (axisLine x j s) i) (ddA x j i) 0)
    (hThird : ∀ j, HasDerivAt (fun s => ddA (axisLine x j s) j k) (dLapTerms j) 0)
    (hLap : ∀ j, HasDerivAt (fun s => ddA (axisLine x k s) j j) (dLapTerms j) 0) :
    (∑ j : Fin 2, deriv (fun s => amplitudeQuantumStress A dA ddA (axisLine x j s) j k) 0) =
      2 * A x ^ 2 *
        deriv (fun s => (∑ j : Fin 2, ddA (axisLine x k s) j j) / A (axisLine x k s)) 0 := by
  have hterm (j : Fin 2) :
      HasDerivAt (fun s => amplitudeQuantumStress A dA ddA (axisLine x j s) j k)
        (2 * (A x * dLapTerms j - ddA x j j * dA x k)) 0 := by
    have h := (((hA j).mul (hThird j)).sub ((hD j j).mul (hD j k))).const_mul 2
    refine h.congr_deriv ?_
    simp only [axisLine_zero]
    ring
  have hl : HasDerivAt (fun s => ∑ j : Fin 2, ddA (axisLine x k s) j j)
      (∑ j : Fin 2, dLapTerms j) 0 :=
    HasDerivAt.fun_sum (fun j _ => hLap j)
  have hr : HasDerivAt
      (fun s => (∑ j : Fin 2, ddA (axisLine x k s) j j) / A (axisLine x k s))
      (((∑ j : Fin 2, dLapTerms j) * A x - (∑ j : Fin 2, ddA x j j) * dA x k) / A x ^ 2) 0 := by
    simpa only [axisLine_zero] using (hl.fun_div (hA k) (by simpa using hpos.ne'))
  rw [hr.deriv]
  simp only [(hterm _).deriv, Fin.sum_univ_two]
  field_simp [hpos.ne']
  ring

/-- Steady Madelung continuity and the force-free stationary momentum
equation imply that the stress tensor has zero divergence in column `k`.
The result is pointwise and assumes positive amplitude and the indicated
Cartesian derivatives on the fluid side. -/
theorem stationaryMadelung_stress_divergence
    (mass gint hbar : ℝ) (hmass : 0 < mass) (A : ℝ × ℝ → ℝ)
    (u dA : ℝ × ℝ → Fin 2 → ℝ) (du ddA : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    (x : ℝ × ℝ) (k : Fin 2) (dLapTerms : Fin 2 → ℝ) (hpos : 0 < A x)
    (hA : ∀ j, HasDerivAt (fun s => A (axisLine x j s)) (dA x j) 0)
    (hU : ∀ j i, HasDerivAt (fun s => u (axisLine x j s) i) (du x j i) 0)
    (hD : ∀ j i, HasDerivAt (fun s => dA (axisLine x j s) i) (ddA x j i) 0)
    (hThird : ∀ j, HasDerivAt (fun s => ddA (axisLine x j s) j k) (dLapTerms j) 0)
    (hLap : ∀ j, HasDerivAt (fun s => ddA (axisLine x k s) j j) (dLapTerms j) 0)
    (hcontinuity : (∑ j : Fin 2, deriv (fun s =>
      A (axisLine x j s) ^ 2 * u (axisLine x j s) j) 0) = 0)
    (hmomentum : mass * (∑ j : Fin 2, u x j * du x j k) +
      gint * (2 * A x * dA x k) -
      hbar ^ 2 / (2 * mass) *
        deriv (fun s => (∑ j : Fin 2, ddA (axisLine x k s) j j) / A (axisLine x k s)) 0 = 0) :
    (∑ j : Fin 2, deriv (fun s =>
      stressTensor mass gint hbar (fun p => A p ^ 2) u (amplitudeQuantumStress A dA ddA)
        (axisLine x j s) j k) 0) = 0 := by
  let Dmass (j : Fin 2) := deriv (fun s =>
    A (axisLine x j s) ^ 2 * u (axisLine x j s) j) 0
  let Dquantum (j : Fin 2) := deriv (fun s =>
    amplitudeQuantumStress A dA ddA (axisLine x j s) j k) 0
  let Dpressure := deriv (fun s =>
    (∑ j : Fin 2, ddA (axisLine x k s) j j) / A (axisLine x k s)) 0
  have hqsum : (∑ j, Dquantum j) = 2 * A x ^ 2 * Dpressure :=
    amplitudeQuantumStress_divergence A dA ddA x k dLapTerms hpos hA hD hThird hLap
  have hterm (j : Fin 2) : deriv (fun s =>
      stressTensor mass gint hbar (fun p => A p ^ 2) u (amplitudeQuantumStress A dA ddA)
        (axisLine x j s) j k) 0 =
      mass * u x k * Dmass j + A x ^ 2 * (mass * (u x j * du x j k)) +
        (if j = k then A x ^ 2 * (gint * (2 * A x * dA x k)) else 0) -
        hbar ^ 2 / (4 * mass) * Dquantum j := by
    have hmassTerm := (((hA j).fun_pow 2).fun_mul (hU j j)).differentiableAt.hasDerivAt
    have hflux := (hmassTerm.fun_mul (hU j k)).const_mul mass
    have hqTerm :
        HasDerivAt (fun s => amplitudeQuantumStress A dA ddA (axisLine x j s) j k)
          (Dquantum j) 0 := by
      have hq := (((hA j).fun_mul (hThird j)).fun_sub
        ((hD j j).fun_mul (hD j k))).const_mul 2
      exact hq.differentiableAt.hasDerivAt
    have hp : HasDerivAt (fun s : ℝ =>
        if j = k then gint / 2 * (A (axisLine x j s) ^ 2) ^ 2 else 0)
        (if j = k then A x ^ 2 * (gint * (2 * A x * dA x k)) else 0) 0 := by
      by_cases hjk : j = k
      · subst j
        simp only [ite_true]
        refine ((((hA k).fun_pow 2).fun_pow 2).const_mul (gint / 2)).congr_deriv ?_
        simp only [axisLine_zero]
        ring
      · simpa only [ite_eq_right hjk] using (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ))
    have ht := (hflux.fun_add hp).fun_sub (hqTerm.const_mul (hbar ^ 2 / (4 * mass)))
    have heq : (fun s =>
        stressTensor mass gint hbar (fun p => A p ^ 2) u (amplitudeQuantumStress A dA ddA)
          (axisLine x j s) j k) =
        fun s => mass * (A (axisLine x j s) ^ 2 * u (axisLine x j s) j *
          u (axisLine x j s) k) +
          (if j = k then gint / 2 * (A (axisLine x j s) ^ 2) ^ 2 else 0) -
          hbar ^ 2 / (4 * mass) * amplitudeQuantumStress A dA ddA (axisLine x j s) j k := by
      funext s
      simp only [stressTensor]
      ring
    rw [heq, ht.deriv]
    simp only [Dmass, axisLine_zero]
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (∑ j, Dmass j) = 0 at hcontinuity
  rw [hcontinuity, hqsum]
  change mass * (∑ j : Fin 2, u x j * du x j k) + gint * (2 * A x * dA x k) -
    hbar ^ 2 / (2 * mass) * Dpressure = 0 at hmomentum
  have hcoef : hbar ^ 2 / (4 * mass) * (2 * A x ^ 2 * Dpressure) =
      A x ^ 2 * (hbar ^ 2 / (2 * mass) * Dpressure) := by
    field_simp [hmass.ne']
    ring
  rw [hcoef]
  linear_combination A x ^ 2 * hmomentum

end Qatlib.Papers.SuperfoilLift19.LiftForce
