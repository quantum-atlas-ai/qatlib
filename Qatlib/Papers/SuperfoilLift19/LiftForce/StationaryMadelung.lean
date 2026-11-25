/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.MadelungStress
public import Qatlib.Papers.SuperfoilLift19.QuantumCirc.LoopWinding

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.LinearCombination

/-!
# Madelung equations for a stationary Gross–Pitaevskii wave

[Musser2019Superfoil], equations (1) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
For a polar wave of positive amplitude, the true Cartesian Laplacian splits
into an amplitude part and a phase part. In the stationary eigenvalue
equation, the imaginary part yields continuity and the real part yields
the stationary Bernoulli equation with the quantum-pressure ratio.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Qatlib.Papers.SuperfoilLift19.QuantumCirc (polarWave phaseFactor polar_wave_density)
open Qatlib.Papers.SuperfoilLift19.QuantumCirc (phaseFactor_comp_hasDerivAt)
open scoped Topology

/-- The exact Cartesian Laplacian of a complex function on the plane. -/
noncomputable def waveLaplacian (ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∑ j : Fin 2, deriv (fun s =>
    deriv (fun r => ψ (axisLine (axisLine x j s) j r)) 0) 0

/-- The Cartesian Laplacian at an interior point depends only on the wave's
values in the open region containing that point. -/
theorem waveLaplacian_eq_on_open {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {ψ χ : ℝ × ℝ → ℂ} (heq : Set.EqOn ψ χ U) {x : ℝ × ℝ} (hx : x ∈ U) :
    waveLaplacian ψ x = waveLaplacian χ x := by
  unfold waveLaplacian
  apply Finset.sum_congr rfl
  intro j _
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_mem_axisLine hU hx j] with s hs
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_mem_axisLine hU hs j] with r hr
  exact heq hr

/-- The stationary Gross–Pitaevskii eigenvalue equation at a point.
The real potential and chemical potential enter with opposite signs. -/
def StationaryGrossPitaevskiiAt (mass gint hbar mu : ℝ)
    (V : ℝ × ℝ → ℝ) (ψ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : Prop :=
  -((hbar ^ 2 / (2 * mass) : ℝ) : ℂ) * waveLaplacian ψ x +
    (↑(V x + gint * ‖ψ x‖ ^ 2 - mu) : ℂ) * ψ x = 0

/-- The first derivative of a complex polar wave along a real parameter. -/
private theorem hasDerivAt_polar_wave {a θ : ℝ → ℝ} {a' θ' s : ℝ}
    (ha : HasDerivAt a a' s) (hθ : HasDerivAt θ θ' s) :
    HasDerivAt (fun r => polarWave (a r) (θ r))
      (((a' : ℂ) + Complex.I * (a s : ℂ) * (θ' : ℂ)) * phaseFactor (θ s)) s := by
  refine ((ha.ofReal_comp).fun_mul (phaseFactor_comp_hasDerivAt hθ)).congr_deriv ?_
  ring

/-- The complex Laplacian of a polar wave has real interior term
`ΔA - A |∇φ|²` and imaginary interior term `2 ∇A · ∇φ + A Δφ`
after factoring out the unit phase. -/
theorem waveLaplacian_polar_on (A φ : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hxU : x ∈ U)
    (hA : ∀ y ∈ U, ∀ j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y ∈ U, ∀ j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφ : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0) :
    waveLaplacian (fun y => polarWave (A y) (φ y)) x =
      ((↑(∑ j : Fin 2, (ddA x j j - A x * dφ x j ^ 2)) : ℂ) +
        Complex.I * (↑(∑ j : Fin 2, (2 * dA x j * dφ x j + A x * ddφ x j j)) : ℂ)) *
        phaseFactor (φ x) := by
  have hfirst (y : ℝ × ℝ) (hy : y ∈ U) (j : Fin 2) :
      deriv (fun r => polarWave (A (axisLine y j r)) (φ (axisLine y j r))) 0 =
        ((dA y j : ℂ) + Complex.I * (A y : ℂ) * (dφ y j : ℂ)) * phaseFactor (φ y) := by
    simpa only [axisLine_zero] using (hasDerivAt_polar_wave (hA y hy j) (hφ y hy j)).deriv
  have hsecond (j : Fin 2) :
      deriv (fun s => deriv (fun r => polarWave
        (A (axisLine (axisLine x j s) j r)) (φ (axisLine (axisLine x j s) j r))) 0) 0 =
        ((↑(ddA x j j - A x * dφ x j ^ 2) : ℂ) +
          Complex.I * (↑(2 * dA x j * dφ x j + A x * ddφ x j j) : ℂ)) *
          phaseFactor (φ x) := by
    have heq : (fun s => deriv (fun r => polarWave
        (A (axisLine (axisLine x j s) j r)) (φ (axisLine (axisLine x j s) j r))) 0)
        =ᶠ[𝓝 0] (fun s => ((dA (axisLine x j s) j : ℂ) +
          Complex.I * (A (axisLine x j s) : ℂ) * (dφ (axisLine x j s) j : ℂ)) *
          phaseFactor (φ (axisLine x j s))) := by
      filter_upwards [eventually_mem_axisLine hU hxU j] with s hs
      exact hfirst _ hs j
    have hproduct := ((hA x hxU j).ofReal_comp.const_mul Complex.I).fun_mul (hDφ j).ofReal_comp
    have hinner := (hDA j).ofReal_comp.fun_add hproduct
    have hexp := phaseFactor_comp_hasDerivAt (hφ x hxU j)
    rw [((hinner.fun_mul hexp).congr_of_eventuallyEq heq).deriv]
    simp only [axisLine_zero]
    push_cast
    linear_combination
      (A x : ℂ) * (dφ x j : ℂ) ^ 2 * phaseFactor (φ x) * Complex.I_sq
  simp only [waveLaplacian, Fin.sum_univ_two, hsecond, Complex.ofReal_add]
  ring

/-- The polar Laplacian identity for amplitude and phase defined
with derivatives on the entire plane. -/
theorem waveLaplacian_polar (A φ : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ)
    (hA : ∀ y j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφ : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0) :
    waveLaplacian (fun y => polarWave (A y) (φ y)) x =
      ((↑(∑ j : Fin 2, (ddA x j j - A x * dφ x j ^ 2)) : ℂ) +
        Complex.I * (↑(∑ j : Fin 2, (2 * dA x j * dφ x j + A x * ddφ x j j)) : ℂ)) *
        phaseFactor (φ x) :=
  waveLaplacian_polar_on A φ dA dφ ddA ddφ x isOpen_univ (Set.mem_univ x)
    (fun y _ => hA y) (fun y _ => hφ y) hDA hDφ

/-- The stationary complex equation is equivalent to the real Bernoulli
equation and the imaginary continuity equation at positive amplitude. -/
theorem stationary_gpe_iff_madelung_on (mass gint hbar mu : ℝ)
    (hmass : 0 < mass) (hhbar : hbar ≠ 0) (V A φ : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (hpos : 0 < A x)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hxU : x ∈ U)
    (hA : ∀ y ∈ U, ∀ j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y ∈ U, ∀ j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφ : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0) :
    StationaryGrossPitaevskiiAt mass gint hbar mu V (fun y => polarWave (A y) (φ y)) x ↔
      (∑ j : Fin 2, (2 * dA x j * dφ x j + A x * ddφ x j j)) = 0 ∧
      V x + gint * A x ^ 2 + hbar ^ 2 / (2 * mass) *
        (∑ j : Fin 2, dφ x j ^ 2) -
        hbar ^ 2 / (2 * mass) * ((∑ j : Fin 2, ddA x j j) / A x) = mu := by
  let kinetic := hbar ^ 2 / (2 * mass)
  let phaseDivergence := ∑ j : Fin 2, (2 * dA x j * dφ x j + A x * ddφ x j j)
  let bernoulli := V x + gint * A x ^ 2 + kinetic * (∑ j : Fin 2, dφ x j ^ 2) -
    kinetic * ((∑ j : Fin 2, ddA x j j) / A x) - mu
  have hkinetic : kinetic ≠ 0 := div_ne_zero (pow_ne_zero _ hhbar)
    (mul_ne_zero (by norm_num) hmass.ne')
  unfold StationaryGrossPitaevskiiAt
  rw [waveLaplacian_polar_on A φ dA dφ ddA ddφ x hU hxU hA hφ hDA hDφ, polar_wave_density]
  have ha : (↑(A x) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have he : phaseFactor (φ x) ≠ 0 := Complex.exp_ne_zero _
  have hfactor :
      -(↑kinetic : ℂ) *
        ((↑(∑ j : Fin 2, (ddA x j j - A x * dφ x j ^ 2)) : ℂ) +
          Complex.I * (phaseDivergence : ℂ)) * phaseFactor (φ x) +
        (↑(V x + gint * A x ^ 2 - mu) : ℂ) * polarWave (A x) (φ x) =
      ((↑(A x * bernoulli) : ℂ) - Complex.I * (↑(kinetic * phaseDivergence) : ℂ))
        * phaseFactor (φ x) := by
    unfold bernoulli polarWave
    simp only [Fin.sum_univ_two]
    push_cast
    field_simp [ha]
    ring
  change _ ↔ phaseDivergence = 0 ∧ _
  rw [← mul_assoc, hfactor, mul_eq_zero, or_iff_left he]
  constructor
  · intro hz
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    simp [Complex.sub_re, Complex.mul_re] at hr
    simp [Complex.sub_im, Complex.mul_im] at hi
    exact ⟨hi.resolve_left hkinetic, sub_eq_zero.mp (hr.resolve_left hpos.ne')⟩
  · rintro ⟨hi, hr⟩
    have hb : bernoulli = 0 := sub_eq_zero.mpr hr
    simp only [hi, hb, mul_zero, Complex.ofReal_zero, sub_zero]

/-- The stationary Madelung equivalence with derivative certificates
on the entire plane. -/
theorem stationary_gpe_iff_madelung (mass gint hbar mu : ℝ)
    (hmass : 0 < mass) (hhbar : hbar ≠ 0) (V A φ : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (hpos : 0 < A x)
    (hA : ∀ y j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφ : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0) :
    StationaryGrossPitaevskiiAt mass gint hbar mu V (fun y => polarWave (A y) (φ y)) x ↔
      (∑ j : Fin 2, (2 * dA x j * dφ x j + A x * ddφ x j j)) = 0 ∧
      V x + gint * A x ^ 2 + hbar ^ 2 / (2 * mass) *
        (∑ j : Fin 2, dφ x j ^ 2) -
        hbar ^ 2 / (2 * mass) * ((∑ j : Fin 2, ddA x j j) / A x) = mu :=
  stationary_gpe_iff_madelung_on mass gint hbar mu hmass hhbar V A φ dA dφ ddA ddφ x hpos
    isOpen_univ (Set.mem_univ x) (fun y _ => hA y) (fun y _ => hφ y) hDA hDφ

/-- A positive-amplitude stationary Gross–Pitaevskii wave in a constant
potential region has divergence-free stress. Continuity follows from
the imaginary equation. Differentiating the real equation and using
symmetry of the phase Hessian gives the stationary momentum balance. -/
theorem stationary_gpe_stress_divergence_on
    (mass gint hbar mu V : ℝ) (hmass : 0 < mass) (hhbar : hbar ≠ 0)
    (A φ : ℝ × ℝ → ℝ) (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (k : Fin 2)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hxU : x ∈ U)
    (dLapTerms : Fin 2 → ℝ)
    (hA : ∀ y ∈ U, ∀ j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y ∈ U, ∀ j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ y ∈ U, ∀ j i, HasDerivAt (fun s => dA (axisLine y j s) i) (ddA y j i) 0)
    (hDφ : ∀ y ∈ U, ∀ j i, HasDerivAt (fun s => dφ (axisLine y j s) i) (ddφ y j i) 0)
    (hsym : ∀ j, ddφ x k j = ddφ x j k)
    (hThird : ∀ j, HasDerivAt (fun s => ddA (axisLine x j s) j k) (dLapTerms j) 0)
    (hLap : ∀ j, HasDerivAt (fun s => ddA (axisLine x k s) j j) (dLapTerms j) 0)
    (hlocal : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < A (axisLine x k s) ∧
      StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
        (fun y => polarWave (A y) (φ y)) (axisLine x k s)) :
    (∑ j : Fin 2, deriv (fun s =>
      stressTensor mass gint hbar (fun p => A p ^ 2) (fun p i => hbar / mass * dφ p i)
        (amplitudeQuantumStress A dA ddA) (axisLine x j s) j k) 0) = 0 := by
  have hx : 0 < A x ∧ StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun y => polarWave (A y) (φ y)) x := by
    simpa only [axisLine_zero] using hlocal.self_of_nhds
  have hmadelung (y : ℝ × ℝ) (hyU : y ∈ U) (hy : 0 < A y)
      (hEq : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
        (fun p => polarWave (A p) (φ p)) y) :=
    (stationary_gpe_iff_madelung_on mass gint hbar mu hmass hhbar
      (fun _ => V) A φ dA dφ ddA ddφ y hy hU hyU hA hφ
      (fun j => hDA y hyU j j) (fun j => hDφ y hyU j j)).1 hEq
  let u (y : ℝ × ℝ) (j : Fin 2) := hbar / mass * dφ y j
  let du (y : ℝ × ℝ) (j i : Fin 2) := hbar / mass * ddφ y j i
  have hvel (j i : Fin 2) :
      HasDerivAt (fun s => u (axisLine x j s) i) (du x j i) 0 :=
    (hDφ x hxU j i).const_mul (hbar / mass)
  have hmassPart (j : Fin 2) :
      deriv (fun s => A (axisLine x j s) ^ 2 * u (axisLine x j s) j) 0 =
        (hbar / mass * A x) * (2 * dA x j * dφ x j + A x * ddφ x j j) := by
    rw [(((hA x hxU j).fun_pow 2).fun_mul (hvel j j)).deriv]
    simp only [axisLine_zero, u, du]
    ring
  have hcontinuity : (∑ j : Fin 2, deriv (fun s =>
      A (axisLine x j s) ^ 2 * u (axisLine x j s) j) 0) = 0 := by
    simp only [hmassPart, ← Finset.mul_sum, (hmadelung x hxU hx.1 hx.2).1, mul_zero]
  let Q := fun s => (∑ j : Fin 2, ddA (axisLine x k s) j j) / A (axisLine x k s)
  let c := hbar ^ 2 / (2 * mass)
  have hQ : HasDerivAt Q (deriv Q 0) 0 := by
    have hL : HasDerivAt (fun s => ∑ j : Fin 2, ddA (axisLine x k s) j j)
        (∑ j : Fin 2, dLapTerms j) 0 := HasDerivAt.fun_sum (fun j _ => hLap j)
    have h := hL.fun_div (hA x hxU k) (by simpa only [axisLine_zero] using hx.1.ne')
    exact h.differentiableAt.hasDerivAt
  have hφSq :
      HasDerivAt (fun s => ∑ j : Fin 2, dφ (axisLine x k s) j ^ 2)
        (∑ j : Fin 2, 2 * dφ x j * ddφ x k j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa using (hDφ x hxU k j).fun_pow 2
  have hBernD :
      HasDerivAt (fun s => V + gint * A (axisLine x k s) ^ 2 +
          c * (∑ j : Fin 2, dφ (axisLine x k s) j ^ 2) - c * Q s)
        (gint * (2 * A x * dA x k) +
          c * (∑ j : Fin 2, 2 * dφ x j * ddφ x k j) - c * deriv Q 0) 0 := by
    have hd := (((hA x hxU k).fun_pow 2).const_mul gint).const_add V
    have hfull := (hd.fun_add (hφSq.const_mul c)).fun_sub (hQ.const_mul c)
    simpa using hfull
  have hBern : (fun s => V + gint * A (axisLine x k s) ^ 2 +
      c * (∑ j : Fin 2, dφ (axisLine x k s) j ^ 2) - c * Q s) =ᶠ[𝓝 (0 : ℝ)] fun _ => mu := by
    filter_upwards [hlocal, eventually_mem_axisLine hU hxU k] with s hs hsU
    exact (hmadelung _ hsU hs.1 hs.2).2
  have hmomentum : mass * (∑ j : Fin 2, u x j * du x j k) +
      gint * (2 * A x * dA x k) - c * deriv Q 0 = 0 := by
    have h0 := (hBernD.congr_of_eventuallyEq hBern.symm).deriv.symm
    have hkinetic :
        mass * (∑ j : Fin 2, u x j * du x j k) =
          c * (∑ j : Fin 2, 2 * dφ x j * ddφ x k j) := by
      simp only [u, du, c, hsym, Fin.sum_univ_two]
      field_simp [hmass.ne']
    rw [hkinetic, add_comm]
    simpa using h0
  exact stationaryMadelung_stress_divergence mass gint hbar hmass A u dA du ddA
    x k dLapTerms hx.1 (hA x hxU) hvel (hDA x hxU) hThird hLap hcontinuity hmomentum

/-- The stationary Gross–Pitaevskii stress balance with derivative
certificates on the entire plane. -/
theorem stationary_gpe_stress_divergence
    (mass gint hbar mu V : ℝ) (hmass : 0 < mass) (hhbar : hbar ≠ 0)
    (A φ : ℝ × ℝ → ℝ) (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (k : Fin 2)
    (dLapTerms : Fin 2 → ℝ)
    (hA : ∀ y j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ y j i, HasDerivAt (fun s => dA (axisLine y j s) i) (ddA y j i) 0)
    (hDφ : ∀ y j i, HasDerivAt (fun s => dφ (axisLine y j s) i) (ddφ y j i) 0)
    (hsym : ∀ j, ddφ x k j = ddφ x j k)
    (hThird : ∀ j, HasDerivAt (fun s => ddA (axisLine x j s) j k) (dLapTerms j) 0)
    (hLap : ∀ j, HasDerivAt (fun s => ddA (axisLine x k s) j j) (dLapTerms j) 0)
    (hlocal : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < A (axisLine x k s) ∧
      StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
        (fun y => polarWave (A y) (φ y)) (axisLine x k s)) :
    (∑ j : Fin 2, deriv (fun s =>
      stressTensor mass gint hbar (fun p => A p ^ 2) (fun p i => hbar / mass * dφ p i)
        (amplitudeQuantumStress A dA ddA) (axisLine x j s) j k) 0) = 0 :=
  stationary_gpe_stress_divergence_on mass gint hbar mu V hmass hhbar A φ dA dφ ddA ddφ x k
    isOpen_univ (Set.mem_univ x) dLapTerms (fun y _ => hA y) (fun y _ => hφ y)
    (fun y _ => hDA y) (fun y _ => hDφ y) hsym hThird hLap hlocal

end Qatlib.Papers.SuperfoilLift19.LiftForce
