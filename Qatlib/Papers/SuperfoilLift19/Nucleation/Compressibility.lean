/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.StationaryMadelung

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compressibility and local sound speed in stationary Madelung flow

[Musser2019Superfoil], equation (3),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
The real stationary Gross–Pitaevskii equation gives a two-point Bernoulli
balance. With the quantum-pressure energy difference `q`, the local squared
sound speed is `c² + (U²-u²)/2 + q/m`. Thus supersonic flow is equivalent to
`2q/m < 3u²-U²-2c²`. Equation (3) is the special case `q = 0`; it is an
analytic criterion, not a proof of vortex nucleation or stall.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfoilLift19.Nucleation

open Qatlib.Papers.SuperfoilLift19.QuantumCirc (polarWave)
open Qatlib.Papers.SuperfoilLift19.LiftForce

/-- The squared Madelung speed associated with the Cartesian phase derivatives. -/
def madelungSpeedSq (hbar mass : ℝ) (dφ : ℝ × ℝ → Fin 2 → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, (hbar / mass * dφ x j) ^ 2

/-- The quantum-pressure energy in the real stationary Madelung equation. -/
def quantumPressureEnergy (hbar mass : ℝ) (A : ℝ × ℝ → ℝ)
    (ddA : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) : ℝ :=
  hbar ^ 2 / (2 * mass) * ((∑ j : Fin 2, ddA x j j) / A x)

/-- The square of the local barotropic sound speed, `c_local² = gρ/m`. -/
def localSoundSpeedSq (gint mass rho : ℝ) : ℝ := gint * rho / mass

/-- The unnormalized residual in equation (3), namely `3u²-U²-2c²`. -/
def compressibilityResidual (farSoundSq speedSq farSpeedSq : ℝ) : ℝ :=
  3 * speedSq - farSpeedSq - 2 * farSoundSq

/-- The left-hand side of equation (3), written with squared speeds. -/
def compressibilityRatio (farSoundSq speedSq farSpeedSq : ℝ) : ℝ :=
  3 / 2 * (speedSq / farSoundSq) - 1 / 2 * (farSpeedSq / farSoundSq) - 1

/-- The density obtained from stationary Bernoulli balance without a
quantum-pressure difference between the local and far-field points. -/
def bernoulliDensity (mass gint farDensity speedSq farSpeedSq : ℝ) : ℝ :=
  farDensity + mass * (farSpeedSq - speedSq) / (2 * gint)

/-- The Bernoulli density with quantum-pressure energy difference `q`. -/
def quantumCorrectedDensity (mass gint farDensity speedSq farSpeedSq q : ℝ) : ℝ :=
  bernoulliDensity mass gint farDensity speedSq farSpeedSq + q / gint

/-- Equation (3) has the same sign as its unnormalized residual when the
far-field squared sound speed is positive. -/
theorem compressibilityRatio_pos_iff {farSoundSq speedSq farSpeedSq : ℝ}
    (hc : 0 < farSoundSq) :
    0 < compressibilityRatio farSoundSq speedSq farSpeedSq ↔
      0 < compressibilityResidual farSoundSq speedSq farSpeedSq := by
  have heq : compressibilityRatio farSoundSq speedSq farSpeedSq =
      compressibilityResidual farSoundSq speedSq farSpeedSq / (2 * farSoundSq) := by
    unfold compressibilityRatio compressibilityResidual
    field_simp [hc.ne']
  rw [heq]
  simpa only [zero_mul] using
    (lt_div_iff₀ (show 0 < 2 * farSoundSq by positivity) :
      0 < compressibilityResidual farSoundSq speedSq farSpeedSq / (2 * farSoundSq) ↔
        0 * (2 * farSoundSq) < compressibilityResidual farSoundSq speedSq farSpeedSq)

/-- The ideal Bernoulli density gives the local sound-speed relation used
in equation (3). -/
theorem localSoundSpeedSq_bernoulliDensity {mass gint farDensity cSq speedSq farSpeedSq : ℝ}
    (hg : 0 < gint) (hm : 0 < mass)
    (hfar : localSoundSpeedSq gint mass farDensity = cSq) :
    localSoundSpeedSq gint mass
      (bernoulliDensity mass gint farDensity speedSq farSpeedSq) =
        cSq + (farSpeedSq - speedSq) / 2 := by
  unfold localSoundSpeedSq at hfar
  unfold localSoundSpeedSq bernoulliDensity
  field_simp [hg.ne', hm.ne'] at hfar ⊢
  nlinarith

/-- A quantum-pressure energy difference shifts the local squared sound
speed by `q/m`. -/
theorem localSoundSpeedSq_quantumCorrectedDensity
    {mass gint farDensity cSq speedSq farSpeedSq q : ℝ}
    (hg : 0 < gint) (hm : 0 < mass)
    (hfar : localSoundSpeedSq gint mass farDensity = cSq) :
    localSoundSpeedSq gint mass
      (quantumCorrectedDensity mass gint farDensity speedSq farSpeedSq q) =
        cSq + (farSpeedSq - speedSq) / 2 + q / mass := by
  unfold localSoundSpeedSq at hfar
  unfold localSoundSpeedSq quantumCorrectedDensity bernoulliDensity
  field_simp [hg.ne', hm.ne'] at hfar ⊢
  nlinarith

/-- Under the exact local sound-speed relation with quantum-pressure
energy difference `q`, supersonic flow is equivalent to the shifted
strict residual inequality. -/
theorem supersonic_iff_residual_of_localSoundSpeedSq
    {localSq farSoundSq speedSq farSpeedSq q : ℝ}
    (hlocal : localSq = farSoundSq + (farSpeedSq - speedSq) / 2 + q) :
    speedSq > localSq ↔
      2 * q < compressibilityResidual farSoundSq speedSq farSpeedSq := by
  rw [hlocal]
  unfold compressibilityResidual
  constructor <;> intro h <;> nlinarith

/-- With no quantum-pressure difference, the supersonic inequality is
exactly the strict form of equation (3). -/
theorem ideal_supersonic_iff_compressibilityRatio_pos
    {mass gint farDensity cSq speedSq farSpeedSq : ℝ}
    (hg : 0 < gint) (hm : 0 < mass) (hc : 0 < cSq)
    (hfar : localSoundSpeedSq gint mass farDensity = cSq) :
    speedSq > localSoundSpeedSq gint mass
      (bernoulliDensity mass gint farDensity speedSq farSpeedSq) ↔
        0 < compressibilityRatio cSq speedSq farSpeedSq := by
  rw [compressibilityRatio_pos_iff hc,
    localSoundSpeedSq_bernoulliDensity hg hm hfar]
  have h := supersonic_iff_residual_of_localSoundSpeedSq
    (localSq := cSq + (farSpeedSq - speedSq) / 2)
    (farSoundSq := cSq) (speedSq := speedSq) (farSpeedSq := farSpeedSq) (q := 0) (by ring)
  simpa using h

/-- The real part of the stationary Gross–Pitaevskii equation in Madelung
variables, with physical squared speed and quantum-pressure energy. -/
theorem stationary_gpe_bernoulli_at (mass gint hbar mu : ℝ)
    (hmass : 0 < mass) (hhbar : hbar ≠ 0) (V A φ : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x : ℝ × ℝ) (hpos : 0 < A x)
    (hA : ∀ y j, HasDerivAt (fun s => A (axisLine y j s)) (dA y j) 0)
    (hφ : ∀ y j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0)
    (hDA : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφ : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0)
    (hEq : StationaryGrossPitaevskiiAt mass gint hbar mu V
      (fun y => polarWave (A y) (φ y)) x) :
    V x + gint * A x ^ 2 + mass / 2 * madelungSpeedSq hbar mass dφ x -
      quantumPressureEnergy hbar mass A ddA x = mu := by
  have hbern := ((stationary_gpe_iff_madelung mass gint hbar mu hmass hhbar
    V A φ dA dφ ddA ddφ x hpos hA hφ hDA hDφ).1 hEq).2
  rw [← hbern]
  unfold madelungSpeedSq quantumPressureEnergy
  simp only [Fin.sum_univ_two]
  field_simp [hmass.ne']

/-- Two points of the same constant-potential stationary Gross–Pitaevskii
wave obey the exact quantum-corrected local sound-speed relation. -/
theorem stationary_gpe_localSoundSpeedSq_eq (mass gint hbar mu V : ℝ)
    (hmass : 0 < mass) (hhbar : hbar ≠ 0)
    (A φ : ℝ × ℝ → ℝ) (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x y : ℝ × ℝ)
    (hxpos : 0 < A x) (hypos : 0 < A y)
    (hA : ∀ z j, HasDerivAt (fun s => A (axisLine z j s)) (dA z j) 0)
    (hφ : ∀ z j, HasDerivAt (fun s => φ (axisLine z j s)) (dφ z j) 0)
    (hDAx : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφx : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0)
    (hDAy : ∀ j, HasDerivAt (fun s => dA (axisLine y j s) j) (ddA y j j) 0)
    (hDφy : ∀ j, HasDerivAt (fun s => dφ (axisLine y j s) j) (ddφ y j j) 0)
    (hEqx : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) x)
    (hEqy : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) y) :
    localSoundSpeedSq gint mass (A x ^ 2) =
      localSoundSpeedSq gint mass (A y ^ 2) +
        (madelungSpeedSq hbar mass dφ y - madelungSpeedSq hbar mass dφ x) / 2 +
        (quantumPressureEnergy hbar mass A ddA x -
          quantumPressureEnergy hbar mass A ddA y) / mass := by
  have hx := stationary_gpe_bernoulli_at mass gint hbar mu hmass hhbar
    (fun _ => V) A φ dA dφ ddA ddφ x hxpos hA hφ hDAx hDφx hEqx
  have hy := stationary_gpe_bernoulli_at mass gint hbar mu hmass hhbar
    (fun _ => V) A φ dA dφ ddA ddφ y hypos hA hφ hDAy hDφy hEqy
  unfold localSoundSpeedSq
  field_simp [hmass.ne']
  nlinarith

/-- The same stationary wave has the explicitly quantum-corrected
Bernoulli density, where `x` is local and `y` is the far-field point. -/
theorem stationary_gpe_density_eq_quantumCorrectedDensity (mass gint hbar mu V : ℝ)
    (hmass : 0 < mass) (hg : 0 < gint) (hhbar : hbar ≠ 0)
    (A φ : ℝ × ℝ → ℝ) (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x y : ℝ × ℝ)
    (hxpos : 0 < A x) (hypos : 0 < A y)
    (hA : ∀ z j, HasDerivAt (fun s => A (axisLine z j s)) (dA z j) 0)
    (hφ : ∀ z j, HasDerivAt (fun s => φ (axisLine z j s)) (dφ z j) 0)
    (hDAx : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφx : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0)
    (hDAy : ∀ j, HasDerivAt (fun s => dA (axisLine y j s) j) (ddA y j j) 0)
    (hDφy : ∀ j, HasDerivAt (fun s => dφ (axisLine y j s) j) (ddφ y j j) 0)
    (hEqx : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) x)
    (hEqy : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) y) :
    A x ^ 2 = quantumCorrectedDensity mass gint (A y ^ 2)
      (madelungSpeedSq hbar mass dφ x) (madelungSpeedSq hbar mass dφ y)
      (quantumPressureEnergy hbar mass A ddA x - quantumPressureEnergy hbar mass A ddA y) := by
  have hs := stationary_gpe_localSoundSpeedSq_eq mass gint hbar mu V hmass hhbar
    A φ dA dφ ddA ddφ x y hxpos hypos hA hφ hDAx hDφx hDAy hDφy hEqx hEqy
  unfold localSoundSpeedSq at hs
  unfold quantumCorrectedDensity bernoulliDensity
  field_simp [hg.ne', hmass.ne'] at hs ⊢
  nlinarith

/-- The exact stationary-GPE supersonic criterion with its quantum-pressure
shift. This proves an analytic inequality only; vortex nucleation and stall
remain separate phenomenological or numerical claims. -/
theorem stationary_gpe_supersonic_iff (mass gint hbar mu V : ℝ)
    (hmass : 0 < mass) (hhbar : hbar ≠ 0)
    (A φ : ℝ × ℝ → ℝ) (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x y : ℝ × ℝ)
    (hxpos : 0 < A x) (hypos : 0 < A y)
    (hA : ∀ z j, HasDerivAt (fun s => A (axisLine z j s)) (dA z j) 0)
    (hφ : ∀ z j, HasDerivAt (fun s => φ (axisLine z j s)) (dφ z j) 0)
    (hDAx : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφx : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0)
    (hDAy : ∀ j, HasDerivAt (fun s => dA (axisLine y j s) j) (ddA y j j) 0)
    (hDφy : ∀ j, HasDerivAt (fun s => dφ (axisLine y j s) j) (ddφ y j j) 0)
    (hEqx : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) x)
    (hEqy : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) y) :
    madelungSpeedSq hbar mass dφ x > localSoundSpeedSq gint mass (A x ^ 2) ↔
      2 * ((quantumPressureEnergy hbar mass A ddA x -
        quantumPressureEnergy hbar mass A ddA y) / mass) <
        compressibilityResidual (localSoundSpeedSq gint mass (A y ^ 2))
          (madelungSpeedSq hbar mass dφ x) (madelungSpeedSq hbar mass dφ y) := by
  exact supersonic_iff_residual_of_localSoundSpeedSq
    (stationary_gpe_localSoundSpeedSq_eq mass gint hbar mu V hmass hhbar
      A φ dA dφ ddA ddφ x y hxpos hypos hA hφ hDAx hDφx hDAy hDφy hEqx hEqy)

/-- If the quantum-pressure energies at the local and far-field points
agree, stationary GPE flow is supersonic exactly when equation (3) holds. -/
theorem stationary_gpe_supersonic_iff_ratio_pos_of_quantum_eq
    (mass gint hbar mu V : ℝ) (hmass : 0 < mass) (hhbar : hbar ≠ 0)
    (A φ : ℝ × ℝ → ℝ) (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) (x y : ℝ × ℝ)
    (hxpos : 0 < A x) (hypos : 0 < A y)
    (hA : ∀ z j, HasDerivAt (fun s => A (axisLine z j s)) (dA z j) 0)
    (hφ : ∀ z j, HasDerivAt (fun s => φ (axisLine z j s)) (dφ z j) 0)
    (hDAx : ∀ j, HasDerivAt (fun s => dA (axisLine x j s) j) (ddA x j j) 0)
    (hDφx : ∀ j, HasDerivAt (fun s => dφ (axisLine x j s) j) (ddφ x j j) 0)
    (hDAy : ∀ j, HasDerivAt (fun s => dA (axisLine y j s) j) (ddA y j j) 0)
    (hDφy : ∀ j, HasDerivAt (fun s => dφ (axisLine y j s) j) (ddφ y j j) 0)
    (hEqx : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) x)
    (hEqy : StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
      (fun z => polarWave (A z) (φ z)) y)
    (hquantum : quantumPressureEnergy hbar mass A ddA x =
      quantumPressureEnergy hbar mass A ddA y)
    (hc : 0 < localSoundSpeedSq gint mass (A y ^ 2)) :
    madelungSpeedSq hbar mass dφ x > localSoundSpeedSq gint mass (A x ^ 2) ↔
      0 < compressibilityRatio (localSoundSpeedSq gint mass (A y ^ 2))
        (madelungSpeedSq hbar mass dφ x) (madelungSpeedSq hbar mass dφ y) := by
  rw [compressibilityRatio_pos_iff hc, stationary_gpe_supersonic_iff mass gint hbar mu V
    hmass hhbar A φ dA dφ ddA ddφ x y hxpos hypos hA hφ hDAx hDφx hDAy hDφy hEqx hEqy]
  rw [hquantum]
  simp

end Qatlib.Papers.SuperfoilLift19.Nucleation
