/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.L2Dynamics.PhaseShears.Phase
import Qatlib.Foundations.L2Dynamics.PhaseShears.Shear

/-!
# Finite words of L2 phase and shear gates

`Gate` combines measurable phase multipliers with measurable coordinate shears on complex L2
over real three-dimensional space. `nativeGate` and `nativeWord` interpret individual gates and
finite words as complex linear isometry equivalences.

The representative-level operations `waveGate` and `waveWord` agree almost everywhere with these
L2 interpretations, and finite words preserve norm and normalization. The gate constructions are
motivated by [ArrazolaEtAl2019].

## Main statements

* `nativeGate_repr`: Agreement between L2 and representative-level gates.
* `nativeWord_repr`: Agreement for finite gate words.
* `nativeWord_norm`: Norm preservation by every finite word.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.L2Dynamics.PhaseShears.Word
/-- Three-dimensional real coordinate space for the gate words. -/
abbrev Pos := Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.Pos
/-- The two real coordinates used as controls for a coordinate shear. -/
abbrev Rest := Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.Rest
/-- Complex L2 over three-dimensional real space with Lebesgue volume. -/
abbrev H := Lp ℂ 2 (volume : Measure Pos)

/-- A measurable phase multiplier or a measurable controlled coordinate shear. -/
inductive Gate where
  | phase (p : Pos→ℝ) (hp : Measurable p)
  | shift (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g)

/-- Interprets a phase or shear gate as a complex linear isometry equivalence of L2. -/
def nativeGate : Gate→(H ≃ₗᵢ[ℂ] H)
  | .phase p hp => Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseEquiv volume p hp
  | .shift i g hg => Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.shiftL2 i g hg

/-- The pointwise action of a phase or shear gate on complex-valued functions. -/
def waveGate : Gate→(Pos→ℂ)→(Pos→ℂ)
  | .phase p _ => fun f x=>Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phase p x*f x
  | .shift i g _ => fun f x=>f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i g x)

/-- The L2 action of a gate agrees almost everywhere with its pointwise action on a
representative. -/
theorem nativeGate_repr (g : Gate) (ψ : H) : nativeGate g ψ =ᵐ[volume] waveGate g ψ := by
  cases g with
  | phase p hp => exact Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseMap_repr volume p hp ψ
  | shift i g hg => exact Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.shiftL2_repr i g hg ψ

/-- The pointwise gate action preserves almost-everywhere equality. -/
theorem waveGate_congr (g : Gate) {f h : Pos→ℂ} (he : f =ᵐ[volume] h) :
    waveGate g f =ᵐ[volume] waveGate g h := by
  cases g with
  | phase p _ => exact he.mono fun x hx=>congrArg (fun z=>Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phase p x*z) hx
  | shift i g hg => exact he.comp_tendsto (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_preserving i g hg).quasiMeasurePreserving.tendsto_ae

/-- Interprets a finite gate list as an L2 isometry equivalence, applying the tail before the
head. -/
def nativeWord : List Gate→(H ≃ₗᵢ[ℂ] H)
  | [] => LinearIsometryEquiv.refl ℂ H
  | g::gs => (nativeWord gs).trans (nativeGate g)

/-- The composition of pointwise gate actions, applying the tail of the list before its head. -/
def waveWord : List Gate→(Pos→ℂ)→(Pos→ℂ)
  | [] => id
  | g::gs => waveGate g ∘ waveWord gs

/-- The L2 interpretation of a gate word agrees almost everywhere with the corresponding
pointwise composition. -/
theorem nativeWord_repr (gs : List Gate) (ψ : H) : nativeWord gs ψ =ᵐ[volume] waveWord gs ψ := by
  induction gs with
  | nil => exact Filter.EventuallyEq.rfl
  | cons g gs ih =>
    exact (nativeGate_repr g (nativeWord gs ψ)).trans (waveGate_congr g ih)

/-- Every finite word of phase and shear gates preserves the L2 norm. -/
theorem nativeWord_norm (gs : List Gate) (ψ : H) : ‖nativeWord gs ψ‖=‖ψ‖ :=
  (nativeWord gs).norm_map ψ

/-- Every finite word of phase and shear gates sends a state of norm one to a state of norm one. -/
theorem nativeWord_normalized (gs : List Gate) (ψ : H) (hψ : ‖ψ‖=1) :
    ‖nativeWord gs ψ‖=1 := by rw [nativeWord_norm,hψ]
end Qatlib.Foundations.L2Dynamics.PhaseShears.Word
