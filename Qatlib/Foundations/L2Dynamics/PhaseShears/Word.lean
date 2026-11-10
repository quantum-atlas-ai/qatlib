/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.L2Dynamics.PhaseShears.Phase
import Qatlib.Foundations.L2Dynamics.PhaseShears.Shear
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.L2Dynamics.PhaseShears.Word
abbrev Pos := Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.Pos
abbrev Rest := Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.Rest
abbrev H := Lp ℂ 2 (volume : Measure Pos)

inductive Gate where
  | phase (p : Pos→ℝ) (hp : Measurable p)
  | shift (i : Fin 3) (g : Rest→ℝ) (hg : Measurable g)

def nativeGate : Gate→(H ≃ₗᵢ[ℂ] H)
  | .phase p hp => Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseEquiv volume p hp
  | .shift i g hg => Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.shiftL2 i g hg

def waveGate : Gate→(Pos→ℂ)→(Pos→ℂ)
  | .phase p _ => fun f x=>Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phase p x*f x
  | .shift i g _ => fun f x=>f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i g x)

theorem nativeGate_repr (g : Gate) (ψ : H) : nativeGate g ψ =ᵐ[volume] waveGate g ψ := by
  cases g with
  | phase p hp => exact Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phaseMap_repr volume p hp ψ
  | shift i g hg => exact Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.shiftL2_repr i g hg ψ

theorem waveGate_congr (g : Gate) {f h : Pos→ℂ} (he : f =ᵐ[volume] h) :
    waveGate g f =ᵐ[volume] waveGate g h := by
  cases g with
  | phase p _ => exact he.mono fun x hx=>congrArg (fun z=>Qatlib.Foundations.L2Dynamics.PhaseShears.Phase.phase p x*z) hx
  | shift i g hg => exact he.comp_tendsto (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_preserving i g hg).quasiMeasurePreserving.tendsto_ae

def nativeWord : List Gate→(H ≃ₗᵢ[ℂ] H)
  | [] => LinearIsometryEquiv.refl ℂ H
  | g::gs => (nativeWord gs).trans (nativeGate g)

def waveWord : List Gate→(Pos→ℂ)→(Pos→ℂ)
  | [] => id
  | g::gs => waveGate g ∘ waveWord gs

theorem nativeWord_repr (gs : List Gate) (ψ : H) : nativeWord gs ψ =ᵐ[volume] waveWord gs ψ := by
  induction gs with
  | nil => exact Filter.EventuallyEq.rfl
  | cons g gs ih =>
    exact (nativeGate_repr g (nativeWord gs ψ)).trans (waveGate_congr g ih)

theorem nativeWord_norm (gs : List Gate) (ψ : H) : ‖nativeWord gs ψ‖=‖ψ‖ :=
  (nativeWord gs).norm_map ψ

theorem nativeWord_normalized (gs : List Gate) (ψ : H) (hψ : ‖ψ‖=1) :
    ‖nativeWord gs ψ‖=1 := by rw [nativeWord_norm,hψ]
end Qatlib.Foundations.L2Dynamics.PhaseShears.Word
