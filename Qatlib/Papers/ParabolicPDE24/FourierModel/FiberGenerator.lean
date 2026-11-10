/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.FourierModel.FourierSystem
import Qatlib.Concepts.ChannelTheory.Naimark.EtaProjection
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.ParabolicPDE24.FourierDefs

def heatA₁ (ε ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,((ω/ε:ℝ):ℂ);((ω/ε:ℝ):ℂ),0]

def heatA₂ (k ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,0;0,((1/(k*ε^2):ℝ):ℂ)]

theorem heatA₁_hermitian (ε ω : ℝ) : (heatA₁ ε ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [heatA₁]

theorem heatA₂_hermitian (k ε : ℝ) : (heatA₂ k ε).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [heatA₂]

def fiberState (k ε ω : ℝ) (amp : ℂ) (t : ℝ) : Fin 2→ℂ :=
  ![signal k ε ω amp t,flux k ε ω amp t]

def fiberDeriv (k ε ω : ℝ) (amp : ℂ) (t : ℝ) : Fin 2→ℂ :=
  ![signalDeriv k ε ω amp t,fluxDeriv k ε ω amp t]

theorem fiber_generator_action {k ε ω : ℝ} (hk : 0<k) (hε : 0<ε) (hω : ω≠0)
    (hm : 4*(k*ε^2)*(k*ω^2)≤3/4) (amp : ℂ) (t : ℝ) :
    ((-Complex.I) •heatA₁ ε ω-heatA₂ k ε)*ᵥ fiberState k ε ω amp t=
      fiberDeriv k ε ω amp t := by
  obtain ⟨hu,hv,_,_⟩ := source_fourier_system hk hε hω hm amp t
  ext i
  fin_cases i
  · simp [heatA₁,heatA₂,fiberState,fiberDeriv,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Matrix.sub_apply,hu]
    left
    ring
  · simp [heatA₁,heatA₂,fiberState,fiberDeriv,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Matrix.sub_apply,hv]
    ring
end Qatlib.Papers.ParabolicPDE24.FourierDefs
