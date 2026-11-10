/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.QubitizedPower
import Qatlib.Papers.NonrevMarkov25.SzegedyFrame
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PolynomialCalc.QubitizedPower
open Qatlib.Foundations.MatrixGeometry.StochasticFrame
namespace Qatlib.Papers.NonrevMarkov25.QubitizedPower
variable {I : Type*} [Fintype I] [DecidableEq I]

def sourceWalk (K : SzegedyFrame.Model I) := walk (SzegedyFrame.encoder K) swap

def sourceSignal (K : SzegedyFrame.Model I) :=
  (Qatlib.Foundations.MarkovChains.ReverseKernel.flat K.transition).map (algebraMap ℝ ℂ)

theorem sourceWalk_unitary (K : SzegedyFrame.Model I) : (sourceWalk K)ᴴ*sourceWalk K=1 :=
  walk_unitary _ _ (SzegedyFrame.encoder_gram K) swap_adjoint swap_squared

theorem source_power_compression (K : SzegedyFrame.Model I) (n : ℕ) :
    (SzegedyFrame.encoder K)ᴴ*sourceWalk K^n*SzegedyFrame.encoder K=
      Polynomial.aeval (sourceSignal K) (Polynomial.Chebyshev.T ℂ (n : ℤ)) := by
  have h :=
      compressed_chebyshev (SzegedyFrame.encoder K) swap
      (SzegedyFrame.encoder_gram K) swap_squared n
  simpa only [sourceWalk,signal,SzegedyFrame.flat_compression,sourceSignal] using h

theorem source_square_compression (K : SzegedyFrame.Model I) :
    (SzegedyFrame.encoder K)ᴴ*sourceWalk K^2*SzegedyFrame.encoder K=
      (2 : ℂ)•(sourceSignal K*sourceSignal K)-1 := by
  rw [source_power_compression]
  simp only [Nat.cast_ofNat,Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat,
    Polynomial.aeval_X,map_one,pow_two]
  simp only [two_smul]
  noncomm_ring

theorem source_projector_reflection (K : SzegedyFrame.Model I)
    (h : sourceSignal K*sourceSignal K=sourceSignal K) :
    (SzegedyFrame.encoder K)ᴴ*sourceWalk K^2*SzegedyFrame.encoder K=(2 : ℂ)•sourceSignal K-1 := by
  rw [source_square_compression,h]
end Qatlib.Papers.NonrevMarkov25.QubitizedPower
