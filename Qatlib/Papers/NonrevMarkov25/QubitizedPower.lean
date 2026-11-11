/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.QubitizedPower
import Qatlib.Papers.NonrevMarkov25.SzegedyFrame

/-!
# Chebyshev compression of qubitized walk powers

The walk `sourceWalk` is built from the forward stochastic frame and swap, with flat
discriminant `sourceSignal`. Compressing its powers evaluates Chebyshev polynomials at this
signal. The square formula and its idempotent-signal specialization expose the reflection
identity used in the walk analysis of [ClaudonPiquemalMonmarche2025].

## Main statements

* `sourceWalk_unitary`: The conjugate transpose of the source walk multiplied by the source walk
  is the identity.
* `source_power_compression`: Compressing the `n`th source-walk power evaluates the `n`th
  Chebyshev polynomial of the first kind at `sourceSignal`.
* `source_projector_reflection`: If the source signal is idempotent, the compressed square of
  the source walk equals twice the signal minus the identity.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PolynomialCalc.QubitizedPower
open Qatlib.Foundations.MatrixGeometry.StochasticFrame
namespace Qatlib.Papers.NonrevMarkov25.QubitizedPower
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The qubitized walk formed from the forward stochastic encoder and the swap operator. -/
def sourceWalk (K : SzegedyFrame.Model I) := walk (SzegedyFrame.encoder K) swap

/-- The complexified flat discriminant of the transition matrix. -/
def sourceSignal (K : SzegedyFrame.Model I) :=
  (Qatlib.Foundations.MarkovChains.ReverseKernel.flat K.transition).map (algebraMap ℝ ℂ)

/-- The conjugate transpose of the source walk multiplied by the source walk is the identity
[ClaudonPiquemalMonmarche2025]. -/
theorem sourceWalk_unitary (K : SzegedyFrame.Model I) : (sourceWalk K)ᴴ*sourceWalk K=1 :=
  walk_unitary _ _ (SzegedyFrame.encoder_gram K) swap_adjoint swap_squared

/-- Compressing the `n`th source-walk power evaluates the `n`th Chebyshev polynomial of the
first kind at `sourceSignal` [ClaudonPiquemalMonmarche2025]. -/
theorem source_power_compression (K : SzegedyFrame.Model I) (n : ℕ) :
    (SzegedyFrame.encoder K)ᴴ*sourceWalk K^n*SzegedyFrame.encoder K=
      Polynomial.aeval (sourceSignal K) (Polynomial.Chebyshev.T ℂ (n : ℤ)) := by
  have h :=
      compressed_chebyshev (SzegedyFrame.encoder K) swap
      (SzegedyFrame.encoder_gram K) swap_squared n
  simpa only [sourceWalk,signal,SzegedyFrame.flat_compression,sourceSignal] using h

/-- The compressed square of the source walk equals twice the square of the signal minus the
identity [ClaudonPiquemalMonmarche2025]. -/
theorem source_square_compression (K : SzegedyFrame.Model I) :
    (SzegedyFrame.encoder K)ᴴ*sourceWalk K^2*SzegedyFrame.encoder K=
      (2 : ℂ)•(sourceSignal K*sourceSignal K)-1 := by
  rw [source_power_compression]
  simp only [Nat.cast_ofNat,Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat,
    Polynomial.aeval_X,map_one,pow_two]
  simp only [two_smul]
  noncomm_ring

/-- If the source signal is idempotent, the compressed square of the source walk equals twice
the signal minus the identity [ClaudonPiquemalMonmarche2025]. -/
theorem source_projector_reflection (K : SzegedyFrame.Model I)
    (h : sourceSignal K*sourceSignal K=sourceSignal K) :
    (SzegedyFrame.encoder K)ᴴ*sourceWalk K^2*SzegedyFrame.encoder K=(2 : ℂ)•sourceSignal K-1 := by
  rw [source_square_compression,h]
end Qatlib.Papers.NonrevMarkov25.QubitizedPower
