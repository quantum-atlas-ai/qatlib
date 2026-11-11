/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.ReverseKernel.Discriminant
import Qatlib.Foundations.MatrixGeometry.StochasticFrame.SwapCompression
import Qatlib.Foundations.MatrixGeometry.StochasticFrame.Reflection

/-!
# Forward and reverse stochastic frames

A `Model` consists of a finite row-stochastic transition matrix and a strictly positive
normalized stationary probability. Its forward and reverse encoders are isometries whose swap
compressions give the flat and curved discriminants. The associated range reflections are
self-adjoint unitaries, providing the frame construction for [ClaudonPiquemalMonmarche2025].

## Main statements

* `flat_compression`: Compressing swap between two forward encoders yields the complexified flat
  discriminant.
* `curved_compression`: Compressing swap between the forward and reverse encoders yields the
  complexified curved discriminant.
* `forward_reflection`: The range reflection of the forward encoder is self-adjoint and has
  identity conjugate-transpose product.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical
namespace Qatlib.Papers.NonrevMarkov25.SzegedyFrame
variable (I : Type*) [Fintype I] [DecidableEq I]

/-- A finite row-stochastic transition matrix equipped with a strictly positive normalized
stationary probability. -/
structure Model where
  transition : Matrix I I ℝ
  stochastic : transition ∈ Matrix.rowStochastic ℝ I
  probability : I → ℝ
  positive : ∀ x,0 < probability x
  normalized : ∑ x, probability x=1
  stationary : Qatlib.Foundations.MarkovChains.ReverseKernel.Stationary transition probability
variable {I}

/-- The row frame associated with the forward transition matrix. -/
def encoder (K : Model I) := Qatlib.Foundations.MatrixGeometry.StochasticFrame.rowFrame K.transition

/-- The row frame associated with the time-reversed transition matrix. -/
def reverseEncoder (K : Model I) :=
    Qatlib.Foundations.MatrixGeometry.StochasticFrame.rowFrame
    (Qatlib.Foundations.MarkovChains.ReverseKernel.reverse K.transition K.probability)

/-- The forward stochastic encoder has identity Gram matrix [ClaudonPiquemalMonmarche2025]. -/
theorem encoder_gram (K : Model I) : (encoder K)ᴴ*encoder K=1 :=
  Qatlib.Foundations.MatrixGeometry.StochasticFrame.rowFrame_gram K.transition K.stochastic

/-- The reverse stochastic encoder has identity Gram matrix [ClaudonPiquemalMonmarche2025]. -/
theorem reverseEncoder_gram (K : Model I) : (reverseEncoder K)ᴴ*reverseEncoder K=1 :=
  Qatlib.Foundations.MatrixGeometry.StochasticFrame.rowFrame_gram _ (Qatlib.Foundations.MarkovChains.ReverseKernel.reverse_stochastic _ _ K.stochastic K.positive K.stationary)

/-- Compressing swap between two forward encoders yields the complexified flat discriminant
[ClaudonPiquemalMonmarche2025]. -/
theorem flat_compression (K : Model I) :
    (encoder K)ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.swap*encoder K=(Qatlib.Foundations.MarkovChains.ReverseKernel.flat K.transition).map (algebraMap ℝ ℂ) :=
  Qatlib.Foundations.MatrixGeometry.StochasticFrame.mixed_compression K.transition K.transition K.stochastic.1

/-- Compressing swap between the forward and reverse encoders yields the complexified curved
discriminant [ClaudonPiquemalMonmarche2025]. -/
theorem curved_compression (K : Model I) :
    (encoder K)ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.swap*reverseEncoder K=(Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability).map (algebraMap ℝ ℂ) :=
  Qatlib.Foundations.MatrixGeometry.StochasticFrame.mixed_compression K.transition _ K.stochastic.1

/-- The range reflection of the forward encoder is self-adjoint and has identity
conjugate-transpose product [ClaudonPiquemalMonmarche2025]. -/
theorem forward_reflection (K : Model I) :
    (Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (encoder K))ᴴ=Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (encoder K) ∧
    (Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (encoder K))ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (encoder K)=1 :=
  ⟨Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection_adjoint _,Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection_unitary _ (encoder_gram K)⟩

/-- The range reflection of the reverse encoder is self-adjoint and has identity
conjugate-transpose product [ClaudonPiquemalMonmarche2025]. -/
theorem reverse_reflection (K : Model I) :
    (Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (reverseEncoder K))ᴴ=Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (reverseEncoder K) ∧
    (Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (reverseEncoder K))ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection (reverseEncoder K)=1 :=
  ⟨Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection_adjoint _,Qatlib.Foundations.MatrixGeometry.StochasticFrame.rangeReflection_unitary _ (reverseEncoder_gram K)⟩
end Qatlib.Papers.NonrevMarkov25.SzegedyFrame
