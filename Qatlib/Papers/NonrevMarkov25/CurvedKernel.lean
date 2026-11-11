/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonrevMarkov25.SzegedyFrame

/-!
# Similarity identities for the curved Markov discriminant

For a `SzegedyFrame.Model`, the curved discriminant is similar to the transition matrix, and its
Gram matrix is similar to the reverse-forward transition product. The module transfers these
relations to characteristic polynomials of the encoded compression and its Gram matrix in the
framework of [ClaudonPiquemalMonmarche2025].

## Main statements

* `curved_similarity`: The curved discriminant equals the transition matrix conjugated by the
  stationary-weight matrix and its inverse.
* `compression_charpoly`: The forward-reverse swap compression has the same characteristic
  polynomial as the complexified transition matrix.
* `compression_gram_charpoly`: The Gram matrix of the forward-reverse swap compression has the
  same characteristic polynomial as the complexified reverse-forward transition product.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.NonrevMarkov25.CurvedKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The curved discriminant equals the transition matrix conjugated by the stationary-weight
matrix and its inverse [ClaudonPiquemalMonmarche2025]. -/
theorem curved_similarity (K : SzegedyFrame.Model I) :
    Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability=
      Qatlib.Foundations.MarkovChains.ReverseKernel.weight K.probability*K.transition*Qatlib.Foundations.MarkovChains.ReverseKernel.weightInv K.probability :=
  Qatlib.Foundations.MarkovChains.ReverseKernel.curved_similarity _ _ K.stochastic K.positive

/-- The transpose Gram matrix of the curved discriminant is the stationary-weight conjugate of
the reverse-forward transition product [ClaudonPiquemalMonmarche2025]. -/
theorem curved_gram_similarity (K : SzegedyFrame.Model I) :
    (Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability)ᵀ*Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability=
      Qatlib.Foundations.MarkovChains.ReverseKernel.weight K.probability*(Qatlib.Foundations.MarkovChains.ReverseKernel.reverse K.transition K.probability*K.transition)*
        Qatlib.Foundations.MarkovChains.ReverseKernel.weightInv K.probability :=
  Qatlib.Foundations.MarkovChains.ReverseKernel.curved_gram_similarity _ _ K.stochastic K.positive K.stationary

/-- The forward-reverse swap compression has the same characteristic polynomial as the
complexified transition matrix [ClaudonPiquemalMonmarche2025]. -/
theorem compression_charpoly (K : SzegedyFrame.Model I) :
    ((SzegedyFrame.encoder K)ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.swap*SzegedyFrame.reverseEncoder K).charpoly=
      (K.transition.map (algebraMap ℝ ℂ)).charpoly := by
  rw [SzegedyFrame.curved_compression,Matrix.charpoly_map,Qatlib.Foundations.MarkovChains.ReverseKernel.curved_charpoly _ _ K.stochastic K.positive,
    Matrix.charpoly_map]

/-- The Gram matrix of the forward-reverse swap compression has the same characteristic
polynomial as the complexified reverse-forward transition product
[ClaudonPiquemalMonmarche2025]. -/
theorem compression_gram_charpoly (K : SzegedyFrame.Model I) :
    (((SzegedyFrame.encoder K)ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.swap*SzegedyFrame.reverseEncoder K)ᴴ*((SzegedyFrame.encoder K)ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.swap*SzegedyFrame.reverseEncoder K)).charpoly=
      ((Qatlib.Foundations.MarkovChains.ReverseKernel.reverse K.transition K.probability*K.transition).map (algebraMap ℝ ℂ)).charpoly := by
  rw [SzegedyFrame.curved_compression]
  have hc (A : Matrix I I ℝ) : (A.map (algebraMap ℝ ℂ))ᴴ=Aᵀ.map (algebraMap ℝ ℂ) := by
    ext x y
    simp
  rw [hc,← Matrix.map_mul,Matrix.charpoly_map,
    Qatlib.Foundations.MarkovChains.ReverseKernel.curved_gram_charpoly _ _ K.stochastic K.positive K.stationary,Matrix.charpoly_map]
end Qatlib.Papers.NonrevMarkov25.CurvedKernel
