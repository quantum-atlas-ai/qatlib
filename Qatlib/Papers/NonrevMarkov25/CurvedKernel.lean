/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonrevMarkov25.SzegedyFrame
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.NonrevMarkov25.CurvedKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem curved_similarity (K : SzegedyFrame.Model I) :
    Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability=
      Qatlib.Foundations.MarkovChains.ReverseKernel.weight K.probability*K.transition*Qatlib.Foundations.MarkovChains.ReverseKernel.weightInv K.probability :=
  Qatlib.Foundations.MarkovChains.ReverseKernel.curved_similarity _ _ K.stochastic K.positive

theorem curved_gram_similarity (K : SzegedyFrame.Model I) :
    (Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability)ᵀ*Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability=
      Qatlib.Foundations.MarkovChains.ReverseKernel.weight K.probability*(Qatlib.Foundations.MarkovChains.ReverseKernel.reverse K.transition K.probability*K.transition)*
        Qatlib.Foundations.MarkovChains.ReverseKernel.weightInv K.probability :=
  Qatlib.Foundations.MarkovChains.ReverseKernel.curved_gram_similarity _ _ K.stochastic K.positive K.stationary

theorem compression_charpoly (K : SzegedyFrame.Model I) :
    ((SzegedyFrame.encoder K)ᴴ*Qatlib.Foundations.MatrixGeometry.StochasticFrame.swap*SzegedyFrame.reverseEncoder K).charpoly=
      (K.transition.map (algebraMap ℝ ℂ)).charpoly := by
  rw [SzegedyFrame.curved_compression,Matrix.charpoly_map,Qatlib.Foundations.MarkovChains.ReverseKernel.curved_charpoly _ _ K.stochastic K.positive,
    Matrix.charpoly_map]

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
