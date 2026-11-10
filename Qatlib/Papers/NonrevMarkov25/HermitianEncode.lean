/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.HermitianLift
import Qatlib.Papers.NonrevMarkov25.SzegedyFrame
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.MatrixAlgebra.HermitianLift
open Qatlib.Foundations.MatrixGeometry.StochasticFrame
namespace Qatlib.Papers.NonrevMarkov25.HermitianEncode

theorem native_encoding {M L R : Type*} [Fintype M] [Fintype L] [Fintype R]
    [DecidableEq M] [DecidableEq L] [DecidableEq R]
    (U : Matrix M M ℂ) (E : Matrix M L ℂ) (F : Matrix M R ℂ)
    (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) (hE : Eᴴ*E=1) (hF : Fᴴ*F=1) :
    (native U)ᴴ=native U ∧ (native U)ᴴ*native U=1 ∧
      (nativeEmbedding E F)ᴴ*nativeEmbedding E F=1 ∧
      (nativeEmbedding E F)ᴴ*native U*nativeEmbedding E F=lift (Eᴴ*U*F) ∧
      (controlled U).submatrix qubitSplit qubitSplit*native (1 : Matrix M M ℂ)=native U :=
  ⟨native_adjoint U,native_unitary U hU hU',nativeEmbedding_gram E F hE hF,
    native_compression U E F,native_controlled_swap U⟩
variable {I : Type*} [Fintype I] [DecidableEq I]

def physical : Matrix (Fin 2 × (I × I)) (Fin 2 × (I × I)) ℂ := native swap

def sourceEmbedding (K : SzegedyFrame.Model I) :=
  nativeEmbedding (SzegedyFrame.encoder K) (SzegedyFrame.reverseEncoder K)
omit [Fintype I] in

theorem physical_adjoint : (physical (I := I))ᴴ=physical := native_adjoint _

theorem physical_unitary : (physical (I := I))ᴴ*physical=1 := by
  apply native_unitary _ swap_unitary
  rw [swap_adjoint,swap_squared]

theorem sourceEmbedding_gram (K : SzegedyFrame.Model I) :
    (sourceEmbedding K)ᴴ*sourceEmbedding K=1 :=
  nativeEmbedding_gram _ _ (SzegedyFrame.encoder_gram K) (SzegedyFrame.reverseEncoder_gram K)

theorem source_compression (K : SzegedyFrame.Model I) :
    (sourceEmbedding K)ᴴ*physical*sourceEmbedding K=
      lift ((Qatlib.Foundations.MarkovChains.ReverseKernel.curved K.transition K.probability).map
        (algebraMap ℝ ℂ)) := by
  unfold sourceEmbedding physical
  rw [native_compression,SzegedyFrame.curved_compression]

theorem source_controlled_word :
    (controlled (swap (I := I))).submatrix qubitSplit qubitSplit*native (1 : Matrix (I × I) (I × I) ℂ)=physical :=
  native_controlled_swap _
end Qatlib.Papers.NonrevMarkov25.HermitianEncode
