/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformDefs
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.LowestPair
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem native_min_rayleigh {A : Matrix I I ℂ} (hA : A.IsHermitian) (v : EuclideanSpace ℂ I) :
    hA.eigenvalues₀ ⟨Fintype.card I-1,by have :=Fintype.card_pos (α:=I);omega⟩*‖v‖^2 ≤
      (inner ℂ v (A.toEuclideanLin v)).re := by
  rw [orderedHermitian_rayleigh hA,spectral_norm_sq_basis (orderedHermitianBasis hA),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
  apply hA.eigenvalues₀_antitone
  change j.val≤Fintype.card I-1
  omega

theorem native_min_le_diagonal {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : I) :
    hA.eigenvalues₀ ⟨Fintype.card I-1,by have :=Fintype.card_pos (α:=I);omega⟩≤(A i i).re := by
  have h:=native_min_rayleigh hA (PiLp.single 2 i (1:ℂ))
  simpa [EuclideanSpace.inner_single_left,Matrix.toLpLin_apply,Matrix.mulVec,
    dotProduct,PiLp.single_apply] using! h
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
