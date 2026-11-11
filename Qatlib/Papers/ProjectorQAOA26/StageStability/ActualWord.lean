/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.MixerWordError
import Qatlib.Papers.ProjectorQAOA26.StageStability.RayTransport

/-!
# Chronological learned-projector circuit words

This module defines `learnedGenerator` and the chronological product of alternating mixer and
cost exponentials. It proves unitarity, phase invariance of the learned generator, and word
perturbation bounds underlying the stage stability analysis of [ZhouAnLiu2026].

## Main statements

* `learnedGenerator_phase`: Multiplying the reference state by a scalar of squared magnitude one
  leaves the learned generator unchanged.
* `chronologicalWord_unitary`: A chronological word is unitary when both its mixer and cost
  generators are Hermitian.
* `chronologicalWord_error`: Changing a Hermitian mixer generator changes the chronological word
  by at most the sum of absolute mixer angles times the generator distance, as in [Zhou et al.,
  Lemma C.2][ZhouAnLiu2026].

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.StageStability
open scoped Matrix Matrix.Norms.L2Operator
open Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The identity minus the rank-one operator formed from the previous state. -/
def learnedGenerator (previous : I → ℂ) : Matrix I I ℂ := 1-rankOne previous

omit [Fintype I] [Nonempty I] in

/-- The learned generator is Hermitian for every previous state. -/
theorem learnedGenerator_hermitian (previous : I → ℂ) :
    (learnedGenerator previous)ᴴ=learnedGenerator previous := by
  unfold learnedGenerator
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
  congr 1
  ext i j
  simp [rankOne,Matrix.vecMulVec_apply,Matrix.conjTranspose_apply,mul_comm]

omit [DecidableEq I] [Nonempty I] in

/-- The rank-one operator of a normalized vector is idempotent. -/
theorem rankOne_idempotent (u : I → ℂ) (hu : l2norm u=1) : rankOne u*rankOne u=rankOne u := by
  simp only [rankOne,Matrix.vecMulVec_mul_vecMulVec]
  rw [← l2inner_eq_dotProduct,l2inner_self_of_norm hu,one_smul]

omit [Nonempty I] in

/-- The learned complementary-projector generator is idempotent when its reference state is
normalized. -/
theorem learnedGenerator_idempotent (u : I → ℂ) (hu : l2norm u=1) :
    learnedGenerator u*learnedGenerator u=learnedGenerator u := by
  have hp:=rankOne_idempotent u hu
  unfold learnedGenerator
  calc
    (1-rankOne u)*(1-rankOne u)=1-rankOne u-rankOne u+rankOne u*rankOne u := by noncomm_ring
    _=1-rankOne u := by rw [hp]; abel

omit [Fintype I] [Nonempty I] in

/-- Multiplying the reference state by a scalar of squared magnitude one leaves the learned
generator unchanged. -/
theorem learnedGenerator_phase (previous : I → ℂ) (z : ℂ) (hz : Complex.normSq z=1) :
    learnedGenerator (z•previous)=learnedGenerator previous := by
  rw [learnedGenerator,rankOne_smul_unit hz]
  rfl

omit [Nonempty I] in

/-- The mixer exponential of a Hermitian generator at a real angle is unitary. -/
theorem mixerExp_unitary (R : Matrix I I ℂ) (hR : Rᴴ=R) (β : ℝ) :
    mixerExp R β∈Matrix.unitaryGroup I ℂ := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star ((-β)•(Complex.I•R))=-((-β)•(Complex.I•R))
  simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_smul,star_trivial,
    conjTranspose_I_smul R hR,smul_neg]

omit [Nonempty I] in

/-- A product of unitary matrix factors is unitary. -/
theorem wordProd_unitary (factors : List (Matrix I I ℂ))
    (hf : ∀ A∈factors,A∈Matrix.unitaryGroup I ℂ) :
    wordProd factors∈Matrix.unitaryGroup I ℂ := by
  induction factors with
  | nil => exact (Matrix.unitaryGroup I ℂ).one_mem
  | cons A rest ih =>
    exact (Matrix.unitaryGroup I ℂ).mul_mem (hf A (by simp))
      (ih (fun B hB => hf B (by simp [hB])))

/-- The product of alternating mixer and cost exponentials with later layers multiplying on the
left. -/
def chronologicalWord (layers : List MixerLayer) (R C : Matrix I I ℂ) : Matrix I I ℂ :=
  wordProd (layers.reverse.map (fun layer => mixerExp R layer.β*mixerExp C layer.γ))

omit [Nonempty I] in

/-- Appending one layer multiplies the chronological word on the left by that layer's mixer and
cost exponentials. -/
theorem chronologicalWord_append (layers : List MixerLayer) (layer : MixerLayer)
    (R C : Matrix I I ℂ) : chronologicalWord (layers++[layer]) R C=
      (mixerExp R layer.β*mixerExp C layer.γ)*chronologicalWord layers R C := by
  simp [chronologicalWord,List.reverse_append,wordProd]

omit [Nonempty I] in

/-- A chronological word is unitary when both its mixer and cost generators are Hermitian. -/
theorem chronologicalWord_unitary (layers : List MixerLayer) (R C : Matrix I I ℂ)
    (hR : Rᴴ=R) (hC : Cᴴ=C) : chronologicalWord layers R C∈Matrix.unitaryGroup I ℂ := by
  apply wordProd_unitary
  intro A hA
  obtain ⟨layer,_,rfl⟩:=List.mem_map.mp hA
  exact (Matrix.unitaryGroup I ℂ).mul_mem (mixerExp_unitary R hR layer.β)
      (mixerExp_unitary C hC layer.γ)

/-- Changing a Hermitian mixer generator changes the chronological word by at most the sum of
absolute mixer angles times the generator distance, as in [Zhou et al., Lemma
C.2][ZhouAnLiu2026]. -/
theorem chronologicalWord_error (layers : List MixerLayer) (R R' C : Matrix I I ℂ)
    (hR : Rᴴ=R) (hR' : R'ᴴ=R') (hC : Cᴴ=C) :
    ‖chronologicalWord layers R C-chronologicalWord layers R' C‖≤
      (layers.map (fun layer => |layer.β|)).sum*‖R-R'‖ := by
  simpa only [chronologicalWord,mixerLayerFactors,List.map_map,Function.comp_def,List.map_reverse,List.sum_reverse]
    using! mixer_word_error_bound layers.reverse R R' C hR hR' hC

/-- For normalized reference states, the learned chronological words differ by at most the sum
of absolute mixer angles times the phase distance between the references. -/
theorem learned_word_error (layers : List MixerLayer) (C : Matrix I I ℂ) (hC : Cᴴ=C)
    (u v : I → ℂ) (hu : l2norm u=1) (hv : l2norm v=1) :
    ‖chronologicalWord layers (learnedGenerator u) C-
      chronologicalWord layers (learnedGenerator v) C‖≤
      (layers.map (fun layer => |layer.β|)).sum*phaseDist u v := by
  apply (chronologicalWord_error layers _ _ C (learnedGenerator_hermitian u)
    (learnedGenerator_hermitian v) hC).trans
  apply mul_le_mul_of_nonneg_left (mixerGen_diff_le hu hv)
  exact List.sum_nonneg (fun x hx => by obtain ⟨l,_,rfl⟩:=List.mem_map.mp hx;exact abs_nonneg _)
end Qatlib.Papers.ProjectorQAOA26.StageStability
