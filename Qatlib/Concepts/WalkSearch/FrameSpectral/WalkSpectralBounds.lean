/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkSpectralDefs
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilation
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.WalkSearch.FrameSpectral.PrintedPlusIDetectorWalkAuxiliary
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.Th4Expander
open scoped Kronecker

private theorem local_inner_self_zero {K : Type} [Fintype K] (w : QState K)
    (h : Qatlib.Foundations.PureStateMath.Inner w w = 0) : w = 0 := by
  let v : EuclideanSpace ℂ K := WithLp.toLp 2 w
  have hcomm : w ⬝ᵥ star w = 0 := by
    rw [dotProduct_comm]
    exact h
  have hi : @inner ℂ (EuclideanSpace ℂ K) _ v v = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact hcomm
  have hz : v = 0 := inner_self_eq_zero.mp hi
  ext x
  have he := congrArg (fun u : EuclideanSpace ℂ K => WithLp.ofLp u x) hz
  simpa only [v, WithLp.ofLp_toLp, Pi.zero_apply] using! he

theorem bipartiteTauEndpointVanishes_proof : BipartiteTauEndpointVanishes := by
  intro H I J _ _ _ _ _ _ A B hA hB u hu s
  let a : QState I := fun i => u (.inl i)
  let b : QState J := fun j => u (.inr j)
  have hd1 : (Aᴴ * B) *ᵥ b = a := by
    have hh := congrArg (fun v : QState (I ⊕ J) => fun i => v (.inl i)) hu
    simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! hh
  have hd2 : (Bᴴ * A) *ᵥ a = b := by
    have hh := congrArg (fun v : QState (I ⊕ J) => fun j => v (.inr j)) hu
    simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! hh
  have hcoeff : -(1 : ℂ) + (if s then Complex.I else -Complex.I) * (Real.sqrt (1 - (1 : ℝ)^2) : ℂ) = -1 := by
    have h0 : (1 : ℝ) - 1^2 = 0 := by norm_num
    rw [h0, Real.sqrt_zero, Complex.ofReal_zero, mul_zero, add_zero]
  have htau : bipartiteTauLinear A B 1 s u = A *ᵥ a - B *ᵥ b := by
    change A *ᵥ a +
        (-(1 : ℂ) + (if s then Complex.I else -Complex.I) * (Real.sqrt (1 - (1 : ℝ)^2) : ℂ)) •
        (B *ᵥ b) = _
    rw [hcoeff, neg_one_smul, sub_eq_add_neg]
  rw [htau]
  let w := A *ᵥ a - B *ᵥ b
  have hAw : Aᴴ *ᵥ w = 0 := by
    dsimp [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show Aᴴ * A = 1 from hA, show (Aᴴ * B) *ᵥ b = a from hd1, Matrix.one_mulVec, sub_self]
  have hBw : Bᴴ *ᵥ w = 0 := by
    dsimp [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show Bᴴ * B = 1 from hB, show (Bᴴ * A) *ᵥ a = b from hd2, Matrix.one_mulVec, sub_self]
  have hinner : Qatlib.Foundations.PureStateMath.Inner w w = 0 := by
    have hw : w = A *ᵥ a - B *ᵥ b := rfl
    have hsplit : Qatlib.Foundations.PureStateMath.Inner w w = Qatlib.Foundations.PureStateMath.Inner (A *ᵥ a) w - Qatlib.Foundations.PureStateMath.Inner (B *ᵥ b) w := by
      rw [hw, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left]
    rw [hsplit, inner_mulVec_left_rect, inner_mulVec_left_rect, hAw, hBw]
    simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct_zero]
  exact local_inner_self_zero w hinner

theorem szegedyTheorem5IntersectionNorm : SzegedyTheorem5IntersectionNorm := by
  intro H I J _ _ _ _ _ _ A B hA hB a b hnorm hab
  have hAi : Aᴴ * A = 1 := show Aᴴ * A = 1 from hA
  have hBi : Bᴴ * B = 1 := show Bᴴ * B = 1 from hB
  have hfix : bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a :=
    (two_isometry_intersection_gram_and_fixed I J H A B a b hAi hBi).2 hab
  have hinner : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ a) (A *ᵥ a) = Qatlib.Foundations.PureStateMath.Inner a a := by
    rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hAi, Matrix.one_mulVec]
  exact ⟨hfix, by rw [hinner]; exact_mod_cast (normalized_iff_inner_self a).mp hnorm⟩

theorem szegedyTheorem5Unified : SzegedyTheorem5Unified :=
  ⟨szegedyTheorem5InteriorNorm, szegedyTheorem5IntersectionNorm⟩

theorem walk_spectral3_clause37 : Clause1Spec := by
  refine ⟨fun I _ _ _ P S hP => ⟨graph_setup P S hP, reachable_span_invariant P hP, reachable_two_plane P hP⟩,
          no_exact_gate_cover,
          graph_bit_access_zero_workspace⟩

theorem walk_spectral3_clause38 : Clause2Spec := by
  refine ⟨fun I _ _ _ P Sc Uc Cc bound => not_empty_find P Sc Uc Cc bound,
          fun I _ _ P Sc Uc Cc bound => not_empty_walk_find P Sc Uc Cc bound,
          fun I _ _ P Mq k t => by simp [walkFindSuccessProb, edgeMarkedSet, MeasureProb]⟩

theorem walk_spectral3_clause39 : Clause3Spec :=
  ⟨szegedyTheorem5Unified, bipartiteTauEndpointVanishes_proof⟩

open Matrix
open Qatlib
open scoped Kronecker

private theorem marker_twice {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (w : QState (DetectionSpace I)) (p : DetectionSpace I) :
    (detectionMarkGate S *ᵥ (detectionMarkGate S *ᵥ w)) p = w p := by
  rw [marker_apply S (detectionMarkGate S *ᵥ w) p, marker_apply S w _]
  simp only [detectionMarkPermutation_involutive S p]

theorem walk_spectral3_clause39_full_endpoint_v2 : WalkSpectral3Clause39FullEndpoint := by
  refine ⟨szegedyTheorem5Unified, bipartiteTauEndpointVanishes_proof, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro I _ _ S U j v c xy
    exact plusIReflectionWord_uncontrolled_marker S U j v c xy
  · intro I _ _ S U j v c xy
    exact plusIWalkWord_uncontrolled_identity S U j v c xy
  · intro I _ _ S
    exact printedFlagShear_involutive S
  · intro I _ _ S U j v c xy
    exact correctedReflectionWord_uncontrolled_identity S U j v c xy
  · intro I _ _ S U j K v c xy
    exact printedWalkBlock_uncontrolled_identity S U j K v c xy
  · intro I _ _ S U hU
    exact rowAccess_reverse_matrix U hU S
  · intro I _ _ S U j hU v c xy
    exact plusIWalkWord_flagShear S U j hU v c xy
  · intro I _ _ S U j hU K v
    exact printedWalkBlock_period_two S U j hU K v

end Qatlib.Concepts.WalkSearch.FrameSpectral
