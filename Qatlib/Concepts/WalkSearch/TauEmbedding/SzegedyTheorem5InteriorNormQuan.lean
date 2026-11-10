/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormStat
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTauScaledIsometryQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

private theorem inner_add_left {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (u + v) w = Qatlib.Foundations.PureStateMath.Inner u w + Qatlib.Foundations.PureStateMath.Inner v w := by
  simp [Qatlib.Foundations.PureStateMath.Inner, star_add, add_dotProduct]

private theorem inner_add_right {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner u (v + w) = Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner u w := by
  simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct_add]

theorem szegedyTheorem5InteriorNorm : SzegedyTheorem5InteriorNorm := by
  intro H I J _ _ _ _ _ _ A B lam hA hB hl hh u hn hu s
  have hnorm : Qatlib.Foundations.PureStateMath.Inner u u = 1 :=
      (normalized_iff_inner_self u).mp hn
  rcases eq_or_lt_of_le hl with hz | hpos
  · have hzero : lam = 0 := hz.symm
    subst lam
    have hblock : (Aᴴ * B) *ᵥ (fun j => u (.inr j)) = 0 := by
      have h := congrArg (fun v : QState (I ⊕ J) => fun i => v (.inl i)) hu
      simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! h
    have hcross : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (B *ᵥ fun j => u (.inr j)) = 0 := by
      rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hblock]
      simp [Qatlib.Foundations.PureStateMath.Inner]
    have hreverse : Qatlib.Foundations.PureStateMath.Inner (B *ᵥ fun j => u (.inr j)) (A *ᵥ fun i => u (.inl i)) = 0 := by
      rw [show Qatlib.Foundations.PureStateMath.Inner (B *ᵥ fun j => u (.inr j)) (A *ᵥ fun i => u (.inl i)) =
        (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i))
          (B *ᵥ fun j => u (.inr j))) from
            star_dotProduct (v := B *ᵥ fun j => u (.inr j))
              (w := A *ᵥ fun i => u (.inl i))]
      simp [hcross]
    have hAi : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => u (.inl i)) =
        Qatlib.Foundations.PureStateMath.Inner (fun i => u (.inl i)) (fun i => u (.inl i)) := by
      rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec,
        show Aᴴ * A = 1 from hA, Matrix.one_mulVec]
    have hBi : Qatlib.Foundations.PureStateMath.Inner (B *ᵥ fun j => u (.inr j)) (B *ᵥ fun j => u (.inr j)) =
        Qatlib.Foundations.PureStateMath.Inner (fun j => u (.inr j)) (fun j => u (.inr j)) := by
      rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec,
        show Bᴴ * B = 1 from hB, Matrix.one_mulVec]
    have hsplit : Qatlib.Foundations.PureStateMath.Inner (fun i => u (.inl i)) (fun i => u (.inl i)) +
        Qatlib.Foundations.PureStateMath.Inner (fun j => u (.inr j)) (fun j => u (.inr j)) = 1 := by
      simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Fintype.sum_sum_type] using!
          hnorm
    have htau : bipartiteTauLinear A B 0 s u =
        (A *ᵥ fun i => u (.inl i)) +
          (if s then Complex.I else -Complex.I) • (B *ᵥ fun j => u (.inr j)) := by
      change (A *ᵥ fun i => u (.inl i)) +
        (-(0 : ℂ) + (if s then Complex.I else -Complex.I) *
          (Real.sqrt (1 - (0 : ℝ)^2) : ℂ)) • (B *ᵥ fun j => u (.inr j)) = _
      norm_num
    rw [htau, inner_add_left, inner_add_right, inner_add_right,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      hcross, hreverse, hAi, hBi]
    cases s <;> simpa [← mul_assoc] using! hsplit
  · rw [szegedyTauScaledIsometry H I J A B lam hA hB hpos hh u u hu hu s, hnorm,
      mul_one]

end Qatlib.Concepts.WalkSearch.TauEmbedding
