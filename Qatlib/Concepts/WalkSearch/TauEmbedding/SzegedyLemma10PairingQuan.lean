/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyLemma10PairingStat

/-!
# Pairing identities for bipartite sources

This module proves `SzegedyLemma10Pairing` by expanding discriminant eigenvector equations into
their component cross-Gram equations. For two sources at a common eigenvalue `0 < lam < 1`, the
left and right frame-image pairings agree, and the mixed pairing is `lam` times the left
pairing.

These bilinear identities support the τ-map norm and scaled-isometry calculations in the
spectral analysis of [Szegedy2004].

## Main statements

* `szegedyLemma10Pairing`: component and mixed pairing identities.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

variable {H I J : Type} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Split a discriminant eigenvector equation into the two component cross-Gram equations. -/
private theorem discriminant_blocks (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (u : QState (I ⊕ J)) (lam : ℝ)
    (hu : bipartiteDiscriminant A B *ᵥ u = (lam : ℂ) • u) :
    (Aᴴ * B) *ᵥ (fun j => u (.inr j)) = (lam : ℂ) • (fun i => u (.inl i)) ∧
    (Bᴴ * A) *ᵥ (fun i => u (.inl i)) = (lam : ℂ) • (fun j => u (.inr j)) := by
  constructor
  · have h := congrArg (fun v : QState (I ⊕ J) => fun i => v (.inl i)) hu
    simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! h
  · have h := congrArg (fun v : QState (I ⊕ J) => fun j => v (.inr j)) hu
    simpa [bipartiteDiscriminant, Matrix.fromBlocks_mulVec] using! h

/-- An isometric frame preserves the state inner product. -/
private theorem frame_inner {K : Type} [Fintype K] [DecidableEq K]
    (F : Matrix H K ℂ) (hF : IsIsometry F) (u v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (F *ᵥ u) (F *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner u v := by
  rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec,
    show Fᴴ * F = 1 from hF, Matrix.one_mulVec]

/-- Establish equal left and right frame pairings and the eigenvalue-scaled cross pairing for
two sources at the same interior discriminant eigenvalue [Szegedy2004]. -/
theorem szegedyLemma10Pairing : SzegedyLemma10Pairing := by
  intro H I J _ _ _ _ _ _ A B lam hA hB hl _hu u v hu hv
  have huv := (discriminant_blocks A B v lam hv).1
  have huu := (discriminant_blocks A B u lam hu).2
  have hcross : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (B *ᵥ fun j => v (.inr j)) =
      (lam : ℂ) * Qatlib.Foundations.PureStateMath.Inner (fun i => u (.inl i)) (fun i => v (.inl i)) := by
    rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, huv,
        Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right]
  have hcross' : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (B *ᵥ fun j => v (.inr j)) =
      (lam : ℂ) * Qatlib.Foundations.PureStateMath.Inner (fun j => u (.inr j)) (fun j => v (.inr j)) := by
    have hmove := inner_mulVec_left_rect Bᴴ (A *ᵥ fun i => u (.inl i))
      (fun j => v (.inr j))
    rw [Matrix.conjTranspose_conjTranspose] at hmove
    rw [← hmove, Matrix.mulVec_mulVec, huu,
        Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left]
    simp
  have hpair := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hl.ne')
    (hcross.symm.trans hcross')
  constructor
  · rw [frame_inner A hA, frame_inner B hB, hpair]
  · rw [frame_inner A hA]
    exact hcross

end Qatlib.Concepts.WalkSearch.TauEmbedding
