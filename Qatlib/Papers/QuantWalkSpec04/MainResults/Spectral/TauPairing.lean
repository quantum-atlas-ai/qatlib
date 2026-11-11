/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyLemma10PairingQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence

/-!
# Pairings and norms of walk eigenvectors

This module records inner product identities for the two isometric embeddings and their
discriminant eigenspaces. These identities give the squared norm `1 - lam ^ 2` of the
transformed walk vector `bipartiteTauLinear` for normalized discriminant eigenvectors. See
[Szegedy2004].

## Main statements

* `szegedyLemma10_pairing`: The isometries preserve inner products, their cross pairing is given
  by `Aᴴ * B`, and discriminant eigenvectors with `0 < lam < 1` have equal component pairings
  and a cross pairing scaled by `lam`.
* `szegedyTheorem5_eigenvector_norm`: For a normalized discriminant eigenvector with `0 ≤ lam <
  1`, either transformed walk vector has squared norm `1 - lam ^ 2`; an isometric image of a
  normalized source vector has squared norm one.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.TauEmbedding

namespace Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral

/-- The isometries preserve inner products, their cross pairing is given by `Aᴴ * B`, and
discriminant eigenvectors with `0 < lam < 1` have equal component pairings and a cross
pairing scaled by `lam`. -/
theorem szegedyLemma10_pairing
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ a a' : QState I, Inner (A *ᵥ a) (A *ᵥ a') = Inner a a') ∧
    (∀ b b' : QState J, Inner (B *ᵥ b) (B *ᵥ b') = Inner b b') ∧
    (∀ a : QState I, ∀ b : QState J,
      Inner (A *ᵥ a) (B *ᵥ b) = Inner a ((Aᴴ * B) *ᵥ b)) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ u v : QState (I ⊕ J),
      bipartiteDiscriminant A B *ᵥ u = (lam : ℂ) • u →
      bipartiteDiscriminant A B *ᵥ v = (lam : ℂ) • v →
      Inner (A *ᵥ fun i => u (Sum.inl i)) (A *ᵥ fun i => v (Sum.inl i)) =
        Inner (B *ᵥ fun j => u (Sum.inr j)) (B *ᵥ fun j => v (Sum.inr j)) ∧
      Inner (A *ᵥ fun i => u (Sum.inl i)) (B *ᵥ fun j => v (Sum.inr j)) =
        (lam : ℂ) * Inner (A *ᵥ fun i => u (Sum.inl i))
          (A *ᵥ fun i => v (Sum.inl i))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a'
    rw [inner_mulVec_left_rect A a (A *ᵥ a'), Matrix.mulVec_mulVec, show Aᴴ * A = 1 from hA,
      Matrix.one_mulVec]
  · intro b b'
    rw [inner_mulVec_left_rect B b (B *ᵥ b'), Matrix.mulVec_mulVec, show Bᴴ * B = 1 from hB,
      Matrix.one_mulVec]
  · intro a b
    rw [inner_mulVec_left_rect A a (B *ᵥ b), Matrix.mulVec_mulVec]
  · intro lam hl hu u v hdu hdv
    exact szegedyLemma10Pairing H I J A B lam hA hB hl hu u v hdu hdv

/-- For a normalized discriminant eigenvector with `0 ≤ lam < 1`, either transformed walk vector
has squared norm `1 - lam ^ 2`; an isometric image of a normalized source vector has squared
norm one. -/
theorem szegedyTheorem5_eigenvector_norm
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ lam : ℝ, 0 ≤ lam → lam < 1 → ∀ u : QState (I ⊕ J),
      Normalized u → bipartiteDiscriminant A B *ᵥ u = (lam : ℂ) • u →
      ∀ s : Bool,
      (∑ k, ‖bipartiteTauLinear A B lam s u k‖ ^ 2) = 1 - lam ^ 2) ∧
    (∀ a : QState I, Normalized a → (∑ k, ‖(A *ᵥ a) k‖ ^ 2) = 1) := by
  refine ⟨?_, ?_⟩
  · intro lam hl hu u hnorm hdu s
    have h := szegedyTheorem5InteriorNorm H I J A B lam hA hB hl hu u hnorm hdu s
    rw [inner_self] at h
    have h' : ((∑ k, ‖bipartiteTauLinear A B lam s u k‖ ^ 2 : ℝ) : ℂ) =
        ((1 - lam ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact h
    exact Complex.ofReal_injective h'
  · intro a hnorm
    have hinner : Inner (A *ᵥ a) (A *ᵥ a) = 1 := by
      rw [inner_mulVec_left_rect A a (A *ᵥ a), Matrix.mulVec_mulVec, show Aᴴ * A = 1 from hA,
        Matrix.one_mulVec]
      exact (normalized_iff_inner_self a).mp hnorm
    rw [inner_self] at hinner
    have h' : ((∑ k, ‖(A *ᵥ a) k‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact hinner
    simpa using! Complex.ofReal_injective h'

end Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral
