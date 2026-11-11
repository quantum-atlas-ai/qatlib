/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma4FrameReflectionQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma5NormBoundQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma6BlockActionQuan
import Qatlib.Concepts.WalkSearch.FrameSpectral.SzegedyLemma7EigenSymmetryQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyLemma10PairingQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormQuan
import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteSpectrumConsumers

/-!
# Source lemmas for bipartite walk spectra

This module collects frame and discriminant statements supporting the bipartite spectral
analysis of [Szegedy2004]. It treats orthogonal frame projections, contraction and block
structure of the discriminant, sign symmetry, and the relation between common frame images and
fixed points.

The later statements give multiplicities on the combined frame range, bilinear pairings for
sources at the same interior eigenvalue, and the norm of their signed τ images.

## Main statements

* `source_lemma_eight_intersection`: common-image and fixed-point characterizations.
* `source_lemma_nine_multiplicities`: endpoint and interior multiplicity formulas.
* `source_theorem_five_norm`: the squared τ-image norm `1 - lam^2`.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.WalkSearch.Spectral.SectionTwelveLemmas

/-- An orthonormal finite family defines an orthogonal projector that fixes the family and
annihilates vectors orthogonal to it; its reflection is twice the projector minus the
identity [Szegedy2004]. -/
theorem source_lemma_four_frame_reflection
    (H ι : Type) [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι]
    (v : ι → QState H)
    (hv : ∀ i j, Inner (v i) (v j) = if i = j then 1 else 0) :
    IsOrthogonalProjector (paperFrameProjection v) ∧
    (∀ l, paperFrameProjection v *ᵥ v l = v l) ∧
    (∀ w : QState H, (∀ l, Inner (v l) w = 0) → paperFrameProjection v *ᵥ w = 0) ∧
    ReflectionAbout (paperFrameProjection v) = (2 : ℂ) • paperFrameProjection v - 1 := by
  obtain ⟨hp, hfix, hkill, -, -⟩ := szegedyLemma4FrameReflection H ι v hv
  exact ⟨hp, hfix, hkill, rfl⟩

/-- For two isometric frames, the bipartite discriminant is a contraction in squared state norm,
and any fixed source has equal images under the two frames [Szegedy2004]. -/
theorem source_lemma_five_norm_bound
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ x : QState (I ⊕ J),
      ∑ p, ‖(bipartiteDiscriminant A B *ᵥ x) p‖ ^ 2 ≤ ∑ p, ‖x p‖ ^ 2) ∧
    (∀ (a : QState I) (b : QState J),
      bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a b → A *ᵥ a = B *ᵥ b) :=
  szegedyLemma5NormBound H I J A B hA hB

/-- Split a bipartite discriminant action into the two off-diagonal component actions
[Szegedy2004]. -/
theorem source_lemma_six_block_action
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (a a' : QState I) (b b' : QState J)
    (h : bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a' b') :
    bipartiteDiscriminant A B *ᵥ Sum.elim a (0 : QState J) = Sum.elim (0 : QState I) b' ∧
    bipartiteDiscriminant A B *ᵥ Sum.elim (0 : QState I) b = Sum.elim a' (0 : QState J) :=
  szegedyLemma6BlockAction H I J A B a a' b b' h

/-- Flipping the sign of one source component changes a discriminant eigenvalue from `lam` to
`-lam` [Szegedy2004]. -/
theorem source_lemma_seven_eigen_symmetry
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (v : QState (I ⊕ J)) (lam : ℝ)
    (h : bipartiteDiscriminant A B *ᵥ v = (lam : ℂ) • v) :
    bipartiteDiscriminant A B *ᵥ paperSourceFlip v = (-(lam : ℂ)) • paperSourceFlip v :=
  szegedyLemma7EigenSymmetry H I J A B v lam h

/-- For isometric frames, equality of frame images is equivalent both to the pair of cross-Gram
equations and to a discriminant fixed-point equation. Such a common image is fixed by the
bipartite walk [Szegedy2004]. -/
theorem source_lemma_eight_intersection
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ (a : QState I) (b : QState J),
      A *ᵥ a = B *ᵥ b ↔ (Aᴴ * B) *ᵥ b = a ∧ (Bᴴ * A) *ᵥ a = b) ∧
    (∀ (a : QState I) (b : QState J), A *ᵥ a = B *ᵥ b →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a) ∧
    (∀ (a : QState I) (b : QState J),
      A *ᵥ a = B *ᵥ b ↔ bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a b) := by
  have hd : ∀ (a : QState I) (b : QState J),
      bipartiteDiscriminant A B *ᵥ Sum.elim a b =
        Sum.elim ((Aᴴ * B) *ᵥ b) ((Bᴴ * A) *ᵥ a) := by
    intro a b
    simp only [bipartiteDiscriminant, Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, zero_add, add_zero]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).1
  · intro a b hab
    have hfix := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).2 hab
    simpa only [bipartiteWalk] using! hfix
  · intro a b
    constructor
    · intro hab
      obtain ⟨h1, h2⟩ := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).1.mp hab
      rw [hd, h1, h2]
    · intro hM
      have h1 : (Aᴴ * B) *ᵥ b = a := by
        have := congrArg (fun w : QState (I ⊕ J) => fun i => w (.inl i)) hM
        simpa only [hd, Sum.elim_inl] using! this
      have h2 : (Bᴴ * A) *ᵥ a = b := by
        have := congrArg (fun w : QState (I ⊕ J) => fun j => w (.inr j)) hM
        simpa only [hd, Sum.elim_inr] using! this
      exact (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).1.mpr ⟨h1, h2⟩

/-- On the combined frame range, the minus-one walk multiplicity is the sum of frame dimensions
minus twice the cross-Gram rank. For an interior positive source eigenvalue, the sum of the
two phase eigenspaces has twice the source eigenspace dimension [Szegedy2004]. -/
theorem source_lemma_nine_multiplicities
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B + 1).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') =
      Fintype.card I + Fintype.card J - 2 * Matrix.rank (Aᴴ * B) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 →
      Module.finrank ℂ ↥((LinearMap.ker
            ((bipartiteWalk A B - bipartitePhase lam true • (1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin') ⊔
        (LinearMap.ker
            ((bipartiteWalk A B - bipartitePhase lam false • (1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin')) =
        2 * Module.finrank ℂ ↥(LinearMap.ker
          ((bipartiteDiscriminant A B - (lam : ℂ) • (1 : Matrix (I ⊕ J) (I ⊕ J) ℂ)).toLin'))) := by
  refine ⟨(bipartite_busy_idle_multiplicity H I J A B hA hB).2.1, ?_⟩
  intro lam hl hl1
  exact (bipartite_tau_eigenspace_pair_equivalence H I J A B lam hA hB hl hl1).2.2

/-- Isometric frames preserve their respective inner products and express cross pairings through
the cross Gram matrix. Two sources at the same interior positive discriminant eigenvalue
have equal component pairings and the stated eigenvalue-scaled cross pairing [Szegedy2004]. -/
theorem source_lemma_ten_inner_products
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ (a a' : QState I), Inner (A *ᵥ a) (A *ᵥ a') = Inner a a') ∧
    (∀ (b b' : QState J), Inner (B *ᵥ b) (B *ᵥ b') = Inner b b') ∧
    (∀ (a : QState I) (b : QState J), Inner (A *ᵥ a) (B *ᵥ b) = Inner a ((Aᴴ * B) *ᵥ b)) ∧
    (∀ (lam : ℝ) (u v : QState (I ⊕ J)), 0 < lam → lam < 1 →
      bipartiteDiscriminant A B *ᵥ u = (lam : ℂ) • u →
      bipartiteDiscriminant A B *ᵥ v = (lam : ℂ) • v →
      Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => v (.inl i)) =
        Inner (B *ᵥ fun j => u (.inr j)) (B *ᵥ fun j => v (.inr j)) ∧
      Inner (A *ᵥ fun i => u (.inl i)) (B *ᵥ fun j => v (.inr j)) =
        (lam : ℂ) * Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => v (.inl i))) := by
  have hAA : Aᴴ * A = 1 := hA
  have hBB : Bᴴ * B = 1 := hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a'
    rw [inner_mulVec_left_rect A a (A *ᵥ a'), Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  · intro b b'
    rw [inner_mulVec_left_rect B b (B *ᵥ b'), Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  · intro a b
    rw [inner_mulVec_left_rect A a (B *ᵥ b), ← Matrix.mulVec_mulVec]
  · intro lam u v hl hl1 hu hv
    exact szegedyLemma10Pairing H I J A B lam hA hB hl hl1 u v hu hv

/-- The signed τ image of a normalized discriminant source with `0 ≤ lam < 1` has
self-inner-product `1 - lam^2`; an isometric image of a normalized left source has
self-inner-product one [Szegedy2004]. -/
theorem source_theorem_five_norm
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ (lam : ℝ) (u : QState (I ⊕ J)), 0 ≤ lam → lam < 1 → Normalized u →
      bipartiteDiscriminant A B *ᵥ u = (lam : ℂ) • u → ∀ s : Bool,
      Inner (bipartiteTauLinear A B lam s u) (bipartiteTauLinear A B lam s u) =
        ((1 - lam ^ 2 : ℝ) : ℂ)) ∧
    (∀ a : QState I, Normalized a → Inner (A *ᵥ a) (A *ᵥ a) = 1) := by
  have hAA : Aᴴ * A = 1 := hA
  refine ⟨?_, ?_⟩
  · intro lam u hl hl1 hn hu s
    exact szegedyTheorem5InteriorNorm H I J A B lam hA hB hl hl1 u hn hu s
  · intro a hn
    have hin : Inner a a = 1 := (normalized_iff_inner_self a).mp hn
    rw [inner_mulVec_left_rect A a (A *ᵥ a), Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
    exact hin

end Qatlib.Concepts.WalkSearch.Spectral.SectionTwelveLemmas
