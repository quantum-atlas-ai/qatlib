/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteSpectrumConsumers
import Qatlib.Concepts.WalkSearch.FrameSpectral.BipartiteSpectralFolding
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BoundarySpectralSectors
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.FrameSpectral
open scoped ComplexOrder

namespace Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral

theorem disc_mulVec_eq_sumElim
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (u : QState (I ⊕ J)) :
    bipartiteDiscriminant A B *ᵥ u =
      Sum.elim ((Aᴴ * B) *ᵥ fun j => u (Sum.inr j))
        ((Bᴴ * A) *ᵥ fun i => u (Sum.inl i)) := by
  rw [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, add_zero, Function.comp_def]

theorem szegedyLemma8_intersection_characterization
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ w : QState H,
      (w ∈ LinearMap.range A.toLin' ∧ w ∈ LinearMap.range B.toLin') ↔
      ∃ a : QState I, ∃ b : QState J, A *ᵥ a = w ∧ B *ᵥ b = w) ∧
    (∀ a : QState I, ∀ b : QState J, A *ᵥ a = B *ᵥ b →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a) ∧
    (∀ a : QState I, ∀ b : QState J,
      A *ᵥ a = B *ᵥ b ↔
      bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a, b, ?_, ?_⟩
      · rwa [Matrix.toLin'_apply] at ha
      · rwa [Matrix.toLin'_apply] at hb
    · rintro ⟨a, b, ha, hb⟩
      exact ⟨⟨a, by rwa [Matrix.toLin'_apply]⟩, ⟨b, by rwa [Matrix.toLin'_apply]⟩⟩
  · intro a b hab
    have h := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).2 hab
    simpa [bipartiteWalk] using! h
  · intro a b
    have hiff := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).1
    rw [hiff]
    constructor
    · rintro ⟨h1, h2⟩
      rw [disc_mulVec_eq_sumElim]
      ext (i | j) <;> simp [h1, h2]
    · intro h
      rw [disc_mulVec_eq_sumElim] at h
      constructor
      · funext i
        have := congrFun h (Sum.inl i)
        simpa using! this
      · funext j
        have := congrFun h (Sum.inr j)
        simpa using! this

private noncomputable def discKerEquiv {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) :
    ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin') ≃ₗ[ℂ]
      (↥(LinearMap.ker ((Bᴴ * A).toLin')) ×
        ↥(LinearMap.ker ((Aᴴ * B).toLin'))) where
  toFun u :=
    (⟨fun i => u.1 (Sum.inl i), by
        have h := u.2
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, disc_mulVec_eq_sumElim] at h
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        funext i
        have := congrFun h (Sum.inr i)
        simpa using! this⟩,
      ⟨fun j => u.1 (Sum.inr j), by
        have h := u.2
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, disc_mulVec_eq_sumElim] at h
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        funext j
        have := congrFun h (Sum.inl j)
        simpa using! this⟩)
  invFun p :=
    ⟨Sum.elim p.1.1 p.2.1, by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, disc_mulVec_eq_sumElim]
      have h1 : (Bᴴ * A) *ᵥ p.1.1 = 0 := by
        have := p.1.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have h2 : (Aᴴ * B) *ᵥ p.2.1 = 0 := by
        have := p.2.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      funext x
      cases x with
      | inl i => simpa only [Sum.elim_inl, Pi.zero_apply] using! congrFun h2 i
      | inr j => simpa only [Sum.elim_inr, Pi.zero_apply] using! congrFun h1 j⟩
  left_inv u := by
    apply Subtype.ext
    funext x
    cases x <;> simp
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> funext x <;> simp
  map_add' u v := by
    apply Prod.ext <;> apply Subtype.ext <;> funext x <;> simp
  map_smul' c u := by
    apply Prod.ext <;> apply Subtype.ext <;> funext x <;> simp

theorem finrank_ker_bipartiteDiscriminant
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) :
    Module.finrank ℂ ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin') =
      Fintype.card I + Fintype.card J - 2 * Matrix.rank (Aᴴ * B) := by
  rw [(discKerEquiv A B).finrank_eq, Module.finrank_prod]
  have hI := LinearMap.finrank_range_add_finrank_ker (Bᴴ * A).toLin'
  have hJ := LinearMap.finrank_range_add_finrank_ker (Aᴴ * B).toLin'
  rw [Matrix.toLin'_apply'] at hI hJ
  change (Bᴴ * A).rank + Module.finrank ℂ ↥(LinearMap.ker (Bᴴ * A).toLin') =
    Module.finrank ℂ (QState I) at hI
  change (Aᴴ * B).rank + Module.finrank ℂ ↥(LinearMap.ker (Aᴴ * B).toLin') =
    Module.finrank ℂ (QState J) at hJ
  rw [Module.finrank_pi] at hI hJ
  have hrank : (Bᴴ * A).rank = (Aᴴ * B).rank := by
    rw [← Matrix.rank_conjTranspose (Bᴴ * A), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  omega

theorem szegedyLemma9_multiplicity
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ s : Bool,
      Module.finrank ℂ ↥(LinearMap.ker
          ((bipartiteWalk A B - bipartitePhase lam s •
            (1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B - (lam : ℂ) •
          (1 : Matrix (I ⊕ J) (I ⊕ J) ℂ)).toLin'))) ∧
    Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteWalk A B + 1).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin') := by
  refine ⟨?_, ?_⟩
  · intro lam hl hu s
    exact (bipartite_busy_phase_fold_multiplicity H I J A B lam hA hB hl hu s).1
  · rw [(bipartite_busy_idle_multiplicity H I J A B hA hB).2.1,
      finrank_ker_bipartiteDiscriminant A B]

end Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral
