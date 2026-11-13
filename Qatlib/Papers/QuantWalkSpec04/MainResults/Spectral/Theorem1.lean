/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteSpectrumConsumers
import Qatlib.Concepts.WalkSearch.TauEmbedding.BipartiteTauCorrespondence
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BoundarySpectralSectors
import Qatlib.Concepts.WalkSearch.FrameSpectral.BipartiteSpectralFolding

/-!
# Spectral structure of the bipartite walk

This module assembles the spectral description of the product of two reflections on their
combined range. `szegedyTheorem1_eigenstructure` supplies an orthonormal eigenbasis, transformed
discriminant eigenvectors, and the endpoint eigenvalue dimension identities. See [Szegedy2004].

## Main statements

* `szegedyTheorem1_eigenstructure`: For two isometries, the bipartite walk has an orthonormal
  eigenbasis on their combined range with eigenvalues among one, minus one, and `bipartitePhase
  lam s` for `0 < lam < 1`, together with the stated eigenvector and multiplicity identities.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.TauEmbedding
open scoped ComplexOrder

namespace Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral

/-- The bipartite discriminant acts on a sum indexed vector by the two cross Gram matrices. -/
private theorem theorem1_disc_mulVec_eq_sumElim
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (u : QState (I ⊕ J)) :
    bipartiteDiscriminant A B *ᵥ u =
      Sum.elim ((Aᴴ * B) *ᵥ fun j => u (Sum.inr j))
        ((Bᴴ * A) *ᵥ fun i => u (Sum.inl i)) := by
  rw [bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, add_zero, Function.comp_def]

/-- The discriminant kernel is linearly equivalent to the product of the two cross Gram kernels. -/
private noncomputable def theorem1_discKerEquiv {H I J : Type} [Fintype H]
    [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) :
    ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin') ≃ₗ[ℂ]
      (↥(LinearMap.ker ((Bᴴ * A).toLin')) ×
        ↥(LinearMap.ker ((Aᴴ * B).toLin'))) where
  toFun u :=
    (⟨fun i => u.1 (Sum.inl i), by
        have h := u.2
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, theorem1_disc_mulVec_eq_sumElim] at h
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        funext i
        have := congrFun h (Sum.inr i)
        simpa using! this⟩,
      ⟨fun j => u.1 (Sum.inr j), by
        have h := u.2
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, theorem1_disc_mulVec_eq_sumElim] at h
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        funext j
        have := congrFun h (Sum.inl j)
        simpa using! this⟩)
  invFun p :=
    ⟨Sum.elim p.1.1 p.2.1, by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, theorem1_disc_mulVec_eq_sumElim]
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

/-- The discriminant kernel dimension equals `card I + card J - 2 * rank (Aᴴ * B)`. -/
private theorem theorem1_finrank_ker_discriminant
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) :
    Module.finrank ℂ ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin') =
      Fintype.card I + Fintype.card J - 2 * Matrix.rank (Aᴴ * B) := by
  rw [(theorem1_discKerEquiv A B).finrank_eq, Module.finrank_prod]
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

/-- For two isometries, the bipartite walk has an orthonormal eigenbasis on their combined range
with eigenvalues among one, minus one, and `bipartitePhase lam s` for `0 < lam < 1`,
together with the stated eigenvector and multiplicity identities. -/
theorem szegedyTheorem1_eigenstructure
    {H I J : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∃ (m : ℕ) (V : Matrix H (Fin m) ℂ) (z : Fin m → ℂ),
      IsIsometry V ∧
      V * Vᴴ = bipartiteTilde A B * matrixPseudoinverse (bipartiteTilde A B) ∧
      bipartiteWalk A B * V = V * Matrix.diagonal z ∧
      m = Matrix.rank (bipartiteTilde A B) ∧
      ∀ i, z i = 1 ∨ z i = -1 ∨
        ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
          (z i = bipartitePhase lam true ∨ z i = bipartitePhase lam false)) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 → ∀ s : Bool, ∀ u : QState (I ⊕ J),
      bipartiteDiscriminant A B *ᵥ u = (lam : ℂ) • u →
      bipartiteWalk A B *ᵥ bipartiteTauLinear A B lam s u =
        bipartitePhase lam s • bipartiteTauLinear A B lam s u ∧
      bipartiteTauLinear A B lam s u ∈
        LinearMap.range (bipartiteTilde A B).toLin') ∧
    (∀ a : QState I, ∀ b : QState J, A *ᵥ a = B *ᵥ b →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a) ∧
    (∀ a : QState I, ∀ b : QState J,
      bipartiteDiscriminant A B *ᵥ Sum.elim a b = 0 →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = -(A *ᵥ a) ∧
      bipartiteWalk A B *ᵥ (B *ᵥ b) = -(B *ᵥ b)) ∧
    (Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B - 1).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B - (1 : Matrix (I ⊕ J) (I ⊕ J) ℂ)).toLin'))) ∧
    (Module.finrank ℂ ↥(LinearMap.ker ((bipartiteWalk A B + 1).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') =
      Module.finrank ℂ ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bipartite_complete_busy_spectral_frame H I J A B hA hB
  · intro lam hl hu s u hdu
    obtain ⟨e, he⟩ :=
      (bipartite_tau_eigenspace_pair_equivalence H I J A B lam hA hB hl hu).2.1 s
    have huK : u ∈ LinearMap.ker
        ((bipartiteDiscriminant A B - (lam : ℂ) •
          (1 : Matrix (I ⊕ J) (I ⊕ J) ℂ)).toLin') := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hdu, sub_self]
    let uK : ↥(LinearMap.ker
        ((bipartiteDiscriminant A B - (lam : ℂ) •
          (1 : Matrix (I ⊕ J) (I ⊕ J) ℂ)).toLin')) := ⟨u, huK⟩
    have hmem := (e uK).2
    rw [Submodule.mem_inf] at hmem
    have hval : (e uK).1 = bipartiteTauLinear A B lam s u := by
      have := he uK
      simpa using! this
    constructor
    · have hk := hmem.1
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec] at hk
      rw [← hval]
      exact sub_eq_zero.mp hk
    · rw [← hval]
      exact hmem.2
  · intro a b hab
    have h := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).2 hab
    simpa [bipartiteWalk] using! h
  · intro a b hd
    rw [theorem1_disc_mulVec_eq_sumElim] at hd
    have hXb : (Aᴴ * B) *ᵥ b = 0 := by
      funext i
      have := congrFun hd (Sum.inl i)
      simpa using! this
    have hYa : (Bᴴ * A) *ᵥ a = 0 := by
      funext j
      have := congrFun hd (Sum.inr j)
      simpa using! this
    constructor
    · have hdA : bipartiteDiscriminant A B *ᵥ Sum.elim a (0 : QState J) = 0 := by
        rw [theorem1_disc_mulVec_eq_sumElim]
        have h1 : (fun j => (Sum.elim a (0 : QState J)) (Sum.inr j)) = (0 : QState J) := rfl
        have h2 : (fun i => (Sum.elim a (0 : QState J)) (Sum.inl i)) = a := rfl
        rw [h1, h2, hYa, Matrix.mulVec_zero]
        funext x
        cases x <;> rfl
      have h := (bipartite_endpoint_kernel_transport H I J A B
        (Sum.elim a (0 : QState J)) hA hB).2.2 hdA
      simpa only [bipartiteTilde, Matrix.fromCols_mulVec_sumElim,
        Matrix.mulVec_zero, add_zero] using! h
    · have hdB : bipartiteDiscriminant A B *ᵥ Sum.elim (0 : QState I) b = 0 := by
        rw [theorem1_disc_mulVec_eq_sumElim]
        have h1 : (fun j => (Sum.elim (0 : QState I) b) (Sum.inr j)) = b := rfl
        have h2 : (fun i => (Sum.elim (0 : QState I) b) (Sum.inl i)) = (0 : QState I) := rfl
        rw [h1, h2, hXb, Matrix.mulVec_zero]
        funext x
        cases x <;> rfl
      have h := (bipartite_endpoint_kernel_transport H I J A B
        (Sum.elim (0 : QState I) b) hA hB).2.2 hdB
      simpa only [bipartiteTilde, Matrix.fromCols_mulVec_sumElim,
        Matrix.mulVec_zero, zero_add] using! h
  · rw [(bipartite_busy_idle_multiplicity H I J A B hA hB).1,
      (bipartite_frame_kernel_and_endpoint_source_dimensions H I J A B hA hB).2.1]
  · rw [(bipartite_busy_idle_multiplicity H I J A B hA hB).2.1,
      theorem1_finrank_ker_discriminant A B]

end Qatlib.Papers.QuantWalkSpec04.MainResults.Spectral
