/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BoundarySpectralSectors
import Qatlib.Concepts.WalkSearch.FrameSpectral.StationaryFixpointSubgoalQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.WalkSearch.FrameSpectral

namespace Qatlib.Concepts.WalkSearch.Spectral.TheoremOneSource

theorem source_theorem_one_spectral
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) :
    (∀ (a : QState I) (b : QState J), A *ᵥ a = B *ᵥ b →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a ∧
      bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a b) ∧
    (∀ (a : QState I) (b : QState J) (lam : ℝ), 0 < lam → lam < 1 →
      Normalized (Sum.elim a b) → (Aᴴ * B) *ᵥ b = (lam : ℂ) • a →
      (Bᴴ * A) *ᵥ a = (lam : ℂ) • b →
      ∀ s : Bool, bipartiteWalk A B *ᵥ bipartiteTau A B a b lam s =
        bipartitePhase lam s • bipartiteTau A B a b lam s) ∧
    (∀ v : QState (I ⊕ J), bipartiteDiscriminant A B *ᵥ v = 0 →
      bipartiteWalk A B *ᵥ (bipartiteTilde A B *ᵥ v) = -(bipartiteTilde A B *ᵥ v)) := by
  have hrow1 : ∀ (a : QState I) (b : QState J), A *ᵥ a = B *ᵥ b →
      bipartiteWalk A B *ᵥ (A *ᵥ a) = A *ᵥ a ∧
      bipartiteDiscriminant A B *ᵥ Sum.elim a b = Sum.elim a b := by
    intro a b hab
    obtain ⟨h1, h2⟩ := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).1.mp hab
    refine ⟨?_, ?_⟩
    · have hfix := (two_isometry_intersection_gram_and_fixed I J H A B a b hA hB).2 hab
      simpa only [bipartiteWalk] using! hfix
    · have hd : bipartiteDiscriminant A B *ᵥ Sum.elim a b =
          Sum.elim ((Aᴴ * B) *ᵥ b) ((Bᴴ * A) *ᵥ a) := by
        simp only [bipartiteDiscriminant, Matrix.fromBlocks_mulVec,
          Matrix.zero_mulVec, zero_add, add_zero]
        rfl
      rw [hd, h1, h2]
  have hrow2 : ∀ (a : QState I) (b : QState J) (lam : ℝ), 0 < lam → lam < 1 →
      Normalized (Sum.elim a b) → (Aᴴ * B) *ᵥ b = (lam : ℂ) • a →
      (Bᴴ * A) *ᵥ a = (lam : ℂ) • b →
      ∀ s : Bool, bipartiteWalk A B *ᵥ bipartiteTau A B a b lam s =
        bipartitePhase lam s • bipartiteTau A B a b lam s := by
    intro a b lam hl hl1 hn hab hba s
    exact (bipartite_normalized_tau_pair H I J A B a b lam hA hB hl hl1 hn hab hba s).2.1
  have hrow4 : ∀ v : QState (I ⊕ J), bipartiteDiscriminant A B *ᵥ v = 0 →
      bipartiteWalk A B *ᵥ (bipartiteTilde A B *ᵥ v) = -(bipartiteTilde A B *ᵥ v) :=
    fun v hv => (bipartite_endpoint_kernel_transport H I J A B v hA hB).2.2 hv
  exact ⟨hrow1, hrow2, hrow4⟩

theorem source_lemma_one_uniform_fixpoint
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P) (hsym : ∀ i j, P i j = P j i) :
    Normalized (SzegedyIsometry P *ᵥ (fun _ => (Real.sqrt (Fintype.card I : ℝ) : ℂ)⁻¹)) ∧
    SzegedyWalk P *ᵥ (SzegedyIsometry P *ᵥ (fun _ => (Real.sqrt (Fintype.card I : ℝ) : ℂ)⁻¹)) =
      SzegedyIsometry P *ᵥ (fun _ => (Real.sqrt (Fintype.card I : ℝ) : ℂ)⁻¹) := by
  have hcard : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hπnn : ∀ x : I, 0 ≤ (1 / (Fintype.card I : ℝ)) := fun _ => by positivity
  have hπsum : (∑ _ : I, (1 / (Fintype.card I : ℝ))) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hrev : IsReversible P (fun _ => 1 / (Fintype.card I : ℝ)) := by
    intro x y
    simp only
    rw [hsym x y]
  have hstat := stationaryFixpointSubgoal I P hP
    (fun _ => 1 / (Fintype.card I : ℝ)) hπnn hπsum hrev
  have hu : SzegedyIsometry P *ᵥ (fun _ => (Real.sqrt (Fintype.card I : ℝ) : ℂ)⁻¹)
      = SzegedyEmbedState P (fun _ => 1 / (Fintype.card I : ℝ)) := by
    unfold SzegedyEmbedState
    congr 1
    funext x
    rw [one_div, Real.sqrt_inv, Complex.ofReal_inv]
  rw [hu]
  exact hstat

end Qatlib.Concepts.WalkSearch.Spectral.TheoremOneSource
