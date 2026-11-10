/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.GraphLaplacian
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
  (rankOneProjector rankOneProjector_mulVec rankOneProjector_isHermitian)
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults

abbrev LatticeVertex (d n : ℕ) := Fin d → Fin n

def latticeGraph (d n : ℕ) : SimpleGraph (LatticeVertex d n) where
  Adj x y := ∃ j : Fin d, x j ≠ y j ∧ ∀ i : Fin d, i ≠ j → x i = y i
  symm := ⟨by
    intro x y h
    obtain ⟨j, hj, hrest⟩ := h
    exact ⟨j, fun hxy => hj hxy.symm, fun i hi => (hrest i hi).symm⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨j, hj, _⟩ := h
    exact hj rfl⟩

noncomputable instance latticeGraphDecidableRel (d n : ℕ) :
    DecidableRel (latticeGraph d n).Adj := Classical.decRel _

noncomputable def latticeLapC (d n : ℕ) :
    Matrix (LatticeVertex d n) (LatticeVertex d n) ℂ :=
  (latticeGraph d n).lapMatrix ℂ

noncomputable def latticeUniform (d n : ℕ) : QState (LatticeVertex d n) :=
  Uniform (LatticeVertex d n)

noncomputable def searchHamiltonian (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    Matrix (LatticeVertex d n) (LatticeVertex d n) ℂ :=
  (γ : ℂ) • latticeLapC d n - rankOneProjector (Ket w)

noncomputable def successAmplitude (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) (t : ℝ) : ℂ :=
  Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ latticeUniform d n)

noncomputable def successProbability (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) (t : ℝ) : ℝ :=
  ‖successAmplitude d n γ w t‖ ^ 2

noncomputable def latticeEnergy (d n : ℕ) (m : LatticeVertex d n) : ℝ :=
  2 * ∑ j : Fin d, (1 - Real.cos (2 * Real.pi * (m j).val / (n : ℝ)))

noncomputable def fourierMode (d n : ℕ) (m : LatticeVertex d n) :
    QState (LatticeVertex d n) :=
  fun x => ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
    Complex.exp (Complex.I * ((∑ j : Fin d,
      (2 * Real.pi * (m j).val / (n : ℝ)) * (x j).val : ℝ) : ℂ))

theorem latticeLapC_isHermitian (d n : ℕ) : (latticeLapC d n).IsHermitian :=
  SimpleGraph.isHermitian_lapMatrix (G := latticeGraph d n) (R := ℂ)

theorem latticeLapC_mulVec_uniform (d n : ℕ) :
    latticeLapC d n *ᵥ latticeUniform d n = 0 := by
  have h1 : latticeUniform d n =
      ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ •
        (fun _ => (1 : ℂ)) := by
    funext x
    simp [latticeUniform, Uniform, Pi.smul_apply, smul_eq_mul]
  have hfree : latticeLapC d n *ᵥ (fun _ => (1 : ℂ)) = 0 :=
    (latticeGraph d n).lapMatrix_mulVec_one_eq_zero ℂ
  rw [h1, Matrix.mulVec_smul, hfree, smul_zero]

theorem searchHamiltonian_isHermitian (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    (searchHamiltonian d n γ w).IsHermitian := by
  unfold searchHamiltonian
  apply Matrix.IsHermitian.sub
  · exact (latticeLapC_isHermitian d n).smul
      (show IsSelfAdjoint ((γ : ℝ) : ℂ) by simp [IsSelfAdjoint])
  · exact rankOneProjector_isHermitian (Ket w)

theorem normalized_latticeUniform (d n : ℕ) (hn : 0 < n) :
    Normalized (latticeUniform d n) := by
  apply normalized_uniform
  exact Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩

theorem inner_ket_uniform (d n : ℕ) (w : LatticeVertex d n) :
    Inner (Ket w) (latticeUniform d n) =
      ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ := by
  rw [inner_apply]
  rw [Finset.sum_eq_single w]
  · simp [latticeUniform, Uniform, Ket]
  · intro b _ hb
    simp [latticeUniform, Uniform, Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem successAmplitude_zero (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    successAmplitude d n γ w 0 =
      ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ := by
  unfold successAmplitude
  rw [hamiltonianEvolution_zero, Matrix.one_mulVec, inner_ket_uniform]

theorem searchHamiltonian_mulVec_uniform (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    searchHamiltonian d n γ w *ᵥ latticeUniform d n =
      -(((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹) • Ket w := by
  unfold searchHamiltonian
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, latticeLapC_mulVec_uniform, smul_zero,
    zero_sub, rankOneProjector_mulVec, inner_ket_uniform, neg_smul]

theorem lattice_weighted_laplacian_psd (d n : ℕ) (hn : 0 < n) :
    (Qatlib.Concepts.GraphEnergy.ZeroEnergy.weightedLaplacian
      (latticeGraph d n)).PosSemidef := by
  haveI : Nonempty (LatticeVertex d n) := ⟨fun _ => ⟨0, hn⟩⟩
  exact Qatlib.Concepts.GraphLaplacian.LaplacianPsd.posSemidef_weighted
    (latticeGraph d n)

end Qatlib.Papers.SpatialSearch03.MainResults
