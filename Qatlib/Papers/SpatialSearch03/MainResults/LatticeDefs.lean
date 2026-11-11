/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.GraphLaplacian
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Finite coordinate graphs and search Hamiltonians

This module defines finite vertex tuples, the graph joining tuples that differ in exactly one
coordinate, and its complex Laplacian. It introduces the uniform state and marked-vertex search
Hamiltonian for the spatial-search formalization of [ChildsGoldstone2004], together with success
amplitudes, a cosine energy expression, and Fourier-mode coordinates.

The main statements establish Hermiticity, normalization, the action on the uniform state, and
positivity of the associated weighted Laplacian.

## Main statements

* `searchHamiltonian_mulVec_uniform`: The search Hamiltonian sends the uniform state to minus
  the marked basis state scaled by the inverse square root of the vertex count.
* `lattice_weighted_laplacian_psd`: For positive `n`, the weighted Laplacian associated with the
  coordinate graph is positive semidefinite.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
  (rankOneProjector rankOneProjector_mulVec rankOneProjector_isHermitian)
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults

/-- A `d`-coordinate vertex whose coordinates lie in `Fin n`. -/
abbrev LatticeVertex (d n : ℕ) := Fin d → Fin n

/-- The simple graph in which two vertices are adjacent exactly when they differ in one
coordinate and agree in all others. -/
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

/-- The complex graph Laplacian matrix of `latticeGraph d n`. -/
noncomputable def latticeLapC (d n : ℕ) :
    Matrix (LatticeVertex d n) (LatticeVertex d n) ℂ :=
  (latticeGraph d n).lapMatrix ℂ

/-- The uniform complex state on the finite vertex type `LatticeVertex d n`. -/
noncomputable def latticeUniform (d n : ℕ) : QState (LatticeVertex d n) :=
  Uniform (LatticeVertex d n)

/-- The real-scaled complex graph Laplacian minus the rank-one projector onto the marked basis
state `Ket w`. -/
noncomputable def searchHamiltonian (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    Matrix (LatticeVertex d n) (LatticeVertex d n) ℂ :=
  (γ : ℂ) • latticeLapC d n - rankOneProjector (Ket w)

/-- The amplitude at the marked vertex after Hamiltonian evolution of the uniform state for time
`t`. -/
noncomputable def successAmplitude (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) (t : ℝ) : ℂ :=
  Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ latticeUniform d n)

/-- The squared norm of the marked-vertex success amplitude. -/
noncomputable def successProbability (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) (t : ℝ) : ℝ :=
  ‖successAmplitude d n γ w t‖ ^ 2

/-- Twice the sum over coordinates of `1 - cos (2π * (m j).val / n)`. -/
noncomputable def latticeEnergy (d n : ℕ) (m : LatticeVertex d n) : ℝ :=
  2 * ∑ j : Fin d, (1 - Real.cos (2 * Real.pi * (m j).val / (n : ℝ)))

/-- The complex exponential mode with coordinate phases `2π * (m j).val / n` and prefactor equal
to the inverse square root of the vertex count. -/
noncomputable def fourierMode (d n : ℕ) (m : LatticeVertex d n) :
    QState (LatticeVertex d n) :=
  fun x => ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
    Complex.exp (Complex.I * ((∑ j : Fin d,
      (2 * Real.pi * (m j).val / (n : ℝ)) * (x j).val : ℝ) : ℂ))

/-- The complex Laplacian of the coordinate graph is Hermitian. -/
theorem latticeLapC_isHermitian (d n : ℕ) : (latticeLapC d n).IsHermitian :=
  SimpleGraph.isHermitian_lapMatrix (G := latticeGraph d n) (R := ℂ)

/-- The complex coordinate-graph Laplacian annihilates the uniform state. -/
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

/-- The marked-vertex search Hamiltonian is Hermitian for every real `γ`. -/
theorem searchHamiltonian_isHermitian (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    (searchHamiltonian d n γ w).IsHermitian := by
  unfold searchHamiltonian
  apply Matrix.IsHermitian.sub
  · exact (latticeLapC_isHermitian d n).smul
      (show IsSelfAdjoint ((γ : ℝ) : ℂ) by simp [IsSelfAdjoint])
  · exact rankOneProjector_isHermitian (Ket w)

/-- The uniform lattice state is normalized when `n` is positive. -/
theorem normalized_latticeUniform (d n : ℕ) (hn : 0 < n) :
    Normalized (latticeUniform d n) := by
  apply normalized_uniform
  exact Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩

/-- The overlap of any vertex basis state with the uniform state is the inverse square root of
the vertex count. -/
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

/-- At time zero, the marked-vertex success amplitude is the inverse square root of the vertex
count. -/
theorem successAmplitude_zero (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    successAmplitude d n γ w 0 =
      ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ := by
  unfold successAmplitude
  rw [hamiltonianEvolution_zero, Matrix.one_mulVec, inner_ket_uniform]

/-- The search Hamiltonian sends the uniform state to minus the marked basis state scaled by the
inverse square root of the vertex count. -/
theorem searchHamiltonian_mulVec_uniform (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    searchHamiltonian d n γ w *ᵥ latticeUniform d n =
      -(((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹) • Ket w := by
  unfold searchHamiltonian
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, latticeLapC_mulVec_uniform, smul_zero,
    zero_sub, rankOneProjector_mulVec, inner_ket_uniform, neg_smul]

/-- For positive `n`, the weighted Laplacian associated with the coordinate graph is positive
semidefinite. -/
theorem lattice_weighted_laplacian_psd (d n : ℕ) (hn : 0 < n) :
    (Qatlib.Concepts.GraphEnergy.ZeroEnergy.weightedLaplacian
      (latticeGraph d n)).PosSemidef := by
  haveI : Nonempty (LatticeVertex d n) := ⟨fun _ => ⟨0, hn⟩⟩
  exact Qatlib.Concepts.GraphLaplacian.LaplacianPsd.posSemidef_weighted
    (latticeGraph d n)

end Qatlib.Papers.SpatialSearch03.MainResults
