/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorSupport
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Compression
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

abbrev Register (N : ℕ) := Fin N→Bool

structure Hamiltonian (N R M : ℕ) (k d : ℕ) (J : ℝ) where
  term : Fin R→Matrix (Register N) (Register N) ℂ
  support : Fin R→Finset (Fin N)
  group : Fin R→Fin M
  supported : ∀i,term i∈onSupport (support i)
  hermitian : ∀i,(term i).IsHermitian
  locality : ∀i,(support i).card ≤ k
  degree : ∀x,((Finset.univ:Finset (Fin R)).filter (fun i=>x∈support i)).card ≤ d
  strength : ∀i,‖term i‖ ≤ J/2

variable {N R M k d : ℕ} {J : ℝ}
namespace Hamiltonian

def labels (h : Hamiltonian N R M k d J) (m : Fin M) : Finset (Fin R) :=
    Finset.univ.filter (fun i=>h.group i=m)

def grouped (h : Hamiltonian N R M k d J) (m : Fin M) : Matrix (Register N) (Register N) ℂ :=
    ∑i∈h.labels m,h.term i

def total (h : Hamiltonian N R M k d J) : Matrix (Register N) (Register N) ℂ := ∑m,h.grouped m

theorem grouped_hermitian (h : Hamiltonian N R M k d J) (m : Fin M) : (h.grouped m).IsHermitian := by
  change (∑i∈h.labels m,h.term i)ᴴ=∑i∈h.labels m,h.term i
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _=>h.hermitian i)

theorem total_hermitian (h : Hamiltonian N R M k d J) : h.total.IsHermitian := by
  change (∑m,h.grouped m)ᴴ=∑m,h.grouped m
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun m _=>h.grouped_hermitian m)

theorem grouped_psd (h : Hamiltonian N R M k d J) (hp : ∀i,(h.term i).PosSemidef) (m : Fin M) : (h.grouped m).PosSemidef := by
  exact Matrix.posSemidef_sum (h.labels m) (fun i _=>hp i)

theorem actual_psd_group_cutoff (h : Hamiltonian N R M k d J) (hp : ∀i,(h.term i).PosSemidef)
    (m : Fin M) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    let hT := Matrix.posSemidef_sum Finset.univ (fun j _=>h.grouped_psd hp j)
    ‖low h.total hT.isHermitian Λ*h.grouped m*low h.total hT.isHermitian Λ‖ ≤ Λ :=
  psd_group_compression h.grouped (h.grouped_psd hp) m Λ hΛ

def neighbors (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) : Finset (Fin R) :=
  Finset.univ.filter (fun i=>¬Disjoint (h.support i) s)

theorem neighbors_eq_union (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) :
    h.neighbors s=s.biUnion (fun x=>(Finset.univ:Finset (Fin R)).filter (fun i=>x∈h.support i)) := by
  ext i
  simp only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion]
  simp only [Finset.disjoint_left,not_forall,not_not]
  constructor
  · rintro ⟨x,hxi,hxs⟩
    exact ⟨x,hxs,hxi⟩
  · rintro ⟨x,hxs,hxi⟩
    exact ⟨x,hxi,hxs⟩

theorem neighbors_card (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) :
    (h.neighbors s).card ≤ s.card*d := by
  rw [neighbors_eq_union]
  calc
    _ ≤ ∑x∈s,((Finset.univ:Finset (Fin R)).filter (fun i=>x∈h.support i)).card := Finset.card_biUnion_le
    _ ≤ ∑_x∈s,d := Finset.sum_le_sum (fun x _=>h.degree x)
    _=s.card*d := by simp

theorem nonneighbor_commute (h : Hamiltonian N R M k d J) (s : Finset (Fin N))
    (B : Matrix (Register N) (Register N) ℂ) (hB : B∈onSupport s) (i : Fin R)
    (hi : i∉h.neighbors s) : Commute (h.term i) B := by
  have hd : Disjoint (h.support i) s := by simpa [neighbors] using hi
  exact disjoint_commute hd (h.term i) B (h.supported i) hB

end Hamiltonian
end Qatlib.Papers.LowEnergyProd24.LocalModel
