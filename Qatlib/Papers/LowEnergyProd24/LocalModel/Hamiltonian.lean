/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TensorSupport
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Compression

/-!
# Bounded local Hamiltonian data

The structure `Hamiltonian` records Hermitian interactions with explicit supports, group labels,
locality, site degree, and a uniform norm bound. The module forms grouped and total
Hamiltonians, bounds the number of neighboring interactions, and controls low-energy compression
of positive semidefinite groups. See [HejaziZiniArrazola2024].

## Main statements

* `Hamiltonian`: A finite family of Hermitian interaction matrices with group labels, supports
  of size at most `k`, at most `d` incident interactions per site, and term norms at most `J /
  2`.
* `actual_psd_group_cutoff`: If every local term is positive semidefinite and `Λ ≥ 0`,
  compressing a grouped Hamiltonian to total energies at most `Λ` gives an operator of norm at
  most `Λ`.
* `neighbors_card`: The number of interactions whose supports meet `s` is at most `s.card * d`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

/-- The computational basis of an `N`-qubit register, represented by Boolean functions on `Fin
N`. -/
abbrev Register (N : ℕ) := Fin N→Bool

/-- A finite family of Hermitian interaction matrices with group labels, supports of size at
most `k`, at most `d` incident interactions per site, and term norms at most `J / 2`. -/
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

/-- The set of local interaction labels assigned to group `m`. -/
def labels (h : Hamiltonian N R M k d J) (m : Fin M) : Finset (Fin R) :=
    Finset.univ.filter (fun i=>h.group i=m)

/-- The sum of the local interaction terms assigned to group `m`. -/
def grouped (h : Hamiltonian N R M k d J) (m : Fin M) : Matrix (Register N) (Register N) ℂ :=
    ∑i∈h.labels m,h.term i

/-- The sum of all grouped Hamiltonians. -/
def total (h : Hamiltonian N R M k d J) : Matrix (Register N) (Register N) ℂ := ∑m,h.grouped m

/-- Each grouped Hamiltonian is Hermitian. -/
theorem grouped_hermitian (h : Hamiltonian N R M k d J) (m : Fin M) : (h.grouped m).IsHermitian := by
  change (∑i∈h.labels m,h.term i)ᴴ=∑i∈h.labels m,h.term i
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _=>h.hermitian i)

/-- The total Hamiltonian is Hermitian. -/
theorem total_hermitian (h : Hamiltonian N R M k d J) : h.total.IsHermitian := by
  change (∑m,h.grouped m)ᴴ=∑m,h.grouped m
  simp only [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun m _=>h.grouped_hermitian m)

/-- If every local term is positive semidefinite, every grouped Hamiltonian is positive
semidefinite. -/
theorem grouped_psd (h : Hamiltonian N R M k d J) (hp : ∀i,(h.term i).PosSemidef) (m : Fin M) : (h.grouped m).PosSemidef := by
  exact Matrix.posSemidef_sum (h.labels m) (fun i _=>hp i)

/-- If every local term is positive semidefinite and `Λ ≥ 0`, compressing a grouped Hamiltonian
to total energies at most `Λ` gives an operator of norm at most `Λ`. -/
theorem actual_psd_group_cutoff (h : Hamiltonian N R M k d J) (hp : ∀i,(h.term i).PosSemidef)
    (m : Fin M) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    let hT := Matrix.posSemidef_sum Finset.univ (fun j _=>h.grouped_psd hp j)
    ‖low h.total hT.isHermitian Λ*h.grouped m*low h.total hT.isHermitian Λ‖ ≤ Λ :=
  psd_group_compression h.grouped (h.grouped_psd hp) m Λ hΛ

/-- The set of interaction labels whose supports meet the site set `s`. -/
def neighbors (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) : Finset (Fin R) :=
  Finset.univ.filter (fun i=>¬Disjoint (h.support i) s)

/-- The interaction neighbors of `s` are the union, over its sites, of the interactions
containing that site. -/
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

/-- The number of interactions whose supports meet `s` is at most `s.card * d`. -/
theorem neighbors_card (h : Hamiltonian N R M k d J) (s : Finset (Fin N)) :
    (h.neighbors s).card ≤ s.card*d := by
  rw [neighbors_eq_union]
  calc
    _ ≤ ∑x∈s,((Finset.univ:Finset (Fin R)).filter (fun i=>x∈h.support i)).card := Finset.card_biUnion_le
    _ ≤ ∑_x∈s,d := Finset.sum_le_sum (fun x _=>h.degree x)
    _=s.card*d := by simp

/-- An interaction outside the neighbors of `s` commutes with every matrix supported on `s`. -/
theorem nonneighbor_commute (h : Hamiltonian N R M k d J) (s : Finset (Fin N))
    (B : Matrix (Register N) (Register N) ℂ) (hB : B∈onSupport s) (i : Fin R)
    (hi : i∉h.neighbors s) : Commute (h.term i) B := by
  have hd : Disjoint (h.support i) s := by simpa [neighbors] using hi
  exact disjoint_commute hd (h.term i) B (h.supported i) hB

end Hamiltonian
end Qatlib.Papers.LowEnergyProd24.LocalModel
