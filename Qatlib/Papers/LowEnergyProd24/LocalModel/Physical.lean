/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian

/-!
# Physical interactions with scalar centers

The structure `PhysicalHamiltonian` bounds the norms of interactions after subtracting real
scalar identity shifts. Its centered model `normalized` has bounded terms, with grouped and
total operators related by explicit scalar centers. The theorem `actual_group_psd_cutoff`
controls compression of positive semidefinite physical groups to a low-energy sector. See
[HejaziZiniArrazola2024].

## Main statements

* `normalized_grouped`: Each normalized grouped Hamiltonian equals its physical grouped
  Hamiltonian minus the group center times the identity.
* `normalized_total`: The normalized total Hamiltonian equals the physical total Hamiltonian
  minus the total center times the identity.
* `actual_group_psd_cutoff`: If every physical grouped Hamiltonian is positive semidefinite and
  `Λ ≥ 0`, its compression to the total-energy sector at most `Λ` has norm at most `Λ`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

/-- A finite family of Hermitian interactions with supports of size at most `k`, site degree at
most `d`, group labels, and real scalar centers leaving every centered term with norm at
most `J / 2`. -/
structure PhysicalHamiltonian (N R M k d : ℕ) (J : ℝ) where
  term : Fin R → Matrix (Register N) (Register N) ℂ
  support : Fin R → Finset (Fin N)
  group : Fin R → Fin M
  supported : ∀ i, term i ∈ onSupport (support i)
  hermitian : ∀ i, (term i).IsHermitian
  locality : ∀ i, (support i).card ≤ k
  degree : ∀ x, ((Finset.univ : Finset (Fin R)).filter (fun i => x ∈ support i)).card ≤ d
  center : Fin R → ℝ
  centered_strength : ∀ i, ‖term i-(center i : ℂ) • 1‖ ≤ J/2

namespace PhysicalHamiltonian
variable {N R M k d : ℕ} {J : ℝ}

/-- The bounded Hamiltonian obtained by subtracting each selected scalar center times the
identity from its physical interaction term. -/
def normalized (h : PhysicalHamiltonian N R M k d J) : Hamiltonian N R M k d J where
  term i := h.term i-(h.center i : ℂ) • 1
  support := h.support
  group := h.group
  supported i := by
    apply (onSupport (h.support i)).sub_mem (h.supported i)
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (onSupport (h.support i)).algebraMap_mem (h.center i : ℂ)
  hermitian i := by
    apply (h.hermitian i).sub
    apply Matrix.isHermitian_one.smul
    change star (h.center i : ℂ)=(h.center i : ℂ)
    exact Complex.conj_ofReal _
  locality := h.locality
  degree := h.degree
  strength := h.centered_strength

/-- The finite set of physical interaction labels assigned to group `m`. -/
def labels (h : PhysicalHamiltonian N R M k d J) (m : Fin M) : Finset (Fin R) :=
  Finset.univ.filter (fun i => h.group i=m)

/-- The sum of the original physical interactions assigned to group `m`. -/
def grouped (h : PhysicalHamiltonian N R M k d J) (m : Fin M) := ∑ i ∈ h.labels m, h.term i

/-- The sum of the original physical grouped Hamiltonians. -/
def total (h : PhysicalHamiltonian N R M k d J) := ∑ m, h.grouped m

/-- The sum of the scalar centers of the interaction terms assigned to group `m`. -/
def groupCenter (h : PhysicalHamiltonian N R M k d J) (m : Fin M) : ℝ :=
    ∑ i ∈ h.labels m, h.center i

/-- The sum of the scalar centers over all groups. -/
def totalCenter (h : PhysicalHamiltonian N R M k d J) : ℝ := ∑ m, h.groupCenter m

/-- Each original physical grouped Hamiltonian is Hermitian. -/
theorem grouped_hermitian (h : PhysicalHamiltonian N R M k d J) (m : Fin M) : (h.grouped m).IsHermitian := by
  change (∑ i ∈ h.labels m, h.term i)ᴴ=∑ i ∈ h.labels m, h.term i
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => h.hermitian i)

/-- The total original physical Hamiltonian is Hermitian. -/
theorem total_hermitian (h : PhysicalHamiltonian N R M k d J) : h.total.IsHermitian := by
  change (∑ m, h.grouped m)ᴴ=∑ m, h.grouped m
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun m _ => h.grouped_hermitian m)

/-- Each normalized grouped Hamiltonian equals its physical grouped Hamiltonian minus the group
center times the identity. -/
theorem normalized_grouped (h : PhysicalHamiltonian N R M k d J) (m : Fin M) :
    h.normalized.grouped m=h.grouped m-(h.groupCenter m : ℂ) • 1 := by
  change (∑ i ∈ h.labels m, (h.term i-(h.center i : ℂ) • 1))=_
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_smul]
  congr 1
  simp only [groupCenter, Complex.ofReal_sum]

/-- The normalized total Hamiltonian equals the physical total Hamiltonian minus the total
center times the identity. -/
theorem normalized_total (h : PhysicalHamiltonian N R M k d J) :
    h.normalized.total=h.total-(h.totalCenter : ℂ) • 1 := by
  change (∑ m, h.normalized.grouped m)=_
  simp_rw [h.normalized_grouped]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_smul]
  congr 1
  simp only [totalCenter, Complex.ofReal_sum]

/-- If every physical grouped Hamiltonian is positive semidefinite and `Λ ≥ 0`, its compression
to the total-energy sector at most `Λ` has norm at most `Λ`. See [HejaziZiniArrazola2024]. -/
theorem actual_group_psd_cutoff (h : PhysicalHamiltonian N R M k d J)
    (hp : ∀ m, (h.grouped m).PosSemidef) (m : Fin M) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ‖low h.total h.total_hermitian Λ*h.grouped m*low h.total h.total_hermitian Λ‖ ≤ Λ :=
  psd_group_compression h.grouped hp m Λ hΛ
end PhysicalHamiltonian
end Qatlib.Papers.LowEnergyProd24.LocalModel
