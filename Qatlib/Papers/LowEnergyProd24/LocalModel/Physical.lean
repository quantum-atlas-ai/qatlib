/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

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

def labels (h : PhysicalHamiltonian N R M k d J) (m : Fin M) : Finset (Fin R) :=
  Finset.univ.filter (fun i => h.group i=m)

def grouped (h : PhysicalHamiltonian N R M k d J) (m : Fin M) := ∑ i ∈ h.labels m, h.term i

def total (h : PhysicalHamiltonian N R M k d J) := ∑ m, h.grouped m

def groupCenter (h : PhysicalHamiltonian N R M k d J) (m : Fin M) : ℝ :=
    ∑ i ∈ h.labels m, h.center i

def totalCenter (h : PhysicalHamiltonian N R M k d J) : ℝ := ∑ m, h.groupCenter m

theorem grouped_hermitian (h : PhysicalHamiltonian N R M k d J) (m : Fin M) : (h.grouped m).IsHermitian := by
  change (∑ i ∈ h.labels m, h.term i)ᴴ=∑ i ∈ h.labels m, h.term i
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => h.hermitian i)

theorem total_hermitian (h : PhysicalHamiltonian N R M k d J) : h.total.IsHermitian := by
  change (∑ m, h.grouped m)ᴴ=∑ m, h.grouped m
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun m _ => h.grouped_hermitian m)

theorem normalized_grouped (h : PhysicalHamiltonian N R M k d J) (m : Fin M) :
    h.normalized.grouped m=h.grouped m-(h.groupCenter m : ℂ) • 1 := by
  change (∑ i ∈ h.labels m, (h.term i-(h.center i : ℂ) • 1))=_
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_smul]
  congr 1
  simp only [groupCenter, Complex.ofReal_sum]

theorem normalized_total (h : PhysicalHamiltonian N R M k d J) :
    h.normalized.total=h.total-(h.totalCenter : ℂ) • 1 := by
  change (∑ m, h.normalized.grouped m)=_
  simp_rw [h.normalized_grouped]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_smul]
  congr 1
  simp only [totalCenter, Complex.ofReal_sum]

theorem actual_group_psd_cutoff (h : PhysicalHamiltonian N R M k d J)
    (hp : ∀ m, (h.grouped m).PosSemidef) (m : Fin M) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ‖low h.total h.total_hermitian Λ*h.grouped m*low h.total h.total_hermitian Λ‖ ≤ Λ :=
  psd_group_compression h.grouped hp m Λ hΛ
end PhysicalHamiltonian
end Qatlib.Papers.LowEnergyProd24.LocalModel
