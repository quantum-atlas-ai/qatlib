/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Physical
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel.PhysicalHamiltonian
variable {N R M k d : ℕ} {J : ℝ}

def directBudget (h : PhysicalHamiltonian N R M k d J) : ℝ := 2*∑ i, ‖h.term i‖

theorem directBudget_term (h : PhysicalHamiltonian N R M k d J) (i : Fin R) :
    ‖h.term i‖ ≤ h.directBudget/2 := by
  have hi : ‖h.term i‖ ≤ ∑ j, ‖h.term j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (h.term j)) (Finset.mem_univ i)
  convert hi using 1
  unfold directBudget
  ring

def asBounded (h : PhysicalHamiltonian N R M k d J) : Hamiltonian N R M k d h.directBudget where
  term := h.term
  support := h.support
  group := h.group
  supported := h.supported
  hermitian := h.hermitian
  locality := h.locality
  degree := h.degree
  strength := h.directBudget_term

theorem asBounded_grouped (h : PhysicalHamiltonian N R M k d J) (m : Fin M) :
    h.asBounded.grouped m=h.grouped m := rfl

theorem asBounded_total (h : PhysicalHamiltonian N R M k d J) : h.asBounded.total=h.total := rfl
end Qatlib.Papers.LowEnergyProd24.LocalModel.PhysicalHamiltonian
