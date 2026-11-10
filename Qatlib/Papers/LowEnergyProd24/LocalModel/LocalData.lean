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
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport

structure LocalData (N R M k d : ℕ) where
  term : Fin R → Matrix (Register N) (Register N) ℂ
  support : Fin R → Finset (Fin N)
  group : Fin R → Fin M
  supported : ∀ i, term i ∈ onSupport (support i)
  hermitian : ∀ i, (term i).IsHermitian
  locality : ∀ i, (support i).card ≤ k
  degree : ∀ x, ((Finset.univ : Finset (Fin R)).filter (fun i => x ∈ support i)).card ≤ d
  commuting : ∀ i j, group i=group j → Commute (term i) (term j)

namespace LocalData
variable {N R M k d : ℕ}

def labels (h : LocalData N R M k d) (m : Fin M) : Finset (Fin R) :=
    Finset.univ.filter (fun i => h.group i=m)

def grouped (h : LocalData N R M k d) (m : Fin M) := ∑ i ∈ h.labels m, h.term i

def total (h : LocalData N R M k d) := ∑ m, h.grouped m

def realize (h : LocalData N R M k d) (J : ℝ) (center : Fin R → ℝ)
    (hstrength : ∀ i, ‖h.term i-(center i : ℂ) • 1‖ ≤ J/2) : PhysicalHamiltonian N R M k d J where
  term := h.term
  support := h.support
  group := h.group
  supported := h.supported
  hermitian := h.hermitian
  locality := h.locality
  degree := h.degree
  center := center
  centered_strength := hstrength

theorem realize_grouped (h : LocalData N R M k d) (J : ℝ) (center : Fin R → ℝ)
    (hs : ∀ i, ‖h.term i-(center i : ℂ) • 1‖ ≤ J/2) (m : Fin M) :
    (h.realize J center hs).grouped m=h.grouped m := rfl

theorem realize_total (h : LocalData N R M k d) (J : ℝ) (center : Fin R → ℝ)
    (hs : ∀ i, ‖h.term i-(center i : ℂ) • 1‖ ≤ J/2) :
    (h.realize J center hs).total=h.total := rfl
end LocalData
end Qatlib.Papers.LowEnergyProd24.LocalModel
