/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Physical

/-!
# Local interaction data with commuting groups

The structure `LocalData` records the supports, groups, Hermiticity, locality, degree, and
commutation properties of a finite interaction family. Given scalar centers satisfying a uniform
norm bound, `realize` turns these data into a physical Hamiltonian while preserving the grouped
operators and their total. See [HejaziZiniArrazola2024].

## Main statements

* `LocalData`: A finite family of Hermitian interactions supported on at most `k` sites, with at
  most `d` interactions incident to any site and pairwise commuting terms within each assigned
  group.
* `realize`: The physical Hamiltonian obtained by equipping local data with real scalar centers
  and a bound of `J / 2` on every centered term norm.
* `realize_total`: Realizing local data with scalar centers preserves the total Hamiltonian.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport

/-- A finite family of Hermitian interactions supported on at most `k` sites, with at most `d`
interactions incident to any site and pairwise commuting terms within each assigned group.
See [HejaziZiniArrazola2024]. -/
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

/-- The finite set of interaction labels assigned to group `m`. -/
def labels (h : LocalData N R M k d) (m : Fin M) : Finset (Fin R) :=
    Finset.univ.filter (fun i => h.group i=m)

/-- The sum of the interactions whose labels belong to group `m`. -/
def grouped (h : LocalData N R M k d) (m : Fin M) := ∑ i ∈ h.labels m, h.term i

/-- The sum of the grouped interaction matrices. -/
def total (h : LocalData N R M k d) := ∑ m, h.grouped m

/-- The physical Hamiltonian obtained by equipping local data with real scalar centers and a
bound of `J / 2` on every centered term norm. -/
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

/-- Realizing local data with scalar centers preserves every grouped Hamiltonian. -/
theorem realize_grouped (h : LocalData N R M k d) (J : ℝ) (center : Fin R → ℝ)
    (hs : ∀ i, ‖h.term i-(center i : ℂ) • 1‖ ≤ J/2) (m : Fin M) :
    (h.realize J center hs).grouped m=h.grouped m := rfl

/-- Realizing local data with scalar centers preserves the total Hamiltonian. -/
theorem realize_total (h : LocalData N R M k d) (J : ℝ) (center : Fin R → ℝ)
    (hs : ∀ i, ‖h.term i-(center i : ℂ) • 1‖ ≤ J/2) :
    (h.realize J center hs).total=h.total := rfl
end LocalData
end Qatlib.Papers.LowEnergyProd24.LocalModel
