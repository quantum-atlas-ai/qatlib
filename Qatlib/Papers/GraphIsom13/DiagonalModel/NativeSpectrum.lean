/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.DiagonalKernels
import Qatlib.Papers.GraphIsom13.BinaryEncoding
import Qatlib.Papers.GraphIsom13.AutoEncoding

/-!
# Spectrum and ground eigenspace of the binary cost Hamiltonian

This module realizes the binary graph-isomorphism cost as the Hermitian matrix `bitHamiltonian`
and identifies its spectrum and least energy. For a graph compared with itself, the zero
eigenspace has dimension equal to the number of graph automorphisms, expressing the ground-space
correspondence in [GaitanClark2014].

## Main statements

* `bitHamiltonian_spectrum`: the spectrum is the range of the binary cost.
* `bitHamiltonian_minimum_zero`: zero minimum energy characterizes isomorphism.
* `ground_eigenspace_finrank`: the dimension of the zero eigenspace counts automorphisms.

## References

* [Gaitan and Clark, 2014][GaitanClark2014]
-/

set_option warningAsError false

namespace Qatlib.Papers.GraphIsom13.DiagonalModel
set_option autoImplicit false
noncomputable section
open Qatlib.Papers.GraphIsom13.GiCost
open Qatlib.Papers.GraphIsom13.BinaryEncoding
open Qatlib.Papers.GraphIsom13.AutoEncoding
open Qatlib.Foundations.MatrixGeometry.DiagonalKernels
variable {N : ℕ}

/-- The diagonal complex Hamiltonian with the binary graph-isomorphism costs as diagonal
entries. -/
def bitHamiltonian (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Matrix (Bits N) (Bits N) ℂ := Matrix.diagonal (fun b => (bitCost G G' b : ℂ))

/-- The binary graph-isomorphism Hamiltonian is Hermitian. -/
theorem bitHamiltonian_hermitian (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : (bitHamiltonian G G').IsHermitian :=
  cost_hermitian _

/-- Each Boolean-register basis vector is an eigenvector with eigenvalue equal to its binary
cost. -/
theorem bitHamiltonian_basis (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (b : Bits N) :
    (bitHamiltonian G G').mulVec (Pi.single b 1) = (bitCost G G' b : ℂ) • Pi.single b 1 := by
  simp only [bitHamiltonian, Matrix.diagonal_mulVec_single, mul_one]
  ext i
  by_cases hi : i = b
  · subst i; simp
  · simp [hi]

/-- The spectrum of the binary Hamiltonian is exactly the range of its costs, viewed as complex
numbers [GaitanClark2014]. -/
theorem bitHamiltonian_spectrum (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    spectrum ℂ (bitHamiltonian G G') = Set.range (fun b : Bits N => (bitCost G G' b : ℂ)) :=
  cost_spectrum _

/-- The minimum binary cost is the least real energy in the Hamiltonian's spectrum
[GaitanClark2014]. -/
theorem bitHamiltonian_least_energy (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    IsLeast {e : ℝ | (e : ℂ) ∈ spectrum ℂ (bitHamiltonian G G')}
      (Qatlib.Foundations.MatrixGeometry.DiagonalKernels.minimumCost (bitCost G G') : ℝ) :=
  minimum_isLeast _

/-- The minimum binary cost is zero if and only if the two graphs are isomorphic
[GaitanClark2014]. -/
theorem bitHamiltonian_minimum_zero (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Qatlib.Foundations.MatrixGeometry.DiagonalKernels.minimumCost (bitCost G G') = 0
      ↔ Nonempty (G ≃g G') := (minimum_zero_iff _).trans (bitCost_zero_iff G G')

/-- The parsing equivalence restricted to zero-cost Boolean registers and zero-cost integer
strings. -/
def zeroBitEquiv (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    {b : Bits N // bitCost G G b = 0} ≃ {s : IntStr N // cost G G s = 0} where
  toFun b := ⟨parseEquiv N b.val,b.property⟩
  invFun s := ⟨(parseEquiv N).symm s.val,by simpa [bitCost] using s.property⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

/-- The equivalence between adjacency-preserving vertex permutations and graph automorphisms. -/
def graphAutEquiv (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    {π : Equiv.Perm (Fin N) // IsAut G π} ≃ (G ≃g G) where
  toFun π := { toEquiv := π.val, map_rel_iff' := fun {a b} => (π.property a b).symm }
  invFun f := ⟨f.toEquiv,fun a b => f.map_rel_iff.symm⟩
  left_inv π := by apply Subtype.ext; rfl
  right_inv f := by cases f; rfl

/-- The equivalence between Boolean coordinates with zero complex-valued cost and graph
automorphisms. -/
def zeroCoordinateAutEquiv (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    {b : Bits N // (bitCost G G b : ℂ) = 0} ≃ (G ≃g G) :=
  ({ toFun := fun b => (⟨b.val,by exact_mod_cast b.property⟩ : {b : Bits N // bitCost G G b = 0})
     invFun := fun b => ⟨b.val,by exact_mod_cast b.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
     {b : Bits N // (bitCost G G b : ℂ) = 0} ≃ {b : Bits N // bitCost G G b = 0}).trans
    ((zeroBitEquiv G).trans ((zeroCostAutEquiv G).trans (graphAutEquiv G)))

/-- For a graph compared with itself, the complex dimension of the Hamiltonian's kernel equals
the number of graph automorphisms. -/
theorem ground_kernel_finrank (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    Module.finrank ℂ (LinearMap.ker (bitHamiltonian G G).toLin') = Nat.card (G ≃g G) := by
  change Module.finrank ℂ (LinearMap.ker (diagonalMap (fun b => (bitCost G G b : ℂ)))) = _
  rw [finrank_kernel]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (zeroCoordinateAutEquiv G)

/-- For a graph compared with itself, the complex dimension of the zero eigenspace equals the
number of graph automorphisms [GaitanClark2014]. -/
theorem ground_eigenspace_finrank (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    Module.finrank ℂ (Module.End.eigenspace ((bitHamiltonian G G).toLin') 0) = Nat.card (G ≃g G) := by
  rw [Module.End.eigenspace_zero]
  exact ground_kernel_finrank G

end
end Qatlib.Papers.GraphIsom13.DiagonalModel
