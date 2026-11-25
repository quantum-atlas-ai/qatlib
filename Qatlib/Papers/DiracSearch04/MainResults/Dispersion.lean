/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DiracSearch04.MainResults.DiracAlgebra
public import Qatlib.Papers.DiracSearch04.MainResults.SearchSpeedup
import Mathlib.Basic.Complex.BigOperators

@[expose] public section

/-!
# Dispersion on the distinguished Dirac spin vector

Combines the lattice momentum coefficients of [ChildsGoldstone2004a], Equations (9)–(10),
with the explicit spin representation used in Equation (34).

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004a]
-/

set_option autoImplicit false

open Matrix
open Qatlib.Papers.DiracSearch04.MainResults

namespace Qatlib.Papers.DiracSearch04.MainResults

/-- In the explicit spin representation, the square of the free Hamiltonian with the lattice
momentum coefficients acts on the distinguished spin vector by the squared dispersion. -/
theorem free_hamiltonian_sq_eta_dispersion (d : ℕ) (ω γ : ℝ) (k : Fin d → ℝ) :
    let H := freeHamiltonian d (fun j => (ω * Real.sin (k j) : ℝ)) (γ * cOf d k : ℝ)
    H *ᵥ (H *ᵥ eta d) = ((ω ^ 2 * sSq d k + γ ^ 2 * (cOf d k) ^ 2 : ℝ) : ℂ) • eta d := by
  dsimp only
  rw [freeHamiltonian_sq_mulVec_eta]
  simp only [sSq, Finset.mul_sum, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]

end Qatlib.Papers.DiracSearch04.MainResults
