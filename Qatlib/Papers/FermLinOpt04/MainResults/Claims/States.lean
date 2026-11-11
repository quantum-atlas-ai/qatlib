/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap

/-!
# Reality and antisymmetry of Gaussian-state parameters

The predicate `IsGaussianState ρ M` includes reality and antisymmetry of its parameter matrix.
This module extracts these two properties as separate theorems for subsequent use. These results
formalize the indicated identities from [Bravyi2005Fermionic].

## Main statements

* `gaussianState_corr_antisymm`: extracts antisymmetry of `M`.
* `gaussianState_corr_real`: extracts vanishing imaginary parts of its entries.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

/-- The parameter matrix of `IsGaussianState ρ M` is antisymmetric. -/
theorem gaussianState_corr_antisymm {n : ℕ} {ρ : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} (hρ : IsGaussianState ρ M) :
    ∀ a b, M a b = -(M b a) :=
  hρ.1

/-- The entries of the parameter matrix of `IsGaussianState ρ M` have zero imaginary part. -/
theorem gaussianState_corr_real {n : ℕ} {ρ : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} (hρ : IsGaussianState ρ M) :
    ∀ a b, (M a b).im = 0 :=
  hρ.2.1

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
