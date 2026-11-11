/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.Closure

/-!
# Parity and conditional Gaussian multiplication

Gaussian operators are even under parity conjugation. Given the full characterization of
Gaussian operators by evenness and commutation of their tensor squares with `Lambda`, the module
derives multiplication closure. These results formalize the indicated identities from
[Bravyi2005Fermionic].

## Main statements

* `theorem1_part1_forward`: extracts evenness of Gaussian operators.
* `corollary1_of_char`: proves multiplication closure under the characterization hypothesis.

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

/-- Every Gaussian operator is even under parity conjugation. This proves the evenness
conclusion in the forward direction of Theorem 1(1) of [Bravyi2005Fermionic]. -/
theorem theorem1_part1_forward {n : ℕ} {X : Fock n} (hX : IsGaussianOperator X) :
    IsEvenOp X :=
  isEvenOp_of_isGaussianOperator hX

/-- Assuming the characterization by evenness and `lambdaCommute`, the product of two Gaussian
operators is Gaussian. This is the conditional form of Corollary 1 of [Bravyi2005Fermionic]. -/
theorem corollary1_of_char {n : ℕ} {X Y : Fock n}
    (hchar : ∀ Z : Fock n, IsGaussianOperator Z ↔ (IsEvenOp Z ∧ lambdaCommute Z))
    (hX : IsGaussianOperator X) (hY : IsGaussianOperator Y) :
    IsGaussianOperator (X * Y) :=
  Qatlib.Papers.FermLinOpt04.MainResults.Model.gaussianOperator_mul_of_char
    hchar hX hY

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
