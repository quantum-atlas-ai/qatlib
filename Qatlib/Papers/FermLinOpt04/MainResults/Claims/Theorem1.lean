/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.Closure
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

theorem theorem1_part1_forward {n : ℕ} {X : Fock n} (hX : IsGaussianOperator X) :
    IsEvenOp X :=
  isEvenOp_of_isGaussianOperator hX

theorem corollary1_of_char {n : ℕ} {X Y : Fock n}
    (hchar : ∀ Z : Fock n, IsGaussianOperator Z ↔ (IsEvenOp Z ∧ lambdaCommute Z))
    (hX : IsGaussianOperator X) (hY : IsGaussianOperator Y) :
    IsGaussianOperator (X * Y) :=
  Qatlib.Papers.FermLinOpt04.MainResults.Model.gaussianOperator_mul_of_char
    hchar hX hY

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
