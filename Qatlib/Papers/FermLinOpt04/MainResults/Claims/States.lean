/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

theorem gaussianState_corr_antisymm {n : ℕ} {ρ : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} (hρ : IsGaussianState ρ M) :
    ∀ a b, M a b = -(M b a) :=
  hρ.1

theorem gaussianState_corr_real {n : ℕ} {ρ : Fock n}
    {M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ} (hρ : IsGaussianState ρ M) :
    ∀ a b, (M a b).im = 0 :=
  hρ.2.1

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
