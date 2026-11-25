/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FermionQFT17.PrepContracts.ResourceScaling

@[expose] public section

/-!
# Comparison of the leading precision powers

Section II.B of arXiv:1711.04006v3 compares the single-species DMRG
preprocessing power with the leading precision power of the previous method.
-/

set_option autoImplicit false

open Qatlib.Papers.FermionQFT17.PrepContracts.ResourceScaling

namespace Qatlib.Papers.FermionQFT17.PrepContracts

/-- The single-species precision exponent is strictly above the previous leading exponent. -/
theorem costExponent_one_improves_previous : (-8 : ℝ) < costExponent 1 :=
  (by norm_num : (-8 : ℝ) < -3.24).trans costExponent_one_bounds.1

/-- For precision strictly between zero and one, the new leading precision power is smaller. -/
theorem costPower_one_lt_previous {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ε ^ costExponent 1 < ε ^ (-8 : ℝ) :=
  Real.rpow_lt_rpow_of_exponent_gt hε hε1 costExponent_one_improves_previous

end Qatlib.Papers.FermionQFT17.PrepContracts
