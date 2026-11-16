/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteGroupAlg.CharP.MonoidAlgebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Action.Pi

@[expose] public section


/-! # The group-algebra generators underlying the Olson threshold

The introduction of *Zero sum subsequences and hidden subgroups*,
arXiv:2304.08376v1, recalls the exact Davenport threshold `1 + n * (p - 1)`.
This module supplies the characteristic and generator-nilpotency input on
the actual `AddMonoidAlgebra (ZMod p) (Fin n → ZMod p)` carrier.
It does not prove the paper's deterministic running-time bound.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ZeroSumImran24.MainResults

open Qatlib.Foundations.FiniteGroupAlg.CharP

/-- The direct group-algebra carrier used for elementary abelian zero-sum sequences has characteristic `p`. -/
theorem olsonCarrier_charP (p n : ℕ) :
    CharP (AddMonoidAlgebra (ZMod p) (Fin n → ZMod p)) p :=
  charP_addMonoidAlgebra

/-- Every augmentation generator on the elementary abelian carrier is `p`-nilpotent for prime `p`. -/
theorem olsonGenerator_pow_eq_zero (p n : ℕ) [Fact (Nat.Prime p)]
    (g : Fin n → ZMod p) :
    (AddMonoidAlgebra.of' (ZMod p) (Fin n → ZMod p) g - 1) ^ p = 0 := by
  apply of'_sub_one_pow_eq_zero
  ext j
  simp

end Qatlib.Papers.ZeroSumImran24.MainResults
