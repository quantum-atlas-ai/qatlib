/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SemigroupLog13.MainResults.MembershipFamily.SourceMembershipFamily

@[expose] public section


/-! A power-index defect in the retained hard-instance membership model. -/
set_option autoImplicit false
namespace Qatlib.Papers.SemigroupLog13.MainResults.MemberProbe
open Qatlib.Papers.SemigroupLog13.MainResults

/-- Index one in the legacy power function multiplies two copies of the generator. -/
theorem legacyOne {S : Type} (mul : S → S → S) (g : S) :
    powMul mul g 1 = mul g g := rfl

/-- Boolean XOR refutes the intended positive-exponent law at exponent one.
This diagnoses the legacy power representation, not the source lower bound. -/
theorem powerOffset : powMul Bool.xor true 1 ≠ true := by decide
end Qatlib.Papers.SemigroupLog13.MainResults.MemberProbe
