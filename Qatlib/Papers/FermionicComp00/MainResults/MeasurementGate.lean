/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

/-!
# Majorana measurement operators

`sourceC` specializes the Majorana matrices to three modes. The module defines the signed two-
and four-Majorana measurement operators `sourceProj2` and `sourceProj4`, together with a
four-Majorana exponential, and expands both operators at the Boolean outcome `true`.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `sourceProj4_one`: expands the four-Majorana operator at outcome `true`.
* `sourceProj2_one`: expands the two-Majorana operator at outcome `true`.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical

namespace Qatlib.Papers.FermionicComp00.MainResults.MeasurementGate

/-- The Majorana matrix at index `j`, given by creation plus annihilation at even indices and by
negative imaginary times annihilation minus creation at odd indices. -/
def sourceMajorana {m : ℕ} (j : Fin (2 * m)) : Matrix (Reg m) (Reg m) ℂ :=
  if j.val % 2 = 0 then
    creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ +
      annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩
  else
    (-Complex.I) •
      (annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ -
        creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩)

/-- The six Majorana matrices on the three-mode register. -/
def sourceC (j : Fin 6) : Matrix (Reg 3) (Reg 3) ℂ := sourceMajorana (m := 3) j

/-- Half the sum of the identity and the signed product of Majorana matrices at indices 0, 1, 3,
and 4, with the sign selected by `z`. -/
def sourceProj4 (z : Bool) : Matrix (Reg 3) (Reg 3) ℂ :=
  (2 : ℂ)⁻¹ • (1 + (if z then 1 else -1) •
    (sourceC 0 * sourceC 1 * sourceC 3 * sourceC 4))

/-- Half the sum of the identity and the product of Majorana matrices at indices 2 and 4 scaled
by negative imaginary for `true` and positive imaginary for `false`. -/
def sourceProj2 (y : Bool) : Matrix (Reg 3) (Reg 3) ℂ :=
  (2 : ℂ)⁻¹ • (1 + (if y then -Complex.I else Complex.I) • (sourceC 2 * sourceC 4))

/-- The exponential of `i * π / 4` times the ordered Majorana product at indices 0, 1, 2, and 3. -/
def sourceFourMajoranaGate : Matrix (Reg 3) (Reg 3) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
    (sourceC 0 * sourceC 1 * sourceC 2 * sourceC 3))

/-- At outcome `true`, `sourceProj4` is half the identity plus half the Majorana product at
indices 0, 1, 3, and 4. -/
theorem sourceProj4_one :
    sourceProj4 true =
      (2 : ℂ)⁻¹ • (1 + sourceC 0 * sourceC 1 * sourceC 3 * sourceC 4) := by
  simp [sourceProj4]

/-- At outcome `true`, `sourceProj2` is half the identity plus half the product at indices 2 and
4 scaled by negative imaginary. -/
theorem sourceProj2_one :
    sourceProj2 true =
      (2 : ℂ)⁻¹ • (1 + (-Complex.I) • (sourceC 2 * sourceC 4)) := by
  simp [sourceProj2]

end Qatlib.Papers.FermionicComp00.MainResults.MeasurementGate
