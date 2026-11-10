/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical

namespace Qatlib.Papers.FermionicComp00.MainResults.MeasurementGate

def sourceMajorana {m : ℕ} (j : Fin (2 * m)) : Matrix (Reg m) (Reg m) ℂ :=
  if j.val % 2 = 0 then
    creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ +
      annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩
  else
    (-Complex.I) •
      (annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ -
        creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩)

def sourceC (j : Fin 6) : Matrix (Reg 3) (Reg 3) ℂ := sourceMajorana (m := 3) j

def sourceProj4 (z : Bool) : Matrix (Reg 3) (Reg 3) ℂ :=
  (2 : ℂ)⁻¹ • (1 + (if z then 1 else -1) •
    (sourceC 0 * sourceC 1 * sourceC 3 * sourceC 4))

def sourceProj2 (y : Bool) : Matrix (Reg 3) (Reg 3) ℂ :=
  (2 : ℂ)⁻¹ • (1 + (if y then -Complex.I else Complex.I) • (sourceC 2 * sourceC 4))

def sourceFourMajoranaGate : Matrix (Reg 3) (Reg 3) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
    (sourceC 0 * sourceC 1 * sourceC 2 * sourceC 3))

theorem sourceProj4_one :
    sourceProj4 true =
      (2 : ℂ)⁻¹ • (1 + sourceC 0 * sourceC 1 * sourceC 3 * sourceC 4) := by
  simp [sourceProj4]

theorem sourceProj2_one :
    sourceProj2 true =
      (2 : ℂ)⁻¹ • (1 + (-Complex.I) • (sourceC 2 * sourceC 4)) := by
  simp [sourceProj2]

end Qatlib.Papers.FermionicComp00.MainResults.MeasurementGate
