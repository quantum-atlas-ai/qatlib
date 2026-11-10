/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.Concentration

def dyadicEncodeRat (bits : ℕ) (z : ℚ × ℚ) : ℤ × ℤ :=
  (⌊(2 : ℚ)^bits * z.1⌋, ⌊(2 : ℚ)^bits * z.2⌋)

noncomputable def dyadicEncode (bits : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊(2 : ℝ)^bits * z.re⌋, ⌊(2 : ℝ)^bits * z.im⌋)

noncomputable def dyadicDecode (bits : ℕ) (z : ℤ × ℤ) : ℂ :=
  (((z.1 : ℝ) / (2 : ℝ)^bits : ℝ) : ℂ) +
    (((z.2 : ℝ) / (2 : ℝ)^bits : ℝ) : ℂ) * Complex.I

noncomputable def dyadicRoundComplex (bits : ℕ) (z : ℂ) : ℂ :=
  dyadicDecode bits (dyadicEncode bits z)

noncomputable def dyadicMatrixRecord {I J : Type*} (bits : ℕ) (A : Matrix I J ℂ) :
    Matrix I J (ℤ × ℤ) := fun i j => dyadicEncode bits (A i j)

noncomputable def dyadicMatrixDecode {I J : Type*} (bits : ℕ) (A : Matrix I J (ℤ × ℤ)) :
    Matrix I J ℂ := fun i j => dyadicDecode bits (A i j)

noncomputable def dyadicRoundMatrix {I J : Type*} (bits : ℕ) (A : Matrix I J ℂ) :
    Matrix I J ℂ := dyadicMatrixDecode bits (dyadicMatrixRecord bits A)

noncomputable def dyadicOpBudget (I : Type*) [Fintype I] (bits : ℕ) : ℝ :=
  2 * (Fintype.card I : ℝ) / (2 : ℝ)^bits

end Qatlib.Concepts.ProbabilityCore.Concentration
