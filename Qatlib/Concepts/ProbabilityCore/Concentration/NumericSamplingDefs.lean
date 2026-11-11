/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Complex.Basic

/-!
# Dyadic encodings of complex matrices

The module records complex numbers as pairs of scaled integer floors and decodes them at a fixed
dyadic precision. Applying this construction entrywise gives matrix records, rounded matrices,
and the dimension dependent error allowance `dyadicOpBudget`.

The matrix norm error estimates built on these definitions belong to the finite matrix setting
of [Bhatia1997].

## Main statements

* `dyadicEncode` and `dyadicDecode`: integer records and complex reconstruction.
* `dyadicRoundMatrix`: entrywise dyadic floor rounding.
* `dyadicOpBudget`: the matrix rounding allowance `2 * |I| / 2 ^ bits`.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- Encode a pair of rational coordinates by flooring each coordinate after multiplication by `2
^ bits`. -/
def dyadicEncodeRat (bits : ℕ) (z : ℚ × ℚ) : ℤ × ℤ :=
  (⌊(2 : ℚ)^bits * z.1⌋, ⌊(2 : ℚ)^bits * z.2⌋)

/-- Encode a complex number as the scaled integer floors of its real and imaginary parts. -/
noncomputable def dyadicEncode (bits : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊(2 : ℝ)^bits * z.re⌋, ⌊(2 : ℝ)^bits * z.im⌋)

/-- Decode an integer pair as real and imaginary coordinates divided by `2 ^ bits`. -/
noncomputable def dyadicDecode (bits : ℕ) (z : ℤ × ℤ) : ℂ :=
  (((z.1 : ℝ) / (2 : ℝ)^bits : ℝ) : ℂ) +
    (((z.2 : ℝ) / (2 : ℝ)^bits : ℝ) : ℂ) * Complex.I

/-- Round a complex number by dyadic floor encoding followed by decoding. -/
noncomputable def dyadicRoundComplex (bits : ℕ) (z : ℂ) : ℂ :=
  dyadicDecode bits (dyadicEncode bits z)

/-- Encode every entry of a complex matrix as an integer pair at the chosen dyadic precision. -/
noncomputable def dyadicMatrixRecord {I J : Type*} (bits : ℕ) (A : Matrix I J ℂ) :
    Matrix I J (ℤ × ℤ) := fun i j => dyadicEncode bits (A i j)

/-- Decode an integer pair matrix entrywise into a complex matrix. -/
noncomputable def dyadicMatrixDecode {I J : Type*} (bits : ℕ) (A : Matrix I J (ℤ × ℤ)) :
    Matrix I J ℂ := fun i j => dyadicDecode bits (A i j)

/-- Round every complex matrix entry by dyadic floor encoding and decoding. -/
noncomputable def dyadicRoundMatrix {I J : Type*} (bits : ℕ) (A : Matrix I J ℂ) :
    Matrix I J ℂ := dyadicMatrixDecode bits (dyadicMatrixRecord bits A)

/-- The dimension dependent matrix rounding error allowance `2 * Fintype.card I / 2 ^ bits`. -/
noncomputable def dyadicOpBudget (I : Type*) [Fintype I] (bits : ℕ) : ℝ :=
  2 * (Fintype.card I : ℝ) / (2 : ℝ)^bits

end Qatlib.Concepts.ProbabilityCore.Concentration
