/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs

/-!
# Rational dyadic matrix rounding

`floorDyadic` rounds a rational number downward to a binary grid. `roundMatrix` symmetrizes
entrywise rounding by averaging transposed entries, and `interpret` casts a rational matrix to
the reals. These definitions provide finite-precision matrix data for semidefinite-programming
constructions motivated by [BrandaoSvore2017].

## Main statements

* `floorDyadic`: rational floor rounding at binary precision.
* `roundMatrix`: symmetric rounding of rational matrix entries.
* `interpret`: entrywise real interpretation.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.DyadicFloor.FloorRounding

/-- Rounds a rational number downward to the dyadic grid of spacing `1 / 2 ^ p`. -/
def floorDyadic (p : ℕ) (x : ℚ) : ℚ := (⌊x * (2 : ℚ)^p⌋ : ℚ)/(2 : ℚ)^p
/-- The symmetric rational matrix obtained by averaging the dyadic floors of each entry and its
transpose entry. -/
def roundMatrix {n : ℕ} (p : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (floorDyadic p (A i j) + floorDyadic p (A j i))/2
/-- Interprets a rational matrix as a real matrix by casting each entry. -/
def interpret {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)
end Qatlib.Concepts.DyadicFloor.FloorRounding
