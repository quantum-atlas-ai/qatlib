/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionMachine
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionRejection
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionValue

/-!
# Exact rational division with polynomial machine bounds

This module combines the uniform division machine with the rational interpretation of its
output. A single finite-state binary Turing machine computes the specified quotient encoding for
every pair of word rationals with nonzero divisor numerator, within quartic time and quadratic
space in the combined word size.

Finite descriptions and polynomial resource bounds have general background in
[KitaevShenVyalyi2002]; the quotient encoding and the explicit machine guarantee are particular
to this development.

## Main statements

* `frontier1` supplies a fixed machine and positive constant `C`, proves `Runs` with bounds `C *
  size^4` and `C * size^2`, and identifies the output's rational value with the exact quotient.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002] provides general background on
  classical and quantum computation.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Runs)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs (input output)

/-- There is one finite-state binary Turing machine and positive constant `C` satisfying `Runs`
for the quotient encoding of every pair of word rationals whose divisor numerator has
positive binary value. The bounds are `C * size^4` for time and `C * size^2` for space, and
the output represents the exact rational quotient. -/
theorem frontier1 :
    ∃ (q : ℕ) (M : TM0.Machine (Option Bool) (Fin (q+1))) (C : ℕ), 0<C ∧
      ∀ (a b : WordRat) (hb : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue b.numerator),
        let c := quotient a b hb
        Runs M (input a.negative b.negative a.numerator a.denominator b.numerator b.denominator)
          (output a.negative b.negative c.numerator c.denominator)
          (C*(size a.numerator a.denominator b.numerator b.denominator)^4)
          (C*(size a.numerator a.denominator b.numerator b.denominator)^2) ∧
        c.toRat = a.toRat / b.toRat := by
  obtain ⟨q,M,C,hC,hM⟩ := uniform_division_machine
  refine ⟨q,M,C,hC,?_⟩
  intro a b hb
  exact ⟨hM a.negative b.negative a.numerator a.denominator b.numerator b.denominator
    a.positive hb b.positive,quotient_value a b hb⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore
