/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionMachine
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionRejection
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionValue
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Runs)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs (input output)

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
