/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtBounds
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareSum
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareAppendWriter
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBase

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Runs)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore (frontier1)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs (input output)
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionMachine (size)

theorem frontier2 :
    ∃ (q : ℕ) (M : TM0.Machine (Option Bool) (Fin (q+1))) (C : ℕ), 0<C ∧
      ∀ (a b : ℕ → WordRat) (K : ℕ),
        (∀ k, size (a k).numerator (a k).denominator (b k).numerator (b k).denominator ≤ K*(1+k)) →
        ∀ (k : ℕ) (hb : 0<Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (b k).numerator),
          let c := quotient (a k) (b k) hb
          Runs M (input (a k).negative (b k).negative (a k).numerator (a k).denominator
            (b k).numerator (b k).denominator)
            (output (a k).negative (b k).negative c.numerator c.denominator)
            ((C*K^4)*(1+k)^4) ((C*K^2)*(1+k)^2) ∧
          c.toRat = (a k).toRat / (b k).toRat := by
  obtain ⟨q,M,C,hC,hM⟩ := frontier1
  refine ⟨q,M,C,hC,?_⟩
  intro a b K hlen k hb
  obtain ⟨hr,hv⟩ := hM (a k) (b k) hb
  refine ⟨Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hr ?_ ?_,hv⟩
  · calc
      _ ≤ C*(K*(1+k))^4 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hlen k) 4)
      _ = _ := by ring
  · calc
      _ ≤ C*(K*(1+k))^2 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (hlen k) 2)
      _ = _ := by ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBase
