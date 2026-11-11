/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic

/-!
# Dyadic Horner evaluation with operation counters

This module defines an integer Horner evaluator `run` with dyadic scaling, operation counters,
and a peak magnitude record in `Result`. The functions `realValue` and `exactValue` provide
real-valued reference evaluations for subsequent error estimates.

The computational background for finite-precision arithmetic is discussed in
[KitaevShenVyalyi2002].

## Main statements

* `Result`: The integer output of Horner evaluation together with its addition, multiplication,
  division, and peak magnitude records.
* `run`: Evaluate integer coefficients recursively by `c + (x * acc) / 2^b`, recording operation
  counts and the largest magnitude of coefficients, products, and accumulated values.
* `exactValue`: Evaluate the real polynomial obtained by dividing every integer coefficient and
  the integer input by `2^b`.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

namespace Qatlib.Foundations.DyadicHorner.HornerError
set_option autoImplicit false

/-- The integer output of Horner evaluation together with its addition, multiplication,
division, and peak magnitude records. -/
structure Result where
  value : ℤ
  additions : ℕ
  multiplications : ℕ
  divisions : ℕ
  peakAbs : ℕ
  deriving DecidableEq

/-- Evaluate integer coefficients recursively by `c + (x * acc) / 2^b`, recording operation
counts and the largest magnitude of coefficients, products, and accumulated values. -/
def run (b : ℕ) (x : ℤ) : List ℤ → Result
  | [] => ⟨0,0,0,0,0⟩
  | c::cs =>
    let r := run b x cs
    let v := c + (x*r.value)/(2^b : ℤ)
    ⟨v,r.additions+1,r.multiplications+1,r.divisions+1,
      max r.peakAbs (max c.natAbs (max (x*r.value).natAbs v.natAbs))⟩

/-- Evaluate real coefficients in ascending degree order by a right-fold Horner recurrence. -/
noncomputable def realValue (cs : List ℝ) (x : ℝ) : ℝ :=
  cs.foldr (fun c acc => c + x*acc) 0

/-- Evaluate the real polynomial obtained by dividing every integer coefficient and the integer
input by `2^b`. -/
noncomputable def exactValue (b : ℕ) (x : ℤ) (cs : List ℤ) : ℝ :=
  realValue (cs.map (fun (c : ℤ) => (c:ℝ)/(2^b:ℝ))) ((x:ℝ)/(2^b:ℝ))
end Qatlib.Foundations.DyadicHorner.HornerError
