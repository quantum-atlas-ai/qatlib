/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumMetro05.MainResults.QuantumBound

/-!
# Sequential metrology precision

This module bounds sums of sequential generator values and applies the ultimate variance based
error inequality to them. It also records the exact error formula when the corresponding
Cramér–Rao expression is saturated. See [GiovannettiLloydMaccone2006].

## Main statements

* `sequential_generator_spectrum`: If every sequential generator value lies in `[a, b]`, their
  sum lies in `[N * a, N * b]`.
* `sequential_error_bound`: For positive resources and bounded sequential generator values, the
  stated Cramér–Rao hypothesis gives error at least `1 / (√ν * N * (b - a))`.
* `eq7_attains_error_bound`: Saturation at total spread `N * spectralSpread a b` yields the
  sequential error `1 / (√ν * N * (b - a))`.

## References

* [Giovannetti et al., 2006][GiovannettiLloydMaccone2006]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound

open Qatlib.Papers.QuantumMetro05.MainResults.Source
open Qatlib.Papers.QuantumMetro05.MainResults.QuantumBound

/-- If every sequential generator value lies in `[a, b]`, their sum lies in `[N * a, N * b]`.
See [GiovannettiLloydMaccone2006]. -/
theorem sequential_generator_spectrum {X : Type} {N : ℕ} (H' : Fin N → X → ℝ)
    {a b : ℝ} (ha : ∀ j x, a ≤ H' j x) (hb : ∀ j x, H' j x ≤ b) (x : X) :
    (N : ℝ) * a ≤ ∑ j, H' j x ∧ ∑ j, H' j x ≤ (N : ℝ) * b :=
  spectralSumBounds (fun j => H' j x) (fun j => ha j x) (fun j => hb j x)

/-- For positive resources and bounded sequential generator values, the stated Cramér–Rao
hypothesis gives error at least `1 / (√ν * N * (b - a))`. See [GiovannettiLloydMaccone2006]. -/
theorem sequential_error_bound {X : Type} [Fintype X] [DecidableEq X]
    {N : ℕ} (hN : 0 < N) (p : FinDist X) (H' : Fin N → X → ℝ) {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b) (ha : ∀ j x, a ≤ H' j x) (hb : ∀ j x, H' j x ≤ b)
    (hcr : δφ * Real.sqrt (p.variance (fun x => ∑ j, H' j x))
            ≥ 1 / (2 * Real.sqrt ν)) :
    1 / (Real.sqrt ν * (N : ℝ) * (b - a)) ≤ δφ :=
  qc_qq_error_bound hN p H' hν hab ha hb hcr

/-- Saturation at total spread `N * spectralSpread a b` yields the sequential error `1 / (√ν * N
* (b - a))`. See [GiovannettiLloydMaccone2006]. -/
theorem eq7_attains_error_bound {N : ℕ} {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b)
    (hcr : δφ * ((N : ℝ) * spectralSpread a b) = 1 / (2 * Real.sqrt ν)) :
    δφ = 1 / (Real.sqrt ν * (N : ℝ) * (b - a)) :=
  eq4_attains_error_bound hν hab hcr

end Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound
