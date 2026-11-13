/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumMetro05.MainResults.ClassicalBound
import Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound.Eq7

/-!
# Abstract metrology precision bounds

This module collects the separable and ultimate precision inequalities for bounded generators
under the stated Cramér–Rao conditions. It identifies their square root resource ratio and
derives the corresponding equality formulas from saturation hypotheses. See
[GiovannettiLloydMaccone2006].

## Main statements

* `ultimate_error_bound`: For `N > 0` generator values in `[a, b]` and positive `ν`, the assumed
  variance based Cramér–Rao inequality implies error at least `1 / (√ν * N * (b - a))`.
* `separable_error_bound`: For a product distribution of `N > 0` probes and a generator in `[a,
  b]`, the assumed Cramér–Rao inequality implies error at least `1 / (√(ν * N) * (b - a))`.
* `enhancement_sq`: The ratio of the separable precision bound to the ultimate precision bound
  equals `√N`.

## References

* [Giovannetti et al., 2006][GiovannettiLloydMaccone2006]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.Abstract

open Qatlib.Papers.QuantumMetro05.MainResults.Source
open Qatlib.Papers.QuantumMetro05.MainResults.ClassicalBound
open Qatlib.Papers.QuantumMetro05.MainResults.QuantumBound
open Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound

/-- For `N > 0` generator values in `[a, b]` and positive `ν`, the assumed variance based
Cramér–Rao inequality implies error at least `1 / (√ν * N * (b - a))`. See
[GiovannettiLloydMaccone2006]. -/
theorem ultimate_error_bound {X : Type} [Fintype X] [DecidableEq X]
    {N : ℕ} (hN : 0 < N) (p : FinDist X) (f : Fin N → X → ℝ) {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b) (ha : ∀ j x, a ≤ f j x) (hb : ∀ j x, f j x ≤ b)
    (hcr : δφ * Real.sqrt (p.variance (fun x => ∑ j, f j x))
            ≥ 1 / (2 * Real.sqrt ν)) :
    1 / (Real.sqrt ν * (N : ℝ) * (b - a)) ≤ δφ :=
  qc_qq_error_bound hN p f hν hab ha hb hcr

/-- For a product distribution of `N > 0` probes and a generator in `[a, b]`, the assumed
Cramér–Rao inequality implies error at least `1 / (√(ν * N) * (b - a))`. -/
theorem separable_error_bound {N d : ℕ} (hN : 0 < N)
    (q : Fin N → FinDist (Fin d)) (H : Fin d → ℝ) {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b) (ha : ∀ x, a ≤ H x) (hb : ∀ x, H x ≤ b)
    (hcr : δφ * Real.sqrt ((productLaw q).variance (fun ω => ∑ j, H (ω j)))
            ≥ 1 / (2 * Real.sqrt ν)) :
    1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)) ≤ δφ :=
  cc_cq_error_bound hN q H hν hab ha hb hcr

/-- Multiplying the ultimate precision bound by `√N` gives the separable precision bound under
the stated positivity hypotheses. See [GiovannettiLloydMaccone2006]. -/
theorem sqrt_N_enhancement {N : ℕ} {ν a b : ℝ} (hN : 0 < N) (hν : 0 < ν)
    (hab : a < b) :
    Real.sqrt (N : ℝ) * (1 / (Real.sqrt ν * (N : ℝ) * (b - a)))
      = 1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hν0 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr hν).ne'
  have hba : (b - a) ≠ 0 := by linarith
  rw [Real.sqrt_mul (le_of_lt hν)]
  set sN : ℝ := Real.sqrt (N : ℝ) with hsNdef
  have hsq2 : sN * sN = (N : ℝ) := by
    rw [hsNdef]; exact Real.mul_self_sqrt (le_of_lt hNpos)
  rw [← hsq2]
  field_simp

/-- The ratio of the separable precision bound to the ultimate precision bound equals `√N`. See
[GiovannettiLloydMaccone2006]. -/
theorem enhancement_sq {N : ℕ} {ν a b : ℝ} (hN : 0 < N) (hν : 0 < ν)
    (hab : a < b) :
    (1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)))
        / (1 / (Real.sqrt ν * (N : ℝ) * (b - a)))
      = Real.sqrt (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hν0 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr hν).ne'
  have hba : (b - a) ≠ 0 := by linarith
  rw [Real.sqrt_mul (le_of_lt hν)]
  set sN : ℝ := Real.sqrt (N : ℝ) with hsNdef
  have hsq2 : sN * sN = (N : ℝ) := by
    rw [hsNdef]; exact Real.mul_self_sqrt (le_of_lt hNpos)
  rw [← hsq2]
  field_simp

/-- If the separable and ultimate Cramér–Rao expressions are saturated at their respective
maximal spreads, their errors equal the stated separable and ultimate precision bounds. See
[GiovannettiLloydMaccone2006]. -/
theorem both_bounds_attainable {N : ℕ} {a b ν δφc δφq : ℝ}
    (hN : 0 < N) (hν : 0 < ν) (hab : a < b)
    (hc : δφc * (Real.sqrt (N : ℝ) * spectralSpread a b) = 1 / (2 * Real.sqrt ν))
    (hq : δφq * ((N : ℝ) * spectralSpread a b) = 1 / (2 * Real.sqrt ν)) :
    δφc = 1 / (Real.sqrt (ν * (N : ℝ)) * (b - a)) ∧
      δφq = 1 / (Real.sqrt ν * (N : ℝ) * (b - a)) :=
  ⟨eq3_attains_error_bound hN hν hab hc, eq4_attains_error_bound hν hab hq⟩

/-- For nonzero `s` and positive resources and spectral width, cancelling `|s|` in the Ramsey
error expression yields `1 / (√ν * N * (b - a))`. -/
theorem ramsey_error_eq {N ν s a b : ℝ} (hν : 0 < ν) (hN : 0 < N) (hab : a < b)
    (hs : s ≠ 0) :
    (1 / Real.sqrt ν) * |s| / (N * (b - a) * |s|)
      = 1 / (Real.sqrt ν * N * (b - a)) := by
  have hν0 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr hν).ne'
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hba : (b - a) ≠ 0 := by linarith
  have hsabs : |s| ≠ 0 := ne_of_gt (abs_pos.mpr hs)
  field_simp

end Qatlib.Papers.QuantumMetro05.MainResults.Abstract
