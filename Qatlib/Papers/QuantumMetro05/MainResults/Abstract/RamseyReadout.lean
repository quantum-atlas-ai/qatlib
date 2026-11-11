/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumMetro05.MainResults.Abstract.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ramsey readout error propagation

This module defines the Ramsey mean `cos θ` and variance `sin θ ^ 2`. Differentiating the scaled
mean yields an exact error propagation formula wherever the sine response is nonzero. See
[GiovannettiLloydMaccone2006].

## Main statements

* `deriv_ramseyMean`: The derivative of the scaled Ramsey mean at `φ` equals `-c * sin (c * φ)`.
* `ramseyError_eq`: At a phase with nonzero sine response, the Ramsey standard deviation divided
  by `√ν` and the absolute mean derivative equals `1 / (√ν * N * (b - a))`.

## References

* [Giovannetti et al., 2006][GiovannettiLloydMaccone2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.Abstract

open Qatlib.Papers.QuantumMetro05.MainResults.Source

/-- The Ramsey readout mean `Real.cos θ`. -/
def ramseyMean (θ : ℝ) : ℝ := Real.cos θ

/-- The Ramsey readout variance `Real.sin θ ^ 2`. -/
def ramseyVar (θ : ℝ) : ℝ := Real.sin θ ^ 2

/-- The derivative of the scaled Ramsey mean at `φ` equals `-c * sin (c * φ)`. -/
theorem deriv_ramseyMean (φ c : ℝ) :
    deriv (fun x => ramseyMean (c * x)) φ = -c * Real.sin (c * φ) := by
  have hinner : HasDerivAt (fun x : ℝ => c * x) c φ := by
    simpa using (hasDerivAt_id (x := φ)).const_mul c
  have houter : HasDerivAt Real.cos (-Real.sin (c * φ)) (c * φ) :=
    Real.hasDerivAt_cos (c * φ)
  have hcomp := houter.comp φ hinner
  have hfun : (fun x : ℝ => ramseyMean (c * x)) = Real.cos ∘ (fun x => c * x) := rfl
  rw [hfun, hcomp.deriv]
  ring

/-- At a phase with nonzero sine response, the Ramsey standard deviation divided by `√ν` and the
absolute mean derivative equals `1 / (√ν * N * (b - a))`. See [GiovannettiLloydMaccone2006]. -/
theorem ramseyError_eq {φ : ℝ} {ν N : ℕ} {a b : ℝ}
    (hν : 0 < ν) (hN : 0 < N) (hab : a < b)
    (hsin : Real.sin ((N : ℝ) * (b - a) * φ) ≠ 0) :
    (Real.sqrt (ramseyVar ((N : ℝ) * (b - a) * φ)) / Real.sqrt ν)
        / |deriv (fun x => ramseyMean ((N : ℝ) * (b - a) * x)) φ|
      = 1 / (Real.sqrt ν * ((N : ℝ) * (b - a))) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 < (N : ℝ) * (b - a) := mul_pos hNr (by linarith)
  have hderiv : deriv (fun x => ramseyMean ((N : ℝ) * (b - a) * x)) φ
      = -((N : ℝ) * (b - a)) * Real.sin ((N : ℝ) * (b - a) * φ) :=
    deriv_ramseyMean φ ((N : ℝ) * (b - a))
  rw [hderiv]
  simp only [ramseyVar, abs_neg, abs_mul, abs_of_pos hc]
  rw [show Real.sqrt (Real.sin ((N : ℝ) * (b - a) * φ) ^ 2)
      = |Real.sin ((N : ℝ) * (b - a) * φ)| from Real.sqrt_sq_eq_abs _]
  have hνpos : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have hsν : Real.sqrt (ν : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hνpos).ne'
  have hsabs : |Real.sin ((N : ℝ) * (b - a) * φ)| ≠ 0 := abs_ne_zero.mpr hsin
  have hcne : ((N : ℝ) * (b - a)) ≠ 0 := hc.ne'
  field_simp [hsν, hsabs, hcne]

end Qatlib.Papers.QuantumMetro05.MainResults.Abstract
