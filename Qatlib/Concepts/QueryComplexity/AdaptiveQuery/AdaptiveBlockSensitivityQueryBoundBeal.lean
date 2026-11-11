/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveBlockSensitivityQueryBoundStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ApproxPolynomialBlockSensitivityBeal

/-!
# Block sensitivity bounds for adaptive quantum queries

This module proves `AdaptiveBlockSensitivityQueryBound` by representing adaptive acceptance
probabilities as Boolean multilinear polynomials and applying polynomial block sensitivity
bounds. A circuit of query depth `T` computing with error at most one third has block
sensitivity at most `16T²`; exact computation gives `8T²`.

The argument transfers the polynomial method of [BealsEtAl2001] to well formed observed
circuits.

## Main statements

* `adaptiveBlockSensitivityQueryBound_of_polynomial`: deduces adaptive query bounds from
  polynomial block sensitivity bounds.
* `adaptiveBlockSensitivityQueryBound`: establishes the bounded error and exact adaptive bounds.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Matrix
open scoped Classical BigOperators

/-- Polynomial block sensitivity bounds imply bounds `16T²` for error at most one third and
`8T²` for exact computation by well formed observed circuits of query depth `T`. -/
theorem adaptiveBlockSensitivityQueryBound_of_polynomial
    (hpoly : ApproximatePolynomialBlockSensitivity) : AdaptiveBlockSensitivityQueryBound := by
  intro n W _ _ _ P ψ f hP hψ
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [Normalized] at hψ
  obtain ⟨p,hdeg,_hmulti,heval⟩ :=
    observed_actual_multilinear_acceptance_polynomial n W P ψ hn hP hψ
  have hrange (x : Fin n → Bool) :
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1 := by
    rw [heval x]
    exact ⟨observedAcceptance_nonneg _ P ψ,
      observedAcceptance_le_one _ (workspaceBitOracle_unitary x) P hP hψ⟩
  have hdegree : (p.totalDegree : ℝ)^2 ≤ (2*(observedQueryDepth P : ℝ))^2 := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr
    exact_mod_cast hdeg
  constructor
  · intro herr
    have hb := hpoly n f p (1/3) (by norm_num) (by norm_num) (fun x =>
      ⟨(hrange x).1,(hrange x).2,by rw [heval x]; exact herr x⟩)
    have hreal : (blockSensitivity f : ℝ) ≤ 16*(observedQueryDepth P : ℝ)^2 := by
      nlinarith
    exact_mod_cast hreal
  · intro hexact
    have hb := hpoly n f p 0 (by norm_num) (by norm_num) (fun x =>
      ⟨(hrange x).1,(hrange x).2,by rw [heval x,hexact x]; norm_num⟩)
    have hreal : (blockSensitivity f : ℝ) ≤ 8*(observedQueryDepth P : ℝ)^2 := by
      nlinarith
    exact_mod_cast hreal

/-- Well formed adaptive observed circuits computing a Boolean function have block sensitivity
at most `16T²` with error at most one third and at most `8T²` for exact computation, where
`T` is query depth. This is the adaptive form of the polynomial method in [Beals et al.,
Theorem 4.13][BealsEtAl2001]. -/
theorem adaptiveBlockSensitivityQueryBound : AdaptiveBlockSensitivityQueryBound :=
  adaptiveBlockSensitivityQueryBound_of_polynomial approximatePolynomialBlockSensitivity

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
