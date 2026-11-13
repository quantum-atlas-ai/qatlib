/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
import Qatlib.Concepts.SearchStopping.GroverSuccess.Section2HalfIterationsSubgoalTigh

/-!
# Q2 simple-differential distinguisher scales

`simpleMarkedFraction` sets the exponential marked scale for a simple differential. The
classical and Q2 cost expressions satisfy an exact quadratic relation, and
`grover_half_budget_iterations` gives a finite-state Grover success guarantee with an explicit
iteration bound. The mathematical context is [KaplanEtAl2015].

## Main statements

* `q2_simple_quadratic_speedup`: The classical simple-differential cost expression equals half
  the square of the Q2 expression.
* `grover_half_budget_iterations`: For marked fraction `0 < ε < 1` on a nonempty finite domain,
  some Grover iteration count at most `π/(8√ε) + 1` achieves marked probability at least one
  half.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

open Complexity

/-- The marked-fraction expression `2^(-hS)` for a simple differential. -/
noncomputable def simpleMarkedFraction (hS : ℝ) : ℝ := pow2 (-hS)

/-- The Q2 simple-differential distinguisher cost expression `2^(hS/2+1)`. -/
noncomputable def q2SimpleDistinguisherCost (hS : ℝ) : ℝ := pow2 (hS / 2 + 1)

/-- The classical simple-differential distinguisher cost expression `2^(hS+1)`. -/
noncomputable def classicalSimpleDistinguisherCost (hS : ℝ) : ℝ := pow2 (hS + 1)

/-- The reciprocal square root of `simpleMarkedFraction hS` is `2^(hS/2)`. See [KaplanEtAl2015]. -/
theorem q2_simple_grover_iterations (hS : ℝ) :
    (Real.sqrt (simpleMarkedFraction hS))⁻¹ = pow2 (hS / 2) := by
  unfold simpleMarkedFraction
  exact inv_sqrt_pow2_neg hS

/-- The Q2 simple-differential cost expression is twice `2^(hS/2)`. See [KaplanEtAl2015]. -/
theorem q2_simple_distinguisher_cost (hS : ℝ) :
    q2SimpleDistinguisherCost hS = 2 * pow2 (hS / 2) := by
  unfold q2SimpleDistinguisherCost
  rw [pow2_add, pow2_one]
  ring

/-- The classical simple-differential cost expression equals half the square of the Q2
expression. See [KaplanEtAl2015]. -/
theorem q2_simple_quadratic_speedup (hS : ℝ) :
    classicalSimpleDistinguisherCost hS = q2SimpleDistinguisherCost hS ^ 2 / 2 := by
  unfold classicalSimpleDistinguisherCost q2SimpleDistinguisherCost
  have hsq : pow2 (hS / 2 + 1) ^ 2 = pow2 (hS + 2) := by
    rw [← Real.rpow_two, ← pow2_mul]
    congr 1
    ring
  rw [hsq]
  have hhalf : (2 : ℝ)⁻¹ = pow2 (-1) := by
    rw [pow2_neg, pow2_one]
  rw [div_eq_mul_inv, hhalf, ← pow2_add]
  congr 1
  ring

/-- For marked fraction `0 < ε < 1` on a nonempty finite domain, some Grover iteration count at
most `π/(8√ε) + 1` achieves marked probability at least one half. See [KaplanEtAl2015]. -/
theorem grover_half_budget_iterations
    {I : Type*} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I)
    (A : Finset I) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hfrac : (A.card : ℝ) / (Fintype.card I : ℝ) = ε) :
    ∃ k : ℕ, (k : ℝ) ≤ Real.pi / (8 * Real.sqrt ε) + 1 ∧
      1 / 2 ≤ Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Concepts.SearchStopping.KnownCount.GroverState A k) A := by
  have hsnonneg : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsle : Real.sqrt ε ≤ 1 := by
    have hs : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε0.le
    nlinarith
  have hslt : Real.sqrt ε < 1 := by
    have hs : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε0.le
    nlinarith
  set θ : ℝ := Real.arcsin (Real.sqrt ε) with hθdef
  have hsin : Real.sin θ = Real.sqrt ε := by
    rw [hθdef]
    exact Real.sin_arcsin (by linarith) hsle
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hε0)
  have hθupper : θ < Real.pi / 2 := by
    rw [hθdef]
    exact Real.arcsin_lt_pi_div_two.mpr hslt
  have hangle : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ) := by
    rw [hsin, Real.sq_sqrt hε0.le, hfrac]
  have hsub :=
    Qatlib.Concepts.SearchStopping.GroverSuccess.section2HalfIterationsSubgoal
  obtain ⟨k, hk, hsucc⟩ := hsub I hN A θ hθpos hθupper hangle
  refine ⟨k, ?_, hsucc⟩
  have hsinlt : Real.sqrt ε < θ := by
    have := Real.sin_lt hθpos
    rwa [hsin] at this
  have hmul : 8 * Real.sqrt ε ≤ 8 * θ := by linarith
  have hdiv : Real.pi / (8 * θ) ≤ Real.pi / (8 * Real.sqrt ε) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hmul
  linarith

end Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
