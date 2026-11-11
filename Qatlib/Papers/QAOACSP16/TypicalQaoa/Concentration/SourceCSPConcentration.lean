/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel.SourceCSPModel

set_option backward.isDefEq.respectTransparency false

/-!
# Chebyshev concentration for typical CSP instances

Lin--Zhu, fixed arXiv:1601.01744v1, Section 4.3, equations (4.30)--(4.35)
(pp.10--11).

Inputs, exactly as in the paper:

* `hE` : the expected QAOA satisfied count over the random constraints is
  `(μ + Ω(1/√D)) m` (equation (4.31));
* `hvar` : its variance is at most `m (k(k-1)D + k)(D+1)` (equation (4.33)).

Output: with probability at least `1 - O(D³/m)` the QAOA expected count is at
least `μm + c m/(2√D)`, so the fraction is at least `μ + c/(2√D)`.

The Chebyshev step and all real arithmetic are proved here; the two analytic
inputs are supplied by the claim files.  This is the finite-distribution form
of the paper's argument, using `FinDist.chebyshev` from Frozen
`ProbabilityCore.Concentration`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.TypicalQaoa.Concentration

open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- One-sided Chebyshev: the lower tail below `E f - ε` has mass at most
`Var f / ε²`.  This is the form used in (4.34). -/
theorem lower_tail_chebyshev (law : FinDist Ω) (f : Ω → ℝ) (ε : ℝ) (hε : 0 < ε) :
    eventMass law (fun ω => f ω < law.expect f - ε) ≤ law.variance f / ε ^ 2 := by
  refine (eventMass_mono law _ _ ?_).trans (chebyshev_strict law f ε hε)
  intro ω hω
  have h1 : ε < law.expect f - f ω := by linarith
  have h2 : ε < |law.expect f - f ω| := by
    rw [abs_of_pos (by linarith)]
    linarith
  rwa [abs_sub_comm]

/-- The mass of the complement is one minus the mass of the event. -/
theorem eventMass_compl (law : FinDist Ω) (E : Ω → Prop) [DecidablePred E] :
    eventMass law (fun ω => ¬ E ω) = 1 - eventMass law E := by
  classical
  unfold eventMass
  have h := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset Ω)) (p := E) (f := law.prob)
  rw [law.sum_one] at h
  linarith

/-- Section 4.3 concentration, equations (4.33)--(4.35): under the expectation
and variance bounds the good event has probability at least
`1 - 4 k(k-1)D(D+1) D / (c² m)`.

Here `X ω` is the QAOA expected satisfied count on the instance sampled at `ω`,
`μ` is the random-assignment mean, `c` the advantage constant and `k` the arity
bound.  The factor `4` comes from evaluating Chebyshev at
`ε = c m/(2√D)` (a one-half slack, as in the paper's `Ω` notation). -/
theorem instance_tail_bound (law : FinDist Ω) (X : Ω → ℝ)
    (μ c : ℝ) (m D k : ℕ) (hm : 0 < m) (hD : 0 < D) (hc : 0 < c)
    (hE : μ * (m : ℝ) + c * (m : ℝ) / Real.sqrt (D : ℝ) ≤ law.expect X)
    (hvar : law.variance X ≤ (m : ℝ) * ((k : ℝ) * ((k : ℝ) - 1) * (D : ℝ) + (k : ℝ))
      * ((D : ℝ) + 1)) :
    1 - 4 * ((k : ℝ) * ((k : ℝ) - 1) * (D : ℝ) + (k : ℝ)) * ((D : ℝ) + 1) * (D : ℝ)
        / (c ^ 2 * (m : ℝ))
      ≤ eventMass law (fun ω => μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)) ≤ X ω) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hsqrt : (0 : ℝ) < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 hDR
  set ε : ℝ := c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (mul_pos hc hmR) (by linarith)
  -- the bad event is contained in the Chebyshev lower tail
  have htwo : c * (m : ℝ) / Real.sqrt (D : ℝ) - c * (m : ℝ) / (2 * Real.sqrt (D : ℝ))
      = c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)) := by
    field_simp [hsqrt.ne']
    ring
  have hsubset : ∀ ω, X ω < μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)) →
      X ω < law.expect X - ε := by
    intro ω hω
    have hge : μ * (m : ℝ) + c * (m : ℝ) / Real.sqrt (D : ℝ) - ε
        ≤ law.expect X - ε := by linarith [hE]
    have hleft : μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ))
        ≤ μ * (m : ℝ) + c * (m : ℝ) / Real.sqrt (D : ℝ) - ε := by
      rw [hεdef]
      linarith [htwo]
    linarith
  have hbad : eventMass law
      (fun ω => X ω < μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)))
      ≤ law.variance X / ε ^ 2 :=
    (eventMass_mono law _ _ hsubset).trans (lower_tail_chebyshev law X ε hε)
  -- Chebyshev threshold algebra
  have hεsq : ε ^ 2 = c ^ 2 * (m : ℝ) ^ 2 / (4 * (D : ℝ)) := by
    rw [hεdef]
    have hsq : (2 * Real.sqrt (D : ℝ)) ^ 2 = 4 * (D : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hDR.le]
      ring
    rw [div_pow, hsq, mul_pow]
  have hbound : law.variance X / ε ^ 2
      ≤ 4 * ((k : ℝ) * ((k : ℝ) - 1) * (D : ℝ) + (k : ℝ)) * ((D : ℝ) + 1) * (D : ℝ)
          / (c ^ 2 * (m : ℝ)) := by
    rw [hεsq]
    have hden : (0 : ℝ) < c ^ 2 * (m : ℝ) ^ 2 / (4 * (D : ℝ)) := by
      have h4D : (0 : ℝ) < 4 * (D : ℝ) := by linarith
      exact div_pos (mul_pos (pow_pos hc 2) (pow_pos hmR 2)) h4D
    rw [div_le_iff₀ hden]
    calc
      law.variance X ≤ (m : ℝ) * ((k : ℝ) * ((k : ℝ) - 1) * (D : ℝ) + (k : ℝ))
          * ((D : ℝ) + 1) := hvar
      _ = 4 * ((k : ℝ) * ((k : ℝ) - 1) * (D : ℝ) + (k : ℝ)) * ((D : ℝ) + 1) * (D : ℝ)
            / (c ^ 2 * (m : ℝ)) * (c ^ 2 * (m : ℝ) ^ 2 / (4 * (D : ℝ))) := by
        field_simp [hc.ne', hmR.ne', hDR.ne']
  -- complement
  have hcompl : eventMass law
      (fun ω => X ω < μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)))
      = 1 - eventMass law
          (fun ω => μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)) ≤ X ω) := by
    have := eventMass_compl law
      (fun ω => μ * (m : ℝ) + c * (m : ℝ) / (2 * Real.sqrt (D : ℝ)) ≤ X ω)
    simpa only [not_le] using this
  linarith [hbad.trans hbound]

end Qatlib.Papers.QAOACSP16.TypicalQaoa.Concentration
