/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRiskWoerner18.VaRQuantile.SourceVaRBisection

set_option backward.isDefEq.respectTransparency false

/-!
# The source CVaR tail readout of Eqs. (6)--(7)

Woerner--Egger, arXiv:1806.06893v1, Section II, Eqs. (6)--(7). Having fixed
`l_alpha = VaR_alpha(X)`, the paper applies the payoff

`f(i) = (i / l_alpha) * f_{l_alpha}(i)`

to the prepared state, so that the accepted-flag probability of the last qubit is
`sum_{i <= l_alpha} (i / l_alpha) p_i`. Because that mass does not sum to one but to
`P[X <= l_alpha]`, the paper multiplies by `l_alpha` and divides by the already
estimated lower-tail mass to obtain Eq. (7).

Both steps are recorded here at the source's level: the flag probability of the
actual preparation, and the normalisation that turns it into the paper's CVaR
target. The paper's normalisation reuses the VaR-stage estimate of `P[X <= l]`, so
the target below is written against the true lower-tail mass; how estimation error
propagates is the separate question handled in the frozen `CVaREstimation` package.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Papers.QRiskWoerner18.PayoffMean
open Qatlib.Papers.QRiskWoerner18.VaRQuantile
open scoped BigOperators

namespace Qatlib.Papers.QRiskWoerner18.CVaREstimation

/-- Eq. (6): the CVaR payoff `f(i) = (i / l) * f_l(i)`, with the paper's division
convention at `l = 0`. -/
noncomputable def sourceCVaRPayoff (l : ℕ) (i : ℕ) : ℝ :=
  (i : ℝ) / (l : ℝ) * sourceThresholdPayoff l i

/-- The accepted-flag mass of Eq. (6), `sum_i p_i (i / l) f_l(i)`. -/
noncomputable def sourceCVaRFlagMass {n : ℕ} (p : FinDist (Fin (2 ^ n))) (l : ℕ) : ℝ :=
  ∑ i : Fin (2 ^ n), p.prob i * sourceCVaRPayoff l (i : ℕ)

/-- The paper's Eq. (7) CVaR target: multiply the flag mass by `l_alpha` and divide by
the lower-tail mass `P[X <= l_alpha]`. -/
noncomputable def sourceCVaRTarget {n : ℕ} (p : FinDist (Fin (2 ^ n))) (l : ℕ) : ℝ :=
  (l : ℝ) * sourceCVaRFlagMass p l / sourceCDF p l

/-- For a positive level the CVaR payoff of Eq. (6) stays inside the source payoff
range `[0, 1]`. -/
theorem sourceCVaRPayoff_mem_Icc (l : ℕ) (hl : 0 < l) (i : ℕ) :
    sourceCVaRPayoff l i ∈ Set.Icc (0 : ℝ) 1 := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  unfold sourceCVaRPayoff sourceThresholdPayoff
  by_cases h : i ≤ l
  · rw [if_pos h]
    refine ⟨mul_nonneg (by positivity) (by norm_num), ?_⟩
    have hi : (i : ℝ) ≤ (l : ℝ) := by exact_mod_cast h
    rw [mul_one]
    exact div_le_one hlR |>.mpr hi
  · rw [if_neg h]
    norm_num

/-- **Source Eq. (6).** For `l > 0`, applying the CVaR payoff to the actual Eq. (3)
preparation makes the accepted-flag probability equal `sum_i p_i (i/l) f_l(i)`. -/
theorem source_cvar_flag_probability (n : ℕ) (p : FinDist (Fin (2 ^ n))) (l : ℕ)
    (hl : 0 < l) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ)) :
    MeasureProb
        (ApplyGate (payoffPreparation A (fun i => sourceCVaRPayoff l (i : ℕ)))
          (Ket (sourceZero n, false)))
        (Finset.univ.filter (fun q : Fin (2 ^ n) × Bool => q.2 = true)) =
      sourceCVaRFlagMass p l := by
  have hf : ∀ i : Fin (2 ^ n), sourceCVaRPayoff l (i : ℕ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => sourceCVaRPayoff_mem_Icc l hl (i : ℕ)
  have hborn := source_born_probability n p A hcolumn
  have hflag := (payoff_actual_rotation_and_mean A (sourceZero n)
    (fun i => sourceCVaRPayoff l (i : ℕ)) hA hf).2
  rw [hflag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hborn i]

/-- **Source Eq. (7).** For `l > 0` and a positive lower-tail mass, multiplying the
flag mass by `l` and dividing by `P[X <= l]` gives the conditional lower-tail readout
`sum_i i p_i f_l(i) / P[X <= l]`, i.e. exactly the paper's CVaR normalisation. -/
theorem source_cvar_normalization (n : ℕ) (p : FinDist (Fin (2 ^ n))) (l : ℕ)
    (hl : 0 < l) (hC : 0 < sourceCDF p l) :
    sourceCVaRTarget p l =
      (∑ i : Fin (2 ^ n), p.prob i * ((i : ℝ) * sourceThresholdPayoff l (i : ℕ))) /
        sourceCDF p l := by
  have hlR : ((l : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
    linarith
  have hCne : sourceCDF p l ≠ 0 := ne_of_gt hC
  have hterm : ∀ i : Fin (2 ^ n),
      (l : ℝ) * (p.prob i * ((i : ℝ) / (l : ℝ) * sourceThresholdPayoff l (i : ℕ))) =
        p.prob i * ((i : ℝ) * sourceThresholdPayoff l (i : ℕ)) := by
    intro i
    field_simp
  have hsum : (l : ℝ) * sourceCVaRFlagMass p l =
      ∑ i : Fin (2 ^ n), p.prob i * ((i : ℝ) * sourceThresholdPayoff l (i : ℕ)) := by
    unfold sourceCVaRFlagMass sourceCVaRPayoff
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  unfold sourceCVaRTarget
  rw [div_eq_div_iff hCne hCne, hsum, mul_comm]

end Qatlib.Papers.QRiskWoerner18.CVaREstimation
