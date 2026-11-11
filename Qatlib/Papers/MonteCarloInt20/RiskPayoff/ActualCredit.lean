/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.RiskPayoff.CreditLoss
import Qatlib.Papers.MonteCarloInt20.RiskPayoff.ExpectedShortfall

/-!
# Finite credit scenarios and atomic tail risk

`scenarioLoss` evaluates the one-factor credit portfolio loss on a scenario space. The module
transfers exposure bounds to strict-tail conditional means and normalized payoffs, then
constructs a two-scenario, one-obligor credit example.

The binary example has an atom at the threshold: its strict-tail conditional mean is one, while
its expected shortfall for selected mass `3/4` is `2/3`. This makes the distinction between the
two risk quantities explicit in the finite credit model. See [KanekoEtAl2020].

## Main statements

* `credit_conditional_bounds` and `credit_normalized_payoff`: bounds for credit risk payoffs.
* `binary_selected_law`: fractional selection of the threshold atom.
* `binary_tail_ES_counter`: distinct strict-tail and expected-shortfall values.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.CreditLoss
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.StrictTail
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.ExpectedShortfall

namespace Qatlib.Papers.MonteCarloInt20.RiskPayoff.ActualCredit

/-- The credit portfolio loss obtained by evaluating common and idiosyncratic factors in a
scenario. -/
def scenarioLoss {X : Type} (D : ℕ) (E a threshold : Fin D → ℝ) (common : X → ℝ) (idio : X → Fin D → ℝ) : X → ℝ :=
  fun x => loss D E a threshold (common x) (idio x)

/-- With exposures in `[0,1]` and positive strict-tail mass, the conditional expected credit
loss lies in `[0,D]`. -/
theorem credit_conditional_bounds {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (D : ℕ) (E a threshold : Fin D → ℝ) (common : X → ℝ) (idio : X → Fin D → ℝ)
    (hE : ∀ i,E i ∈ Set.Icc (0:ℝ) 1) (q : ℝ)
    (hT : 0<tailMass p (scenarioLoss D E a threshold common idio) q) :
    (tailLaw p (scenarioLoss D E a threshold common idio) q hT).expect
      (scenarioLoss D E a threshold common idio) ∈ Set.Icc (0:ℝ) D :=
  tailLaw_mean_bounds p _ q D (fun x => loss_bounds D E a threshold (common x) (idio x) hE) hT

/-- With exposures in `[0,1]`, nonnegative scale `C`, and `C*D ≤ 1`, the normalized strict-tail
credit payoff lies in `[0,1]`. -/
theorem credit_normalized_payoff {X : Type} (D : ℕ) (E a threshold : Fin D → ℝ)
    (common : X → ℝ) (idio : X → Fin D → ℝ) (hE : ∀ i,E i ∈ Set.Icc (0:ℝ) 1)
    (C q : ℝ) (hC : 0≤C) (hCD : C*D≤1) (x : X) :
    normalizedPayoff C q (scenarioLoss D E a threshold common idio x) ∈ Set.Icc (0:ℝ) 1 :=
  normalizedPayoff_bounds C q _ D hC (loss_bounds D E a threshold (common x) (idio x) hE) hCD

/-- The uniform finite probability law on the two Boolean scenarios. -/
def halfLaw : FinDist Bool where
  prob _ := 1/2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The binary loss, equal to one in the true scenario and zero in the false scenario. -/
def binaryLoss (b : Bool) : ℝ := if b then 1 else 0

/-- The binary loss is realized by the displayed one-obligor credit model with unit exposure and
zero factor loading. -/
theorem binaryLoss_is_credit (b : Bool) : binaryLoss b=
    loss 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 (fun _ => if b then -1 else 1) := by
  cases b <;> norm_num [binaryLoss,loss,theta,factor]

/-- At threshold zero, the binary loss has strict-tail mass, threshold-atom mass, and
unnormalized tail loss all equal to `1/2`. -/
theorem binary_tail_atom : tailMass halfLaw binaryLoss 0=1/2 ∧ atomMass halfLaw binaryLoss 0=1/2 ∧ tailLoss halfLaw binaryLoss 0=1/2 := by
  norm_num [tailMass,tailLoss,tailWeight,atomMass,atomWeight,halfLaw,binaryLoss,Fintype.sum_bool]

/-- Threshold zero brackets the upper-tail selection mass `3/4` for the binary loss. -/
theorem binary_quantile : QuantileBracket halfLaw binaryLoss 0 (3/4) := by
  rw [QuantileBracket,binary_tail_atom.1,binary_tail_atom.2.1]
  norm_num

/-- The conditional mean of the binary loss strictly above zero is one. -/
theorem binary_strict_mean :
    (tailLaw halfLaw binaryLoss 0 (by rw [binary_tail_atom.1]; norm_num)).expect binaryLoss=1 := by
  rw [tailLaw_mean,binary_tail_atom.1,binary_tail_atom.2.2]
  norm_num

/-- The expected shortfall of the binary loss for upper-tail selection mass `3/4` is `2/3`. -/
theorem binary_expected_shortfall : expectedShortfall halfLaw binaryLoss (3/4)=2/3 := by
  rw [expectedShortfall_formula halfLaw binaryLoss 0 (3/4) (by norm_num) binary_quantile,
    binary_tail_atom.1,binary_tail_atom.2.2]
  norm_num

/-- The selected binary law at mass `3/4` assigns probability `1/3` to false and `2/3` to true. -/
theorem binary_selected_law :
    (selectedLaw halfLaw binaryLoss 0 (3/4) (by norm_num) binary_quantile).prob false=1/3 ∧
    (selectedLaw halfLaw binaryLoss 0 (3/4) (by norm_num) binary_quantile).prob true=2/3 := by
  norm_num [selectedLaw,selectedWeight,tailWeight,atomWeight,atomFraction,tailMass,atomMass,halfLaw,binaryLoss,Fintype.sum_bool]

/-- No real threshold gives the binary loss a strict-tail mass of `3/4`. See [KanekoEtAl2020]. -/
theorem binary_no_exact_tail_quantile (q : ℝ) : tailMass halfLaw binaryLoss q≠3/4 := by
  by_cases h0 : q<0
  · have h1 : q<1 := by linarith
    norm_num [tailMass,tailWeight,halfLaw,binaryLoss,Fintype.sum_bool,h0,h1]
  · by_cases h1 : q<1 <;> norm_num [tailMass,tailWeight,halfLaw,binaryLoss,Fintype.sum_bool,h0,h1]

/-- The binary credit example has strict-tail conditional mean one and expected shortfall `2/3`
at selection mass `3/4`, so these quantities differ. See [KanekoEtAl2020]. -/
theorem binary_tail_ES_counter :
    (tailLaw halfLaw binaryLoss 0 (by rw [binary_tail_atom.1]; norm_num)).expect binaryLoss=1 ∧
    expectedShortfall halfLaw binaryLoss (3/4)=2/3 ∧
    (tailLaw halfLaw binaryLoss 0 (by rw [binary_tail_atom.1]; norm_num)).expect binaryLoss≠
      expectedShortfall halfLaw binaryLoss (3/4) := by
  rw [binary_strict_mean,binary_expected_shortfall]
  norm_num

end Qatlib.Papers.MonteCarloInt20.RiskPayoff.ActualCredit
