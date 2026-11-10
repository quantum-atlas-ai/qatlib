/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.RiskPayoff.CreditLoss
import Qatlib.Papers.MonteCarloInt20.RiskPayoff.ExpectedShortfall
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.CreditLoss
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.StrictTail
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.ExpectedShortfall

namespace Qatlib.Papers.MonteCarloInt20.RiskPayoff.ActualCredit

def scenarioLoss {X : Type} (D : ℕ) (E a threshold : Fin D → ℝ) (common : X → ℝ) (idio : X → Fin D → ℝ) : X → ℝ :=
  fun x => loss D E a threshold (common x) (idio x)

theorem credit_conditional_bounds {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (D : ℕ) (E a threshold : Fin D → ℝ) (common : X → ℝ) (idio : X → Fin D → ℝ)
    (hE : ∀ i,E i ∈ Set.Icc (0:ℝ) 1) (q : ℝ)
    (hT : 0<tailMass p (scenarioLoss D E a threshold common idio) q) :
    (tailLaw p (scenarioLoss D E a threshold common idio) q hT).expect
      (scenarioLoss D E a threshold common idio) ∈ Set.Icc (0:ℝ) D :=
  tailLaw_mean_bounds p _ q D (fun x => loss_bounds D E a threshold (common x) (idio x) hE) hT

theorem credit_normalized_payoff {X : Type} (D : ℕ) (E a threshold : Fin D → ℝ)
    (common : X → ℝ) (idio : X → Fin D → ℝ) (hE : ∀ i,E i ∈ Set.Icc (0:ℝ) 1)
    (C q : ℝ) (hC : 0≤C) (hCD : C*D≤1) (x : X) :
    normalizedPayoff C q (scenarioLoss D E a threshold common idio x) ∈ Set.Icc (0:ℝ) 1 :=
  normalizedPayoff_bounds C q _ D hC (loss_bounds D E a threshold (common x) (idio x) hE) hCD

def halfLaw : FinDist Bool where
  prob _ := 1/2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

def binaryLoss (b : Bool) : ℝ := if b then 1 else 0

theorem binaryLoss_is_credit (b : Bool) : binaryLoss b=
    loss 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 (fun _ => if b then -1 else 1) := by
  cases b <;> norm_num [binaryLoss,loss,theta,factor]

theorem binary_tail_atom : tailMass halfLaw binaryLoss 0=1/2 ∧ atomMass halfLaw binaryLoss 0=1/2 ∧ tailLoss halfLaw binaryLoss 0=1/2 := by
  norm_num [tailMass,tailLoss,tailWeight,atomMass,atomWeight,halfLaw,binaryLoss,Fintype.sum_bool]

theorem binary_quantile : QuantileBracket halfLaw binaryLoss 0 (3/4) := by
  rw [QuantileBracket,binary_tail_atom.1,binary_tail_atom.2.1]
  norm_num

theorem binary_strict_mean :
    (tailLaw halfLaw binaryLoss 0 (by rw [binary_tail_atom.1]; norm_num)).expect binaryLoss=1 := by
  rw [tailLaw_mean,binary_tail_atom.1,binary_tail_atom.2.2]
  norm_num

theorem binary_expected_shortfall : expectedShortfall halfLaw binaryLoss (3/4)=2/3 := by
  rw [expectedShortfall_formula halfLaw binaryLoss 0 (3/4) (by norm_num) binary_quantile,
    binary_tail_atom.1,binary_tail_atom.2.2]
  norm_num

theorem binary_selected_law :
    (selectedLaw halfLaw binaryLoss 0 (3/4) (by norm_num) binary_quantile).prob false=1/3 ∧
    (selectedLaw halfLaw binaryLoss 0 (3/4) (by norm_num) binary_quantile).prob true=2/3 := by
  norm_num [selectedLaw,selectedWeight,tailWeight,atomWeight,atomFraction,tailMass,atomMass,halfLaw,binaryLoss,Fintype.sum_bool]

theorem binary_no_exact_tail_quantile (q : ℝ) : tailMass halfLaw binaryLoss q≠3/4 := by
  by_cases h0 : q<0
  · have h1 : q<1 := by linarith
    norm_num [tailMass,tailWeight,halfLaw,binaryLoss,Fintype.sum_bool,h0,h1]
  · by_cases h1 : q<1 <;> norm_num [tailMass,tailWeight,halfLaw,binaryLoss,Fintype.sum_bool,h0,h1]

theorem binary_tail_ES_counter :
    (tailLaw halfLaw binaryLoss 0 (by rw [binary_tail_atom.1]; norm_num)).expect binaryLoss=1 ∧
    expectedShortfall halfLaw binaryLoss (3/4)=2/3 ∧
    (tailLaw halfLaw binaryLoss 0 (by rw [binary_tail_atom.1]; norm_num)).expect binaryLoss≠
      expectedShortfall halfLaw binaryLoss (3/4) := by
  rw [binary_strict_mean,binary_expected_shortfall]
  norm_num

end Qatlib.Papers.MonteCarloInt20.RiskPayoff.ActualCredit
