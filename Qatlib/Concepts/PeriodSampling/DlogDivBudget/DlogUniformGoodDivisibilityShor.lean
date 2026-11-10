/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogUniformGoodDivisibilityStat
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogGoodPairCounting
import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogPrimePowerDivisibilityShor
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.DlogGoodProb
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget
open Qatlib
open scoped Classical BigOperators

theorem dlog_probEvent_one {X : Type} [Fintype X] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] :
    law.probEvent (L := 1) (fun ω => E (ω 0)) =
      ∑ x ∈ Finset.univ.filter E, law.prob x := by
  have h := law.expect_coord (L := 1) 0 (fun x => if E x then (1 : ℝ) else 0)
  simpa only [FinDist.probEvent, Finset.sum_filter, mul_ite, mul_one, mul_zero] using h

theorem dlog_uniform_good_divisibility_mass (p q w : ℕ) [NeZero q] :
    (dlogUniformGoodLaw p q).probEvent (L := 1)
      (fun ω => (w : ℤ) ∣ dlogCprime p q (ω 0).val) =
    ((Finset.univ.filter fun c : Fin q =>
      dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c).card : ℝ) /
      (Fintype.card (dlogGoodCType p q) : ℝ) := by
  rw [dlog_probEvent_one (dlogUniformGoodLaw p q)
    (fun c : dlogGoodCType p q => (w : ℤ) ∣ dlogCprime p q c.val)]
  simp only [dlogUniformGoodLaw, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 1
  congr 1
  rw [← Fintype.card_subtype]
  rw [← Fintype.card_subtype]
  apply Fintype.card_congr
  exact
    { toFun := fun c => ⟨c.val.val, c.val.property, c.property⟩
      invFun := fun c => ⟨⟨c.val, c.property.1⟩, c.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem dlogUniformGoodDivisibility : DlogUniformGoodDivisibility := by
  intro p q _ _ hprime hp hpq hq w hw hwp
  rw [dlog_uniform_good_divisibility_mass]
  have hcount := (dlogGoodPairCounting p q 0 hprime hp hpq).1
  have hdiv := (dlogPrimePowerDivisibility p q hprime hp hpq hq).2.2 w hw hwp
  have hcard : Fintype.card (dlogGoodCType p q) =
      (Finset.univ.filter fun c : Fin q => dlogSmallResidue p q c).card :=
    Fintype.card_subtype _
  have hcpos : (0 : ℝ) < Fintype.card (dlogGoodCType p q) := by
    exact_mod_cast Fintype.card_pos
  have hcountR : ((q / 12 : ℕ) : ℝ) ≤ Fintype.card (dlogGoodCType p q) := by
    rw [hcard]
    exact_mod_cast hcount
  have hdivR : ((Finset.univ.filter fun c : Fin q =>
      dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c).card : ℝ) ≤
      (((p - 1) / w + 1 : ℕ) : ℝ) := by exact_mod_cast hdiv
  calc
    _ ≤ ((Finset.univ.filter fun c : Fin q =>
        dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c).card : ℝ) /
        (Fintype.card (dlogGoodCType p q) : ℝ) *
        (Fintype.card (dlogGoodCType p q) : ℝ) :=
      mul_le_mul_of_nonneg_left hcountR (by positivity)
    _ = _ := div_mul_cancel₀ _ (ne_of_gt hcpos)
    _ ≤ _ := hdivR

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
