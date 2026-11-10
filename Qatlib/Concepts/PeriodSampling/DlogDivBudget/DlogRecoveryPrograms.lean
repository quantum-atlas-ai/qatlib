/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open Qatlib
open scoped Classical

def dlogIsPrimePower (w : ℕ) : Prop := ∃ ℓ e, Nat.Prime ℓ ∧ 1 ≤ e ∧ ℓ ^ e = w

instance instDecidableDlogIsPrimePowerAnd : DecidablePred
    (fun w : ℕ => dlogIsPrimePower w ∧ 18 < w) :=
  fun w => Classical.propDecidable _

def dlogGoodCType (p q : ℕ) : Type := {c : Fin q // dlogSmallResidue p q c}

instance instDlogGoodCTypeFintype (p q : ℕ) : Fintype (dlogGoodCType p q) :=
  Subtype.fintype _

instance instDlogGoodCTypeDecidableEq (p q : ℕ) : DecidableEq (dlogGoodCType p q) :=
  Subtype.instDecidableEq

instance instDlogGoodCTypeNonempty (p q : ℕ) [NeZero q] : Nonempty (dlogGoodCType p q) :=
  ⟨⟨0, by
    unfold dlogSmallResidue centeredResidue
    have hv : ((0 : Fin q) : ℕ) = 0 := by simp
    rw [show (((0 : Fin q) : ℕ) * (p - 1) : ℤ) = 0 by rw [hv]; simp]
    simp only [Int.zero_emod]
    split
    · simp only [abs_zero, Int.cast_zero]
      positivity
    · exfalso
      have h2 : (0 : ℤ) ≤ (q : ℤ) / 2 :=
        Int.ediv_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ))
          (by norm_num : (0 : ℤ) ≤ 2)
      exact absurd h2 (by assumption)⟩⟩

noncomputable def dlogUniformGoodLaw (p q : ℕ) [NeZero q] :
    FinDist (dlogGoodCType p q) where
  prob _ := (Fintype.card (dlogGoodCType p q) : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hne : ((Fintype.card (dlogGoodCType p q) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

def dlogCommonPpDivides (p q : ℕ) {t : ℕ}
    (ω : Fin t → dlogGoodCType p q) : Prop :=
  ∃ w ∈ (Nat.divisors (p - 1)).filter
      (fun w => dlogIsPrimePower w ∧ 18 < w),
    ∀ i, (w : ℤ) ∣ dlogCprime p q (ω i).val

instance dlogCommonPpDividesDecidable (p q : ℕ) {t : ℕ} :
    DecidablePred (dlogCommonPpDivides (p := p) (q := q) (t := t)) :=
  fun ω => Classical.propDecidable _

def dlogGoodOutcome (p q r : ℕ) (o : Fin q × Fin q × ZMod p) : Prop :=
  dlogGoodPair p q r o.1 o.2.1

instance instDecidableDlogGoodOutcome (p q r : ℕ) :
    DecidablePred (dlogGoodOutcome p q r) := fun o => Classical.propDecidable _

def dlogGoodCountGE (p q r t L : ℕ)
    (ω : Fin L → Fin q × Fin q × ZMod p) : Prop :=
  (t : ℝ) ≤ ∑ j, if dlogGoodOutcome p q r (ω j) then (1 : ℝ) else 0

instance instDecidableDlogGoodCountGE (p q r t L : ℕ) :
    DecidablePred (dlogGoodCountGE p q r t L) :=
  fun ω => Classical.propDecidable _

noncomputable def dlogBornLaw (p q : ℕ) [NeZero p] (g x : ZMod p)
    (hnorm : Normalized (dlogTwoDimState p q g x)) :
    FinDist (Fin q × Fin q × ZMod p) where
  prob o := BornProb (dlogTwoDimState p q g x) o
  nonneg o := bornProb_nonneg _ o
  sum_one := hnorm

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
