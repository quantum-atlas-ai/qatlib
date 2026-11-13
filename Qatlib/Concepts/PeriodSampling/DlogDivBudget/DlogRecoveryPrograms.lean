/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Finite sampling laws for discrete-logarithm recovery

This module defines finite distributions and events for the discrete-logarithm recovery analysis
in [Shor1997]. The distribution `dlogUniformGoodLaw` is uniform on small-residue first
coordinates, and `dlogCommonPpDivides` detects a common prime-power divisor of the sampled
scaled coefficients.

The module also defines good full outcomes, a threshold event for their count, and the Born
distribution `dlogBornLaw` associated with a normalized two-dimensional sampling state.

## Main statements

* `dlogUniformGoodLaw`: the uniform law on small-residue coordinates.
* `dlogCommonPpDivides`: the common prime-power divisibility event.
* `dlogGoodCountGE`: a lower threshold for the number of good outcomes.
* `dlogBornLaw`: the finite sampling law given by Born probabilities.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open Qatlib
open scoped Classical

/-- The natural number is a positive power of a prime. -/
def dlogIsPrimePower (w : ℕ) : Prop := ∃ ℓ e, Nat.Prime ℓ ∧ 1 ≤ e ∧ ℓ ^ e = w

instance instDecidableDlogIsPrimePowerAnd : DecidablePred
    (fun w : ℕ => dlogIsPrimePower w ∧ 18 < w) :=
  fun _w => Classical.propDecidable _

/-- The subtype of Fourier-sampling first coordinates satisfying `dlogSmallResidue p q`. -/
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

/-- The uniform finite probability distribution on the small-residue coordinate subtype. -/
noncomputable def dlogUniformGoodLaw (p q : ℕ) [NeZero q] :
    FinDist (dlogGoodCType p q) where
  prob _ := (Fintype.card (dlogGoodCType p q) : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hne : ((Fintype.card (dlogGoodCType p q) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- Some prime-power divisor of `p - 1` greater than eighteen divides every `dlogCprime` value
in the sample. -/
def dlogCommonPpDivides (p q : ℕ) {t : ℕ}
    (ω : Fin t → dlogGoodCType p q) : Prop :=
  ∃ w ∈ (Nat.divisors (p - 1)).filter
      (fun w => dlogIsPrimePower w ∧ 18 < w),
    ∀ i, (w : ℤ) ∣ dlogCprime p q (ω i).val

instance dlogCommonPpDividesDecidable (p q : ℕ) {t : ℕ} :
    DecidablePred (dlogCommonPpDivides (p := p) (q := q) (t := t)) :=
  fun _ω => Classical.propDecidable _

/-- The first two coordinates of a sampling outcome form a good discrete-logarithm pair. -/
def dlogGoodOutcome (p q r : ℕ) (o : Fin q × Fin q × ZMod p) : Prop :=
  dlogGoodPair p q r o.1 o.2.1

instance instDecidableDlogGoodOutcome (p q r : ℕ) :
    DecidablePred (dlogGoodOutcome p q r) := fun _o => Classical.propDecidable _

/-- At least `t` of the `L` sampled outcomes satisfy `dlogGoodOutcome`. -/
def dlogGoodCountGE (p q r t L : ℕ)
    (ω : Fin L → Fin q × Fin q × ZMod p) : Prop :=
  (t : ℝ) ≤ ∑ j, if dlogGoodOutcome p q r (ω j) then (1 : ℝ) else 0

instance instDecidableDlogGoodCountGE (p q r t L : ℕ) :
    DecidablePred (dlogGoodCountGE p q r t L) :=
  fun _ω => Classical.propDecidable _

/-- The finite Born-probability distribution of a normalized two-dimensional discrete-logarithm
sampling state. -/
noncomputable def dlogBornLaw (p q : ℕ) [NeZero p] (g x : ZMod p)
    (hnorm : Normalized (dlogTwoDimState p q g x)) :
    FinDist (Fin q × Fin q × ZMod p) where
  prob o := BornProb (dlogTwoDimState p q g x) o
  nonneg o := bornProb_nonneg _ o
  sum_one := hnorm

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
