/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression
import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedProgressionWindow
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliAmplifiedNoise
import Qatlib.Concepts.AmpTransform.ErrorStream.ConditionalAmplifiedNoise
import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamSuccessMass
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation

/-!
# Finite noise sampling and candidate selection

This module defines finite Bernoulli noise streams, uniform fair-bit tapes, and threshold-based
draws for executions associated with amplified period recovery [Cornwell2014]. It also records
the general noise-envelope expression and its single-mark specialization.

Fresh observations unite a candidate progression with noise. `aqCandidateLikelihood` assigns a
Bernoulli likelihood expression to consistent observations, `aqFreshDisambiguate` selects a
compatible candidate by that expression, and `aqExecutionCost` keeps oracle-access and
classical-work charges separate.

## Main statements

* `bernoulliStreamLaw`: the finite product law of independent Bernoulli sites.
* `bernoulliFairStream`: generate threshold-based draws from a family of fair-bit tapes.
* `aqFreshDisambiguate`: select a compatible candidate by its likelihood expression.
* `aqFreshPassCost`: record the oracle and classical charges of a fresh pass.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

set_option autoImplicit false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib
open scoped Classical BigOperators

/-- The real envelope expression `(L + M^2) / ((N - L - M) * (L + M))`. -/
noncomputable def aqEnvelopeBound (N M L : ℝ) : ℝ :=
  (L + M ^ 2) / ((N - L - M) * (L + M))

/-- The single-mark real envelope expression `1 / (N - L - 1)`. -/
noncomputable def aqM1Envelope (N L : ℝ) : ℝ := 1 / (N - L - 1)

/-- The predicate that `L` lies in the open interval `(-1, N - 1)`. -/
def aqM1OpenWindow (N : ℕ) (L : ℝ) : Prop := -1 < L ∧ L < (N : ℝ) - 1

/-- The finite Boolean law with true probability `p` and false probability `1 - p`, for `0 ≤ p ≤
1`. -/
noncomputable def bernoulliSiteLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    cases b <;> simp [hp, sub_nonneg.mpr hp1]
  sum_one := by
    rw [Fintype.sum_bool]
    simp

/-- The product distribution of `N` independent Boolean sites with common Bernoulli parameter
`p`. -/
noncomputable def bernoulliStreamLaw (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FinDist (Fin N → Bool) where
  prob σ := (bernoulliSiteLaw p hp hp1).probOf σ
  nonneg σ := Finset.prod_nonneg fun i _ => (bernoulliSiteLaw p hp hp1).nonneg (σ i)
  sum_one := (bernoulliSiteLaw p hp hp1).sum_probOf N

/-- The uniform distribution on `k`-bit registers, assigning mass `2⁻ᵏ` to every register. -/
noncomputable def uniformFairTapeLaw (k : ℕ) : FinDist (Reg k) where
  prob ω := ((2 : ℝ) ^ k)⁻¹
  nonneg _ := by positivity
  sum_one := by
    classical
    have hcard : Fintype.card (Reg k) = 2 ^ k := card_reg k
    have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    calc
      ∑ _ω : Reg k, ((2 : ℝ) ^ k)⁻¹ = Fintype.card (Reg k) * ((2 : ℝ) ^ k)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (2 : ℝ) ^ k * ((2 : ℝ) ^ k)⁻¹ := by rw [hcard, Nat.cast_pow]; norm_num
      _ = 1 := by rw [mul_inv_cancel₀ h2]

/-- The product distribution of `N` independent uniform `k`-bit registers. -/
noncomputable def uniformFairTapeProductLaw (k N : ℕ) : FinDist (Fin N → Reg k) where
  prob tapes := (uniformFairTapeLaw k).probOf tapes
  nonneg tapes := Finset.prod_nonneg fun i _ => (uniformFairTapeLaw k).nonneg (tapes i)
  sum_one := (uniformFairTapeLaw k).sum_probOf N

/-- The natural-number floor of `p * 2^k` used as an integer threshold. -/
noncomputable def bernoulliFairThreshold (k : ℕ) (p : ℝ) : ℕ := Nat.floor (p * (2 : ℝ) ^ k)

/-- Return true exactly when the integer encoded by the `k`-bit register is below
`bernoulliFairThreshold k p`. -/
noncomputable def bernoulliFairDraw (k : ℕ) (p : ℝ) (bits : Reg k) : Bool :=
  decide ((bitVecEquiv k bits).val < bernoulliFairThreshold k p)

/-- Apply `bernoulliFairDraw k p` separately to each register in a length-`N` family of tapes. -/
noncomputable def bernoulliFairStream (k N : ℕ) (p : ℝ) (tapes : Fin N → Reg k) : Fin N → Bool :=
  fun i => bernoulliFairDraw k p (tapes i)

/-- The real ratio `bernoulliFairThreshold k p / 2^k` associated with the integer threshold. -/
noncomputable def bernoulliFairParameter (k : ℕ) (p : ℝ) : ℝ :=
  (bernoulliFairThreshold k p : ℝ) / (2 : ℝ) ^ k

/-- The union of the progression `aqProgressionSet N s M P` with a supplied noise set. -/
def aqFreshObservation (N s M P : ℕ) (noise : Finset (Fin N)) : Finset (Fin N) :=
  aqProgressionSet N s M P ∪ noise

/-- The union of the candidate progression with all positions at which the Boolean noise stream
is true. -/
def aqFreshMarked (N s M P : ℕ) (σ : Fin N → Bool) : Finset (Fin N) :=
  aqProgressionSet N s M P ∪ Finset.filter (fun i : Fin N => σ i = true) Finset.univ

/-- The predicate that the progression with candidate period `P` is contained in the observed
set. -/
def aqCandidateConsistent (N s M : ℕ) (P : ℕ) (obs : Finset (Fin N)) : Prop :=
  aqProgressionSet N s M P ⊆ obs

/-- The Bernoulli likelihood expression `p` to the number of observed sites outside the
candidate progression times `1 - p` to the number of unobserved sites outside it. The
expression is zero when the candidate progression is not contained in the observation. -/
noncomputable def aqCandidateLikelihood (N s M P : ℕ) (p : ℝ) (obs : Finset (Fin N)) : ℝ :=
  if aqCandidateConsistent N s M P obs then
    p ^ (obs \ aqProgressionSet N s M P).card *
      (1 - p) ^ ((Finset.univ \ aqProgressionSet N s M P) \ obs).card
  else 0

/-- The subset of candidate periods whose progressions are contained in the observed set. -/
noncomputable def aqFreshCompatible (N s M : ℕ) (cands : Finset ℕ) (obs : Finset (Fin N)) :
    Finset ℕ :=
  cands.filter fun P => aqCandidateConsistent N s M P obs

/-- Fold over the compatible candidate list, retaining the candidate with the largest likelihood
expression seen so far and keeping the current choice on ties. Return `none` when there are
no compatible candidates. -/
noncomputable def aqFreshDisambiguate (N s M : ℕ) (cands : Finset ℕ) (p : ℝ)
    (obs : Finset (Fin N)) : Option ℕ :=
  (aqFreshCompatible N s M cands obs).toList.foldl
    (fun best P => match best with
      | none => some P
      | some b =>
          if aqCandidateLikelihood N s M P p obs > aqCandidateLikelihood N s M b p obs then
            some P
          else some b)
    none

/-- The number of sites in the progression for `P'` that are absent from the progression for
`P`. -/
def aqCandidateSeparation (N s M P P' : ℕ) : ℕ :=
  (aqProgressionSet N s M P' \ aqProgressionSet N s M P).card

/-- A pair of natural-number charges recording oracle accesses and classical work. -/
structure aqExecutionCost where

  oracleAccesses : ℕ

  classicalWork : ℕ
  deriving DecidableEq, Repr

/-- Add oracle-access and classical-work charges componentwise. -/
def aqExecutionCost.add (a b : aqExecutionCost) : aqExecutionCost :=
  { oracleAccesses := a.oracleAccesses + b.oracleAccesses
    classicalWork := a.classicalWork + b.classicalWork }

/-- The fresh-pass cost record with `N * t` oracle accesses and `N * k + t` units of classical
work. -/
def aqFreshPassCost (N t k : ℕ) : aqExecutionCost :=
  { oracleAccesses := N * t
    classicalWork := N * k + t }

/-- The public amplification round count `aqRounds N M`. -/
noncomputable def aqPublicRoundCount (N M : ℕ) : ℕ := aqRounds N M

/-- The layer amplification round count `aqRounds N L`. -/
noncomputable def aqLayerRoundCount (N M L : ℕ) : ℕ := aqRounds N L

/-- The natural-number difference between the public round count and the layer round count. -/
noncomputable def aqLayerRoundGap (N M L : ℕ) : ℕ :=
    aqPublicRoundCount N M - aqLayerRoundCount N M L

end Qatlib.Concepts.AmpTransform.ErrorStream
