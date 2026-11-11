/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellUnconditional
import Qatlib.Concepts.SpinorSampling.Matching.MatchedIntersectionConcentration

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Sparse Tail

Retained Bell Sparse Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m : ℕ}

/-- Complete original `cohort_observation_address_expect` guarantee for `RetainedBellSparseTail`; all source hypotheses and output obligations are retained. -/
theorem cohort_observation_address_expect (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (f : (Fin n → S) × (Fin m → S) → ℝ) :
    (cohortObservationLaw (n:=n) (m:=m) a b c k hz τ τ.injective).expect
      (fun ω => f (ω.1,ω.2.1))=
        (productLaw (cohortLaw (uniformLaw S) n) (cohortLaw (uniformLaw S) m)).expect f := by
  rw [product_law_expect]
  unfold FinDist.expect
  change (∑ ω : (J : Fin n → S) × (L : Fin m → S) × (matchedSites J L τ → Bool),_)=_
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro L _
  change (∑ h : matchedSites J L τ → Bool,
    ((cohortLaw (uniformLaw S) n).prob J*(cohortLaw (uniformLaw S) m).prob L*
      (nativeMatchedLaw a b c k hz J L τ τ.injective).prob h)*f (J,L))=
        (cohortLaw (uniformLaw S) n).prob J*((cohortLaw (uniformLaw S) m).prob L*f (J,L))
  calc
    _ = ((cohortLaw (uniformLaw S) n).prob J*(cohortLaw (uniformLaw S) m).prob L*f (J,L))*
        ∑ h,(nativeMatchedLaw a b c k hz J L τ τ.injective).prob h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [(nativeMatchedLaw a b c k hz J L τ τ.injective).sum_one]; ring

/-- Complete original `pooled_single_small_mass` guarantee for `RetainedBellSparseTail`; all source hypotheses and output obligations are retained. -/
theorem pooled_single_small_mass (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (r₀ : ℝ) :
    pooledSmallMass (n:=n) (m:=m) (K:=1) a b c k hz τ r₀=matchedSmallMass τ n m r₀ := by
  let p := cohortObservationLaw (n:=n) (m:=m) a b c k hz τ τ.injective
  let f := fun ω : CohortObservation n m τ =>
    if ((matchedSites ω.1 ω.2.1 τ).card : ℝ)<r₀ then (1 : ℝ) else 0
  have hpoint (ω : Fin 1 → CohortObservation n m τ) :
      (if (pooledMatches τ ω : ℝ)<r₀ then (1 : ℝ) else 0)=f (ω 0) := by
    simp [pooledMatches,observedRvec,f]
  unfold pooledSmallMass freshObservationBlocks
  simp_rw [hpoint]
  calc
    _ = p.expect f := p.expect_coord (0 : Fin 1) f
    _ = matchedSmallMass τ n m r₀ :=
      cohort_observation_address_expect a b c k hz τ
        (fun z => if ((matchedSites z.1 z.2 τ).card : ℝ)<r₀ then 1 else 0)

-- A genuine one-block guarantee: no small-match probability is supplied.
/-- Complete original `clipped_pooled_sparse_tail` guarantee for `RetainedBellSparseTail`; all source hypotheses and output obligations are retained. -/
theorem clipped_pooled_sparse_tail (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (hn0 : 0<n) (hn : n≤Fintype.card S) (hm : m≤Fintype.card S)
    (p₀ : ℚ) (ε : ℝ) (hmean : bellMean a b c k τ≤(p₀ : ℝ)) (hε : 0<ε) :
    (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ 1).expect
      (fun ω => if ε< |(clippedPooledMeanQ p₀ τ ω : ℝ)-bellMean a b c k τ| then 1 else 0)≤
        2*Real.exp (-(n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ)))+
          2*Real.exp (-((n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ)))*ε^2/
            (4*((p₀ : ℝ)+ε))) := by
  have ht := clipped_pooled_unconditional_tail (n:=n) (m:=m) (K:=1) a b c k hz τ p₀ ε
    ((n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))) hmean hε
  rw [pooled_single_small_mass] at ht
  exact ht.trans (add_le_add (matched_intersection_lower_tail τ n m hn0 hn hm) (le_refl _))

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.cohort_observation_address_expect
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_single_small_mass
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.clipped_pooled_sparse_tail
