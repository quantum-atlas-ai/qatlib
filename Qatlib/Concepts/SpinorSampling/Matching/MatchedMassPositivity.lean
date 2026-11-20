/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Matching.MatchedEventSymmetry
public import Qatlib.Concepts.SpinorSampling.Matching.MatchedFiberConstruction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Mass Positivity

Matched Mass Positivity constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators

variable {S : Type} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in

/-- Every pair of fixed arrays has positive joint point mass under the independent uniform
cohort laws on a nonempty site space. -/
theorem pairAddressMass_pos {S : Type} [_scopeInst0 : Fintype S] [_scopeInst1 : DecidableEq S] [Nonempty S]
    {n m : ℕ} (z : (Fin n → S) × (Fin m → S)) : 0 < pairAddressMass z := by
  unfold pairAddressMass
  have hJ : 0 < (cohortLaw (uniformLaw S) n).prob z.1 := by
    change 0 < ∏ i : Fin n, (uniformLaw S).prob (z.1 i)
    apply Finset.prod_pos
    intro i hi
    unfold uniformLaw
    positivity
  have hK : 0 < (cohortLaw (uniformLaw S) m).prob z.2 := by
    change 0 < ∏ i : Fin m, (uniformLaw S).prob (z.2 i)
    apply Finset.prod_pos
    intro i hi
    unfold uniformLaw
    positivity
  exact mul_pos hJ hK

/-- The exact matched-set event for `A` has positive mass when `A` has positive size and both
uniform cohorts are at least that long. -/
theorem matched_fiber_filter_mass_pos [Nonempty S]
    (τ : Equiv.Perm S) (A : Finset S) {k n m : ℕ}
    (hcard : A.card=k) (hk0 : 0 < k) (hkn : k ≤ n) (hkm : k ≤ m) :
    0 < (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => matchedSites z.1 z.2 τ=A), pairAddressMass z) := by
  obtain ⟨J,K,hJ⟩ := padded_matched_fiber_nonempty τ A hcard hk0 hkn hkm
  let z : (Fin n → S) × (Fin m → S) := (J,K)
  have hz : z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => matchedSites z.1 z.2 τ=A) := by
    simp [z,hJ]
  apply Finset.sum_pos'
  · intro x hx
    exact (pairAddressMass_pos x).le
  · exact ⟨z,hz,pairAddressMass_pos z⟩

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.pairAddressMass_pos
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_fiber_filter_mass_pos
