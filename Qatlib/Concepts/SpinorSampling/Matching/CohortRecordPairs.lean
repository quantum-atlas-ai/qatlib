/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.SelectedSignProducts

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Cohort Record Pairs

Cohort Record Pairs constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

/-- Complete original `finite_expect_comm` guarantee for `CohortRecordPairs`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_comm {X Y : Type} [Fintype X] [Fintype Y]
    (p : FinDist X) (q : FinDist Y) (F : X → Y → ℝ) :
    p.expect (fun x => q.expect (F x))=q.expect (fun y => p.expect (fun x => F x y)) := by
  unfold FinDist.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `signed_cohort_expect` guarantee for `CohortRecordPairs`; all source hypotheses and output obligations are retained. -/
theorem signed_cohort_expect {n : ℕ} (a : S → ℝ) (ha : ∀ x, |a x| ≤ 1)
    (F : (Fin n → S × Bool) → ℝ) :
    (cohortLaw (signedRecordLaw a ha) n).expect F=
      (cohortLaw (uniformLaw S) n).expect (fun J =>
        (conditionalSigns a ha J).expect (fun Q => F (fun i => (J i,Q i)))) :=
  signed_cohort_disintegration a ha F

/-- Complete original `signed_pair_disintegration` guarantee for `CohortRecordPairs`; all source hypotheses and output obligations are retained. -/
theorem signed_pair_disintegration {n m : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (F : ((Fin n → S × Bool) × (Fin m → S × Bool)) → ℝ) :
    (productLaw (cohortLaw (signedRecordLaw a ha) n) (cohortLaw (signedRecordLaw b hb) m)).expect F=
      (cohortLaw (uniformLaw S) n).expect (fun J => (cohortLaw (uniformLaw S) m).expect (fun K =>
        (productLaw (conditionalSigns a ha J) (conditionalSigns b hb K)).expect
          (fun z => F (fun i => (J i,z.1 i),fun i => (K i,z.2 i))))) := by
  rw [product_law_expect,signed_cohort_expect a ha]
  congr 1
  funext J
  have hinner (Q : Fin n → Bool) :
      (cohortLaw (signedRecordLaw b hb) m).expect (fun ν => F (fun i => (J i,Q i),ν))=
        (cohortLaw (uniformLaw S) m).expect (fun K => (conditionalSigns b hb K).expect
          (fun R => F (fun i => (J i,Q i),fun i => (K i,R i)))) :=
    signed_cohort_expect b hb _
  simp_rw [hinner]
  rw [finite_expect_comm]
  congr 1
  funext K
  exact (product_law_expect (conditionalSigns a ha J) (conditionalSigns b hb K)
    (fun z => F (fun i => (J i,z.1 i),fun i => (K i,z.2 i)))).symm

/-- Complete original `signed_pair_site_projection` guarantee for `CohortRecordPairs`; all source hypotheses and output obligations are retained. -/
theorem signed_pair_site_projection {n m : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (F : ((Fin n → S) × (Fin m → S)) → ℝ) :
    (productLaw (cohortLaw (signedRecordLaw a ha) n) (cohortLaw (signedRecordLaw b hb) m)).expect
      (fun z => F (fun i => (z.1 i).1,fun i => (z.2 i).1))=
      (productLaw (cohortLaw (uniformLaw S) n) (cohortLaw (uniformLaw S) m)).expect F := by
  rw [signed_pair_disintegration,product_law_expect]
  simp only [finite_expect_const]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finite_expect_comm
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_pair_disintegration
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_pair_site_projection
