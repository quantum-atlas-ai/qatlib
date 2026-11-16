/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteGroups.CyclicActions.Center
public import Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition.Lemma32

@[expose] public section


/-! # Actual commutation implied by the pinned Sigma model

The literal source hypotheses force every pair of Sigma elements to commute.
This diagnoses why no noncommuting pair can satisfy the old Lemma 3.2 header;
it does not count a proof from that impossible premise as an algorithm result
or refute the source's conditional statement (arXiv:1001.0608v1).
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement
open Qatlib.Foundations.FiniteGroups.CyclicActions.Center
open Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition

namespace Qatlib.Papers.GroupIsom10.MainResults.SigmaDiag

/-- Every actual pair in the pinned Sigma family commutes under its full hypotheses. -/
theorem sourceSigmaComm {G : Type*} [Group G] [Fintype G]
    {A : Subgroup G} {y : G} {m : ℕ} {S : Set G}
    (hD : InD A y m) (hS : IsSigma S) {w z : G} (hw : w ∈ S) (hz : z ∈ S) :
    w * z = z * w := by
  by_contra h
  have hne : ⁅w, z⁆ ≠ 1 := fun he => h (commutatorElement_eq_one_iff_mul_comm.mp he)
  by_cases hwA : w ∈ A
  · exact h (centralOfCopr A hD.normal hD.comm hwA (hS.coprime w hw) z)
  · have hzA : z ∈ A := by
      by_contra hzA
      exact not_both_not_mem hD hS hw hz hne ⟨hwA, hzA⟩
    exact h (centralOfCopr A hD.normal hD.comm hzA (hS.coprime z hz) w).symm

end Qatlib.Papers.GroupIsom10.MainResults.SigmaDiag
