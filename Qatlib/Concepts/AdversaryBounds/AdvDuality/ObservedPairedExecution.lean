/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryVisits
import Mathlib.Tactic.Abel

/-!
# Paired observed executions and inner products

`observedPairedTraces` and `observedPairedVisits` run an observed circuit with two oracles while
pairing equal measurement outcomes. Their projections recover the individual executions, and
`observed_paired_inner_telescope` expresses the change in the sum of terminal inner products as
a sum of query contributions. This supplies an adaptive branchwise identity for hybrid arguments
of the kind used in [BennettEtAl1997].

## Main statements

* `observedPairedTraces_metadata`: Paired terminal traces have equal classical metadata.
* `observed_paired_inner_telescope`: Only query steps contribute to the change in summed paired
  inner products.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Pairs terminal traces of the same observed circuit under two oracles and initial states,
matching the measurement outcomes in both executions. -/
noncomputable def observedPairedTraces (A B : Matrix I I ℂ) :
    ObservedCircuit I → QState I → QState I → List (BranchTrace I × BranchTrace I)
  | .halt accepted, psi, phi =>
      [({ state := psi, accepted := accepted, queries := 0, gates := 0,
          measurements := 0, outcomes := [] },
        { state := phi, accepted := accepted, queries := 0, gates := 0,
          measurements := 0, outcomes := [] })]
  | .step (.gate U) next, psi, phi =>
      (observedPairedTraces A B next (ApplyGate U psi) (ApplyGate U phi)).map
        (fun t => ({ t.1 with gates := t.1.gates + 1 },
          { t.2 with gates := t.2.gates + 1 }))
  | .step .query next, psi, phi =>
      (observedPairedTraces A B next (ApplyGate A psi) (ApplyGate B phi)).map
        (fun t => ({ t.1 with queries := t.1.queries + 1 },
          { t.2 with queries := t.2.queries + 1 }))
  | .measure n label next, psi, phi =>
      (List.ofFn (fun o : Fin n =>
        (observedPairedTraces A B (next o)
          (Collapse psi (Finset.univ.filter (fun i => label i = o)))
          (Collapse phi (Finset.univ.filter (fun i => label i = o)))).map
            (fun t =>
              ({ t.1 with measurements := t.1.measurements + 1, outcomes := (n, o.val) :: t.1.outcomes },
                { t.2 with measurements := t.2.measurements + 1, outcomes := (n, o.val) :: t.2.outcomes })))).flatten
  | .project M onFalse onTrue, psi, phi =>
      (observedPairedTraces A B onFalse
        (ProjectiveBranch M false psi) (ProjectiveBranch M false phi)).map
          (fun t =>
            ({ t.1 with measurements := t.1.measurements + 1, outcomes := (2, 0) :: t.1.outcomes },
              { t.2 with measurements := t.2.measurements + 1, outcomes := (2, 0) :: t.2.outcomes })) ++
      (observedPairedTraces A B onTrue
        (ProjectiveBranch M true psi) (ProjectiveBranch M true phi)).map
          (fun t =>
            ({ t.1 with measurements := t.1.measurements + 1, outcomes := (2, 1) :: t.1.outcomes },
              { t.2 with measurements := t.2.measurements + 1, outcomes := (2, 1) :: t.2.outcomes }))

/-- Lists pairs of states immediately before corresponding oracle queries, following matching
measurement outcomes in the two executions. -/
noncomputable def observedPairedVisits (A B : Matrix I I ℂ) :
    ObservedCircuit I → QState I → QState I → List (QState I × QState I)
  | .halt _, _, _ => []
  | .step (.gate U) next, psi, phi =>
      observedPairedVisits A B next (ApplyGate U psi) (ApplyGate U phi)
  | .step .query next, psi, phi =>
      (psi, phi) :: observedPairedVisits A B next (ApplyGate A psi) (ApplyGate B phi)
  | .measure n label next, psi, phi =>
      (List.ofFn (fun o : Fin n => observedPairedVisits A B (next o)
        (Collapse psi (Finset.univ.filter (fun i => label i = o)))
        (Collapse phi (Finset.univ.filter (fun i => label i = o))))).flatten
  | .project M onFalse onTrue, psi, phi =>
      observedPairedVisits A B onFalse
        (ProjectiveBranch M false psi) (ProjectiveBranch M false phi) ++
      observedPairedVisits A B onTrue
        (ProjectiveBranch M true psi) (ProjectiveBranch M true phi)

/-- Projecting paired terminal traces onto their first components recovers the observed traces
for oracle `A` and initial state `psi`. -/
theorem observedPairedTraces_left (A B : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi phi : QState I) :
    (observedPairedTraces A B P psi phi).map Prod.fst = observedTraces A P psi := by
  induction P generalizing psi phi with
  | halt accepted => rfl
  | step s next ih =>
    cases s with
    | gate U =>
      simpa only [observedPairedTraces, observedTraces, List.map_map,
        Function.comp_def] using
        congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with gates := t.gates + 1 }))
          (ih (ApplyGate U psi) (ApplyGate U phi))
    | query =>
      simpa only [observedPairedTraces, observedTraces, List.map_map,
        Function.comp_def] using
        congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with queries := t.queries + 1 }))
          (ih (ApplyGate A psi) (ApplyGate B phi))
  | measure n label next ih =>
    simp only [observedPairedTraces, observedTraces, List.map_flatten,
      List.map_ofFn, Function.comp_def]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext o
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun ts : List (BranchTrace I) =>
        ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (n, o.val) :: t.outcomes }))
        (ih o (Collapse psi (Finset.univ.filter (fun i => label i = o)))
          (Collapse phi (Finset.univ.filter (fun i => label i = o))))
  | project M onFalse onTrue ihFalse ihTrue =>
    simpa only [observedPairedTraces, observedTraces, List.map_append,
      List.map_map, Function.comp_def] using!
      congrArg₂ List.append
        (congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (2, 0) :: t.outcomes }))
          (ihFalse (ProjectiveBranch M false psi) (ProjectiveBranch M false phi)))
        (congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (2, 1) :: t.outcomes }))
          (ihTrue (ProjectiveBranch M true psi) (ProjectiveBranch M true phi)))

/-- Projecting paired terminal traces onto their second components recovers the observed traces
for oracle `B` and initial state `phi`. -/
theorem observedPairedTraces_right (A B : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi phi : QState I) :
    (observedPairedTraces A B P psi phi).map Prod.snd = observedTraces B P phi := by
  induction P generalizing psi phi with
  | halt accepted => rfl
  | step s next ih =>
    cases s with
    | gate U =>
      simpa only [observedPairedTraces, observedTraces, List.map_map,
        Function.comp_def] using
        congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with gates := t.gates + 1 }))
          (ih (ApplyGate U psi) (ApplyGate U phi))
    | query =>
      simpa only [observedPairedTraces, observedTraces, List.map_map,
        Function.comp_def] using
        congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with queries := t.queries + 1 }))
          (ih (ApplyGate A psi) (ApplyGate B phi))
  | measure n label next ih =>
    simp only [observedPairedTraces, observedTraces, List.map_flatten,
      List.map_ofFn, Function.comp_def]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext o
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun ts : List (BranchTrace I) =>
        ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (n, o.val) :: t.outcomes }))
        (ih o (Collapse psi (Finset.univ.filter (fun i => label i = o)))
          (Collapse phi (Finset.univ.filter (fun i => label i = o))))
  | project M onFalse onTrue ihFalse ihTrue =>
    simpa only [observedPairedTraces, observedTraces, List.map_append,
      List.map_map, Function.comp_def] using!
      congrArg₂ List.append
        (congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (2, 0) :: t.outcomes }))
          (ihFalse (ProjectiveBranch M false psi) (ProjectiveBranch M false phi)))
        (congrArg (fun ts : List (BranchTrace I) =>
          ts.map (fun t => { t with measurements := t.measurements + 1, outcomes := (2, 1) :: t.outcomes }))
          (ihTrue (ProjectiveBranch M true psi) (ProjectiveBranch M true phi)))

/-- The first components of paired query visits are exactly the states recorded by
`observedQueryVisits` for oracle `A`. -/
theorem observedPairedVisits_left (A B : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi phi : QState I) :
    (observedPairedVisits A B P psi phi).map Prod.fst =
      (observedQueryVisits A P psi).map Prod.snd := by
  induction P generalizing psi phi with
  | halt accepted => rfl
  | step s next ih =>
    cases s with
    | gate U => exact ih (ApplyGate U psi) (ApplyGate U phi)
    | query =>
      simp only [observedPairedVisits, observedQueryVisits, List.map_cons,
        List.map_map, Function.comp_def, ih]
  | measure n label next ih =>
    simp only [observedPairedVisits, observedQueryVisits, List.map_flatten,
      List.map_ofFn, Function.comp_def, ih]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedPairedVisits, observedQueryVisits, List.map_append,
      ihFalse, ihTrue]

/-- The second components of paired query visits are exactly the states recorded by
`observedQueryVisits` for oracle `B`. -/
theorem observedPairedVisits_right (A B : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi phi : QState I) :
    (observedPairedVisits A B P psi phi).map Prod.snd =
      (observedQueryVisits B P phi).map Prod.snd := by
  induction P generalizing psi phi with
  | halt accepted => rfl
  | step s next ih =>
    cases s with
    | gate U => exact ih (ApplyGate U psi) (ApplyGate U phi)
    | query =>
      simp only [observedPairedVisits, observedQueryVisits, List.map_cons,
        List.map_map, Function.comp_def, ih]
  | measure n label next ih =>
    simp only [observedPairedVisits, observedQueryVisits, List.map_flatten,
      List.map_ofFn, Function.comp_def, ih]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedPairedVisits, observedQueryVisits, List.map_append,
      ihFalse, ihTrue]

/-- Every pair of terminal traces has equal acceptance flags, query counts, gate counts,
measurement counts, and outcome histories. -/
theorem observedPairedTraces_metadata (A B : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi phi : QState I) (t : BranchTrace I × BranchTrace I)
    (ht : t ∈ observedPairedTraces A B P psi phi) :
    t.1.accepted = t.2.accepted ∧ t.1.queries = t.2.queries ∧
      t.1.gates = t.2.gates ∧ t.1.measurements = t.2.measurements ∧
      t.1.outcomes = t.2.outcomes := by
  induction P generalizing psi phi t with
  | halt accepted =>
    simp only [observedPairedTraces, List.mem_singleton] at ht
    subst t
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | step s next ih =>
    cases s with
    | gate U =>
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      rcases ih (ApplyGate U psi) (ApplyGate U phi) u hu with ⟨ha, hq, hg, hm, ho⟩
      exact ⟨ha, hq, congrArg (fun k : ℕ => k + 1) hg, hm, ho⟩
    | query =>
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      rcases ih (ApplyGate A psi) (ApplyGate B phi) u hu with ⟨ha, hq, hg, hm, ho⟩
      exact ⟨ha, congrArg (fun k : ℕ => k + 1) hq, hg, hm, ho⟩
  | measure n label next ih =>
    obtain ⟨xs, hxs, ht⟩ := List.mem_flatten.mp ht
    obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hxs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    rcases ih o (Collapse psi (Finset.univ.filter (fun i => label i = o)))
      (Collapse phi (Finset.univ.filter (fun i => label i = o))) u hu with
      ⟨ha, hq, hg, hm, ho⟩
    exact ⟨ha, hq, hg, congrArg (fun k : ℕ => k + 1) hm,
      congrArg (fun os : List (ℕ × ℕ) => (n, o.val) :: os) ho⟩
  | project M onFalse onTrue ihFalse ihTrue =>
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      rcases ihFalse (ProjectiveBranch M false psi) (ProjectiveBranch M false phi)
        u hu with ⟨ha, hq, hg, hm, ho⟩
      exact ⟨ha, hq, hg, congrArg (fun k : ℕ => k + 1) hm,
        congrArg (fun os : List (ℕ × ℕ) => (2, 0) :: os) ho⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      rcases ihTrue (ProjectiveBranch M true psi) (ProjectiveBranch M true phi)
        u hu with ⟨ha, hq, hg, hm, ho⟩
      exact ⟨ha, hq, hg, congrArg (fun k : ℕ => k + 1) hm,
        congrArg (fun os : List (ℕ × ℕ) => (2, 1) :: os) ho⟩

/-- Summing inner products of the two states collapsed onto matching measurement fibers recovers
their original inner product. -/
private theorem paired_inner_collapse_partition (psi phi : QState I) {n : ℕ}
    (label : I → Fin n) :
    (∑ o : Fin n,
      Qatlib.Foundations.PureStateMath.Inner (Collapse psi (Finset.univ.filter (fun i => label i = o)))
        (Collapse phi (Finset.univ.filter (fun i => label i = o)))) = Qatlib.Foundations.PureStateMath.Inner psi phi := by
  have hfiber (o : Fin n) :
      Qatlib.Foundations.PureStateMath.Inner (Collapse psi (Finset.univ.filter (fun i => label i = o)))
        (Collapse phi (Finset.univ.filter (fun i => label i = o))) =
      ∑ i, if label i = o then (starRingEnd ℂ) (psi i) * phi i else 0 := by
    rw [inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : label i = o <;> simp [collapse_apply, h]
  simp_rw [hfiber]
  rw [inner_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

omit [DecidableEq I] in

/-- Applying an orthogonal projector to both arguments of the inner product equals applying it
only to the second argument. -/
private theorem paired_inner_projector {M : Matrix I I ℂ}
    (hM : IsOrthogonalProjector M) (psi phi : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate M psi) (ApplyGate M phi) = Qatlib.Foundations.PureStateMath.Inner psi (ApplyGate M phi) := by
  have hMM : M.conjTranspose * M = M := by
    have hstar : M.conjTranspose = M := hM.2
    rw [hstar]
    exact hM.1
  simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hMM,
    Matrix.dotProduct_mulVec]

omit [DecidableEq I] in

/-- The inner product is additive in its second argument. -/
private theorem paired_inner_add_right (psi phi chi : QState I) :
    Qatlib.Foundations.PureStateMath.Inner psi (phi + chi) = Qatlib.Foundations.PureStateMath.Inner psi phi + Qatlib.Foundations.PureStateMath.Inner psi chi := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]

/-- The sum of inner products over the two matching branches of an orthogonal projective
measurement equals the original inner product. -/
private theorem paired_inner_projective_add {M : Matrix I I ℂ}
    (hM : IsOrthogonalProjector M) (psi phi : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ProjectiveBranch M false psi) (ProjectiveBranch M false phi) +
      Qatlib.Foundations.PureStateMath.Inner (ProjectiveBranch M true psi) (ProjectiveBranch M true phi) =
      Qatlib.Foundations.PureStateMath.Inner psi phi := by
  change Qatlib.Foundations.PureStateMath.Inner (ApplyGate (1 - M) psi) (ApplyGate (1 - M) phi) +
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate M psi) (ApplyGate M phi) = Qatlib.Foundations.PureStateMath.Inner psi phi
  rw [paired_inner_projector (isOrthogonalProjector_compl hM),
    paired_inner_projector hM, ← paired_inner_add_right]
  have hsum : ApplyGate (1 - M) phi + ApplyGate M phi = phi := by
    simp [ApplyGate, Matrix.sub_mulVec]
  rw [hsum]

/-- For a well-formed observed circuit, the sum of terminal paired inner products equals the
initial inner product plus the sum of inner-product changes at paired query visits. -/
theorem observed_paired_inner_telescope (A B : Matrix I I ℂ) (P : ObservedCircuit I)
    (hP : observedWellFormed P) (psi phi : QState I) :
    ((observedPairedTraces A B P psi phi).map
      (fun t => Qatlib.Foundations.PureStateMath.Inner t.1.state t.2.state)).sum =
    Qatlib.Foundations.PureStateMath.Inner psi phi + ((observedPairedVisits A B P psi phi).map
      (fun v => Qatlib.Foundations.PureStateMath.Inner (ApplyGate A v.1) (ApplyGate B v.2) - Qatlib.Foundations.PureStateMath.Inner v.1 v.2)).sum := by
  induction P generalizing psi phi with
  | halt accepted =>
    simp only [observedPairedTraces, observedPairedVisits, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | step s next ih =>
    cases s with
    | gate U =>
      simp only [observedPairedTraces, observedPairedVisits, List.map_map,
        Function.comp_def]
      rw [ih hP.2 (ApplyGate U psi) (ApplyGate U phi), inner_applyGate hP.1]
    | query =>
      simp only [observedPairedTraces, observedPairedVisits, List.map_map,
        Function.comp_def, List.map_cons, List.sum_cons]
      rw [ih hP (ApplyGate A psi) (ApplyGate B phi)]
      abel
  | measure n label next ih =>
    simp only [observedPairedTraces, observedPairedVisits, List.map_flatten,
      List.sum_flatten, List.map_map, Function.comp_def, List.map_ofFn, List.sum_ofFn]
    have hnext (o : Fin n) := ih o (hP o)
      (Collapse psi (Finset.univ.filter (fun i => label i = o)))
      (Collapse phi (Finset.univ.filter (fun i => label i = o)))
    simp only [hnext]
    rw [Finset.sum_add_distrib, paired_inner_collapse_partition]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedPairedTraces, observedPairedVisits, List.map_append,
      List.sum_append, List.map_map, Function.comp_def]
    rw [ihFalse hP.2.1 (ProjectiveBranch M false psi) (ProjectiveBranch M false phi),
      ihTrue hP.2.2 (ProjectiveBranch M true psi) (ProjectiveBranch M true phi)]
    rw [← paired_inner_projective_add hP.1 psi phi]
    abel

end Qatlib.Concepts.AdversaryBounds.AdvDuality
