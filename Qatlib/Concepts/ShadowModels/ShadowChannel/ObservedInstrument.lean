/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedEvent

/-!
# Kraus instruments of observed circuits

`ObservedKrausLeaf` records a branch operator together with acceptance, query and gate counts,
measurement counts, and outcomes. `observedKrausLeaves` extracts these leaves from an observed
circuit, and applying their operators reproduces its state-dependent traces.

For a well-formed circuit and unitary oracle, the leaf operators form a complete Kraus family.
`observedInstrument` packages this family as an instrument, with branch probabilities,
acceptance, and expected queries matching the observed trace semantics. See [Watrous2018] for
background.

## Main statements

* `observedTraces_eq_krausLeaves`: state traces arise from the extracted Kraus leaves.
* `observedLeaf_complete`: the leaf operators satisfy Kraus completeness.
* `observedInstrument_expected_queries`: instrument averaging agrees with expected observed
  queries.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix

variable {D : ℕ}

/-- A circuit branch described by its operator, acceptance flag, query, gate, and measurement
counts, and ordered measurement outcomes. -/
structure ObservedKrausLeaf (D : ℕ) where
  operator : Operator D
  accepted : Bool
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  outcomes : List (ℕ × ℕ)

/-- Apply the leaf operator to an input state and retain the leaf's acceptance flag, counters,
and outcome history. -/
noncomputable def ObservedKrausLeaf.toTrace (leaf : ObservedKrausLeaf D)
    (ψ : QState (Fin D)) : BranchTrace (Fin D) where
  state := ApplyGate leaf.operator ψ
  accepted := leaf.accepted
  queries := leaf.queries
  gates := leaf.gates
  measurements := leaf.measurements
  outcomes := leaf.outcomes

/-- Prepend an operation to a leaf by right-multiplying its operator, adding the supplied
resource counts, and prefixing the outcome history. -/
noncomputable def ObservedKrausLeaf.prepend (U : Operator D)
    (q g m : ℕ) (outcomes : List (ℕ × ℕ)) (leaf : ObservedKrausLeaf D) :
    ObservedKrausLeaf D where
  operator := leaf.operator * U
  accepted := leaf.accepted
  queries := leaf.queries + q
  gates := leaf.gates + g
  measurements := leaf.measurements + m
  outcomes := outcomes ++ leaf.outcomes

/-- Extract all branch operators and metadata from an observed circuit for the given oracle. -/
noncomputable def observedKrausLeaves (oracle : Operator D) :
    ObservedCircuit (Fin D) → List (ObservedKrausLeaf D)
  | .halt accepted => [⟨1, accepted, 0, 0, 0, []⟩]
  | .step (.gate U) next =>
      (observedKrausLeaves oracle next).map (ObservedKrausLeaf.prepend U 0 1 0 [])
  | .step .query next =>
      (observedKrausLeaves oracle next).map (ObservedKrausLeaf.prepend oracle 1 0 0 [])
  | .measure n label next =>
      (List.ofFn (fun o : Fin n => (observedKrausLeaves oracle (next o)).map
        (ObservedKrausLeaf.prepend (Projector (Finset.univ.filter (fun i => label i = o)))
          0 0 1 [(n, o.val)]))).flatten
  | .project P onFalse onTrue =>
      (observedKrausLeaves oracle onFalse).map
        (ObservedKrausLeaf.prepend (1 - P) 0 0 1 [(2, 0)]) ++
      (observedKrausLeaves oracle onTrue).map
        (ObservedKrausLeaf.prepend P 0 0 1 [(2, 1)])

/-- The number of terminal branches of an observed circuit, counting all measurement and
projection branches. -/
def observedLeafCount : ObservedCircuit (Fin D) → ℕ
  | .halt _ => 1
  | .step _ next => observedLeafCount next
  | .measure n _ next => ∑ o : Fin n, observedLeafCount (next o)
  | .project _ onFalse onTrue => observedLeafCount onFalse + observedLeafCount onTrue

/-- The extracted Kraus leaf list has length equal to `observedLeafCount`. -/
theorem observedKrausLeaves_length (oracle : Operator D) (program : ObservedCircuit (Fin D)) :
    (observedKrausLeaves oracle program).length = observedLeafCount program := by
  induction program with
  | halt accepted => rfl
  | step s next ih => cases s <;> simpa [observedKrausLeaves, observedLeafCount] using ih
  | measure n label next ih =>
    simp only [observedKrausLeaves, List.length_flatten, List.map_ofFn,
      Function.comp_def, List.length_map, List.sum_ofFn, observedLeafCount]
    exact Finset.sum_congr rfl fun o _ => ih o
  | project P onFalse onTrue ihFalse ihTrue =>
    simp [observedKrausLeaves, observedLeafCount, ihFalse, ihTrue]

/-- Observed circuit traces are obtained by applying each extracted Kraus leaf to the input
state. -/
theorem observedTraces_eq_krausLeaves (oracle : Operator D)
    (program : ObservedCircuit (Fin D)) (ψ : QState (Fin D)) :
    observedTraces oracle program ψ =
      (observedKrausLeaves oracle program).map (fun leaf => leaf.toTrace ψ) := by
  induction program generalizing ψ with
  | halt accepted =>
    simp [observedTraces, observedKrausLeaves, ObservedKrausLeaf.toTrace, applyGate_one]
  | step s next ih =>
    cases s <;>
      simp [observedTraces, observedKrausLeaves, ih, List.map_map, Function.comp_def,
        ObservedKrausLeaf.toTrace, ObservedKrausLeaf.prepend, applyGate_mul]
  | measure n label next ih =>
    simp [observedTraces, observedKrausLeaves, ih, List.map_flatten, List.map_ofFn,
      List.map_map, Function.comp_def, ObservedKrausLeaf.toTrace,
      ObservedKrausLeaf.prepend, Collapse, applyGate_mul]
  | project P onFalse onTrue ihFalse ihTrue =>
    simp [observedTraces, observedKrausLeaves, ihFalse, ihTrue, List.map_append,
      List.map_map, Function.comp_def, ObservedKrausLeaf.toTrace,
      ObservedKrausLeaf.prepend, ProjectiveBranch, applyGate_mul]

/-- The Kraus leaf at a valid finite branch index in the extracted leaf list. -/
noncomputable def observedLeaf (oracle : Operator D) (program : ObservedCircuit (Fin D))
    (i : Fin (observedLeafCount program)) : ObservedKrausLeaf D :=
  (observedKrausLeaves oracle program).get
    (Fin.cast (observedKrausLeaves_length oracle program).symm i)

/-- Enumerating `observedLeaf` over its finite index type recovers the extracted Kraus leaf
list. -/
theorem observedLeaf_ofFn (oracle : Operator D) (program : ObservedCircuit (Fin D)) :
    List.ofFn (observedLeaf oracle program) = observedKrausLeaves oracle program := by
  have h := List.ofFn_congr (observedKrausLeaves_length oracle program)
    (observedKrausLeaves oracle program).get
  simpa only [List.ofFn_get, observedLeaf] using! h.symm

/-- The observed trace list is the finite enumeration of indexed Kraus leaves applied to the
input state. -/
theorem observedTraces_eq_ofFn (oracle : Operator D) (program : ObservedCircuit (Fin D))
    (ψ : QState (Fin D)) :
    observedTraces oracle program ψ =
      List.ofFn (fun i => (observedLeaf oracle program i).toTrace ψ) := by
  rw [observedTraces_eq_krausLeaves, ← observedLeaf_ofFn oracle program, List.map_ofFn]
  rfl

/-- Prepending `U` to each leaf conjugates the sum of their Kraus effects by `U`. -/
private theorem krausEffect_prepend (U : Operator D) (q g m : ℕ)
    (outcomes : List (ℕ × ℕ)) (leaves : List (ObservedKrausLeaf D)) :
    ((leaves.map (ObservedKrausLeaf.prepend U q g m outcomes)).map
      (fun leaf => leaf.operator.conjTranspose * leaf.operator)).sum =
      U.conjTranspose * (leaves.map
        (fun leaf => leaf.operator.conjTranspose * leaf.operator)).sum * U := by
  induction leaves with
  | nil => simp
  | cons leaf leaves ih =>
    simp only [List.map_cons, List.sum_cons, ObservedKrausLeaf.prepend,
      Matrix.conjTranspose_mul, ih, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The computational basis projectors onto the fibers of a finite label map sum to the
identity. -/
private theorem projector_partition_sum {n : ℕ} (label : Fin D → Fin n) :
    ∑ o : Fin n, Projector (Finset.univ.filter (fun i => label i = o)) = (1 : Operator D) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Projector, Matrix.sum_apply]
  · simp [Projector, Matrix.sum_apply, hij]

/-- For a well-formed observed circuit with unitary oracle, the sum of the extracted leaf Kraus
effects is the identity. -/
theorem observedKrausLeaves_complete (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program) :
    ((observedKrausLeaves oracle program).map
      (fun leaf => leaf.operator.conjTranspose * leaf.operator)).sum = 1 := by
  induction program with
  | halt accepted => simp [observedKrausLeaves]
  | step s next ih =>
    cases s with
    | gate U =>
      rw [observedKrausLeaves, krausEffect_prepend, ih hProgram.2, Matrix.mul_one]
      have h := (Matrix.mem_unitaryGroup_iff').mp hProgram.1
      simpa only [Matrix.star_eq_conjTranspose] using h
    | query =>
      rw [observedKrausLeaves, krausEffect_prepend, ih hProgram, Matrix.mul_one]
      have h := (Matrix.mem_unitaryGroup_iff').mp hOracle
      simpa only [Matrix.star_eq_conjTranspose] using h
  | measure n label next ih =>
    simp only [observedKrausLeaves, List.map_flatten, List.sum_flatten,
      List.map_ofFn, List.map_map, Function.comp_def, List.sum_ofFn]
    have hbranch (o : Fin n) := krausEffect_prepend
      (Projector (Finset.univ.filter (fun i => label i = o))) 0 0 1 [(n, o.val)]
      (observedKrausLeaves oracle (next o))
    simp only [List.map_map, Function.comp_def] at hbranch
    simp_rw [hbranch, ih _ (hProgram _), Matrix.mul_one, projector_conjTranspose,
      projector_mul_self]
    exact projector_partition_sum label
  | project P onFalse onTrue ihFalse ihTrue =>
    rw [observedKrausLeaves, List.map_append, List.sum_append,
      krausEffect_prepend, krausEffect_prepend, ihFalse hProgram.2.1,
      ihTrue hProgram.2.2, Matrix.mul_one, Matrix.mul_one]
    have hP : P.conjTranspose = P := hProgram.1.2
    have hC := isOrthogonalProjector_compl hProgram.1
    have hCstar : (1 - P).conjTranspose = 1 - P := hC.2
    rw [hP, hProgram.1.1, hCstar, hC.1]
    exact sub_add_cancel 1 P

/-- For a well-formed observed circuit with unitary oracle, the indexed leaf operators form a
complete Kraus family. -/
theorem observedLeaf_complete (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program) :
    ∑ i : Fin (observedLeafCount program),
      (observedLeaf oracle program i).operator.conjTranspose *
        (observedLeaf oracle program i).operator = 1 := by
  rw [← List.sum_ofFn]
  change (List.ofFn (fun i => (fun leaf : ObservedKrausLeaf D =>
    leaf.operator.conjTranspose * leaf.operator) (observedLeaf oracle program i))).sum = 1
  rw [List.ofFn_comp' (observedLeaf oracle program)
    (fun leaf : ObservedKrausLeaf D => leaf.operator.conjTranspose * leaf.operator),
    observedLeaf_ofFn]
  exact observedKrausLeaves_complete oracle hOracle program hProgram

/-- The quantum instrument whose outcomes are the indexed Kraus leaves of a well-formed observed
circuit with unitary oracle. -/
noncomputable def observedInstrument (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program) :
    Instrument (Fin (observedLeafCount program)) D D :=
  Instrument.ofKraus (fun i => (observedLeaf oracle program i).operator)
    (observedLeaf_complete oracle hOracle program hProgram)

/-- Applying an instrument branch to an input outer product gives the outer product of the
corresponding observed branch state. -/
theorem observedInstrument_branch_outerProduct (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program)
    (ψ : QState (Fin D)) (i : Fin (observedLeafCount program)) :
    (observedInstrument oracle hOracle program hProgram).branch i (outerProduct ψ) =
      outerProduct ((observedLeaf oracle program i).toTrace ψ).state := by
  change conjBranch (observedLeaf oracle program i).operator (outerProduct ψ) = _
  exact conjBranch_outerProduct _ _

/-- An indexed instrument outcome has weight equal to the branch mass of the corresponding
observed trace. -/
theorem instrumentProb_observedInstrument (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program)
    (ψ : QState (Fin D)) (i : Fin (observedLeafCount program)) :
    instrumentProb (observedInstrument oracle hOracle program hProgram) (outerProduct ψ) i =
      branchMass ((observedLeaf oracle program i).toTrace ψ).state := by
  rw [instrumentProb, observedInstrument_branch_outerProduct, trace_outerProduct]
  simp only [Complex.ofReal_re]
  rfl

/-- The list of instrument branch outputs on an outer product equals the list of outer products
of observed branch states. -/
theorem observedInstrument_branches_eq_traces (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program)
    (ψ : QState (Fin D)) :
    List.ofFn (fun i =>
      (observedInstrument oracle hOracle program hProgram).branch i (outerProduct ψ)) =
      (observedTraces oracle program ψ).map (fun trace => outerProduct trace.state) := by
  rw [observedTraces_eq_ofFn, List.map_ofFn]
  congr 1
  funext i
  exact observedInstrument_branch_outerProduct oracle hOracle program hProgram ψ i

/-- Coarsening the leaf instrument by acceptance gives the same accepting weight as observed
circuit acceptance. -/
theorem observedInstrument_acceptance (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program)
    (ψ : QState (Fin D)) :
    instrumentProb ((observedInstrument oracle hOracle program hProgram).coarsen
      (fun i => (observedLeaf oracle program i).accepted)) (outerProduct ψ) true =
      observedAcceptance oracle program ψ := by
  rw [instrumentProb_coarsen, ← observedEventMass_accepted, observedEventMass,
    observedTraces_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_filter, instrumentProb_observedInstrument, ObservedKrausLeaf.toTrace,
    Function.comp_def]

/-- Instrument-weighted sums of any real trace statistic equal the corresponding
branch-mass-weighted sums over observed traces. -/
theorem observedInstrument_weighted_traces (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program)
    (ψ : QState (Fin D)) (f : BranchTrace (Fin D) → ℝ) :
    (∑ i : Fin (observedLeafCount program),
      instrumentProb (observedInstrument oracle hOracle program hProgram) (outerProduct ψ) i *
        f ((observedLeaf oracle program i).toTrace ψ)) =
      ((observedTraces oracle program ψ).map (fun trace => branchMass trace.state * f trace)).sum := by
  rw [observedTraces_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  simp only [instrumentProb_observedInstrument, Function.comp_def]

/-- The instrument-weighted mean of leaf query counts equals `expectedObservedQueries`. -/
theorem observedInstrument_expected_queries (oracle : Operator D)
    (hOracle : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (program : ObservedCircuit (Fin D)) (hProgram : observedWellFormed program)
    (ψ : QState (Fin D)) :
    (∑ i : Fin (observedLeafCount program),
      instrumentProb (observedInstrument oracle hOracle program hProgram) (outerProduct ψ) i *
        (observedLeaf oracle program i).queries) = expectedObservedQueries oracle program ψ := by
  rw [expectedObservedQueries_eq_sum]
  exact observedInstrument_weighted_traces oracle hOracle program hProgram ψ
    (fun trace => (trace.queries : ℝ))

end Qatlib.Concepts.ShadowModels.ShadowChannel
