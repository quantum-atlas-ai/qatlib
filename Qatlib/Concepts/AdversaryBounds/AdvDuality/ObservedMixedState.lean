/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning

/-!
# Mixed state execution and continuation costs

`MixedBranchTrace` records operator-valued branch states together with acceptance, resource
counts, and outcomes. `observedMixedTraces` executes observed circuits by conjugating the input
operator along each branch, and `mixedExpectedQueries` weights query counts by the real trace of
each branch state. The connection with Kraus operators and quantum instruments follows the
formalism in [Watrous2018].

`continueObserved` replaces Boolean termination with a selected continuation. `mixedJoin`
combines the resulting branch metadata, and the continuation theorems express both the complete
branch list and its expected query cost.

## Main statements

* `observedMixedTraces_pure` agrees with pure state execution after taking outer products.
* `observedMixedTraces_instrument` identifies branch states with instrument outputs.
* `observedMixedTraces_mass_and_density` proves positivity and mass conservation under the
  stated hypotheses.
* `mixed_continuation_actual_cost` splits expected cost into the prefix cost and continuation
  costs on its branch states.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped ComplexOrder

variable {D : ℕ}

/-- A terminal branch record with an operator-valued state, acceptance flag, resource counts,
and measurement outcomes. -/
structure MixedBranchTrace (D : ℕ) where
  state : Operator D
  accepted : Bool
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  outcomes : List (ℕ × ℕ)

/-- Applies a Kraus leaf's conjugation map to the input operator and records the leaf's
classical metadata. -/
noncomputable def leafMixedTrace (t : ObservedKrausLeaf D) (ρ : Operator D) :
    MixedBranchTrace D :=
  ⟨conjBranch t.operator ρ, t.accepted, t.queries, t.gates, t.measurements, t.outcomes⟩

/-- Converts a pure branch trace into a mixed branch trace by taking the outer product of its
state and retaining the metadata. -/
noncomputable def pureTraceToMixed (t : BranchTrace (Fin D)) : MixedBranchTrace D :=
  ⟨outerProduct t.state, t.accepted, t.queries, t.gates, t.measurements, t.outcomes⟩

/-- The real part of the trace of a mixed branch's state operator. -/
noncomputable def mixedMass (t : MixedBranchTrace D) : ℝ := (Matrix.trace t.state).re

/-- Combines a prefix trace with a continuation trace by adding resource counts and
concatenating outcomes, using the continuation's state and acceptance flag. -/
def mixedJoin (t u : MixedBranchTrace D) : MixedBranchTrace D :=
  ⟨u.state, u.accepted, t.queries + u.queries, t.gates + u.gates,
    t.measurements + u.measurements, t.outcomes ++ u.outcomes⟩

/-- Enumerates operator-valued terminal branches of an observed circuit by conjugation along
gates, queries, and measurement branches, accumulating resource counts and outcomes. -/
noncomputable def observedMixedTraces (oracle : Operator D) :
    ObservedCircuit (Fin D) → Operator D → List (MixedBranchTrace D)
  | .halt accepted, ρ =>
      [{ state := ρ
         accepted := accepted
         queries := 0
         gates := 0
         measurements := 0
         outcomes := [] }]
  | .step (.gate U) next, ρ =>
      (observedMixedTraces oracle next (conjBranch U ρ)).map fun t =>
        ⟨t.state, t.accepted, t.queries, t.gates + 1, t.measurements, t.outcomes⟩
  | .step .query next, ρ =>
      (observedMixedTraces oracle next (conjBranch oracle ρ)).map fun t =>
        ⟨t.state, t.accepted, t.queries + 1, t.gates, t.measurements, t.outcomes⟩
  | .measure n label next, ρ =>
      (List.ofFn fun o : Fin n =>
        (observedMixedTraces oracle (next o)
            (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
          fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
            (n, o.val) :: t.outcomes⟩).flatten
  | .project P onFalse onTrue, ρ =>
      (observedMixedTraces oracle onFalse (conjBranch (1 - P) ρ)).map
        (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
          (2, 0) :: t.outcomes⟩) ++
      (observedMixedTraces oracle onTrue (conjBranch P ρ)).map
        fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
          (2, 1) :: t.outcomes⟩

/-- The sum of each mixed branch's query count weighted by the real trace of its state operator. -/
noncomputable def mixedExpectedQueries (oracle : Operator D) (program : ObservedCircuit (Fin D))
    (ρ : Operator D) : ℝ :=
  ((observedMixedTraces oracle program ρ).map fun t => mixedMass t * t.queries).sum

/-- Replaces each Boolean halt of an observed circuit with the continuation selected by that
Boolean result. -/
def continueObserved {I : Type} :
    ObservedCircuit I → (Bool → ObservedCircuit I) → ObservedCircuit I
  | .halt a, k => k a
  | .step s next, k => .step s (continueObserved next k)
  | .measure n label next, k => .measure n label fun o => continueObserved (next o) k
  | .project P onFalse onTrue, k =>
      .project P (continueObserved onFalse k) (continueObserved onTrue k)

/-- Prepending an operator and metadata to a Kraus leaf agrees with first conjugating the input
and then adding that metadata to the resulting mixed trace. -/
private theorem leafMixedTrace_prepend (U : Operator D) (q g m : ℕ)
    (outcomes : List (ℕ × ℕ)) (leaf : ObservedKrausLeaf D) (ρ : Operator D) :
    (fun t => ⟨t.state, t.accepted, t.queries + q, t.gates + g, t.measurements + m,
        outcomes ++ t.outcomes⟩) (leafMixedTrace leaf (conjBranch U ρ))
      = leafMixedTrace (Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedKrausLeaf.prepend U q g m outcomes leaf) ρ := by
  rcases leaf with ⟨op, acc, q', g', m', outs⟩
  have hst : conjBranch op (conjBranch U ρ) = conjBranch (op * U) ρ := by
    simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
  simp only [leafMixedTrace, Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedKrausLeaf.prepend,
      hst]

/-- Mixed execution equals the list obtained by applying `leafMixedTrace` to every observed
Kraus leaf and the common input operator. -/
private theorem observedMixedTraces_eq_krausLeaves (oracle : Operator D)
    (program : ObservedCircuit (Fin D)) (ρ : Operator D) :
    observedMixedTraces oracle program ρ =
      (observedKrausLeaves oracle program).map fun leaf => leafMixedTrace leaf ρ := by
  induction program generalizing ρ with
  | halt accepted =>
    simp [observedMixedTraces, observedKrausLeaves, leafMixedTrace]
  | step s next ih =>
    cases s with
    | gate U =>
      simp only [observedMixedTraces, observedKrausLeaves, ih (conjBranch U ρ), List.map_map]
      exact List.map_congr_left fun leaf _ =>
        leafMixedTrace_prepend U 0 1 0 [] leaf ρ
    | query =>
      simp only [observedMixedTraces, observedKrausLeaves, ih (conjBranch oracle ρ),
        List.map_map]
      exact List.map_congr_left fun leaf _ =>
        leafMixedTrace_prepend oracle 1 0 0 [] leaf ρ
  | measure n label next ih =>
    have key : ∀ o : Fin n,
        (observedMixedTraces oracle (next o)
            (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
            (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
              (n, o.val) :: t.outcomes⟩)
          = ((observedKrausLeaves oracle (next o)).map
              (Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedKrausLeaf.prepend
                (Projector (Finset.univ.filter fun i => label i = o)) 0 0 1 [(n, o.val)])).map
              fun leaf => leafMixedTrace leaf ρ := by
      intro o
      simp only [ih o (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ),
        List.map_map]
      exact List.map_congr_left fun leaf _ =>
        leafMixedTrace_prepend _ 0 0 1 [(n, o.val)] leaf ρ
    simp only [observedMixedTraces, observedKrausLeaves]
    rw [List.map_flatten, List.map_ofFn]
    exact congrArg List.flatten (congrArg List.ofFn (funext key))
  | project P0 onFalse onTrue ihFalse ihTrue =>
    simp only [observedMixedTraces, observedKrausLeaves,
      ihFalse (conjBranch (1 - P0) ρ), ihTrue (conjBranch P0 ρ), List.map_map,
      List.map_append]
    congr 1
    · exact List.map_congr_left fun leaf _ => leafMixedTrace_prepend _ 0 0 1 [(2, 0)] leaf ρ
    · exact List.map_congr_left fun leaf _ => leafMixedTrace_prepend _ 0 0 1 [(2, 1)] leaf ρ

/-- Mixed traces are precisely the indexed observed leaves applied to the input operator, and
their list length is `observedLeafCount`. -/
theorem observedMixedTraces_leaf_correspondence (O : Operator D) (P : ObservedCircuit (Fin D))
    (ρ : Operator D) :
    observedMixedTraces O P ρ = List.ofFn (fun i => leafMixedTrace (observedLeaf O P i) ρ) ∧
      (observedMixedTraces O P ρ).length = observedLeafCount P := by
  refine ⟨?_, ?_⟩
  · rw [observedMixedTraces_eq_krausLeaves, ← observedLeaf_ofFn O P, List.map_ofFn]
    rfl
  · rw [observedMixedTraces_eq_krausLeaves, List.length_map, observedKrausLeaves_length]

/-- Executing on a pure state's outer product agrees with pure execution followed by converting
each trace with `pureTraceToMixed`. -/
theorem observedMixedTraces_pure (O : Operator D) (P : ObservedCircuit (Fin D))
    (ψ : QState (Fin D)) :
    observedMixedTraces O P (outerProduct ψ) = (observedTraces O P ψ).map pureTraceToMixed := by
  rw [observedMixedTraces_eq_krausLeaves, observedTraces_eq_krausLeaves, List.map_map]
  refine List.map_congr_left fun leaf _ => ?_
  simp only [leafMixedTrace, ObservedKrausLeaf.toTrace, ApplyGate]
  rw [conjBranch_outerProduct]
  rfl

/-- For a unitary oracle and well-formed circuit, the indexed instrument branch outputs are
exactly the state fields of the mixed trace list. -/
theorem observedMixedTraces_instrument (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : ObservedCircuit (Fin D))
    (hP : observedWellFormed P) (ρ : Operator D) :
    List.ofFn (fun i => (observedInstrument O hO P hP).branch i ρ) =
      (observedMixedTraces O P ρ).map MixedBranchTrace.state := by
  rw [(observedMixedTraces_leaf_correspondence O P ρ).1, List.map_ofFn]
  rfl

/-- For a unitary oracle and well-formed circuit, total mixed branch mass equals the real trace
of the input operator. -/
theorem observedMixedTraces_mass_sum (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : ObservedCircuit (Fin D))
    (hP : observedWellFormed P) (ρ : Operator D) :
    ((observedMixedTraces O P ρ).map mixedMass).sum = (Matrix.trace ρ).re := by
  calc ((observedMixedTraces O P ρ).map mixedMass).sum
      = ∑ i : Fin (observedLeafCount P),
          instrumentProb (observedInstrument O hO P hP) ρ i := by
        rw [(observedMixedTraces_leaf_correspondence O P ρ).1, List.map_ofFn, List.sum_ofFn]
        exact Finset.sum_congr rfl fun i _ => rfl
    _ = (Matrix.trace ρ).re := sum_instrumentProb (observedInstrument O hO P hP) ρ

/-- For a unitary oracle and well-formed circuit, positive semidefinite inputs yield positive
semidefinite branch states with nonnegative mass. Total mass is the input's real trace and
equals one for density operators. -/
theorem observedMixedTraces_mass_and_density (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : ObservedCircuit (Fin D))
    (hP : observedWellFormed P) (ρ : Operator D) :
    (ρ.PosSemidef → ∀ t ∈ observedMixedTraces O P ρ, t.state.PosSemidef ∧ 0 ≤ mixedMass t) ∧
      ((observedMixedTraces O P ρ).map mixedMass).sum = (Matrix.trace ρ).re ∧
      (IsDensityOperator ρ → ((observedMixedTraces O P ρ).map mixedMass).sum = 1) := by
  refine ⟨fun hρ t ht => ?_, observedMixedTraces_mass_sum O hO P hP ρ, fun hρ => ?_⟩
  · rw [(observedMixedTraces_leaf_correspondence O P ρ).1] at ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    have hpsd : ((leafMixedTrace (observedLeaf O P i) ρ).state).PosSemidef :=
      (completelyPositive_conjBranch (observedLeaf O P i).operator).positive hρ
    exact ⟨hpsd, (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1⟩
  · rw [observedMixedTraces_mass_sum O hO P hP ρ, hρ.2]
    rfl

/-- An instrument-probability-weighted statistic of indexed mixed leaves equals the
mixed-mass-weighted trace statistic. The theorem also records the trace-sum formula for
mixed expected queries. -/
theorem observedMixedTraces_event_statistic (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : ObservedCircuit (Fin D))
    (hP : observedWellFormed P) (ρ : Operator D) (f : MixedBranchTrace D → ℝ) :
    (∑ i : Fin (observedLeafCount P),
        instrumentProb (observedInstrument O hO P hP) ρ i
          * f (leafMixedTrace (observedLeaf O P i) ρ))
      = ((observedMixedTraces O P ρ).map (fun t => mixedMass t * f t)).sum ∧
      mixedExpectedQueries O P ρ
        = ((observedMixedTraces O P ρ).map (fun t => mixedMass t * t.queries)).sum := by
  refine ⟨?_, rfl⟩
  rw [(observedMixedTraces_leaf_correspondence O P ρ).1, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- For a unitary oracle and well-formed circuit, mixed expected queries equal the indexed sum
of instrument probabilities times leaf query counts. -/
theorem mixedExpectedQueries_eq_instrumentProb (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : ObservedCircuit (Fin D))
    (hP : observedWellFormed P) (ρ : Operator D) :
    mixedExpectedQueries O P ρ
      = ∑ i : Fin (observedLeafCount P),
          instrumentProb (observedInstrument O hO P hP) ρ i * (observedLeaf O P i).queries :=
  (observedMixedTraces_event_statistic O hO P hP ρ fun t => (t.queries : ℝ)).1.symm

/-- A trace update preserving state and acceptance and compatible with `mixedJoin` commutes with
expanding a list through its selected continuations. -/
private theorem observedMixedTraces_continue_update (O : Operator D)
    (k : Bool → ObservedCircuit (Fin D)) (u : MixedBranchTrace D → MixedBranchTrace D)
    (hstate : ∀ t, (u t).state = t.state) (hacc : ∀ t, (u t).accepted = t.accepted)
    (hjoin : ∀ t x, u (mixedJoin t x) = mixedJoin (u t) x)
    (l : List (MixedBranchTrace D)) :
    (l.flatMap fun t => (observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)).map u
      = (l.map u).flatMap
          fun t => (observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t) := by
  rw [List.map_flatMap, List.flatMap_map]
  refine congrArg (fun F => List.flatMap F l) (funext fun t => ?_)
  rw [← hacc t, ← hstate t, List.map_map]
  congr 1
  exact funext fun x => hjoin t x

/-- Flat-mapping a function over a flattened list of mixed trace lists equals flat-mapping it
within each list and then concatenating. -/
private theorem flatten_flatMap (L : List (List (MixedBranchTrace D)))
    (g : MixedBranchTrace D → List (MixedBranchTrace D)) :
    L.flatten.flatMap g = L.flatMap fun x => x.flatMap g := by
  induction L with
  | nil => simp
  | cons x L ih => simp [List.flatMap_append, ih]

/-- Execution of a continued circuit expands each prefix trace through its selected continuation
and joins their metadata. A well-formed prefix with well-formed continuations produces a
well-formed continued circuit. -/
theorem mixed_continuation_list_and_legality (O : Operator D) (P : ObservedCircuit (Fin D))
    (k : Bool → ObservedCircuit (Fin D)) (ρ : Operator D) :
    observedMixedTraces O (continueObserved P k) ρ =
      (observedMixedTraces O P ρ).flatMap
        (fun t => (observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)) ∧
      (observedWellFormed P → (∀ b, observedWellFormed (k b)) →
        observedWellFormed (continueObserved P k)) := by
  refine ⟨?_, ?_⟩
  · induction P generalizing ρ with
    | halt accepted =>
      simp only [continueObserved, observedMixedTraces, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [show mixedJoin ⟨ρ, accepted, 0, 0, 0, []⟩
            = (id : MixedBranchTrace D → MixedBranchTrace D) from
          funext fun u => by simp [mixedJoin], List.map_id]
    | step s next ih =>
      cases s with
      | gate U =>
        simp only [continueObserved, observedMixedTraces, ih (conjBranch U ρ)]
        exact observedMixedTraces_continue_update O k
          (fun t => ⟨t.state, t.accepted, t.queries, t.gates + 1, t.measurements, t.outcomes⟩)
          (fun _ => rfl) (fun _ => rfl)
          (fun t x => by
            cases t; cases x; simp only [mixedJoin]; congr 1; omega)
          (observedMixedTraces O next (conjBranch U ρ))
      | query =>
        simp only [continueObserved, observedMixedTraces, ih (conjBranch O ρ)]
        exact observedMixedTraces_continue_update O k
          (fun t => ⟨t.state, t.accepted, t.queries + 1, t.gates, t.measurements, t.outcomes⟩)
          (fun _ => rfl) (fun _ => rfl)
          (fun t x => by
            cases t; cases x; simp only [mixedJoin]; congr 1; omega)
          (observedMixedTraces O next (conjBranch O ρ))
    | measure n label next ih =>
      simp only [continueObserved, observedMixedTraces]
      have key : ∀ o : Fin n,
          (observedMixedTraces O (continueObserved (next o) k)
              (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
              (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                (n, o.val) :: t.outcomes⟩)
            = ((observedMixedTraces O (next o)
                  (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
                (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                  (n, o.val) :: t.outcomes⟩)).flatMap
                (fun t => (observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)) := by
        intro o
        rw [ih o (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)]
        exact observedMixedTraces_continue_update O k
          (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
            (n, o.val) :: t.outcomes⟩)
          (fun _ => rfl) (fun _ => rfl)
          (fun t x => by
            cases t; cases x; simp only [mixedJoin]; congr 1; omega)
          (observedMixedTraces O (next o)
            (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ))
      calc (List.ofFn fun o : Fin n =>
              (observedMixedTraces O (continueObserved (next o) k)
                (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
                (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                  (n, o.val) :: t.outcomes⟩)).flatten
          = (List.ofFn fun o : Fin n =>
              (((observedMixedTraces O (next o)
                  (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
                  (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                    (n, o.val) :: t.outcomes⟩)).flatMap
                  (fun t => (observedMixedTraces O (k t.accepted) t.state).map
                    (mixedJoin t)))).flatten :=
            congrArg List.flatten (congrArg List.ofFn (funext key))
        _ = ((List.ofFn fun o : Fin n =>
                (observedMixedTraces O (next o)
                  (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
                  (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                    (n, o.val) :: t.outcomes⟩)).map
                (fun x => x.flatMap
                  (fun t => (observedMixedTraces O (k t.accepted) t.state).map
                    (mixedJoin t)))).flatten := by
          rw [List.map_ofFn]
          rfl
        _ = ((List.ofFn fun o : Fin n =>
                (observedMixedTraces O (next o)
                  (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
                  (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                    (n, o.val) :: t.outcomes⟩)).flatMap
                (fun x => x.flatMap
                  (fun t => (observedMixedTraces O (k t.accepted) t.state).map
                    (mixedJoin t)))) :=
            rfl
        _ = ((List.ofFn fun o : Fin n =>
                (observedMixedTraces O (next o)
                  (conjBranch (Projector (Finset.univ.filter fun i => label i = o)) ρ)).map
                  (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
                    (n, o.val) :: t.outcomes⟩)).flatten).flatMap
                (fun t => (observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)) :=
            (flatten_flatMap _ _).symm
    | project P0 onFalse onTrue ihFalse ihTrue =>
      simp only [continueObserved, observedMixedTraces,
        ihFalse (conjBranch (1 - P0) ρ), ihTrue (conjBranch P0 ρ)]
      rw [observedMixedTraces_continue_update O k
        (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
          (2, 0) :: t.outcomes⟩) (fun _ => rfl) (fun _ => rfl)
        (fun t x => by
          cases t; cases x; simp only [mixedJoin]; congr 1; omega)
        (observedMixedTraces O onFalse (conjBranch (1 - P0) ρ)),
        observedMixedTraces_continue_update O k
        (fun t => ⟨t.state, t.accepted, t.queries, t.gates, t.measurements + 1,
          (2, 1) :: t.outcomes⟩) (fun _ => rfl) (fun _ => rfl)
        (fun t x => by
          cases t; cases x; simp only [mixedJoin]; congr 1; omega)
        (observedMixedTraces O onTrue (conjBranch P0 ρ)),
        List.flatMap_append]
  · intro hP hk
    induction P with
    | halt accepted => exact hk accepted
    | step s next ih =>
      cases s with
      | gate U => exact ⟨hP.1, ih hP.2⟩
      | query => exact ih hP
    | measure _ _ next ih => exact fun o => ih o (hP o)
    | project _ onFalse onTrue ihFalse ihTrue =>
      exact ⟨hP.1, ihFalse hP.2.1, ihTrue hP.2.2⟩

/-- The sum of a flat-mapped list of real lists equals the sum of the individual list sums. -/
private theorem sum_flatMap_weight {α : Type*} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A list sum of pointwise real additions equals the sum of the two mapped list sums. -/
private theorem sum_map_add {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- Real-valued functions agreeing on every element of a list have equal mapped list sums. -/
private theorem sum_map_congr {α : Type*} {f g : α → ℝ} (l : List α)
    (h : ∀ x ∈ l, f x = g x) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- A constant right factor can be pulled outside a real mapped list sum. -/
private theorem sum_map_mul_const {α : Type*} (l : List α) (f : α → ℝ) (r : ℝ) :
    (l.map fun a => f a * r).sum = (l.map f).sum * r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring


/-- For a unitary oracle and well-formed prefix and continuations, expected queries of the
continued circuit equal the prefix expectation plus the sum of continuation expectations on
its unnormalized branch states. -/
theorem mixed_continuation_actual_cost (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : ObservedCircuit (Fin D))
    (hP : observedWellFormed P) (k : Bool → ObservedCircuit (Fin D))
    (hk : ∀ b, observedWellFormed (k b)) (ρ : Operator D) :
    mixedExpectedQueries O (continueObserved P k) ρ = mixedExpectedQueries O P ρ +
      ((observedMixedTraces O P ρ).map
        (fun t => mixedExpectedQueries O (k t.accepted) t.state)).sum := by
  have hlist := (mixed_continuation_list_and_legality O P k ρ).1
  rw [show mixedExpectedQueries O (continueObserved P k) ρ =
      ((observedMixedTraces O (continueObserved P k) ρ).map
        (fun t => mixedMass t * t.queries)).sum from rfl,
    hlist, List.map_flatMap, sum_flatMap_weight]
  have key : ∀ t ∈ observedMixedTraces O P ρ,
      (((observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)).map
          (fun s => mixedMass s * s.queries)).sum
        = mixedMass t * t.queries
          + mixedExpectedQueries O (k t.accepted) t.state := by
    intro t _
    calc (((observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)).map
            (fun s => mixedMass s * s.queries)).sum
        = ((observedMixedTraces O (k t.accepted) t.state).map
            (fun u => mixedMass (mixedJoin t u) * (mixedJoin t u).queries)).sum := by
          rw [List.map_map]
          rfl
      _ = ((observedMixedTraces O (k t.accepted) t.state).map
              (fun u => mixedMass u * (t.queries : ℝ))).sum
          + ((observedMixedTraces O (k t.accepted) t.state).map
              (fun u => mixedMass u * u.queries)).sum := by
          rw [← sum_map_add]
          exact sum_map_congr _ fun u _ => by
            rw [show mixedMass (mixedJoin t u) = mixedMass u from rfl,
              show (mixedJoin t u).queries = t.queries + u.queries from rfl]
            push_cast
            ring
      _ = ((observedMixedTraces O (k t.accepted) t.state).map mixedMass).sum * (t.queries : ℝ)
          + mixedExpectedQueries O (k t.accepted) t.state := by
          rw [sum_map_mul_const]
          rfl
      _ = mixedMass t * (t.queries : ℝ)
          + mixedExpectedQueries O (k t.accepted) t.state := by
          rw [observedMixedTraces_mass_sum O hO _ (hk t.accepted) t.state]
          rfl
  have hmap : ((observedMixedTraces O P ρ).map
        (fun t => (((observedMixedTraces O (k t.accepted) t.state).map (mixedJoin t)).map
          (fun s => mixedMass s * s.queries)).sum)).sum
      = ((observedMixedTraces O P ρ).map
          (fun t => mixedMass t * t.queries
            + mixedExpectedQueries O (k t.accepted) t.state)).sum :=
    sum_map_congr _ key
  rw [hmap, sum_map_add]
  rfl

end Qatlib.Concepts.AdversaryBounds.AdvDuality
