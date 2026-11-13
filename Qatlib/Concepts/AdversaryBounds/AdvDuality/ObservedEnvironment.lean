/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.AdaptiveQuery.RawProcess.ObservedCircuitLaws
import Mathlib.Tactic.SimpRw

/-!
# Hidden environments for observed circuits

`liftObservedEnvironment` extends an observed circuit to a product register, with its explicit
gates and measurements acting on the first component. `environmentTrace` transforms the
environment part of each branch, and `sliceEnvironmentTrace` extracts a fixed environment
coordinate. These tensor constructions use the composite system formalism of [Watrous2018].

`hiddenTableOracle` selects an oracle block according to the environment coordinate. The
execution lemmas relate lifted circuits to environment transformations and to individual blocks
without changing the recorded branch metadata.

## Main statements

* `liftObservedEnvironment_wellFormed` preserves circuit well-formedness.
* `observed_environment_intertwining` lifts an oracle intertwining relation to complete branch
  lists.
* `observed_hiddenTable_slices` identifies each environment slice with execution under its
  selected oracle.
* `hiddenTableOracle_unitary` proves unitarity when every oracle block is unitary.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

variable {I : Type u} {E : Type v}

/-- Extends an observed circuit to a product register by tensoring explicit gates and projectors
with the environment identity and reading measurement labels from the system coordinate. -/
noncomputable def liftObservedEnvironment
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] :
    ObservedCircuit I → ObservedCircuit (I × E)
  | .halt accepted => .halt accepted
  | .step (.gate G) next =>
      .step (.gate (TensorGate G (1 : Matrix E E ℂ)))
        (liftObservedEnvironment next)
  | .step .query next =>
      .step .query (liftObservedEnvironment next)
  | .measure n label next =>
      .measure n (fun x => label x.1)
        (fun o => liftObservedEnvironment (next o))
  | .project Q onFalse onTrue =>
      .project (TensorGate Q (1 : Matrix E E ℂ))
        (liftObservedEnvironment onFalse)
        (liftObservedEnvironment onTrue)

variable [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- Applies `W` to the environment component of a branch state while retaining all classical
trace fields. -/
noncomputable def environmentTrace (W : Matrix E E ℂ)
    (t : BranchTrace (I × E)) : BranchTrace (I × E) :=
  { t with state := ApplyGate (TensorGate (1 : Matrix I I ℂ) W) t.state }

/-- Restricts a branch state to the fixed environment coordinate `a`, retaining acceptance,
resource counts, and outcomes. -/
def sliceEnvironmentTrace (a : E) (t : BranchTrace (I × E)) : BranchTrace I where
  state := fun i => t.state (i, a)
  accepted := t.accepted
  queries := t.queries
  gates := t.gates
  measurements := t.measurements
  outcomes := t.outcomes

/-- The block diagonal oracle on a product register whose block at environment coordinate `a` is
`O a`. -/
def hiddenTableOracle (O : E → Matrix I I ℂ) :
    Matrix (I × E) (I × E) ℂ :=
  fun x y => if x.2 = y.2 then O x.2 x.1 y.1 else 0

/-- Tensoring an orthogonal projector with the environment identity preserves the orthogonal
projector property. -/
private theorem observedEnvironment_projector_lift (Q : Matrix I I ℂ)
    (hQ : IsOrthogonalProjector Q) :
    IsOrthogonalProjector (TensorGate Q (1 : Matrix E E ℂ)) := by
  have hid : Q * Q = Q := hQ.1
  have hstar : Q.conjTranspose = Q := hQ.2
  refine ⟨?_, ?_⟩
  · change
      TensorGate Q (1 : Matrix E E ℂ) *
        TensorGate Q (1 : Matrix E E ℂ) =
      TensorGate Q (1 : Matrix E E ℂ)
    rw [tensorGate_mul, hid, Matrix.one_mul]
  · change
      (TensorGate Q (1 : Matrix E E ℂ)).conjTranspose =
      TensorGate Q (1 : Matrix E E ℂ)
    rw [tensorGate_conjTranspose, hstar, Matrix.conjTranspose_one]

/-- Lifting an observed circuit to an additional environment preserves its well-formedness. -/
theorem liftObservedEnvironment_wellFormed (P : ObservedCircuit I)
    (hP : observedWellFormed P) :
    observedWellFormed (liftObservedEnvironment (E := E) P) := by
  induction P with
  | halt accepted => trivial
  | step s next ih =>
      cases s with
      | gate G =>
          exact ⟨tensorGate_unitary hP.1 (Submonoid.one_mem _), ih hP.2⟩
      | query =>
          exact ih hP
  | measure n label next ih =>
      exact fun o => ih o (hP o)
  | project Q onFalse onTrue ihFalse ihTrue =>
      exact ⟨observedEnvironment_projector_lift Q hP.1,
        ihFalse hP.2.1, ihTrue hP.2.2⟩

/-- Tensoring the complementary system projector with the environment identity equals the
complement of the lifted matrix. -/
private theorem observedEnvironment_complement (Q : Matrix I I ℂ) :
    TensorGate (1 - Q) (1 : Matrix E E ℂ) =
      1 - TensorGate Q (1 : Matrix E E ℂ) := by
  have h :
      TensorGate (1 - Q) (1 : Matrix E E ℂ) =
        TensorGate (1 : Matrix I I ℂ) (1 : Matrix E E ℂ) -
          TensorGate Q (1 : Matrix E E ℂ) := by
    funext x y
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    simp only [tensorGate_apply, Matrix.sub_apply, sub_mul]
  simpa only [tensorGate_one] using h

/-- Selecting a binary measurement branch commutes with tensoring its system matrix with the
environment identity. -/
private theorem observedEnvironment_selector (Q : Matrix I I ℂ)
    (outcome : Bool) :
    (if outcome then TensorGate Q (1 : Matrix E E ℂ)
      else 1 - TensorGate Q (1 : Matrix E E ℂ)) =
      TensorGate (if outcome then Q else 1 - Q) (1 : Matrix E E ℂ) := by
  cases outcome with
  | false => exact (observedEnvironment_complement Q).symm
  | true => rfl

/-- A gate on the system component commutes with an arbitrary matrix acting on the environment
component. -/
private theorem observedEnvironment_gate_commute (G : Matrix I I ℂ)
    (W : Matrix E E ℂ) (psi : QState (I × E)) :
    ApplyGate (TensorGate G (1 : Matrix E E ℂ))
        (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) psi) =
      ApplyGate (TensorGate (1 : Matrix I I ℂ) W)
        (ApplyGate (TensorGate G (1 : Matrix E E ℂ)) psi) := by
  simp_rw [← applyGate_mul, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

/-- The projector for a label depending only on the system coordinate is the corresponding
system projector tensored with the environment identity. -/
private theorem observedEnvironment_label_projector {n : ℕ}
    (label : I → Fin n) (o : Fin n) :
    Projector (Finset.univ.filter (fun x : I × E => label x.1 = o)) =
      TensorGate
        (Projector (Finset.univ.filter (fun i : I => label i = o)))
        (1 : Matrix E E ℂ) := by
  funext x y
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [Projector, tensorGate_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Prod.mk.injEq, hij, hab]

/-- Collapsing on a system label commutes with applying a matrix to the environment component. -/
private theorem observedEnvironment_collapse_commute {n : ℕ}
    (label : I → Fin n) (o : Fin n) (W : Matrix E E ℂ)
    (psi : QState (I × E)) :
    Collapse (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) psi)
        (Finset.univ.filter (fun x : I × E => label x.1 = o)) =
      ApplyGate (TensorGate (1 : Matrix I I ℂ) W)
        (Collapse psi
          (Finset.univ.filter (fun x : I × E => label x.1 = o))) := by
  simpa only [Collapse, observedEnvironment_label_projector] using
    observedEnvironment_gate_commute
      (Projector (Finset.univ.filter (fun i : I => label i = o))) W psi

/-- A branch of a lifted binary projective measurement commutes with a matrix acting on the
environment component. -/
private theorem observedEnvironment_project_commute (Q : Matrix I I ℂ)
    (W : Matrix E E ℂ) (outcome : Bool) (psi : QState (I × E)) :
    ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) outcome
        (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) psi) =
      ApplyGate (TensorGate (1 : Matrix I I ℂ) W)
        (ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) outcome psi) := by
  simpa only [ProjectiveBranch, observedEnvironment_selector] using
    observedEnvironment_gate_commute (if outcome then Q else 1 - Q) W psi

/-- An oracle intertwining relation through the environment matrix extends to the complete
observed execution. The resulting branch list is obtained by applying `environmentTrace W`
to each trace of the second execution. -/
theorem observed_environment_intertwining (W : Matrix E E ℂ)
    (A B : Matrix (I × E) (I × E) ℂ)
    (hAB : A * TensorGate (1 : Matrix I I ℂ) W =
      TensorGate (1 : Matrix I I ℂ) W * B)
    (P : ObservedCircuit I) (psi : QState (I × E)) :
    observedTraces A (liftObservedEnvironment (E := E) P)
        (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) psi) =
      (observedTraces B (liftObservedEnvironment (E := E) P) psi).map
        (environmentTrace W) := by
  have hquery (phi : QState (I × E)) :
      ApplyGate A (ApplyGate (TensorGate (1 : Matrix I I ℂ) W) phi) =
        ApplyGate (TensorGate (1 : Matrix I I ℂ) W) (ApplyGate B phi) := by
    rw [← applyGate_mul, hAB, applyGate_mul]
  induction P generalizing psi with
  | halt accepted => rfl
  | step s next ih =>
      cases s with
      | gate G =>
          simpa only [liftObservedEnvironment, observedTraces,
            observedEnvironment_gate_commute, List.map_map,
            Function.comp_def, environmentTrace] using
            congrArg
              (fun ts : List (BranchTrace (I × E)) =>
                ts.map (fun t => { t with gates := t.gates + 1 }))
              (ih (ApplyGate (TensorGate G (1 : Matrix E E ℂ)) psi))
      | query =>
          simpa only [liftObservedEnvironment, observedTraces, hquery,
            List.map_map, Function.comp_def, environmentTrace] using
            congrArg
              (fun ts : List (BranchTrace (I × E)) =>
                ts.map (fun t => { t with queries := t.queries + 1 }))
              (ih (ApplyGate B psi))
  | measure n label next ih =>
      simp only [liftObservedEnvironment, observedTraces, List.map_flatten,
        List.map_ofFn, Function.comp_def]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext o
      simpa only [observedEnvironment_collapse_commute, List.map_map,
        Function.comp_def, environmentTrace] using
        congrArg
          (fun ts : List (BranchTrace (I × E)) =>
            ts.map (fun t =>
              { t with
                measurements := t.measurements + 1
                outcomes := (n, o.val) :: t.outcomes }))
          (ih o (Collapse psi
            (Finset.univ.filter (fun x : I × E => label x.1 = o))))
  | project Q onFalse onTrue ihFalse ihTrue =>
      simpa only [liftObservedEnvironment, observedTraces,
        observedEnvironment_project_commute, List.map_append, List.map_map,
        Function.comp_def, environmentTrace] using!
        congrArg₂ List.append
          (congrArg
            (fun ts : List (BranchTrace (I × E)) =>
              ts.map (fun t =>
                { t with
                  measurements := t.measurements + 1
                  outcomes := (2, 0) :: t.outcomes }))
            (ihFalse
              (ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) false psi)))
          (congrArg
            (fun ts : List (BranchTrace (I × E)) =>
              ts.map (fun t =>
                { t with
                  measurements := t.measurements + 1
                  outcomes := (2, 1) :: t.outcomes }))
            (ihTrue
              (ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) true psi)))

/-- Taking a fixed environment slice after a lifted system gate agrees with applying the
original gate to that slice. -/
private theorem observedEnvironment_gate_slice (G : Matrix I I ℂ)
    (psi : QState (I × E)) (a : E) :
    (fun i => ApplyGate (TensorGate G (1 : Matrix E E ℂ)) psi (i, a)) =
      ApplyGate G (fun i => psi (i, a)) := by
  funext i
  simp only [ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_ite, ite_mul]

/-- The slice at environment coordinate `a` of a hidden table oracle application is the
application of `O a` to the corresponding input slice. -/
private theorem observedEnvironment_oracle_slice (O : E → Matrix I I ℂ)
    (psi : QState (I × E)) (a : E) :
    (fun i => ApplyGate (hiddenTableOracle O) psi (i, a)) =
      ApplyGate (O a) (fun i => psi (i, a)) := by
  funext i
  simp only [ApplyGate, hiddenTableOracle, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

/-- Taking an environment slice commutes with collapse onto an outcome determined by the system
label. -/
private theorem observedEnvironment_collapse_slice {n : ℕ}
    (label : I → Fin n) (o : Fin n) (psi : QState (I × E)) (a : E) :
    (fun i => Collapse psi
      (Finset.univ.filter (fun x : I × E => label x.1 = o)) (i, a)) =
      Collapse (fun i => psi (i, a))
        (Finset.univ.filter (fun i : I => label i = o)) := by
  funext i
  simp only [collapse_apply, Finset.mem_filter, Finset.mem_univ, true_and]

/-- An environment slice of a lifted binary measurement branch equals the original measurement
branch applied to that slice. -/
private theorem observedEnvironment_project_slice (Q : Matrix I I ℂ)
    (outcome : Bool) (psi : QState (I × E)) (a : E) :
    (fun i =>
      ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) outcome psi (i, a)) =
      ProjectiveBranch Q outcome (fun i => psi (i, a)) := by
  simpa only [ProjectiveBranch, observedEnvironment_selector] using
    observedEnvironment_gate_slice (if outcome then Q else 1 - Q) psi a

/-- Slicing every trace of a lifted execution under a hidden table oracle gives exactly the
traces under the selected oracle block on the sliced input state. -/
theorem observed_hiddenTable_slices (O : E → Matrix I I ℂ)
    (P : ObservedCircuit I) (psi : QState (I × E)) (a : E) :
    (observedTraces (hiddenTableOracle O)
      (liftObservedEnvironment (E := E) P) psi).map (sliceEnvironmentTrace a) =
      observedTraces (O a) P (fun i => psi (i, a)) := by
  induction P generalizing psi with
  | halt accepted => rfl
  | step st next ih =>
    cases st with
    | gate G =>
      have h := congrArg
        (fun ts : List (BranchTrace I) => ts.map (fun t => {t with gates := t.gates+1}))
        (ih (ApplyGate (TensorGate G (1 : Matrix E E ℂ)) psi))
      rw [observedEnvironment_gate_slice] at h
      simpa only [liftObservedEnvironment, observedTraces, List.map_map,
        Function.comp_def, sliceEnvironmentTrace] using h
    | query =>
      have h := congrArg
        (fun ts : List (BranchTrace I) => ts.map (fun t => {t with queries := t.queries+1}))
        (ih (ApplyGate (hiddenTableOracle O) psi))
      rw [observedEnvironment_oracle_slice] at h
      simpa only [liftObservedEnvironment, observedTraces, List.map_map,
        Function.comp_def, sliceEnvironmentTrace] using h
  | measure n label next ih =>
    simp only [liftObservedEnvironment, observedTraces, List.map_flatten,
      List.map_ofFn, Function.comp_def]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext o
    have h := congrArg
      (fun ts : List (BranchTrace I) => ts.map
        (fun t => {t with measurements := t.measurements+1, outcomes := (n,o.val)::t.outcomes}))
      (ih o (Collapse psi (Finset.univ.filter (fun x : I × E => label x.1=o))))
    rw [observedEnvironment_collapse_slice] at h
    simpa only [List.map_map, Function.comp_def, sliceEnvironmentTrace] using h
  | project Q onFalse onTrue ihFalse ihTrue =>
    simp only [liftObservedEnvironment, observedTraces, List.map_append]
    apply congrArg₂ List.append
    · have h := congrArg
        (fun ts : List (BranchTrace I) => ts.map
          (fun t => {t with measurements := t.measurements+1, outcomes := (2,0)::t.outcomes}))
        (ihFalse (ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) false psi))
      rw [observedEnvironment_project_slice] at h
      simpa only [List.map_map, Function.comp_def, sliceEnvironmentTrace] using h
    · have h := congrArg
        (fun ts : List (BranchTrace I) => ts.map
          (fun t => {t with measurements := t.measurements+1, outcomes := (2,1)::t.outcomes}))
        (ihTrue (ProjectiveBranch (TensorGate Q (1 : Matrix E E ℂ)) true psi))
      rw [observedEnvironment_project_slice] at h
      simpa only [List.map_map, Function.comp_def, sliceEnvironmentTrace] using h

/-- A hidden table oracle is unitary whenever each of its oracle blocks is unitary. -/
theorem hiddenTableOracle_unitary (O : E → Matrix I I ℂ)
    (hO : ∀ a, O a ∈ Matrix.unitaryGroup I ℂ) :
    hiddenTableOracle O ∈ Matrix.unitaryGroup (I × E) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  rcases x with ⟨i,a⟩; rcases y with ⟨j,b⟩
  by_cases hab : a=b
  · subst b
    have h : (O a).conjTranspose * O a = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp (hO a)
    have he := congrArg (fun M : Matrix I I ℂ => M i j) h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hiddenTableOracle,
      Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq, ite_mul, mul_ite] using he
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hiddenTableOracle,
      Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq, hab, Ne.symm hab, ite_mul, mul_ite]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
