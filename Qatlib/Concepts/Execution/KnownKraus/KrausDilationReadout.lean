/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Mathlib.Data.List.OfFn

/-!
# Reading out a Kraus dilation

`krausReadoutProgram` applies a supplied dilation matrix and measures a labeling of its ancilla
register. Assuming the matrix has the prescribed Kraus action on an initialized ancilla, the
module computes its pure and reduced mixed branch traces, following the measurement construction
of [NielsenChuang2010].

`reduceKrausMixedTrace` removes the ancilla while retaining the outcome and resource records.
Unitarity of the supplied matrix ensures well-formedness and a zero query budget.

## Main statements

* `kraus_readout_pure_traces`: pure branches are the labeled components of the Kraus dilation.
* `kraus_readout_mixed_traces`: reduced mixed branches are coarse sums of Kraus conjugations.
* `kraus_readout_valid_budget`: a unitary readout program is well-formed and uses no queries.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false

namespace Qatlib.Concepts.Execution.KnownKraus

open Matrix

/-- The observed circuit that applies `W`, measures the ancilla label, and halts with the
prescribed acceptance flag. -/
noncomputable def krausReadoutProgram {d s t : ℕ}
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (label : Fin s → Fin t) (accept : Fin t → Bool) :
    ObservedCircuit (Fin d × Fin s) :=
  .step (.gate W) (.measure t (fun x => label x.2) (fun o => .halt (accept o)))

/-- Relabels a joint mixed branch operator to system and ancilla coordinates and traces out the
ancilla, retaining its classical record and resource counts. -/
noncomputable def reduceKrausMixedTrace {d s : ℕ}
    (b : MixedBranchTrace (d * s)) : MixedBranchTrace d :=
  ⟨PartialTrace (relabelGate finProdFinEquiv.symm b.state), b.accepted,
    b.queries, b.gates, b.measurements, b.outcomes⟩

/-- Flattening a finite list of singleton lists recovers the list of their entries. -/
private theorem krausReadout_flatten_singletons {α : Type*} {n : ℕ}
    (f : Fin n → α) :
    (List.ofFn (fun o : Fin n => [f o])).flatten = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.flatten_cons, List.singleton_append,
        ih (fun i => f i.succ), List.ofFn_succ (f := f)]

/-- If `W` realizes the Kraus action on the initialized ancilla, its readout traces are
precisely the labeled components of that action. Each branch records zero queries, one gate,
and one measurement. -/
theorem kraus_readout_pure_traces {d s t : ℕ}
    (K : Fin s → Operator d) (zero : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hW : ∀ psi : QState (Fin d),
      ApplyGate W (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)) =
        fun x => ApplyGate (K x.2) psi x.1)
    (label : Fin s → Fin t) (accept : Fin t → Bool)
    (O : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (psi : QState (Fin d)) :
    observedTraces O (krausReadoutProgram W label accept)
        (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)) =
      List.ofFn (fun o : Fin t =>
        (⟨(fun x => if label x.2 = o then ApplyGate (K x.2) psi x.1 else 0),
          accept o, 0, 1, 1, [(t, o.val)]⟩ : BranchTrace (Fin d × Fin s))) := by
  simp only [krausReadoutProgram, observedTraces, List.map_cons, List.map_nil,
    krausReadout_flatten_singletons, List.map_ofFn]
  apply congrArg List.ofFn
  funext o
  have hstate :
      Collapse (ApplyGate W (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)))
          (Finset.univ.filter (fun x : Fin d × Fin s => label x.2 = o)) =
        (fun x => if label x.2 = o then ApplyGate (K x.2) psi x.1 else 0) := by
    rw [hW]
    funext x
    simp only [collapse_apply, Finset.mem_filter, Finset.mem_univ, true_and]
  exact congrArg
    (fun state => (⟨state, accept o, 0, 1, 1, [(t, o.val)]⟩ :
      BranchTrace (Fin d × Fin s))) hstate

/-- Applying a matrix to a basis ket returns the corresponding matrix column. -/
private theorem krausReadout_apply_ket {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (j i : I) : ApplyGate M (Qatlib.Foundations.PureStateMath.Ket j) i = M i j := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, ket_apply, mul_ite]

/-- The prescribed dilation action on initialized pure inputs determines the corresponding
columns of `W` to be the Kraus matrix entries. -/
private theorem krausReadout_column {d s : ℕ}
    (K : Fin s → Operator d) (zero : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hW : ∀ psi : QState (Fin d),
      ApplyGate W (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)) =
        fun x => ApplyGate (K x.2) psi x.1)
    (i j : Fin d) (a : Fin s) : W (i, a) (j, zero) = K a i j := by
  have h := congrFun (hW (Qatlib.Foundations.PureStateMath.Ket j)) (i, a)
  rw [tensorState_ket_ket] at h
  simpa only [krausReadout_apply_ket] using h

/-- Relabeling matrix indices commutes with conjugate transpose. -/
private theorem krausReadout_relabel_star {I J : Type*} (e : I ≃ J)
    (M : Matrix I I ℂ) :
    relabelGate e M.conjTranspose = (relabelGate e M).conjTranspose := by
  ext i j
  rfl

/-- Relabeling commutes with matrix conjugation by a gate. -/
private theorem krausReadout_relabel_sandwich {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (M X : Matrix I I ℂ) :
    relabelGate e (M * X * M.conjTranspose) =
      relabelGate e M * relabelGate e X * (relabelGate e M).conjTranspose := by
  rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul, Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul,
    krausReadout_relabel_star]

/-- The projector for a transported outcome label is the relabeling of the original outcome
projector. -/
private theorem krausReadout_relabel_projector {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) {t : ℕ} (label : I → Fin t) (o : Fin t) :
    Projector (Finset.univ.filter (fun j : J => label (e.symm j) = o)) =
      relabelGate e (Projector (Finset.univ.filter (fun i : I => label i = o))) := by
  ext i j
  simp only [Projector, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i = j
  · subst j
    simp
  · have h' : e.symm i ≠ e.symm j := fun hh => h (e.symm.injective hh)
    simp [h, h']

/-- The ancilla block indexed by `a` and `b` of the dilated input is `K a * rho * (K
b).conjTranspose`, assuming the prescribed initialized columns. -/
private theorem krausReadout_joint_block {d s : ℕ}
    (K : Fin s → Operator d) (zero : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hcol : ∀ (i j : Fin d) (a : Fin s), W (i, a) (j, zero) = K a i j)
    (rho : Operator d) (i j : Fin d) (a b : Fin s) :
    (W * TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)) * W.conjTranspose) (i, a) (j, b) =
      (K a * rho * (K b).conjTranspose) i j := by
  have hleft (k : Fin d) (c : Fin s) :
      (W * TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))) (i, a) (k, c) =
        if c = zero then (K a * rho) i k else 0 := by
    by_cases hc : c = zero
    · subst c
      simp [Matrix.mul_apply, tensorGate_apply, outerProduct_apply, ket_apply,
        Fintype.sum_prod_type, mul_ite, hcol]
    · simp [Matrix.mul_apply, tensorGate_apply, outerProduct_apply, ket_apply,
        Fintype.sum_prod_type, hc]
  change (∑ y : Fin d × Fin s,
      (W * TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))) (i, a) y *
        star (W (j, b) y)) =
    ∑ k : Fin d, (K a * rho) i k * star (K b j k)
  simp only [Fintype.sum_prod_type, hleft, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol]

/-- After projection onto a coarse ancilla label and partial trace, the branch operator is the
sum of the Kraus conjugations with that label. -/
private theorem krausReadout_reduced_branch {d s t : ℕ}
    (K : Fin s → Operator d) (zero : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hcol : ∀ (i j : Fin d) (a : Fin s), W (i, a) (j, zero) = K a i j)
    (label : Fin s → Fin t) (o : Fin t) (rho : Operator d) :
    PartialTrace
        (Projector (Finset.univ.filter (fun x : Fin d × Fin s => label x.2 = o)) *
          (W * TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero)) * W.conjTranspose) *
          (Projector (Finset.univ.filter
            (fun x : Fin d × Fin s => label x.2 = o))).conjTranspose) =
      ∑ a : Fin s, if label a = o then K a * rho * (K a).conjTranspose else 0 := by
  rw [projector_conjTranspose]
  ext i j
  simp only [PartialTrace, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Projector, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : label a = o
  · simpa only [ha, if_true, one_mul, mul_one] using
      krausReadout_joint_block K zero W hcol rho i j a a
  · simp [ha]

/-- A matrix with the prescribed initialized Kraus action produces reduced mixed readout traces
equal to the coarse Kraus sums. Each trace retains the acceptance rule and records zero
queries, one gate, and one measurement. -/
theorem kraus_readout_mixed_traces {d s t : ℕ}
    (K : Fin s → Operator d) (zero : Fin s)
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hW : ∀ psi : QState (Fin d),
      ApplyGate W (TensorState psi (Qatlib.Foundations.PureStateMath.Ket zero)) =
        fun x => ApplyGate (K x.2) psi x.1)
    (label : Fin s → Fin t) (accept : Fin t → Bool)
    (O : Operator (d * s)) (rho : Operator d) :
    (observedMixedTraces O
        (relabelObserved finProdFinEquiv (krausReadoutProgram W label accept))
        (relabelGate finProdFinEquiv (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))))).map
        (reduceKrausMixedTrace (d := d) (s := s)) =
      List.ofFn (fun o : Fin t =>
        (⟨∑ a : Fin s, if label a = o then K a * rho * (K a).conjTranspose else 0,
          accept o, 0, 1, 1, [(t, o.val)]⟩ : MixedBranchTrace d)) := by
  have hcol := krausReadout_column K zero W hW
  have hstate (o : Fin t) :
      PartialTrace (relabelGate finProdFinEquiv.symm
        (conjBranch
          (Projector (Finset.univ.filter (fun x : Fin (d * s) =>
            label (finProdFinEquiv.symm x).2 = o)))
          (conjBranch (relabelGate finProdFinEquiv W)
            (relabelGate finProdFinEquiv
              (TensorGate rho (outerProduct (Qatlib.Foundations.PureStateMath.Ket zero))))))) =
        ∑ a : Fin s, if label a = o then K a * rho * (K a).conjTranspose else 0 := by
    rw [conjBranch_apply, conjBranch_apply,
      krausReadout_relabel_projector finProdFinEquiv (fun x : Fin d × Fin s => label x.2) o,
      ← krausReadout_relabel_sandwich, ← krausReadout_relabel_sandwich,
      relabelGate_relabelGate]
    exact krausReadout_reduced_branch K zero W hcol label o rho
  simp only [krausReadoutProgram, relabelObserved, observedMixedTraces,
    List.map_cons, List.map_nil, krausReadout_flatten_singletons,
    List.map_ofFn, Function.comp_apply]
  apply congrArg List.ofFn
  funext o
  change (⟨_, accept o, 0, 1, 1, [(t, o.val)]⟩ : MixedBranchTrace d) = _
  exact congrArg
    (fun state => (⟨state, accept o, 0, 1, 1, [(t, o.val)]⟩ : MixedBranchTrace d))
    (hstate o)

/-- A readout program with unitary `W` is well-formed and has query budget zero. -/
theorem kraus_readout_valid_budget {d s t : ℕ}
    (W : Matrix (Fin d × Fin s) (Fin d × Fin s) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d × Fin s) ℂ)
    (label : Fin s → Fin t) (accept : Fin t → Bool) :
    observedWellFormed (krausReadoutProgram W label accept) ∧
      observedQueryBudget (krausReadoutProgram W label accept) = 0 := by
  constructor
  · exact ⟨hW, fun _ => True.intro⟩
  · simp [krausReadoutProgram, observedQueryBudget]

end Qatlib.Concepts.Execution.KnownKraus
