/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Circuit relabeling

`relabelCircuit` transports every gate in a query circuit along an equivalence of basis labels.
The module proves compatibility with identity, inverse, composition, concatenation, and
repetition.

`run_relabelCircuit_readout` identifies the transported execution and measurement probabilities,
while `relabelCircuit_legality_resources` preserves unitarity and all recorded circuit counts.
These are finite basis-change identities for the circuit formalism of [NielsenChuang2010].

## Main statements

* `relabelCircuit_equivalence_laws`: gives identity, composition, and inverse laws.
* `run_relabelCircuit_readout`: transports circuit execution and event probabilities.
* `relabelCircuit_legality_resources`: preserves circuit legality, query count, gate count, and
  size.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.GateVocabulary.GateVocab

open Matrix

set_option autoImplicit false

variable {I J K : Type*}

/-- Transports a gate step along a basis equivalence and leaves query steps unchanged. -/
noncomputable def relabelStep (e : I ≃ J) : Step I → Step J
  | Step.gate U => Step.gate (relabelGate e U)
  | Step.query => Step.query

/-- Relabels every step of a circuit along the given basis equivalence. -/
noncomputable def relabelCircuit (e : I ≃ J) (C : Circuit I) : Circuit J :=
  C.map (relabelStep e)

/-- Relabeling a gate step relabels its gate matrix. -/
@[simp] theorem relabelStep_gate (e : I ≃ J) (U : Matrix I I ℂ) :
    relabelStep e (Step.gate U) = Step.gate (relabelGate e U) := rfl

/-- Relabeling a query step leaves it a query step. -/
@[simp] theorem relabelStep_query (e : I ≃ J) : relabelStep e Step.query = Step.query := rfl

/-- Relabeling the empty circuit gives the empty circuit. -/
@[simp] theorem relabelCircuit_nil (e : I ≃ J) : relabelCircuit e ([] : Circuit I) = [] := rfl

/-- Relabeling a gate-prefixed circuit relabels the leading matrix and the remaining circuit. -/
@[simp] theorem relabelCircuit_gate (e : I ≃ J) (U : Matrix I I ℂ) (C : Circuit I) :
    relabelCircuit e (Step.gate U :: C) = Step.gate (relabelGate e U) :: relabelCircuit e C := rfl

/-- Relabeling a query-prefixed circuit preserves the leading query and relabels the remaining
circuit. -/
@[simp] theorem relabelCircuit_query (e : I ≃ J) (C : Circuit I) :
    relabelCircuit e (Step.query :: C) = Step.query :: relabelCircuit e C := rfl

/-- Relabeling a matrix by the identity equivalence leaves it unchanged. -/
theorem relabelGate_refl (U : Matrix I I ℂ) : relabelGate (Equiv.refl I) U = U :=
  Matrix.reindex_refl_refl U

/-- Successive matrix relabelings equal relabeling by the composed equivalence. -/
theorem relabelGate_trans (e : I ≃ J) (f : J ≃ K) (U : Matrix I I ℂ) :
    relabelGate f (relabelGate e U) = relabelGate (e.trans f) U := by
  ext i k
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply]

/-- Relabeling a matrix and then relabeling by the inverse equivalence returns the original
matrix. -/
theorem relabelGate_symm (e : I ≃ J) (U : Matrix I I ℂ) :
    relabelGate e.symm (relabelGate e U) = U := by
  ext i j
  show (U.submatrix e.symm e.symm).submatrix e.symm.symm e.symm.symm i j = U i j
  rw [Matrix.submatrix_submatrix, Equiv.symm_symm]
  simp only [Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]

/-- Relabeling a circuit step by the identity equivalence leaves it unchanged. -/
theorem relabelStep_refl (s : Step I) : relabelStep (Equiv.refl I) s = s := by
  cases s with
  | gate U => exact congrArg Step.gate (relabelGate_refl U)
  | query => rfl

/-- Successive step relabelings equal relabeling by the composed equivalence. -/
theorem relabelStep_trans (e : I ≃ J) (f : J ≃ K) (s : Step I) :
    relabelStep f (relabelStep e s) = relabelStep (e.trans f) s := by
  cases s with
  | gate U => exact congrArg Step.gate (relabelGate_trans e f U)
  | query => rfl

/-- Relabeling a step and then relabeling by the inverse equivalence returns the original step. -/
theorem relabelStep_symm (e : I ≃ J) (s : Step I) :
    relabelStep e.symm (relabelStep e s) = s := by
  cases s with
  | gate U => exact congrArg Step.gate (relabelGate_symm e U)
  | query => rfl

/-- Circuit relabeling commutes with concatenation. -/
theorem relabelCircuit_append (e : I ≃ J) (C D : Circuit I) :
    relabelCircuit e (C ++ D) = relabelCircuit e C ++ relabelCircuit e D := by
  show (C ++ D).map (relabelStep e) = C.map (relabelStep e) ++ D.map (relabelStep e)
  exact List.map_append

/-- Circuit relabeling commutes with concatenation and with circuit repetition. -/
theorem relabelCircuit_composition_laws (e : I ≃ J) (C D : Circuit I) (k : ℕ) :
    relabelCircuit e (C ++ D) = relabelCircuit e C ++ relabelCircuit e D ∧
      relabelCircuit e (RepeatCircuit C k) = RepeatCircuit (relabelCircuit e C) k := by
  refine ⟨relabelCircuit_append e C D, ?_⟩
  induction k with
  | zero => simp [relabelCircuit, RepeatCircuit]
  | succ k ih => simp only [RepeatCircuit, relabelCircuit_append, ih, RepeatCircuit]

/-- Circuit relabeling satisfies the identity, composition, and inverse equivalence laws. -/
theorem relabelCircuit_equivalence_laws (e : I ≃ J) (f : J ≃ K) (C : Circuit I) :
    relabelCircuit (Equiv.refl I) C = C ∧
      relabelCircuit f (relabelCircuit e C) = relabelCircuit (e.trans f) C ∧
      relabelCircuit e.symm (relabelCircuit e C) = C := by
  constructor
  · induction C with
    | nil => rfl
    | cons s C ih => cases s <;> simp [ih, relabelGate_refl]
  constructor
  · induction C with
    | nil => rfl
    | cons s C ih => cases s <;> simp [ih, relabelGate_trans]
  · induction C with
    | nil => rfl
    | cons s C ih => cases s <;> simp [ih, relabelGate_symm]

/-- Relabeling the oracle, circuit, and initial state transports the final state by the same
equivalence. Measurement probability is preserved when the event is transported along that
equivalence. -/
theorem run_relabelCircuit_readout {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (W : Matrix I I ℂ) (C : Circuit I) (ψ : QState I)
    (S : Finset I) :
    Run (relabelGate e W) (relabelCircuit e C) (relabelState e ψ)
      = relabelState e (Run W C ψ) ∧
      MeasureProb (Run (relabelGate e W) (relabelCircuit e C) (relabelState e ψ))
        (S.map e.toEmbedding) = MeasureProb (Run W C ψ) S := by
  have hrun : ∀ (C : Circuit I) (ψ : QState I),
      Run (relabelGate e W) (relabelCircuit e C) (relabelState e ψ)
        = relabelState e (Run W C ψ) := by
    intro C
    induction C with
    | nil => intro _; rfl
    | cons s C ih =>
      intro ψ
      cases s with
      | gate U => simp only [relabelCircuit_gate, run_gate, applyGate_relabelGate, ih]
      | query => simp only [relabelCircuit_query, run_query, applyGate_relabelGate, ih]
  refine ⟨hrun C ψ, ?_⟩
  rw [hrun C ψ, measureProb_relabelState]

namespace CircuitRelabel

/-- Relabeling square matrices preserves multiplication. -/
theorem relabelGate_mul (e : I ≃ J) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M N : Matrix I I ℂ) :
    relabelGate e (M * N) = relabelGate e M * relabelGate e N :=
  Matrix.reindexAlgEquiv_mul ℂ ℂ e M N

/-- Relabeling the identity matrix gives the identity matrix. -/
theorem relabelGate_one {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · have h' : ¬ (e.symm i = e.symm j) := fun hh => h (e.symm.injective hh)
    simp [h, h']

end CircuitRelabel

/-- A relabeled matrix is unitary exactly when the original matrix is unitary. -/
theorem relabelGate_mem_unitaryGroup {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (U : Matrix I I ℂ) :
    relabelGate e U ∈ Matrix.unitaryGroup J ℂ ↔ U ∈ Matrix.unitaryGroup I ℂ := by
  have hstar : ∀ (V : Matrix I I ℂ), (relabelGate e V)ᴴ = relabelGate e Vᴴ := by
    intro V
    ext i j
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.conjTranspose_apply]
  constructor
  · intro h
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h ⊢
    calc Uᴴ * U
        = relabelGate e.symm (relabelGate e (Uᴴ * U)) := (relabelGate_symm e (Uᴴ * U)).symm
      _ = relabelGate e.symm (relabelGate e Uᴴ * relabelGate e U) := by
          rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul e Uᴴ U]
      _ = relabelGate e.symm ((relabelGate e U)ᴴ * relabelGate e U) := by rw [hstar]
      _ = relabelGate e.symm 1 := by rw [h]
      _ = 1 := Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one e.symm
  · intro h
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h ⊢
    calc (relabelGate e U)ᴴ * relabelGate e U
        = relabelGate e Uᴴ * relabelGate e U :=
          congrArg (fun M : Matrix J J ℂ => M * relabelGate e U) (hstar U)
      _ = relabelGate e (Uᴴ * U) := (Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul e Uᴴ U).symm
      _ = relabelGate e 1 := by rw [h]
      _ = 1 := Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one e

/-- Relabeling preserves unitary-circuit legality, query count, gate count, and circuit size. -/
theorem relabelCircuit_legality_resources {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (C : Circuit I) :
    (IsUnitaryCircuit (relabelCircuit e C) ↔ IsUnitaryCircuit C) ∧
      QueryCount (relabelCircuit e C) = QueryCount C ∧
      GateCount (relabelCircuit e C) = GateCount C ∧
      Size (relabelCircuit e C) = Size C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro hC
      induction C with
      | nil => exact isUnitaryCircuit_nil
      | cons s C ih =>
        cases s with
        | gate U =>
          rw [relabelCircuit_gate] at hC
          obtain ⟨hU, hC'⟩ :=
            (isUnitaryCircuit_gate (relabelGate e U) (relabelCircuit e C)).mp hC
          rw [isUnitaryCircuit_gate]
          exact ⟨(relabelGate_mem_unitaryGroup e U).1 hU, ih hC'⟩
        | query =>
          rw [relabelCircuit_query] at hC
          rw [isUnitaryCircuit_query]
          exact ih ((isUnitaryCircuit_query (relabelCircuit e C)).mp hC)
    · intro hC
      induction C with
      | nil => exact isUnitaryCircuit_nil
      | cons s C ih =>
        cases s with
        | gate U =>
          obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
          rw [relabelCircuit_gate, isUnitaryCircuit_gate]
          exact ⟨(relabelGate_mem_unitaryGroup e U).2 hU, ih hC'⟩
        | query =>
          rw [relabelCircuit_query, isUnitaryCircuit_query]
          exact ih ((isUnitaryCircuit_query C).mp hC)
  · induction C with
    | nil => rfl
    | cons s C ih => cases s <;> simp [ih]
  · induction C with
    | nil => rfl
    | cons s C ih => cases s <;> simp [ih]
  · induction C with
    | nil => rfl
    | cons s C ih => cases s <;> simp [ih]

end Qatlib.Concepts.GateVocabulary.GateVocab
