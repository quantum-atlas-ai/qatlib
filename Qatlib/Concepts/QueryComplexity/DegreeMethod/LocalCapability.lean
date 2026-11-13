/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics

/-!
# Local capabilities for query circuits

This module packages explicit local operations as `HasControlled`, `HasInverse`, and
`HasPrepare`, with unitary witnesses and circuit semantics. `LiftCircuitTo`, `HasDiscard`,
`ActsOnLeft`, and `ActsOnRight` describe adding an untouched register, tracing it out, and
operations confined to one tensor factor.

The circuit wrappers count the supplied controlled or inverse matrix as a local gate; their zero
query counts concern these explicit witnesses. `noFreeControlled_lift` shows that tensoring a
nonidentity gate with a control identity does not supply the controlled gate specification.
Background on these local operations is given in [NielsenChuang2010], and the query model is
developed in [BealsEtAl2001].

## Main statements

* `blockDiag_unitary` and `controlledGate_unitary` establish unitarity of block diagonal and
  controlled matrices.
* `HasControlled.run_step_false`, `HasControlled.run_step_true`, and `HasInverse.run_cancel`
  give the operational behavior of supplied local capabilities.
* `run_liftCircuitTo_liftedOracle` preserves an untouched tensor factor, while
  `discard_liftedRun` and `measureProb_discard_liftedRun` recover the original state and event
  probabilities.
- `commute_actsOnLeft_actsOnRight` proves commutation for operations on separate factors.
* `uniform_program_quantifier_order` requires one algorithm for every instance;
  `perInstanceChoice_solves` and `no_uniform_program` exhibit why separate instance-dependent
  choices do not meet that requirement.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped ComplexOrder

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- States that `U` belongs to the unitary matrix group on `I`. -/
def HasUnitary (U : Matrix I I ℂ) : Prop := U ∈ Matrix.unitaryGroup I ℂ

/-- Forms the block diagonal matrix on `C × I` whose block indexed by `c` is `W c`. Entries
between distinct values of the first register vanish. -/
noncomputable def BlockDiag {C : Type*} [Fintype C] [DecidableEq C]
    (W : C → Matrix I I ℂ) : Matrix (C × I) (C × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then W q.1 p.2 q.2 else 0

omit [Fintype I] [DecidableEq I] in

/-- Evaluates a `BlockDiag W` entry as the corresponding block entry when the control indices
agree, and as zero otherwise. -/
theorem blockDiag_apply {C : Type*} [Fintype C] [DecidableEq C] (W : C → Matrix I I ℂ)
    (p q : C × I) :
    BlockDiag W p q = if p.1 = q.1 then W q.1 p.2 q.2 else 0 := rfl

/-- A block diagonal matrix is unitary when each of its blocks is unitary. -/
theorem blockDiag_unitary {C : Type*} [Fintype C] [DecidableEq C] (W : C → Matrix I I ℂ)
    (hW : ∀ c, W c ∈ Matrix.unitaryGroup I ℂ) :
    BlockDiag W ∈ Matrix.unitaryGroup (C × I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext p p'
  obtain ⟨a, i⟩ := p
  obtain ⟨a', i'⟩ := p'
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    BlockDiag, Matrix.of_apply, RCLike.star_def, Matrix.one_apply]
  rcases eq_or_ne a a' with h | h
  · subst h
    have hunit : (W a)ᴴ * W a = 1 := by
      have hh := (Matrix.mem_unitaryGroup_iff').mp (hW a)
      rwa [Matrix.star_eq_conjTranspose] at hh
    have hent : (∑ b : I, (starRingEnd ℂ) (W a b i) * W a b i')
        = ((W a)ᴴ * W a) i i' := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun b _ => by rw [Matrix.conjTranspose_apply, RCLike.star_def]
    have hterm : ∀ x : C, x ≠ a →
        (∑ b : I, (starRingEnd ℂ) (if x = a then W a b i else 0)
            * (if x = a then W a b i' else 0)) = 0 := by
      intro x hx
      rw [Finset.sum_eq_zero fun b (_ : b ∈ Finset.univ) => by simp [hx]]
    rw [Fintype.sum_eq_single a hterm]
    simp only [ite_true]
    rw [hent, hunit]
    by_cases hii : i = i' <;> simp [Matrix.one_apply, hii]
  · rw [ite_eq_right (fun e => h (congrArg Prod.fst e))]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hxa : x = a
    · simp [hxa, h]
    · simp [hxa]

/-- Constructs the controlled version of `U`, acting as the identity on the `false` control
block and as `U` on the `true` block. This is the standard controlled operation of [Nielsen
and Chuang, 2010][NielsenChuang2010]. -/
noncomputable def ControlledGate (U : Matrix I I ℂ) : Matrix (Bool × I) (Bool × I) ℂ :=
  BlockDiag fun b : Bool => if b then U else (1 : Matrix I I ℂ)

/-- Specifies the four Boolean control blocks of a controlled `U`: identity on `false`, `U` on
`true`, and zero off the diagonal. This predicate describes matrix entries without
separately requiring unitarity. -/
def IsControlledGate (cU : Matrix (Bool × I) (Bool × I) ℂ) (U : Matrix I I ℂ) : Prop :=
  (∀ i j, cU (false, i) (false, j) = if i = j then 1 else 0) ∧
    (∀ i j, cU (true, i) (true, j) = U i j) ∧
    (∀ i j, cU (false, i) (true, j) = 0) ∧
    (∀ i j, cU (true, i) (false, j) = 0)

/-- Packages an explicitly supplied unitary controlled matrix together with its
`IsControlledGate` specification for `U`. -/
structure HasControlled (U : Matrix I I ℂ) where

  controlled : Matrix (Bool × I) (Bool × I) ℂ

  controlled_unitary : controlled ∈ Matrix.unitaryGroup (Bool × I) ℂ

  is_controlled : IsControlledGate controlled U

omit [Fintype I] in

/-- The canonical block diagonal matrix `ControlledGate U` satisfies `IsControlledGate` for
every matrix `U`. -/
theorem isControlledGate_controlledGate (U : Matrix I I ℂ) :
    IsControlledGate (ControlledGate U) U := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩ <;>
    simp [ControlledGate, BlockDiag, Matrix.one_apply]

/-- The canonical controlled matrix is unitary whenever `U` is unitary. -/
theorem controlledGate_unitary {U : Matrix I I ℂ} (hU : HasUnitary U) :
    ControlledGate U ∈ Matrix.unitaryGroup (Bool × I) ℂ :=
  blockDiag_unitary _ fun b => by
    cases b with
    | false => exact Submonoid.one_mem _
    | true => exact hU

/-- Builds a `HasControlled U` witness from an explicit unitary matrix `U` using `ControlledGate
U`. -/
noncomputable def controlled_of_explicit {U : Matrix I I ℂ} (hU : HasUnitary U) :
    HasControlled U :=
  ⟨ControlledGate U, controlledGate_unitary hU, isControlledGate_controlledGate U⟩

/-- Extracts unitarity of `U` from a unitary matrix satisfying its controlled gate
specification. -/
theorem HasControlled.unitary {U : Matrix I I ℂ} (h : HasControlled U) : HasUnitary U := by
  obtain ⟨h00, h11, h01, h10⟩ := h.is_controlled
  show U ∈ Matrix.unitaryGroup I ℂ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  have hmul : h.controlled * h.controlledᴴ = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff).mp h.controlled_unitary
    rwa [Matrix.star_eq_conjTranspose] at hh
  have hf : ∑ b : I, h.controlled (true, i) (false, b)
        * (starRingEnd ℂ) (h.controlled (true, j) (false, b)) = 0 := by
    rw [Finset.sum_eq_zero fun b (_ : b ∈ Finset.univ) => by rw [h10, zero_mul]]
  have hsplit : ∑ x : Bool, ∑ b : I, h.controlled (true, i) (x, b)
        * (starRingEnd ℂ) (h.controlled (true, j) (x, b))
      = ∑ b : I, U i b * (starRingEnd ℂ) (U j b) := by
    rw [Fintype.sum_bool]
    simp only [hf, add_zero]
    exact Finset.sum_congr rfl fun b _ => by rw [h11, h11]
  calc (U * Uᴴ) i j = ∑ b : I, U i b * (starRingEnd ℂ) (U j b) := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
    _ = ∑ x : Bool, ∑ b : I, h.controlled (true, i) (x, b)
          * (starRingEnd ℂ) (h.controlled (true, j) (x, b)) := hsplit.symm
    _ = (h.controlled * h.controlledᴴ) (true, i) (true, j) := by
        simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
          RCLike.star_def]
    _ = (1 : Matrix (Bool × I) (Bool × I) ℂ) (true, i) (true, j) := by rw [hmul]
    _ = (1 : Matrix I I ℂ) i j := by simp [Matrix.one_apply]

omit [Fintype I] in
/-- If `U` is not the identity, `TensorGate 1 U` fails the controlled gate specification for
`U`. Its `false` control block still applies `U`, whereas the specification requires the
identity there. -/
theorem noFreeControlled_lift (U : Matrix I I ℂ) (hU : ¬ U = 1) :
    ¬ IsControlledGate (TensorGate (1 : Matrix Bool Bool ℂ) U) U := by
  rintro ⟨h00, -, -, -⟩
  apply hU
  ext i j
  have he := h00 i j
  rw [tensorGate_apply] at he
  simpa [Matrix.one_apply] using he

/-- A matrix satisfying `IsControlledGate cU U` leaves `Ket false ⊗ ψ` unchanged. -/
theorem applyGate_isControlledGate_ket_false {cU : Matrix (Bool × I) (Bool × I) ℂ}
    {U : Matrix I I ℂ} (hspec : IsControlledGate cU U) (ψ : QState I) :
    ApplyGate cU (TensorState (Ket false) ψ) = TensorState (Ket false) ψ := by
  obtain ⟨h00, h11, h01, h10⟩ := hspec
  funext p
  obtain ⟨b, i⟩ := p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorState, Ket]
  cases b with
  | false => simp [h00]
  | true => simp [h10]

/-- A matrix satisfying `IsControlledGate cU U` maps `Ket true ⊗ ψ` to `Ket true ⊗ ApplyGate U
ψ`. -/
theorem applyGate_isControlledGate_ket_true {cU : Matrix (Bool × I) (Bool × I) ℂ}
    {U : Matrix I I ℂ} (hspec : IsControlledGate cU U) (ψ : QState I) :
    ApplyGate cU (TensorState (Ket true) ψ) = TensorState (Ket true) (ApplyGate U ψ) := by
  obtain ⟨h00, h11, h01, h10⟩ := hspec
  funext p
  obtain ⟨b, i⟩ := p
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorState, Ket]
  cases b with
  | true => simp [h11]
  | false => simp [h01]

/-- Turns the supplied controlled matrix into a circuit consisting of one local gate. -/
def HasControlled.step {U : Matrix I I ℂ} (h : HasControlled U) : Circuit (Bool × I) :=
  [Step.gate h.controlled]

/-- The singleton circuit supplied by a `HasControlled` witness is a unitary circuit. -/
theorem HasControlled.step_isUnitary {U : Matrix I I ℂ} (h : HasControlled U) :
    IsUnitaryCircuit h.step :=
  (isUnitaryCircuit_gate _ _).mpr ⟨h.controlled_unitary, isUnitaryCircuit_nil⟩

/-- The controlled gate circuit has zero query steps because the supplied controlled matrix is
represented as a local gate. -/
theorem HasControlled.queryCount_step {U : Matrix I I ℂ} (h : HasControlled U) :
    QueryCount h.step = 0 := rfl

/-- The controlled gate circuit contains exactly one local gate. -/
theorem HasControlled.gateCount_step {U : Matrix I I ℂ} (h : HasControlled U) :
    GateCount h.step = 1 := rfl

/-- Running the supplied controlled gate circuit with control `false` leaves the target state
unchanged, for any oracle matrix `W`. -/
theorem HasControlled.run_step_false {U : Matrix I I ℂ} (h : HasControlled U)
    (W : Matrix (Bool × I) (Bool × I) ℂ) (ψ : QState I) :
    Run W h.step (TensorState (Ket false) ψ) = TensorState (Ket false) ψ := by
  simp only [HasControlled.step, run_gate, run_nil]
  exact applyGate_isControlledGate_ket_false h.is_controlled ψ

/-- Running the supplied controlled gate circuit with control `true` applies `U` to the target
and preserves the control, for any oracle matrix `W`. -/
theorem HasControlled.run_step_true {U : Matrix I I ℂ} (h : HasControlled U)
    (W : Matrix (Bool × I) (Bool × I) ℂ) (ψ : QState I) :
    Run W h.step (TensorState (Ket true) ψ) = TensorState (Ket true) (ApplyGate U ψ) := by
  simp only [HasControlled.step, run_gate, run_nil]
  exact applyGate_isControlledGate_ket_true h.is_controlled ψ

/-- Prepending the supplied controlled gate circuit to `C` preserves the query count of `C`. -/
theorem queryCount_append_controlledStep {U : Matrix I I ℂ} (h : HasControlled U)
    (C : Circuit (Bool × I)) : QueryCount (h.step ++ C) = QueryCount C := by
  rw [queryCount_append, h.queryCount_step, zero_add]

/-- Packages an explicitly supplied unitary inverse gate for `U`, with both matrix
multiplication cancellation identities. -/
structure HasInverse (U : Matrix I I ℂ) where

  invGate : Matrix I I ℂ

  inv_unitary : invGate ∈ Matrix.unitaryGroup I ℂ

  left_inv : invGate * U = 1

  right_inv : U * invGate = 1

/-- A matrix with a unitary two-sided inverse is itself unitary. -/
theorem HasInverse.unitary {U : Matrix I I ℂ} (h : HasInverse U) : HasUnitary U := by
  have h1 : h.invGateᴴ * h.invGate = 1 := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp h.inv_unitary
    rwa [Matrix.star_eq_conjTranspose] at hh
  have hUeq : U = h.invGateᴴ := by
    calc U = 1 * U := (one_mul U).symm
      _ = (h.invGateᴴ * h.invGate) * U := by rw [h1]
      _ = h.invGateᴴ * (h.invGate * U) := Matrix.mul_assoc _ _ _
      _ = h.invGateᴴ * 1 := by rw [h.left_inv]
      _ = h.invGateᴴ := mul_one _
  show U ∈ Matrix.unitaryGroup I ℂ
  rw [hUeq]
  exact conjTranspose_mem_unitaryGroup h.inv_unitary

/-- Constructs a `HasInverse U` witness for a unitary matrix `U` using its conjugate transpose. -/
noncomputable def inverse_of_inv {U : Matrix I I ℂ} (hU : HasUnitary U) : HasInverse U where
  invGate := Uᴴ
  inv_unitary := conjTranspose_mem_unitaryGroup hU
  left_inv := by
    have hh := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at hh
  right_inv := by
    have hh := (Matrix.mem_unitaryGroup_iff).mp hU
    rwa [Matrix.star_eq_conjTranspose] at hh

/-- Applying the supplied inverse gate after `U` restores any state `ψ`. -/
theorem applyGate_inverse_cancel {U : Matrix I I ℂ} (h : HasInverse U) (ψ : QState I) :
    ApplyGate h.invGate (ApplyGate U ψ) = ψ := by
  rw [← applyGate_mul, h.left_inv, applyGate_one]

/-- Applying `U` after its supplied inverse gate restores any state `ψ`. -/
theorem applyGate_inverse_cancel' {U : Matrix I I ℂ} (h : HasInverse U) (ψ : QState I) :
    ApplyGate U (ApplyGate h.invGate ψ) = ψ := by
  rw [← applyGate_mul, h.right_inv, applyGate_one]

/-- Turns the supplied inverse matrix into a circuit consisting of one local gate. -/
def HasInverse.step {U : Matrix I I ℂ} (h : HasInverse U) : Circuit I :=
  [Step.gate h.invGate]

/-- The singleton circuit supplied by a `HasInverse` witness is a unitary circuit. -/
theorem HasInverse.step_isUnitary {U : Matrix I I ℂ} (h : HasInverse U) :
    IsUnitaryCircuit h.step :=
  (isUnitaryCircuit_gate _ _).mpr ⟨h.inv_unitary, isUnitaryCircuit_nil⟩

/-- The inverse gate circuit has zero query steps because its supplied matrix is represented as
a local gate. -/
theorem HasInverse.queryCount_step {U : Matrix I I ℂ} (h : HasInverse U) :
    QueryCount h.step = 0 := rfl

/-- The inverse gate circuit contains exactly one local gate. -/
theorem HasInverse.gateCount_step {U : Matrix I I ℂ} (h : HasInverse U) :
    GateCount h.step = 1 := rfl

/-- Running the inverse gate circuit followed by the local gate `U` restores the input state,
independently of the oracle matrix. -/
theorem HasInverse.run_cancel {U : Matrix I I ℂ} (h : HasInverse U) (W : Matrix I I ℂ)
    (ψ : QState I) : Run W (h.step ++ [Step.gate U]) ψ = ψ := by
  simp only [HasInverse.step, List.cons_append, List.nil_append, run_gate, run_nil]
  rw [← applyGate_mul, h.right_inv, applyGate_one]

/-- Packages a unitary circuit with zero queries that prepares `ψ` from the basis state `Ket i₀`
when run with the identity oracle. -/
structure HasPrepare (ψ : QState I) (i₀ : I) where

  prep : Circuit I

  unitary : IsUnitaryCircuit prep

  query_free : QueryCount prep = 0

  produces : Run 1 prep (Ket i₀) = ψ

/-- A preparation circuit from `HasPrepare` produces its specified state for every oracle matrix
because it contains no queries. -/
theorem HasPrepare.run_oracle {ψ : QState I} {i₀ : I} (h : HasPrepare ψ i₀)
    (W : Matrix I I ℂ) : Run W h.prep (Ket i₀) = ψ := by
  rw [run_eq_of_queryCount_eq_zero W 1 h.prep h.query_free (Ket i₀), h.produces]

/-- Every state equipped with a `HasPrepare` witness is normalized. -/
theorem HasPrepare.normalized {ψ : QState I} {i₀ : I} (h : HasPrepare ψ i₀) :
    Normalized ψ := by
  have hh := normalized_run (1 : Matrix I I ℂ) (Submonoid.one_mem _) h.prep h.unitary
    (normalized_ket i₀)
  rwa [h.produces] at hh

/-- Provides preparation of a basis state from itself using the empty circuit. -/
def hasPrepare_ket (i : I) : HasPrepare (Ket i) i where
  prep := []
  unitary := isUnitaryCircuit_nil
  query_free := rfl
  produces := rfl

/-- Extends a circuit to an additional register `J` by tensoring each local gate with its
identity matrix and retaining query steps. Its execution uses the oracle supplied on the
enlarged state space. -/
noncomputable def LiftCircuitTo (J : Type*) [Fintype J] [DecidableEq J] :
    Circuit I → Circuit (I × J)
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate U (1 : Matrix J J ℂ)) :: LiftCircuitTo J C
  | Step.query :: C => Step.query :: LiftCircuitTo J C

omit [Fintype I] [DecidableEq I] in

/-- Lifting the empty circuit to an additional register gives the empty circuit. -/
@[simp] theorem liftCircuitTo_nil (J : Type*) [Fintype J] [DecidableEq J] :
    LiftCircuitTo J ([] : Circuit I) = [] := rfl

omit [Fintype I] [DecidableEq I] in

/-- Lifting a circuit headed by a local gate tensors that gate with the identity on `J` and
recursively lifts the remaining circuit. -/
@[simp] theorem liftCircuitTo_gate (J : Type*) [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (C : Circuit I) :
    LiftCircuitTo J (Step.gate U :: C)
      = Step.gate (TensorGate U (1 : Matrix J J ℂ)) :: LiftCircuitTo J C := rfl

omit [Fintype I] [DecidableEq I] in

/-- Lifting a circuit headed by a query preserves that query and recursively lifts the remaining
circuit. -/
@[simp] theorem liftCircuitTo_query (J : Type*) [Fintype J] [DecidableEq J]
    (C : Circuit I) :
    LiftCircuitTo J (Step.query :: C) = Step.query :: LiftCircuitTo J C := rfl

omit [Fintype I] [DecidableEq I] in

/-- The general register lift `LiftCircuitTo Bool` agrees with the existing Boolean register
lift `LiftCircuit`. -/
theorem liftCircuitTo_bool (C : Circuit I) : LiftCircuitTo Bool C = LiftCircuit C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp [ih, LiftCircuit, LiftGate]

/-- Lifting a unitary circuit to an additional register preserves unitarity of its local gates. -/
theorem isUnitaryCircuit_liftCircuitTo {C : Circuit I} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (LiftCircuitTo J C) := by
  revert hC
  induction C with
  | nil => intro _; exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      intro h
      obtain ⟨hU, hC⟩ := (isUnitaryCircuit_gate U C).mp h
      rw [liftCircuitTo_gate, isUnitaryCircuit_gate]
      exact ⟨tensorGate_unitary hU (Submonoid.one_mem _), ih hC⟩
    | query =>
      intro h
      rw [liftCircuitTo_query, isUnitaryCircuit_query]
      exact ih ((isUnitaryCircuit_query C).mp h)

omit [Fintype I] [DecidableEq I] in

/-- Lifting a circuit to an additional register preserves its query count. -/
theorem queryCount_liftCircuitTo (J : Type*) [Fintype J] [DecidableEq J] (C : Circuit I) :
    QueryCount (LiftCircuitTo J C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

omit [Fintype I] [DecidableEq I] in

/-- Lifting a circuit to an additional register preserves its local gate count. -/
theorem gateCount_liftCircuitTo (J : Type*) [Fintype J] [DecidableEq J] (C : Circuit I) :
    GateCount (LiftCircuitTo J C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

omit [Fintype I] [DecidableEq I] in

/-- Lifting a circuit to an additional register preserves its total circuit size. -/
theorem size_liftCircuitTo (J : Type*) [Fintype J] [DecidableEq J] (C : Circuit I) :
    Size (LiftCircuitTo J C) = Size C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [ih]

omit [DecidableEq I] in
/-- Running a lifted circuit with oracle `W ⊗ 1` on a product input equals the original run with
`W`, tensored with the untouched second state. -/
theorem run_liftCircuitTo_liftedOracle (J : Type*) [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (χ : QState J) :
    Run (TensorGate W (1 : Matrix J J ℂ)) (LiftCircuitTo J C) (TensorState ψ χ)
      = TensorState (Run W C ψ) χ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [liftCircuitTo_gate, run_gate, applyGate_tensorGate, applyGate_one]
      exact ih _
    | query =>
      simp only [liftCircuitTo_query, run_query, applyGate_tensorGate, applyGate_one]
      exact ih _

/-- With the identity oracle, running a lifted circuit on a product state executes the original
circuit on the first factor and preserves the second. -/
theorem run_liftCircuitTo (J : Type*) [Fintype J] [DecidableEq J] (C : Circuit I)
    (ψ : QState I) (χ : QState J) :
    Run 1 (LiftCircuitTo J C) (TensorState ψ χ) = TensorState (Run 1 C ψ) χ := by
  rw [show (1 : Matrix (I × J) (I × J) ℂ)
      = TensorGate (1 : Matrix I I ℂ) (1 : Matrix J J ℂ) from tensorGate_one.symm,
    run_liftCircuitTo_liftedOracle J (1 : Matrix I I ℂ) C ψ χ]

/-- Packages positive semidefiniteness and trace one for a joint matrix, providing the
hypotheses used to obtain a density operator after tracing out its second register. -/
structure HasDiscard {D E : ℕ} (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) where

  posSemidef : ρ.PosSemidef

  trace_one : Matrix.trace ρ = 1

/-- The partial trace of a joint matrix equipped with `HasDiscard` is a density operator. This
is the reduced-state construction described in [Nielsen and Chuang,
2010][NielsenChuang2010]. -/
theorem HasDiscard.density {D E : ℕ} {ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (h : HasDiscard ρ) : IsDensityOperator (PartialTrace ρ) :=
  isDensityOperator_partialTrace h.posSemidef h.trace_one

/-- Tracing out a normalized untouched register after a lifted run with identity oracle leaves
the outer product of the original circuit output. -/
theorem discard_liftedRun {D E : ℕ} (C : Circuit (Fin D))
    (ψ : QState (Fin D)) {φ : QState (Fin E)} (hφ : Normalized φ) :
    PartialTrace (outerProduct (Run 1 (LiftCircuitTo (Fin E) C) (TensorState ψ φ)))
      = outerProduct (Run 1 C ψ) := by
  rw [run_liftCircuitTo (Fin E) C ψ φ, partialTrace_outerProduct_tensorState _ hφ]

/-- Measuring `S` in the first register after a lifted run with identity oracle has the original
output probability when the untouched second register is normalized. -/
theorem measureProb_discard_liftedRun {D E : ℕ} (C : Circuit (Fin D))
    (ψ : QState (Fin D)) {φ : QState (Fin E)} (hφ : Normalized φ) (S : Finset (Fin D)) :
    MeasureProb (Run 1 (LiftCircuitTo (Fin E) C) (TensorState ψ φ)) (S ×ˢ Finset.univ)
      = MeasureProb (Run 1 C ψ) S := by
  rw [run_liftCircuitTo (Fin E) C ψ φ, measureProb_tensorState_left hφ]

/-- A lifted unitary circuit with identity oracle, applied to normalized product inputs, yields
an output outer product equipped with `HasDiscard`. -/
theorem hasDiscard_liftedRun {D E : ℕ} (C : Circuit (Fin D)) (hC : IsUnitaryCircuit C)
    {ψ : QState (Fin D)} (hψ : Normalized ψ)
    {φ : QState (Fin E)} (hφ : Normalized φ) :
    HasDiscard (outerProduct (Run 1 (LiftCircuitTo (Fin E) C) (TensorState ψ φ))) where
  posSemidef := outerProduct_posSemidef _
  trace_one := by
    have hjoint : Normalized (Run 1 (LiftCircuitTo (Fin E) C) (TensorState ψ φ)) := by
      rw [run_liftCircuitTo (Fin E) C ψ φ]
      exact normalized_tensorState
        (normalized_run (1 : Matrix (Fin D) (Fin D) ℂ) (Submonoid.one_mem _) C hC hψ) hφ
    rw [trace_outerProduct]
    exact_mod_cast hjoint

/-- States that a matrix on `I × J` has the form `U ⊗ 1`, so it acts only on the left register.
This predicate does not impose unitarity on `U`. -/
def ActsOnLeft (W : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ U : Matrix I I ℂ, W = TensorGate U (1 : Matrix J J ℂ)

/-- States that a matrix on `I × J` has the form `1 ⊗ V`, so it acts only on the right register.
This predicate does not impose unitarity on `V`. -/
def ActsOnRight (W : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ V : Matrix J J ℂ, W = TensorGate (1 : Matrix I I ℂ) V

/-- Tensoring a unitary left-register matrix with the identity on the right gives a unitary
joint matrix. -/
theorem actsOnLeft_mem_unitaryGroup {U : Matrix I I ℂ} (hU : HasUnitary U) :
    TensorGate U (1 : Matrix J J ℂ) ∈ Matrix.unitaryGroup (I × J) ℂ :=
  tensorGate_unitary hU (Submonoid.one_mem _)

/-- For a nonempty right register, `U ⊗ 1` is unitary exactly when `U` is unitary. -/
theorem tensorGate_one_left_mem_unitaryGroup_iff [Nonempty J] {U : Matrix I I ℂ} :
    TensorGate U (1 : Matrix J J ℂ) ∈ Matrix.unitaryGroup (I × J) ℂ
      ↔ HasUnitary U := by
  constructor
  · intro h
    have hh := (Matrix.mem_unitaryGroup_iff).mp h
    rw [Matrix.star_eq_conjTranspose] at hh
    have h' : TensorGate (U * Uᴴ) (1 : Matrix J J ℂ) = 1 := by
      have e1 : TensorGate U (1 : Matrix J J ℂ) * (TensorGate U (1 : Matrix J J ℂ))ᴴ
          = TensorGate (U * Uᴴ) (1 : Matrix J J ℂ) := by
        rw [tensorGate_conjTranspose, Matrix.conjTranspose_one, tensorGate_mul,
          Matrix.one_mul]
      rw [← e1]
      exact hh
    show U ∈ Matrix.unitaryGroup I ℂ
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i k
    obtain ⟨j⟩ := ‹Nonempty J›
    have e := congrFun (congrFun h' (i, j)) (k, j)
    simp only [TensorGate, Matrix.kronecker_apply, Matrix.one_apply] at e ⊢
    simp only [Prod.mk.injEq] at e ⊢
    simp at e ⊢
    exact e
  · exact actsOnLeft_mem_unitaryGroup

/-- For a nonempty right register, a matrix acting only on the left is unitary exactly when it
can be represented as `U ⊗ 1` with unitary `U`. -/
theorem ActsOnLeft.unitary_iff [Nonempty J] {W : Matrix (I × J) (I × J) ℂ}
    (hW : ActsOnLeft W) :
    W ∈ Matrix.unitaryGroup (I × J) ℂ
      ↔ ∃ U : Matrix I I ℂ, HasUnitary U ∧ W = TensorGate U (1 : Matrix J J ℂ) := by
  obtain ⟨U, rfl⟩ := hW
  exact ⟨fun h => ⟨U, tensorGate_one_left_mem_unitaryGroup_iff.mp h, rfl⟩,
    fun ⟨_, hV, hVW⟩ => hVW ▸ actsOnLeft_mem_unitaryGroup hV⟩

/-- Matrices acting only on opposite tensor factors commute, without requiring either matrix to
be unitary. -/
theorem commute_actsOnLeft_actsOnRight {W W' : Matrix (I × J) (I × J) ℂ}
    (hW : ActsOnLeft W) (hW' : ActsOnRight W') : W * W' = W' * W := by
  obtain ⟨U, rfl⟩ := hW
  obtain ⟨V, rfl⟩ := hW'
  rw [tensorGate_mul, tensorGate_mul, Matrix.mul_one U, Matrix.one_mul V,
    Matrix.one_mul U, Matrix.mul_one V]

/-- Applying a unitary on a normalized left factor of a product state preserves every
right-register event probability. The right factor need not be normalized for this identity. -/
theorem measureProb_actsOnLeft_right {U : Matrix I I ℂ} (hU : HasUnitary U)
    {ψ : QState I} (hψ : Normalized ψ)
    (φ : QState J) (T : Finset J) :
    MeasureProb (ApplyGate (TensorGate U (1 : Matrix J J ℂ)) (TensorState ψ φ))
        (Finset.univ ×ˢ T) = MeasureProb φ T := by
  rw [applyGate_tensorGate, applyGate_one,
    measureProb_tensorState_right (normalized_applyGate hU hψ)]

omit [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] in
/-- Reassociating two successive identity-register extensions of `U` gives the single extension
`U ⊗ 1` on the combined ancillary register. -/
theorem actsOnLeft_lift (U : Matrix I I ℂ) :
    relabelGate (Equiv.prodAssoc I J K)
        (TensorGate (TensorGate U (1 : Matrix J J ℂ)) (1 : Matrix K K ℂ))
      = TensorGate U (1 : Matrix (J × K) (J × K) ℂ) := by
  rw [relabelGate_prodAssoc, tensorGate_one]

variable {F : Type*}

/-- Expands a fixed-space query upper bound into valid error bounds, unitary oracles, and the
existence of one bounded-query algorithm that succeeds for every instance. The algorithm is
chosen before the instance, as in the query model of [Beals et al., 2001][BealsEtAl2001]. -/
theorem uniform_program_quantifier_order (O : F → Matrix I I ℂ) (Acc : F → Finset I)
    (ε : ℝ) (k : ℕ) :
    FixedSpaceQueryUpperBound O Acc ε k ↔
      0 ≤ ε ∧ ε < 1 ∧ (∀ f, O f ∈ Matrix.unitaryGroup I ℂ) ∧
        ∃ A : QueryAlgorithm I, QueryCount A.circuit ≤ k ∧
          ∀ f : F, 1 - ε ≤ MeasureProb (Run (O f) A.circuit A.start) (Acc f) := by
  rw [fixedSpaceQueryUpperBound_iff_queryAlgorithm]
  constructor
  · rintro ⟨hε, hO, A, hk, hs⟩
    exact ⟨hε.1, hε.2, hO, A, hk, hs⟩
  · rintro ⟨hε1, hε2, hO, A, hk, hs⟩
    exact ⟨⟨hε1, hε2⟩, hO, A, hk, hs⟩

/-- Defines a two-instance Boolean oracle family: the identity for `false` and `PauliZ` for
`true`. -/
noncomputable def instanceOracle : Bool → Matrix Bool Bool ℂ :=
  fun b => if b then PauliZ else 1

/-- Assigns each Boolean instance the singleton acceptance set containing that same Boolean
value. -/
def instanceAcc : Bool → Finset Bool :=
  fun b => if b then {true} else {false}

/-- Each Boolean instance possesses a zero-query unitary circuit and normalized initial state
with success probability at least one when the circuit and state may be chosen separately
for that instance. -/
theorem perInstanceChoice_solves :
    ∀ b : Bool, ∃ C : Circuit Bool, ∃ ψ₀ : QState Bool, IsUnitaryCircuit C ∧ Normalized ψ₀ ∧
      QueryCount C = 0 ∧ 1 ≤ MeasureProb (Run (instanceOracle b) C ψ₀) (instanceAcc b) := by
  intro b
  refine ⟨[], if b then Ket true else Ket false, isUnitaryCircuit_nil, ?_, rfl, ?_⟩
  · cases b <;> exact normalized_ket _
  · cases b <;> simp [instanceOracle, instanceAcc, MeasureProb, bornProb_ket]

/-- No single algorithm solves both Boolean instances exactly with zero queries in the fixed
state space. A zero-query output is oracle-independent and cannot assign probability one to
both disjoint singleton acceptance sets. -/
theorem no_uniform_program : ¬ FixedSpaceQueryUpperBound instanceOracle instanceAcc 0 0 := by
  rintro ⟨hε, hO, C, ψ₀, hC, hψ₀, hcount, hsolve⟩
  have hq0 : QueryCount C = 0 := Nat.le_zero.mp hcount
  have hrun : Run (instanceOracle false) C ψ₀ = Run (instanceOracle true) C ψ₀ :=
    run_eq_of_queryCount_eq_zero _ _ C hq0 ψ₀
  have hnorm : Normalized (Run (instanceOracle false) C ψ₀) :=
    normalized_run _ (hO false) C hC hψ₀
  have h0 : (1 : ℝ) ≤ MeasureProb (Run (instanceOracle false) C ψ₀)
      ({false} : Finset Bool) := by
    simpa [instanceAcc] using hsolve false
  have h1 : (1 : ℝ) ≤ MeasureProb (Run (instanceOracle false) C ψ₀)
      ({true} : Finset Bool) := by
    have h1' := hsolve true
    rw [← hrun] at h1'
    simpa [instanceAcc] using h1'
  have hsplit : MeasureProb (Run (instanceOracle false) C ψ₀) ({false} : Finset Bool)
      + MeasureProb (Run (instanceOracle false) C ψ₀) ({true} : Finset Bool) = 1 := by
    rw [← measureProb_univ hnorm]
    unfold MeasureProb
    rw [Fintype.sum_bool]
    simp only [Finset.sum_singleton]
    ring
  linarith

end Qatlib.Concepts.QueryComplexity.DegreeMethod
