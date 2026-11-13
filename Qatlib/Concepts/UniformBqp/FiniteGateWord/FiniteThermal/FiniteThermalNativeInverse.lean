/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalZeroReflection

/-!
# Native thermal programs and their inverses

This module defines `ThermalNativeStep`, its lowering to finite gate codes, legality, and
reversal with native adjoints. It proves that legal native inverses implement the matrix adjoint
and undo a forward run with the same lowered gate count and zero queries.

The native cost model and explicit expansion of Toffoli steps connect these programs to
elementary circuit decompositions as in [BarencoEtAl1995]. Expanding Toffoli steps preserves
lowering, legality, and inverse semantics.

## Main statements

* `thermalNative_program_inverse_matrix`: lowering a native inverse implements the adjoint word
  matrix.
* `thermalNative_paid_inverse`: inverse execution restores every input with matching gate count.
* `thermalNative_lower_length_bound`: lowered length is at most four times the native program
  cost.
* `thermalNative_expand_inverse_run`: Toffoli expansion preserves the inverse run.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

/-- The fifteen-gate Toffoli word is legal when its two controls and target are distinct wires
of type `Fin n`. -/
private theorem tof_legal {n : ℕ} (a b t : Fin n) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalToffoliWord a.val b.val t.val)=true := by
  have hab' : a.val≠b.val := fun h => hab (Fin.ext h)
  have hat' : a.val≠t.val := fun h => hat (Fin.ext h)
  have hbt' : b.val≠t.val := fun h => hbt (Fin.ext h)
  simp [thermalToffoliWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,a.isLt,b.isLt,t.isLt,hab',hat',hbt']

/-- For three distinct wires, the matrix of the adjoint finite Toffoli word equals the matrix of
the forward word. -/
theorem thermalToffoli_adjoint_matrix {n : ℕ} (a b t : Fin n)
    (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalToffoliWord a.val b.val t.val)) =
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalToffoliWord a.val b.val t.val) := by
  let g := thermalToffoliWord a.val b.val t.val
  let f (x : Qatlib.Foundations.PureStateMath.Reg n) :=
      Function.update x t (x t ^^ (x a && x b))
  have hf (x : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n g)
      (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket (f x) := by
    rw [thermalToffoliWord_compile n a b t hab hat hbt]
    exact (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x
  have hff (x : Qatlib.Foundations.PureStateMath.Reg n) : f (f x)=x := by
    funext u
    by_cases hut : u=t
    · subst u
      simp [f,hat,hbt]
    · simp [f,Function.update_of_ne hut]
  have hrun (x : Qatlib.Foundations.PureStateMath.Reg n) : Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint g)) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n g) (Qatlib.Foundations.PureStateMath.Ket x) := by
    have hp := (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finite_gate_word_paid_adjoint_semantics n g (Qatlib.Foundations.PureStateMath.Ket (f x))
      (tof_legal a b t hab hat hbt)).2.2.1
    simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append] at hp
    change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint g))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n g) (Qatlib.Foundations.PureStateMath.Ket (f x)))=Qatlib.Foundations.PureStateMath.Ket (f x) at hp
    rw [hf,hff] at hp
    exact hp.trans (hf x).symm
  ext i j
  have hh := congrFun (hrun j) i
  simpa [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket] using hh

/-- The single-qubit diagonal matrix with entries one and `i`, representing the S gate. -/
def thermalSMatrix : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then Complex.I else 1)
/-- The single-qubit diagonal matrix with entries one and `-i`, representing the adjoint S gate. -/
def thermalSDGMatrix : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then -Complex.I else 1)

/-- The square of the T-gate matrix equals `thermalSMatrix`. -/
theorem thermalT_two : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate^2=thermalSMatrix := by
  unfold Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate Qatlib.Foundations.PureStateMath.Rz thermalSMatrix
  rw [Matrix.diagonal_pow]
  congr 1
  funext b
  cases b
  · simp
  · change Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I)^2=Complex.I
    rw [← Complex.exp_nat_mul]
    calc
      _ = Complex.exp ((Real.pi:ℂ)/2*Complex.I) := by congr 1; push_cast; ring
      _ = Complex.I := Complex.exp_pi_div_two_mul_I

/-- The square of the adjoint T-gate matrix equals `thermalSDGMatrix`. -/
theorem thermalTAdj_two : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGateAdj^2=thermalSDGMatrix := by
  unfold Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGateAdj Qatlib.Foundations.PureStateMath.Rz thermalSDGMatrix
  rw [Matrix.diagonal_pow]
  congr 1
  funext b
  cases b
  · simp
  · change Complex.exp (((-(Real.pi/4):ℝ):ℂ)*Complex.I)^2 = -Complex.I
    rw [← Complex.exp_nat_mul]
    calc
      _ = Complex.exp (-((Real.pi:ℂ)/2*Complex.I)) := by congr 1; push_cast; ring
      _ = -Complex.I := by rw [Complex.exp_neg,Complex.exp_pi_div_two_mul_I]; norm_num

/-- The native instruction type consisting of a fixed finite gate code, a Toffoli instruction,
or Z, S, and adjoint-S instructions on typed wires. -/
inductive ThermalNativeStep (n : ℕ) where
  | fixed : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode → ThermalNativeStep n
  | ccx : Fin n → Fin n → Fin n → ThermalNativeStep n
  | z : Fin n → ThermalNativeStep n
  | s : Fin n → ThermalNativeStep n
  | sdg : Fin n → ThermalNativeStep n
  deriving Repr

/-- Lowers a native instruction to finite gate codes: fixed codes are singletons, Toffoli and Z
use their finite words, and S and adjoint S use two T or adjoint-T codes. -/
def thermalNativeLower {n : ℕ} : ThermalNativeStep n → List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode
  | .fixed g => [g]
  | .ccx a b t => thermalToffoliWord a.val b.val t.val
  | .z w => thermalZWord w.val
  | .s w => [.t w.val,.t w.val]
  | .sdg w => [.tdg w.val,.tdg w.val]

/-- The native adjoint operation, taking code adjoints, fixing Toffoli and Z, and interchanging
S with adjoint S. -/
def thermalNativeAdj {n : ℕ} : ThermalNativeStep n → ThermalNativeStep n
  | .fixed g => .fixed (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeAdjoint g)
  | .ccx a b t => .ccx a b t
  | .z w => .z w
  | .s w => .sdg w
  | .sdg w => .s w

/-- The native legality predicate: fixed codes must be legal, Toffoli wires must be pairwise
distinct, and Z, S, and adjoint S are always legal on typed wires. -/
def thermalNativeLegal {n : ℕ} : ThermalNativeStep n → Prop
  | .fixed g => Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal n g=true
  | .ccx a b t => a≠b ∧ a≠t ∧ b≠t
  | .z _ | .s _ | .sdg _ => True

/-- For a legal native instruction, lowering its native adjoint gives the same matrix as taking
the finite-word adjoint of its lowering. -/
theorem thermalNative_step_inverse_matrix {n : ℕ} (g : ThermalNativeStep n) (hg : thermalNativeLegal g) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeLower (thermalNativeAdj g))=
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalNativeLower g)) := by
  cases g with
  | fixed g => rfl
  | ccx a b t => exact (thermalToffoli_adjoint_matrix a b t hg.1 hg.2.1 hg.2.2).symm
  | z w => exact (thermalZWord_inverse_transport w).1.symm
  | s w => rfl
  | sdg w => rfl

/-- The matrix of a concatenated finite word `gs ++ hs` is the matrix of `hs` multiplied by the
matrix of `gs`. -/
theorem thermalWordMatrix_append (n : ℕ) (gs hs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (gs++hs)=Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n hs*Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n gs := by
  unfold Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix
  rw [List.foldl_append,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_fold_acc]
  rfl

/-- Lowers a native program by concatenating the lowered words of all its instructions. -/
def thermalNativeProgram {n : ℕ} (gs : List (ThermalNativeStep n)) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  gs.flatMap thermalNativeLower

/-- The native program obtained by reversing the instruction list and taking each native
adjoint. -/
def thermalNativeInverse {n : ℕ} (gs : List (ThermalNativeStep n)) : List (ThermalNativeStep n) :=
  gs.reverse.map thermalNativeAdj

/-- For a program of legal native instructions, lowering its native inverse gives the same
matrix as the finite-word adjoint of its lowering. -/
theorem thermalNative_program_inverse_matrix {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs))=
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalNativeProgram gs)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hh := thermalNative_step_inverse_matrix g (hg g (by simp))
    have ht := ih (by intro a ha;exact hg a (by simp [ha]))
    have hl : thermalNativeProgram (thermalNativeInverse (g::gs))=
        thermalNativeProgram (thermalNativeInverse gs)++thermalNativeLower (thermalNativeAdj g) := by
      simp [thermalNativeProgram,thermalNativeInverse,List.flatMap_append]
    have hr : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalNativeProgram (g::gs))=
        Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalNativeProgram gs)++Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalNativeLower g) := by
      simp [thermalNativeProgram,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint,List.reverse_append,List.map_append]
    rw [hl,hr,thermalWordMatrix_append,thermalWordMatrix_append,hh,ht]

/-- The lowering of a legal native instruction is a legal finite word. -/
theorem thermalNative_step_lower_legal {n : ℕ} (g : ThermalNativeStep n) (hg : thermalNativeLegal g) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalNativeLower g)=true := by
  cases g with
  | fixed g => simpa [thermalNativeLower,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal] using! hg
  | ccx a b t => exact tof_legal a b t hg.1 hg.2.1 hg.2.2
  | z w => simp [thermalNativeLower,thermalZWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,w.isLt]
  | s w => simp [thermalNativeLower,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,w.isLt]
  | sdg w => simp [thermalNativeLower,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,w.isLt]

/-- The native adjoint of a legal native instruction is legal. -/
theorem thermalNative_adj_legal {n : ℕ} (g : ThermalNativeStep n) (hg : thermalNativeLegal g) :
    thermalNativeLegal (thermalNativeAdj g) := by
  cases g with
  | fixed g => exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeAdjoint_spec n g hg).1
  | ccx a b t => exact hg
  | z w => trivial
  | s w => trivial
  | sdg w => trivial

/-- A program whose native instructions are all legal lowers to a legal finite word. -/
theorem thermalNative_program_legal {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalNativeProgram gs)=true := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hh := thermalNative_step_lower_legal g (hg g (by simp))
    have ht := ih (by intro a ha;exact hg a (by simp [ha]))
    simpa only [thermalNativeProgram,List.flatMap_cons,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true]
      using And.intro hh ht

/-- Every instruction in the native inverse of a legal native program is legal. -/
theorem thermalNative_inverse_legal {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) :
    ∀ g∈thermalNativeInverse gs,thermalNativeLegal g := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact thermalNative_adj_legal b (hg b (List.mem_reverse.mp hb))

/-- Taking the native adjoint of an instruction preserves the length of its lowering. -/
theorem thermalNative_step_inverse_length {n : ℕ} (g : ThermalNativeStep n) :
    (thermalNativeLower (thermalNativeAdj g)).length=(thermalNativeLower g).length := by
  cases g <;> rfl

/-- A native program and its native inverse have lowered words of equal length. -/
theorem thermalNative_program_inverse_length {n : ℕ} (gs : List (ThermalNativeStep n)) :
    (thermalNativeProgram (thermalNativeInverse gs)).length=(thermalNativeProgram gs).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hl : thermalNativeProgram (thermalNativeInverse (g::gs))=
        thermalNativeProgram (thermalNativeInverse gs)++thermalNativeLower (thermalNativeAdj g) := by
      simp [thermalNativeProgram,thermalNativeInverse,List.flatMap_append]
    rw [hl,List.length_append,thermalNative_step_inverse_length,ih]
    simp [thermalNativeProgram,Nat.add_comm]

/-- The native instruction cost, equal to fifteen for Toffoli and one for every other
instruction. -/
def thermalNativeGateCost {n : ℕ} : ThermalNativeStep n → ℕ
  | .ccx _ _ _ => 15
  | _ => 1

/-- The sum of `thermalNativeGateCost` over a native program. -/
def thermalNativeProgramCost {n : ℕ} (gs : List (ThermalNativeStep n)) : ℕ :=
  (gs.map thermalNativeGateCost).sum

/-- The length of the lowered native program is at most four times `thermalNativeProgramCost`. -/
theorem thermalNative_lower_length_bound {n : ℕ} (gs : List (ThermalNativeStep n)) :
    (thermalNativeProgram gs).length ≤ 4*thermalNativeProgramCost gs := by
  have hs (g : ThermalNativeStep n) : (thermalNativeLower g).length ≤ 4*thermalNativeGateCost g := by
    cases g <;> simp [thermalNativeLower,thermalNativeGateCost,thermalToffoliWord,thermalZWord]
  induction gs with
  | nil => simp [thermalNativeProgram,thermalNativeProgramCost]
  | cons g gs ih =>
    have hh := hs g
    simp only [thermalNativeProgram,List.flatMap_cons,List.length_append]
    change (thermalNativeLower g).length+(thermalNativeProgram gs).length ≤ _
    simp only [thermalNativeProgramCost,List.map_cons,List.sum_cons]
    change (thermalNativeLower g).length+(thermalNativeProgram gs).length ≤
      4*(thermalNativeGateCost g+thermalNativeProgramCost gs)
    omega

/-- For a legal native program, running its lowered inverse after its lowering restores any
input state. The lowered inverse has the same gate count as the forward lowering and has
zero queries. -/
theorem thermalNative_paid_inverse {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram (thermalNativeInverse gs)))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram gs)) psi)=psi ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram (thermalNativeInverse gs)))=
      Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram gs)) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram (thermalNativeInverse gs)))=0 := by
  refine ⟨?_,?_,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1⟩
  · have hp := (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finite_gate_word_paid_adjoint_semantics n (thermalNativeProgram gs) psi
      (thermalNative_program_legal gs hg)).2.2.1
    simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append] at hp
    change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalNativeProgram gs)))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram gs)) psi)=psi at hp
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hp ⊢
    rw [thermalNative_program_inverse_matrix gs hg]
    exact hp
  · rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2,
      thermalNative_program_inverse_length]

/-- Expands a native Toffoli instruction into its finite codes wrapped as fixed native
instructions and leaves every other instruction as a singleton. -/
def thermalNativeExpandStep {n : ℕ} : ThermalNativeStep n → List (ThermalNativeStep n)
  | .ccx a b t => (thermalToffoliWord a.val b.val t.val).map .fixed
  | g => [g]

/-- Expands every native Toffoli instruction in a program by concatenating the lists from
`thermalNativeExpandStep`. -/
def thermalNativeExpandCCX {n : ℕ} (gs : List (ThermalNativeStep n)) : List (ThermalNativeStep n) :=
  gs.flatMap thermalNativeExpandStep

/-- Wrapping each finite gate code as a fixed native instruction and then lowering recovers the
original code list. -/
private theorem native_program_fixed {n : ℕ} (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) :
    thermalNativeProgram (gs.map (ThermalNativeStep.fixed (n:=n)))=gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [thermalNativeProgram,thermalNativeLower] using congrArg (List.cons g) ih

/-- Expanding native Toffoli instructions leaves the lowered finite program unchanged. -/
theorem thermalNative_expand_program {n : ℕ} (gs : List (ThermalNativeStep n)) :
    thermalNativeProgram (thermalNativeExpandCCX gs)=thermalNativeProgram gs := by
  have hh (g : ThermalNativeStep n) :
      thermalNativeProgram (thermalNativeExpandStep g)=thermalNativeLower g := by
    cases g with
    | ccx a b t => exact native_program_fixed _
    | fixed g => rfl
    | z w => rfl
    | s w => rfl
    | sdg w => rfl
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change thermalNativeProgram (thermalNativeExpandStep g++thermalNativeExpandCCX gs)=_
    simp only [thermalNativeProgram,List.flatMap_append]
    change thermalNativeProgram (thermalNativeExpandStep g)++thermalNativeProgram
        (thermalNativeExpandCCX gs)=_
    rw [hh,ih]
    rfl

/-- Expanding a legal native program into fixed Toffoli decompositions preserves legality of
every instruction. -/
theorem thermalNative_expand_legal {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) :
    ∀ g∈thermalNativeExpandCCX gs,thermalNativeLegal g := by
  intro g hmem
  obtain ⟨a,ha,hgmem⟩ := List.mem_flatMap.mp hmem
  have hlegal := hg a ha
  cases a with
  | ccx a b t =>
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hgmem
    have hl := tof_legal a b t hlegal.1 hlegal.2.1 hlegal.2.2
    exact (List.all_eq_true.mp hl) c hc
  | fixed a =>
    simp only [thermalNativeExpandStep,List.mem_singleton] at hgmem
    subst g
    exact hlegal
  | z w =>
    simp only [thermalNativeExpandStep,List.mem_singleton] at hgmem
    subst g
    exact hlegal
  | s w =>
    simp only [thermalNativeExpandStep,List.mem_singleton] at hgmem
    subst g
    exact hlegal
  | sdg w =>
    simp only [thermalNativeExpandStep,List.mem_singleton] at hgmem
    subst g
    exact hlegal

/-- For a legal native program, taking the native inverse after Toffoli expansion gives the same
lowered matrix as taking the native inverse before expansion. -/
theorem thermalNative_expand_inverse_matrix {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse (thermalNativeExpandCCX gs)))=
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeProgram (thermalNativeInverse gs)) := by
  rw [thermalNative_program_inverse_matrix _ (thermalNative_expand_legal gs hg),
    thermalNative_program_inverse_matrix gs hg,thermalNative_expand_program]

/-- For a legal native program, Toffoli expansion before taking the native inverse preserves the
lowered inverse action on every input state. -/
theorem thermalNative_expand_inverse_run {n : ℕ} (gs : List (ThermalNativeStep n))
    (hg : ∀ g∈gs,thermalNativeLegal g) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram (thermalNativeInverse (thermalNativeExpandCCX gs)))) psi =
      Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeProgram (thermalNativeInverse gs))) psi := by
  simp only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,thermalNative_expand_inverse_matrix gs hg]

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
