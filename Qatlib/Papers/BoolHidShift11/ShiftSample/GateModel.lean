/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel.SourceBHSP

@[expose] public section


/-! # The actual two-oracle sampling word of Figure 1

All gates act on the answer bit together with the input register. Only XOR
oracle constructors have query cost. The Hadamard and phase gates are fixed,
independent of either unknown truth table.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.ShiftSample.GateModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open scoped BigOperators

/-- Flip the answer bit according to a Boolean oracle and retain the input. -/
def oracleMap {n : ℕ} (f : Reg n → Bool) (p : Bool × Reg n) : Bool × Reg n :=
  (Bool.xor p.1 (f p.2),p.2)

/-- Standard XOR queries are involutions, without any promise on the function. -/
theorem oracleInv {n : ℕ} (f : Reg n → Bool) : Function.Involutive (oracleMap f) := by
  rintro ⟨b,x⟩
  cases b <;> cases h : f x <;> simp [oracleMap,h]

/-- The standard answer-bit XOR oracle as an actual unitary matrix. -/
def oracleGate {n : ℕ} (f : Reg n → Bool) : Matrix (Bool × Reg n) (Bool × Reg n) ℂ :=
  permMatrix (oracleMap f)

/-- The actual oracle matrix is unitary. -/
theorem oracleUnit {n : ℕ} (f : Reg n → Bool) :
    oracleGate f ∈ Matrix.unitaryGroup (Bool × Reg n) ℂ :=
  permMatrix_unitary (oracleInv f)

/-- Oracle action on arbitrary, possibly entangled, input amplitudes. -/
theorem oracleApply {n : ℕ} (f : Reg n → Bool) (ψ : QState (Bool × Reg n))
    (b : Bool) (x : Reg n) : ApplyGate (oracleGate f) ψ (b,x) = ψ (Bool.xor b (f x),x) :=
  applyGate_permMatrix (oracleInv f) ψ (b,x)

/-- A sampling gate is fixed Hadamard, fixed answer phase, or one XOR query. -/
inductive Gate (n : ℕ) where
  | had
  | phase
  | query (f : Reg n → Bool)

/-- Concrete matrix semantics for each allowed sampling gate. -/
def matrix {n : ℕ} : Gate n → Matrix (Bool × Reg n) (Bool × Reg n) ℂ
  | .had => TensorGate 1 (HadamardN n)
  | .phase => TensorGate PauliZ 1
  | .query f => oracleGate f

/-- Every constructor denotes an actual unitary on the same joint register. -/
theorem gateUnit {n : ℕ} (g : Gate n) : matrix g ∈ Matrix.unitaryGroup (Bool × Reg n) ℂ := by
  cases g with
  | had => exact tensorGate_unitary (Submonoid.one_mem _) (hadamardN_unitary n)
  | phase => exact tensorGate_unitary pauliZ_unitary (Submonoid.one_mem _)
  | query f => exact oracleUnit f

/-- Evaluate a gate word in order by actual matrix action. -/
def eval {n : ℕ} (gs : List (Gate n)) (ψ : QState (Bool × Reg n)) : QState (Bool × Reg n) :=
  gs.foldl (fun v g => ApplyGate (matrix g) v) ψ

/-- The cost of a word is its literal number of oracle constructors. -/
def queryCount {n : ℕ} (gs : List (Gate n)) : ℕ :=
  (gs.filter (fun g => match g with | .query _ => true | _ => false)).length

/-- The actual sampling word uses the two supplied XOR oracles exactly once. -/
def word {n : ℕ} (f g : Reg n → Bool) : List (Gate n) :=
  [.had,.query f,.phase,.query g,.had]

/-- Figure 1 costs exactly two oracle calls, with no truth-table-dependent free gate. -/
theorem twoQueries {n : ℕ} (f g : Reg n → Bool) : queryCount (word f g) = 2 := by
  rfl

/-- Matrix evaluation of any word preserves normalization. -/
theorem evalNorm {n : ℕ} (gs : List (Gate n)) (ψ : QState (Bool × Reg n))
    (hψ : Normalized ψ) : Normalized (eval gs ψ) := by
  induction gs generalizing ψ with
  | nil => exact hψ
  | cons g gs ih => exact ih _ (normalized_applyGate (gateUnit g) hψ)

/-- The output state of Figure 1 starts with a zero answer and zero input register. -/
def output {n : ℕ} (f g : Reg n → Bool) : QState (Bool × Reg n) :=
  eval (word f g) (Ket (false,ZeroStr n))

/-- The sampling circuit is normalized for every pair of Boolean functions. -/
theorem outputNorm {n : ℕ} (f g : Reg n → Bool) : Normalized (output f g) :=
  evalNorm _ _ (normalized_ket _)

/-- The input-register Hadamard acts on each answer-bit slice of any entangled state. -/
theorem hadApply {n : ℕ} (ψ : QState (Bool × Reg n)) (b : Bool) (u : Reg n) :
    ApplyGate (matrix (.had : Gate n)) ψ (b,u) =
      ∑ x : Reg n, HadamardN n u x * ψ (b,x) := by
  simp [matrix,ApplyGate,TensorGate,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.one_apply]

/-- The answer-register phase gate multiplies each slice by its actual sign. -/
theorem phaseApply {n : ℕ} (ψ : QState (Bool × Reg n)) (b : Bool) (x : Reg n) :
    ApplyGate (matrix (.phase : Gate n)) ψ (b,x) =
      (if b then (-1:ℂ) else 1) * ψ (b,x) := by
  cases b <;> simp [matrix,ApplyGate,TensorGate,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Matrix.one_apply,PauliZ]

end Qatlib.Papers.BoolHidShift11.ShiftSample.GateModel
