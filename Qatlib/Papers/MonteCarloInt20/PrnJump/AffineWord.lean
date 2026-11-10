/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.Recurrence
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Classical ENNReal
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Affine
open Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg

def powerPair (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) : ℕ → (ZMod (2^n))ˣ × ZMod (2^n)
  | 0 => (a,c)
  | q+1 => let p := powerPair n a c q; (p.1*p.1, (p.1:ZMod (2^n))*p.2+p.2)

theorem powerPair_apply (n : ℕ) (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n)) (q : ℕ) :
    ((powerPair n a c q).1:ZMod (2^n))*x+(powerPair n a c q).2 = lcg (a:ZMod (2^n)) c x (2^q) := by
  induction q generalizing x with
  | zero => simp [powerPair, lcg]
  | succ q ih =>
    have h := lcg_restart (a:ZMod (2^n)) c x (2^q) (2^q)
    rw [← ih x, ← ih] at h
    simp only [powerPair, Units.val_mul, pow_succ]
    rw [show 2^q*2=2^q+2^q by omega, h]
    ring

def mulControl {n k : ℕ} (q : Fin k) (a : (ZMod (2^n))ˣ) : Equiv.Perm (Reg k × ZMod (2^n)) where
  toFun p := (p.1, if p.1 q then (a:ZMod (2^n))*p.2 else p.2)
  invFun p := (p.1, if p.1 q then ((a⁻¹:(ZMod (2^n))ˣ):ZMod (2^n))*p.2 else p.2)
  left_inv p := by
    rcases p with ⟨bits,x⟩
    (try dsimp only)
    by_cases h : bits q = true <;> simp [h, ← mul_assoc, ← Units.val_mul]
  right_inv p := by
    rcases p with ⟨bits,x⟩
    (try dsimp only)
    by_cases h : bits q = true <;> simp [h, ← mul_assoc, ← Units.val_mul]

def addControl {n k : ℕ} (q : Fin k) (c : ZMod (2^n)) : Equiv.Perm (Reg k × ZMod (2^n)) where
  toFun p := (p.1, if p.1 q then p.2+c else p.2)
  invFun p := (p.1, if p.1 q then p.2-c else p.2)
  left_inv p := by rcases p with ⟨bits,x⟩; (try dsimp only); by_cases h : bits q = true <;> simp [h]
  right_inv p := by rcases p with ⟨bits,x⟩; (try dsimp only); by_cases h : bits q = true <;> simp [h]

theorem perm_basis {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (x : I) :
    permMatrix e *ᵥ Ket x = Ket (e x) := by
  ext y
  simp [permMatrix, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]

inductive JumpOp (k : ℕ) where
  | mul (q : Fin k)
  | add (q : Fin k)

noncomputable def opMatrix {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    JumpOp k → Matrix (Reg k × ZMod (2^n)) (Reg k × ZMod (2^n)) ℂ
  | .mul q => permMatrix (mulControl q (powerPair n a c q.val).1)
  | .add q => permMatrix (addControl q (powerPair n a c q.val).2)

def operations {k : ℕ} (qs : List (Fin k)) : List (JumpOp k) :=
  qs.flatMap (fun q => [.mul q, .add q])

noncomputable def program {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) : Circuit (Reg k × ZMod (2^n)) :=
  (operations qs).map (fun op => Step.gate (opMatrix a c op))

def exponent {k : ℕ} (qs : List (Fin k)) (bits : Reg k) : ℕ :=
  (qs.map (fun q => if bits q then 2^q.val else 0)).sum

theorem block_basis {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (q : Fin k) (bits : Reg k) (x : ZMod (2^n)) :
    Run 1 (program a c [q]) (Ket (bits,x)) =
      Ket (bits, if bits q then lcg (a:ZMod (2^n)) c x (2^q.val) else x) := by
  simp only [program, operations, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_nil, run_gate, run_nil, ApplyGate, opMatrix]
  rw [perm_basis, perm_basis]
  by_cases hb : bits q = true
  · simpa [mulControl, addControl, hb] using!
      congrArg (fun y : ZMod (2^n) => Ket (bits,y)) (powerPair_apply n a c x q.val)
  · simp [mulControl, addControl, hb]

theorem program_unitary {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) : IsUnitaryCircuit (program a c qs) := by
  have hop (op : JumpOp k) : opMatrix a c op ∈ Matrix.unitaryGroup (Reg k × ZMod (2^n)) ℂ := by
    cases op with
    | mul q => exact permMatrix_unitary_of_injective (mulControl q (powerPair n a c q.val).1).injective
    | add q => exact permMatrix_unitary_of_injective (addControl q (powerPair n a c q.val).2).injective
  intro U hU
  rcases List.mem_map.mp hU with ⟨op,_,he⟩
  have hmat : opMatrix a c op = U := by injection he
  rw [← hmat]
  exact hop op

theorem program_basis {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) (bits : Reg k) (x : ZMod (2^n)) :
    Run 1 (program a c qs) (Ket (bits,x)) = Ket (bits,lcg (a:ZMod (2^n)) c x (exponent qs bits)) := by
  induction qs generalizing x with
  | nil => simp [program, operations, exponent, lcg, run_nil]
  | cons q qs ih =>
    have hp : program a c (q::qs) = program a c [q] ++ program a c qs := by
      simp [program, operations]
    rw [hp, run_append, block_basis]
    cases h : bits q
    · simpa [exponent, h] using! ih x
    · rw [ih]
      simp only [exponent, List.map_cons, List.sum_cons, h, if_true, lcg_restart]

theorem exponent_all {k : ℕ} (bits : Reg k) :
    exponent (List.ofFn (fun q : Fin k => q)) bits = booleanWordLSBValue k bits := by
  simp only [exponent, List.map_ofFn, Function.comp_def, List.sum_ofFn, boolean_word_lsb_value]
  apply Finset.sum_congr rfl
  intro q _
  cases bits q <;> simp

theorem program_counts {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) : GateCount (program a c qs) = 2*qs.length ∧ QueryCount (program a c qs) = 0 := by
  induction qs with
  | nil => simp [program, operations]
  | cons q qs ih =>
    have hp : program a c (q::qs) =
        Step.gate (opMatrix a c (.mul q)) :: Step.gate (opMatrix a c (.add q)) :: program a c qs := by
      simp [program, operations]
    rw [hp]
    simp only [gateCount_gate, queryCount_gate, List.length_cons]
    rw [ih.1, ih.2]
    omega

theorem full_jump_basis {n k : ℕ} (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n)) (bits : Reg k) :
    Run 1 (program a c (List.ofFn (fun q : Fin k => q))) (Ket (bits,x)) =
      Ket (bits, lcg (a:ZMod (2^n)) c x (booleanWordLSBValue k bits)) := by
  rw [program_basis, exponent_all]

theorem strided_jump_basis (n s d : ℕ) (hd : 0<d) (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n))
    (j : Fin (2^s)) (i : Fin (2^d+1)) :
    let k := s+d+1
    let bits :=
        Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat k (strided (2^d) j i)
    Run 1 (program a c (List.ofFn (fun q : Fin k => q))) (Ket (bits,x)) =
      Ket (bits, lcg (a:ZMod (2^n)) c x (strided (2^d) j i)) := by
  (try dsimp only)
  rw [full_jump_basis, Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat_value,
    Nat.mod_eq_of_lt (strided_bit_bound s d hd j i)]

def multiplicationCount {k : ℕ} : List (JumpOp k) → ℕ
  | [] => 0
  | .mul _ :: ops => multiplicationCount ops + 1
  | .add _ :: ops => multiplicationCount ops

theorem operations_mul_count {k : ℕ} (qs : List (Fin k)) :
    multiplicationCount (operations qs) = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change multiplicationCount (operations qs)+1 = qs.length+1
    rw [ih]

noncomputable def paidProgram {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) (ψ : QState (Reg k × ZMod (2^n))) (hψ : Normalized ψ) :
    CostedLaw ((Reg k × ZMod (2^n)) × ℕ) :=
  (bornDistribution (Run 1 (program a c qs) ψ)
    ((program_unitary a c qs).normalized_run
      (show (1 : Matrix (Reg k × ZMod (2^n)) (Reg k × ZMod (2^n)) ℂ) ∈ Matrix.unitaryGroup _ ℂ by simp) hψ)).map
    (fun out => ((out, GateCount (program a c qs)), multiplicationCount (operations qs)))

theorem paidProgram_count {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n))
    (qs : List (Fin k)) (ψ : QState (Reg k × ZMod (2^n))) (hψ : Normalized ψ) :
    CostedLaw.expectedCost (paidProgram a c qs ψ hψ) = (qs.length : ℝ≥0∞) := by
  simp only [CostedLaw.expectedCost, paidProgram, CostedLaw.expectation_map]
  rw [CostedLaw.expectation_const, operations_mul_count]

end Qatlib.Papers.MonteCarloInt20.PrnJump.Affine
