/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Matrix

namespace Qatlib.Papers.NANDTreeQuery07.MainResults

def bitReal (x : Bool) : ℝ := if x then 1 else 0

@[simp] theorem bitReal_false : bitReal false = 0 := rfl

@[simp] theorem bitReal_true : bitReal true = 1 := rfl

def oracleBit (x : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  BitOracleOn (fun _ : Bool => x)

theorem oracleBit_unitary (x : Bool) :
    oracleBit x ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  bitOracleOn_unitary _

def Rmat (t : ℝ) : Matrix Bool Bool ℂ :=
  fun i j => if i = j then (Real.cos t : ℂ) else Complex.I * (Real.sin t : ℂ)

def controlledR (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q =>
    if p.2 then (if q.2 then Rmat t p.1 q.1 else 0)
    else (if q.2 then 0 else if p.1 = q.1 then 1 else 0)

def hamiltonianOracle (x : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q =>
    if p.2 = q.2 then (if p.1 = !q.1 then -((bitReal x : ℝ) : ℂ) else 0) else 0

theorem hamiltonianOracle_isHermitian (x : Bool) :
    (hamiltonianOracle x).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  funext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases x <;> cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [hamiltonianOracle, bitReal]

theorem hamiltonianOracle_sq (x : Bool) :
    hamiltonianOracle x * hamiltonianOracle x =
      (fun p q : Bool × Bool => if p = q then ((bitReal x : ℝ) : ℂ) ^ 2 else 0) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases x <;> cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [hamiltonianOracle, bitReal, Matrix.mul_apply, ← Finset.univ_product_univ,
      Finset.sum_product, Fintype.univ_bool]

theorem ApplyGate_add {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ φ : QState I) :
    ApplyGate U (ψ + φ) = ApplyGate U ψ + ApplyGate U φ := by
  simpa [ApplyGate] using Matrix.mulVec_add U ψ φ

theorem ApplyGate_smul {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  simpa [ApplyGate] using Matrix.mulVec_smul U c ψ

theorem applyGate_oracleBit_ket (x b a : Bool) :
    ApplyGate (oracleBit x) (Ket (b, a)) = Ket (b, a ^^ x) := by
  simpa [oracleBit] using
    (applyGate_bitOracleOn_ket (f := fun _ : Bool => x) b a)

theorem applyGate_controlledR_ket_false (t : ℝ) (b : Bool) :
    ApplyGate (controlledR t) (Ket (b, false)) = Ket (b, false) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  cases b <;> cases p1 <;> cases p2 <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, controlledR, Rmat, Ket]

theorem applyGate_controlledR_ket_true (t : ℝ) (b : Bool) :
    ApplyGate (controlledR t) (Ket (b, true)) =
      (Real.cos t : ℂ) • Ket (b, true) + (Complex.I * (Real.sin t : ℂ)) • Ket (!b, true) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  cases b <;> cases p1 <;> cases p2 <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, controlledR, Rmat, Ket,
      Pi.add_apply, Pi.smul_apply]

theorem two_query_realizes_hamiltonian_evolution (x : Bool) (t : ℝ) (b : Bool) :
    Run (oracleBit x) [Step.query, Step.gate (controlledR t), Step.query] (Ket (b, false)) =
      (Real.cos (bitReal x * t) : ℂ) • Ket (b, false) +
        (Complex.I * (Real.sin (bitReal x * t) : ℂ)) • Ket (!b, false) := by
  cases x
  · simp only [run_query, run_gate, run_nil]
    rw [applyGate_oracleBit_ket]
    simp only [Bool.false_xor]
    rw [applyGate_controlledR_ket_false, applyGate_oracleBit_ket]
    simp only [Bool.false_xor, bitReal_false, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.ofReal_zero, mul_zero, Complex.ofReal_one]
    simp
  · simp only [run_query, run_gate, run_nil]
    rw [applyGate_oracleBit_ket]
    simp only [Bool.false_xor]
    rw [applyGate_controlledR_ket_true]
    rw [ApplyGate_add, ApplyGate_smul, ApplyGate_smul,
      applyGate_oracleBit_ket, applyGate_oracleBit_ket]
    simp only [Bool.true_xor, Bool.not_true, bitReal_true, one_mul]

theorem two_query_ancilla_returns (x : Bool) (t : ℝ) (b b' : Bool) :
    Run (oracleBit x) [Step.query, Step.gate (controlledR t), Step.query]
      (Ket (b, false)) (b', true) = 0 := by
  rw [two_query_realizes_hamiltonian_evolution]
  simp [Pi.add_apply, Pi.smul_apply, Ket]

end Qatlib.Papers.NANDTreeQuery07.MainResults
