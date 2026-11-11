/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# A Two Query Hamiltonian Simulation Block

This module gives an explicit Boolean basis calculation for the two query simulation
construction in [ChildsEtAl2009Formula]. `oracleBit` flips an ancillary bit according to the
input, `controlledR` applies a rotation on the true ancilla sector, and `hamiltonianOracle`
records the associated negative bit flip Hamiltonian.

## Main statements

* `oracleBit_unitary` proves unitarity of the bit oracle, and `hamiltonianOracle_isHermitian`
  proves Hermiticity of the Hamiltonian.
* `hamiltonianOracle_sq` computes the square of the Hamiltonian as a scalar diagonal matrix.
* `two_query_realizes_hamiltonian_evolution` gives the cosine and sine amplitudes of the query,
  rotation, query block on a basis state with a false ancilla.
* `two_query_ancilla_returns` shows that every amplitude in the true ancilla sector vanishes
  after this block.

## References

* [Childs et al., 2009][ChildsEtAl2009Formula]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open scoped Matrix

namespace Qatlib.Papers.NANDTreeQuery07.MainResults

/-- The real encoding of a Boolean, equal to zero for `false` and one for `true`. -/
def bitReal (x : Bool) : ℝ := if x then 1 else 0

/-- The real encoding of `false` is zero. -/
@[simp] theorem bitReal_false : bitReal false = 0 := rfl

/-- The real encoding of `true` is one. -/
@[simp] theorem bitReal_true : bitReal true = 1 := rfl

/-- The two Boolean register bit oracle for the constant input `x`, which preserves the first
register and XORs `x` into the second. -/
def oracleBit (x : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  BitOracleOn (fun _ : Bool => x)

/-- The constant input bit oracle `oracleBit x` is a unitary matrix. This is an oracle component
associated with the two query simulation in [ChildsEtAl2009Formula]. -/
theorem oracleBit_unitary (x : Bool) :
    oracleBit x ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  bitOracleOn_unitary _

/-- The Boolean indexed matrix with diagonal entries `cos t` and off diagonal entries `i * sin
t`. -/
def Rmat (t : ℝ) : Matrix Bool Bool ℂ :=
  fun i j => if i = j then (Real.cos t : ℂ) else Complex.I * (Real.sin t : ℂ)

/-- The matrix that acts as `Rmat t` on the first Boolean register when the second is true, and
as the identity when it is false. -/
def controlledR (t : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q =>
    if p.2 then (if q.2 then Rmat t p.1 q.1 else 0)
    else (if q.2 then 0 else if p.1 = q.1 then 1 else 0)

/-- The matrix that flips the first Boolean register with coefficient `-bitReal x` while
preserving the second register. -/
def hamiltonianOracle (x : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q =>
    if p.2 = q.2 then (if p.1 = !q.1 then -((bitReal x : ℝ) : ℂ) else 0) else 0

/-- The Hamiltonian oracle matrix is Hermitian for either Boolean input. This is a matrix
component associated with the two query simulation in [ChildsEtAl2009Formula]. -/
theorem hamiltonianOracle_isHermitian (x : Bool) :
    (hamiltonianOracle x).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  funext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases x <;> cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [hamiltonianOracle, bitReal]

/-- The square of the Hamiltonian oracle is diagonal with every diagonal entry equal to
`(bitReal x)^2`, viewed as a complex number. This is a matrix identity associated with the
two query simulation in [ChildsEtAl2009Formula]. -/
theorem hamiltonianOracle_sq (x : Bool) :
    hamiltonianOracle x * hamiltonianOracle x =
      (fun p q : Bool × Bool => if p = q then ((bitReal x : ℝ) : ℂ) ^ 2 else 0) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases x <;> cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [hamiltonianOracle, bitReal, Matrix.mul_apply, ← Finset.univ_product_univ,
      Finset.sum_product, Fintype.univ_bool]

/-- Applying a matrix gate distributes over addition of quantum state vectors. -/
theorem ApplyGate_add {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ φ : QState I) :
    ApplyGate U (ψ + φ) = ApplyGate U ψ + ApplyGate U φ := by
  simpa [ApplyGate] using Matrix.mulVec_add U ψ φ

/-- Applying a matrix gate commutes with multiplication of a quantum state vector by a complex
scalar. -/
theorem ApplyGate_smul {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  simpa [ApplyGate] using Matrix.mulVec_smul U c ψ

/-- On a basis state `(b, a)`, the bit oracle produces the basis state `(b, a ^^ x)`. This is a
basis state identity associated with the two query simulation in [ChildsEtAl2009Formula]. -/
theorem applyGate_oracleBit_ket (x b a : Bool) :
    ApplyGate (oracleBit x) (Ket (b, a)) = Ket (b, a ^^ x) := by
  simpa [oracleBit] using
    (applyGate_bitOracleOn_ket (f := fun _ : Bool => x) b a)

/-- The controlled rotation fixes every basis state whose second register is false. -/
theorem applyGate_controlledR_ket_false (t : ℝ) (b : Bool) :
    ApplyGate (controlledR t) (Ket (b, false)) = Ket (b, false) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  cases b <;> cases p1 <;> cases p2 <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, controlledR, Rmat, Ket]

/-- On a basis state `(b, true)`, the controlled rotation gives the superposition with
coefficient `cos t` at `(b, true)` and `i * sin t` at `(!b, true)`. This is a basis state
component associated with the two query simulation in [ChildsEtAl2009Formula]. -/
theorem applyGate_controlledR_ket_true (t : ℝ) (b : Bool) :
    ApplyGate (controlledR t) (Ket (b, true)) =
      (Real.cos t : ℂ) • Ket (b, true) + (Complex.I * (Real.sin t : ℂ)) • Ket (!b, true) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  cases b <;> cases p1 <;> cases p2 <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, controlledR, Rmat, Ket,
      Pi.add_apply, Pi.smul_apply]

/-- Starting from `(b, false)`, the query, controlled rotation, query circuit gives coefficients
`cos (bitReal x * t)` at `(b, false)` and `i * sin (bitReal x * t)` at `(!b, false)`. This
is the explicit basis state simulation associated with the two query construction used in
the query bound of [ChildsEtAl2009Formula]. -/
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

/-- After the two query simulation block starts in `(b, false)`, the amplitude at every basis
state `(b', true)` is zero. This is the ancilla return component associated with the two
query simulation in [ChildsEtAl2009Formula]. -/
theorem two_query_ancilla_returns (x : Bool) (t : ℝ) (b b' : Bool) :
    Run (oracleBit x) [Step.query, Step.gate (controlledR t), Step.query]
      (Ket (b, false)) (b', true) = 0 := by
  rw [two_query_realizes_hamiltonian_evolution]
  simp [Pi.add_apply, Pi.smul_apply, Ket]

end Qatlib.Papers.NANDTreeQuery07.MainResults
