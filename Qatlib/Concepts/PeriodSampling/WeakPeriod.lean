/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.CipherCircuits.CipherOracle

/-!
# Fourier support from a weak XOR period

This module constructs a Hadamard-query-Hadamard circuit for a Boolean-register function and
derives its output amplitudes using binary characters. If XOR translation by `s` preserves the
function, every Fourier label with character value minus one on `s` has zero amplitude, the
support principle underlying period sampling described in [NielsenChuang2010] and weak-period
sampling in [SantoliSchaffner2017].

The argument requires only translation invariance, with no additional condition on collisions of
function values. It proves normalization, one-query resource counts, and zero probability for
the entire nonorthogonal event.

## Main statements

* `output_amplitude`: the character-sum formula for the circuit output.
* `output_zero_of_nonorthogonal`: vanishing amplitudes for labels nonorthogonal to a period.
* `nonorthogonal_event_zero`: zero total measurement probability for those labels.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Santoli and Schaffner, 2017][SantoliSchaffner2017]
-/

namespace Qatlib.Concepts.PeriodSampling.WeakPeriod
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
variable {n m : ℕ}

/-- The circuit space consisting of an `n`-bit input register, an `m`-bit output register, and a
Boolean flag. -/
abbrev Space (n m : ℕ) := Qatlib.Concepts.CipherCircuits.CipherOracle.Whole (Reg n) (Fin m)

/-- Bitwise XOR translation of the register `x` by `s`. -/
def shift (x s : Reg n) : Reg n := fun i => x i ^^ s i

/-- Applying XOR translation by `s` twice restores the original register. -/
theorem shift_twice (x s : Reg n) : shift (shift x s) s = x := by
  funext i; simp [shift]

/-- The register permutation given by XOR translation by `s`, with itself as inverse. -/
def shiftEquiv (s : Reg n) : Equiv.Perm (Reg n) where
  toFun := fun x => shift x s
  invFun := fun x => shift x s
  left_inv := fun x => shift_twice x s
  right_inv := fun x => shift_twice x s

/-- The binary character given by the product of minus-one factors at coordinates where both
registers are true. -/
def character (y x : Reg n) : ℂ := ∏ i, if y i && x i then -1 else 1

/-- A binary character evaluated on an XOR translate is the product of its values on the
original register and the translation. -/
theorem character_shift (y x s : Reg n) :
    character y (shift x s) = character y x * character y s := by
  rw [character, character, character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hy : y i <;> cases hx : x i <;> cases hs : s i <;> simp [shift, hx, hs]

/-- The complex normalization factor `(1 / √2) ^ n` for the `n`-qubit Hadamard transform. -/
def scale (n : ℕ) : ℂ := ((Real.sqrt 2 : ℂ)⁻¹)^n

/-- Each entry of `HadamardN n` is `scale n` times the corresponding binary character. -/
theorem hadamard_entry (y x : Reg n) :
    HadamardN n y x = scale n * character y x := by
  exact hadamardN_apply y x

/-- The Hadamard transform on the input register tensored with identity on the output register
and flag. -/
def inputGate (n m : ℕ) : Matrix (Space n m) (Space n m) ℂ :=
  TensorGate (HadamardN n) (1 : Matrix (Reg m × Bool) (Reg m × Bool) ℂ)

/-- The permutation-matrix oracle computing `f` in the cipher-oracle workspace. -/
def query (f : Reg n → Reg m) : Matrix (Space n m) (Space n m) ℂ :=
  (Qatlib.Concepts.CipherCircuits.CipherOracle.computePerm f).permMatrix ℂ

/-- The circuit applying an input Hadamard gate, one oracle query, and a second input Hadamard
gate. -/
def word (n m : ℕ) : Circuit (Space n m) :=
  [.gate (inputGate n m), .query, .gate (inputGate n m)]

/-- The basis state with both registers zero and the flag false. -/
def initial (n m : ℕ) : QState (Space n m) := Ket (ZeroStr n, ZeroStr m, false)

/-- The result of running the Hadamard-query-Hadamard circuit with the function oracle on the
zero initial state. -/
def output (f : Reg n → Reg m) : QState (Space n m) := Run (query f) (word n m) (initial n m)

/-- The Hadamard-query-Hadamard word is a unitary circuit. -/
theorem word_unitary (n m : ℕ) : IsUnitaryCircuit (word n m) := by
  have h : inputGate n m ∈ Matrix.unitaryGroup (Space n m) ℂ :=
    tensorGate_unitary (hadamardN_unitary n) (Submonoid.one_mem _)
  simp [word, h]

/-- The output state of the function-query circuit is normalized. See [SantoliSchaffner2017]. -/
theorem output_normalized (f : Reg n → Reg m) : Normalized (output f) := by
  exact normalized_run (query f) (Qatlib.Concepts.CipherCircuits.CipherOracle.permutation_unitary _) (word n m)
    (word_unitary n m) (normalized_ket _)

/-- The function-query circuit uses one oracle query and two gates. See [SantoliSchaffner2017]. -/
theorem word_resources (n m : ℕ) : QueryCount (word n m) = 1 ∧ GateCount (word n m) = 2 := by
  simp [word, QueryCount, GateCount]

/-- The input gate applies the Hadamard matrix on each fixed output-register and flag fiber. -/
theorem inputGate_action (ψ : QState (Space n m)) (y : Reg n) (z : Reg m × Bool) :
    (inputGate n m *ᵥ ψ) (y,z) = ∑ x : Reg n, HadamardN n y x * ψ (x,z) := by
  simp [inputGate, TensorGate, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

/-- The first Hadamard gate gives amplitude `scale n` exactly on states with zero output
register and false flag. -/
theorem first_gate (x : Reg n) (z : Reg m) (b : Bool) :
    (inputGate n m *ᵥ initial n m) (x,z,b) =
      scale n * (if z = ZeroStr m ∧ b = false then 1 else 0) := by
  rw [inputGate_action]
  by_cases hz : z = ZeroStr m <;> by_cases hb : b = false <;>
    simp [initial, Ket, hz, hb, hadamardN_apply_zero_right, scale]

/-- After the first gate and oracle query, the amplitude is `scale n` exactly when the output
register equals `f x` and the flag is false. -/
theorem after_query (f : Reg n → Reg m) (x : Reg n) (z : Reg m) (b : Bool) :
    (query f *ᵥ (inputGate n m *ᵥ initial n m)) (x,z,b) =
      scale n * (if z = f x ∧ b = false then 1 else 0) := by
  rw [query, Matrix.permMatrix_mulVec]
  change (inputGate n m *ᵥ initial n m) (x,
      Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor z (f x), b) = _
  rw [first_gate]
  have hz : Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor z (f x) = ZeroStr m ↔ z = f x := by
    constructor
    · intro h
      have hh := congrArg (fun w => Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor w (f x)) h
      have hzero : Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor (ZeroStr m) (f x) = f x := by
        funext i
        simp [Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor, ZeroStr]
      simpa only [Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor_twice, hzero] using hh
    · rintro rfl
      funext i; simp [Qatlib.Concepts.CipherCircuits.CipherOracle.bankXor, ZeroStr]
  simp only [hz]

/-- The output amplitude is `scale n ^ 2` times the binary-character sum over inputs whose
function value and flag match the output. -/
theorem output_amplitude (f : Reg n → Reg m) (y : Reg n) (z : Reg m) (b : Bool) :
    output f (y,z,b) = scale n ^ 2 *
      ∑ x : Reg n, character y x * (if z = f x ∧ b = false then 1 else 0) := by
  change (inputGate n m *ᵥ (query f *ᵥ (inputGate n m *ᵥ initial n m))) (y,z,b) = _
  rw [inputGate_action]
  simp_rw [after_query, hadamard_entry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- If XOR translation by `s` preserves `f`, every output amplitude with `character y s = -1`
vanishes. -/
theorem output_zero_of_nonorthogonal (f : Reg n → Reg m) (s : Reg n)
    (hperiod : ∀ x, f (shift x s) = f x) (y : Reg n)
    (hy : character y s = -1) (z : Reg m) (b : Bool) : output f (y,z,b) = 0 := by
  let g : Reg n → ℂ := fun x => character y x * (if z = f x ∧ b = false then 1 else 0)
  have hg : (∑ x, g x) = -(∑ x, g x) := by
    calc
      (∑ x, g x) = ∑ x, g (shift x s) := (Equiv.sum_comp (shiftEquiv s) g).symm
      _ = -(∑ x, g x) := by
        simp only [g, character_shift, hperiod, hy]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hz : (∑ x, g x) = 0 := by linear_combination (1 / 2 : ℂ) * hg
  rw [output_amplitude]
  change scale n ^ 2 * (∑ x, g x) = 0
  rw [hz, mul_zero]

/-- Under XOR-period invariance, each basis outcome with `character y s = -1` has zero Born
probability. -/
theorem born_zero_of_nonorthogonal (f : Reg n → Reg m) (s : Reg n)
    (hp : ∀ x, f (shift x s) = f x) (y : Reg n) (hy : character y s = -1)
    (z : Reg m) (b : Bool) : BornProb (output f) (y,z,b) = 0 := by
  simp [BornProb, output_zero_of_nonorthogonal f s hp y hy z b]

/-- Under XOR-period invariance, the event of all output labels with character minus one on the
period has total measurement probability zero. See [SantoliSchaffner2017]. -/
theorem nonorthogonal_event_zero (f : Reg n → Reg m) (s : Reg n)
    (hp : ∀ x, f (shift x s) = f x) :
    MeasureProb (output f) (Finset.univ.filter (fun q : Space n m => character q.1 s = -1)) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  exact born_zero_of_nonorthogonal f s hp q.1 (Finset.mem_filter.mp hq).2 q.2.1 q.2.2
end
end Qatlib.Concepts.PeriodSampling.WeakPeriod
