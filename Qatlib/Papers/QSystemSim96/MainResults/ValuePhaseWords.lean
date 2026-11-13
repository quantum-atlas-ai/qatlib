/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Mathlib.Tactic

/-!
# Bitwise phases and reversible phase computation

This module implements the bitwise numeric phase and compute-phase-uncompute constructions of
[Zalka1998], Eqs. (7)-(10), using local reflection-gate words. `numericPhaseWord` weights
individual bit phases according to `bitVecEquiv`, and `valuePhaseAngles` places the same phases
on designated physical wires.

Given a legal program that actually computes the specified value, `computed_value_phase`
restores the input basis memory with the corresponding numeric phase. The module also proves
coherent action on finite superpositions, legality of the composite word, and exact gate and
query counts.

## Main statements

* `numericPhaseWord_ket` and `numericPhaseWord_resources` implement a numeric phase with one
  local gate per bit and no queries.
* `computePhaseUncompute_basis` restores an input after phases on its computed basis result.
* `computed_value_phase` and `computed_value_phase_superposition` specialize this action to an
  encoded value on chosen wires.
* `computed_value_phase_cost` and `computed_value_phase_legal` give the exact resources and
  legality of the composite word.

## References

* [Zalka, 1998][Zalka1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Matrix
open scoped BigOperators
noncomputable section
namespace Qatlib.Papers.QSystemSim96.MainResults

/-- The one-qubit diagonal gate that fixes `false` and multiplies `true` by `exp (I * θ)`. -/
def bitPhase (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then Complex.exp (Complex.I * (θ : ℂ)) else 1)

/-- The one-qubit phase gate is unitary for every real angle. -/
theorem bitPhase_unitary (θ : ℝ) : bitPhase θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    bitPhase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst b
    cases a <;> simp [← Complex.exp_conj, ← Complex.exp_add]
  · simp [h]

/-- Applying a phase gate on wire `i` preserves a basis register and contributes `exp (I * θ)`
exactly when its bit at `i` is true. -/
theorem wireBitPhase_ket (n : ℕ) (i : Fin n) (θ : ℝ) (x : Reg n) :
    ApplyGate (wireGate n i (bitPhase θ)) (Ket x) =
      Complex.exp (Complex.I * ((if x i then θ else 0 : ℝ) : ℂ)) • Ket x := by
  rw [applyGate_wireGate_ket]
  have hf : Function.update x i (x i) = x := Function.update_eq_self i x
  cases h : x i
  · have hu : Function.update x i false = x := by simpa only [h] using hf
    simp [bitPhase, hu]
  · have hu : Function.update x i true = x := by simpa only [h] using hf
    simp [bitPhase, hu]

/-- The list of local one-qubit phase gates specified by wire-angle pairs. -/
def bitPhaseWord {n : ℕ} (angles : List (Fin n × ℝ)) : List (ReflectionGate n) :=
  angles.map fun p => .inl (p.1, bitPhase p.2)

/-- A phase word preserves a basis register and multiplies it by the exponential of the sum of
angles whose selected bits are true. -/
theorem bitPhaseWord_ket {n : ℕ} (angles : List (Fin n × ℝ)) (x : Reg n) :
    Run 1 (reflectionCompile (bitPhaseWord angles)) (Ket x) =
      Complex.exp (Complex.I * (((angles.map fun p => if x p.1 then p.2 else 0).sum : ℝ) : ℂ)) • Ket x := by
  rw [run_reflectionCompile]
  induction angles with
  | nil => simp [bitPhaseWord, reflectionProgramMatrix]
  | cons p angles ih =>
    simp only [bitPhaseWord] at ih
    simp only [bitPhaseWord, List.map_cons, reflectionProgramMatrix, applyGate_mul,
        reflectionGateMatrix]
    rw [wireBitPhase_ket, reflectionApplyGate_smul, ih, smul_smul]
    simp only [List.sum_cons]
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Every phase word is legal, compiles to one gate per wire-angle pair, and makes no queries. -/
theorem bitPhaseWord_resources {n : ℕ} (angles : List (Fin n × ℝ)) :
    reflectionLegal (bitPhaseWord angles) ∧
    GateCount (reflectionCompile (bitPhaseWord angles)) = angles.length ∧
    QueryCount (reflectionCompile (bitPhaseWord angles)) = 0 := by
  refine ⟨?_, ?_, queryCount_reflectionCompile _⟩
  · intro g hg
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
    exact bitPhase_unitary _
  · rw [gateCount_reflectionCompile]
    simp [bitPhaseWord]

/-- The phase word assigning angle `c * 2 ^ (n - 1 - i.val)` to each wire `i` in the register's
most-significant-bit encoding. -/
def numericPhaseWord (n : ℕ) (c : ℝ) : List (ReflectionGate n) :=
  bitPhaseWord ((List.finRange n).map fun i => (i, c * (2 : ℝ) ^ (n-1-i.val)))

/-- The numeric phase word preserves a basis register while multiplying it by `exp (I * c *
value)`, where `value` is its `bitVecEquiv` encoding, implementing [Zalka1998], Eq. (9). -/
theorem numericPhaseWord_ket (n : ℕ) (c : ℝ) (x : Reg n) :
    Run 1 (reflectionCompile (numericPhaseWord n c)) (Ket x) =
      Complex.exp (Complex.I * ((c * (bitVecEquiv n x).val : ℝ) : ℂ)) • Ket x := by
  rw [numericPhaseWord, bitPhaseWord_ket]
  congr 3
  simp only [List.map_map, Function.comp_apply, ← Fin.sum_univ_def]
  rw [bitVecEquiv_binary_msb_expansion]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The numeric phase word is legal and uses exactly `n` local gates and no queries, matching
the one-phase-per-bit construction of [Zalka1998], Eq. (9). -/
theorem numericPhaseWord_resources (n : ℕ) (c : ℝ) :
    reflectionLegal (numericPhaseWord n c) ∧
    GateCount (reflectionCompile (numericPhaseWord n c)) = n ∧
    QueryCount (reflectionCompile (numericPhaseWord n c)) = 0 := by
  simpa [numericPhaseWord] using bitPhaseWord_resources
    ((List.finRange n).map fun i => (i, c * (2 : ℝ) ^ (n - 1 - i.val)))

/-- If a legal program `C` sends basis input `s` to basis result `t`, computing, applying the
specified bit phases, and running the adjoint restores `s` with the phase determined by the
selected bits of `t`. -/
theorem computePhaseUncompute_basis {n : ℕ} (C : List (ReflectionGate n))
    (hC : reflectionLegal C) (angles : List (Fin n × ℝ)) (s t : Reg n)
    (hcompute : Run 1 (reflectionCompile C) (Ket s) = Ket t) :
    Run 1 (reflectionCompile (C ++ bitPhaseWord angles ++ reflectionAdjoint C)) (Ket s) =
      Complex.exp (Complex.I * (((angles.map fun p => if t p.1 then p.2 else 0).sum : ℝ) : ℂ)) • Ket s := by
  have hu : (reflectionProgramMatrix C)ᴴ * reflectionProgramMatrix C = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (reflectionProgramMatrix_unitary C hC)
  have hinv : Run 1 (reflectionCompile (reflectionAdjoint C)) (Ket t) = Ket s := by
    rw [← hcompute, run_reflectionCompile, run_reflectionCompile, reflectionAdjoint_matrix C hC,
      ← applyGate_mul, hu, applyGate_one]
  rw [reflectionCompile_append, reflectionCompile_append, run_append, run_append,
    hcompute, bitPhaseWord_ket, run_reflectionCompile_smul, hinv]

/-- The compiled compute-phase-uncompute word uses exactly `2 * C.length + angles.length` gates
and no queries. -/
theorem computePhaseUncompute_cost {n : ℕ} (C : List (ReflectionGate n))
    (angles : List (Fin n × ℝ)) :
    GateCount (reflectionCompile (C ++ bitPhaseWord angles ++ reflectionAdjoint C)) =
      2 * C.length + angles.length ∧
    QueryCount (reflectionCompile (C ++ bitPhaseWord angles ++ reflectionAdjoint C)) = 0 := by
  rw [gateCount_reflectionCompile, queryCount_reflectionCompile]
  simp [List.length_append, bitPhaseWord]
  omega

/-- The wire-angle list assigning the binary weight `c * 2 ^ (r - 1 - j.val)` to value bit `j`
on its designated physical wire. -/
def valuePhaseAngles {n r : ℕ} (wires : Fin r ↪ Fin n) (c : ℝ) : List (Fin n × ℝ) :=
  (List.finRange r).map fun j => (wires j, c * (2 : ℝ) ^ (r - 1 - j.val))

/-- If the legal program computes a basis result containing the specified value on the
designated wires, its compute-phase-uncompute word restores the full input with phase `exp
(I * c * value)`. -/
theorem computed_value_phase {n r : ℕ} (C : List (ReflectionGate n))
    (hC : reflectionLegal C) (wires : Fin r ↪ Fin n) (c : ℝ)
    (input result : Reg n) (value : Reg r)
    (hcompute : Run 1 (reflectionCompile C) (Ket input) = Ket result)
    (hvalue : ∀ j, result (wires j) = value j) :
    Run 1 (reflectionCompile
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C)) (Ket input) =
      Complex.exp (Complex.I * ((c * (bitVecEquiv r value).val : ℝ) : ℂ)) • Ket input := by
  rw [computePhaseUncompute_basis C hC _ input result hcompute]
  have hsum : ((valuePhaseAngles wires c).map fun p =>
      if result p.1 then p.2 else 0).sum = c * (bitVecEquiv r value).val := by
    simp only [valuePhaseAngles, List.map_map, Function.comp_apply, ← Fin.sum_univ_def]
    simp_rw [hvalue]
    rw [bitVecEquiv_binary_msb_expansion]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hsum]

/-- The compiled value-phase word uses exactly `2 * C.length + r` local gates and no queries,
giving the explicit cost of [Zalka1998], Eqs. (7)-(10). -/
theorem computed_value_phase_cost {n r : ℕ} (C : List (ReflectionGate n))
    (wires : Fin r ↪ Fin n) (c : ℝ) :
    GateCount (reflectionCompile
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C)) =
        2 * C.length + r ∧
    QueryCount (reflectionCompile
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C)) = 0 := by
  simpa [valuePhaseAngles] using computePhaseUncompute_cost C (valuePhaseAngles wires c)

/-- A legal computation program remains legal when followed by the value-bit phases and its
reversed adjoint, validating the local construction of [Zalka1998], Eqs. (7)-(10). -/
theorem computed_value_phase_legal {n r : ℕ} (C : List (ReflectionGate n))
    (hC : reflectionLegal C) (wires : Fin r ↪ Fin n) (c : ℝ) :
    reflectionLegal
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C) := by
  simp only [reflectionLegal_append]
  exact ⟨⟨hC, (bitPhaseWord_resources _).1⟩, reflectionAdjoint_legal C hC⟩

/-- If one legal program computes the specified value for every indexed basis input, the
value-phase construction multiplies each coefficient in any finite superposition by its
corresponding numeric phase and restores its input register, coherently implementing
[Zalka1998], Eqs. (7)-(10). -/
theorem computed_value_phase_superposition {X : Type} [Fintype X]
    {n r : ℕ} (C : List (ReflectionGate n)) (hC : reflectionLegal C)
    (wires : Fin r ↪ Fin n) (c : ℝ) (input result : X → Reg n)
    (value : X → Reg r) (a : X → ℂ)
    (hcompute : ∀ x, Run 1 (reflectionCompile C) (Ket (input x)) = Ket (result x))
    (hvalue : ∀ x j, result x (wires j) = value x j) :
    Run 1 (reflectionCompile
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C))
        (∑ x, a x • Ket (input x)) =
      ∑ x, (a x * Complex.exp
        (Complex.I * ((c * (bitVecEquiv r (value x)).val : ℝ) : ℂ))) • Ket (input x) := by
  rw [run_reflectionCompile]
  change (Matrix.mulVecLin _) (∑ x, a x • Ket (input x)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul]
  have hx := computed_value_phase C hC wires c (input x) (result x) (value x)
    (hcompute x) (hvalue x)
  rw [run_reflectionCompile] at hx
  change a x • ApplyGate _ (Ket (input x)) = _
  rw [hx, smul_smul]

end Qatlib.Papers.QSystemSim96.MainResults
