/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Mathlib.Tactic
set_option warningAsError false
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

def bitPhase (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then Complex.exp (Complex.I * (θ : ℂ)) else 1)

theorem bitPhase_unitary (θ : ℝ) : bitPhase θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    bitPhase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst b
    cases a <;> simp [← Complex.exp_conj, ← Complex.exp_add]
  · simp [h]

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

def bitPhaseWord {n : ℕ} (angles : List (Fin n × ℝ)) : List (ReflectionGate n) :=
  angles.map fun p => .inl (p.1, bitPhase p.2)

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

def numericPhaseWord (n : ℕ) (c : ℝ) : List (ReflectionGate n) :=
  bitPhaseWord ((List.finRange n).map fun i => (i, c * (2 : ℝ) ^ (n-1-i.val)))

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

theorem numericPhaseWord_resources (n : ℕ) (c : ℝ) :
    reflectionLegal (numericPhaseWord n c) ∧
    GateCount (reflectionCompile (numericPhaseWord n c)) = n ∧
    QueryCount (reflectionCompile (numericPhaseWord n c)) = 0 := by
  simpa [numericPhaseWord] using bitPhaseWord_resources
    ((List.finRange n).map fun i => (i, c * (2 : ℝ) ^ (n - 1 - i.val)))

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

theorem computePhaseUncompute_cost {n : ℕ} (C : List (ReflectionGate n))
    (angles : List (Fin n × ℝ)) :
    GateCount (reflectionCompile (C ++ bitPhaseWord angles ++ reflectionAdjoint C)) =
      2 * C.length + angles.length ∧
    QueryCount (reflectionCompile (C ++ bitPhaseWord angles ++ reflectionAdjoint C)) = 0 := by
  rw [gateCount_reflectionCompile, queryCount_reflectionCompile]
  simp [List.length_append, bitPhaseWord]
  omega

def valuePhaseAngles {n r : ℕ} (wires : Fin r ↪ Fin n) (c : ℝ) : List (Fin n × ℝ) :=
  (List.finRange r).map fun j => (wires j, c * (2 : ℝ) ^ (r - 1 - j.val))

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

theorem computed_value_phase_cost {n r : ℕ} (C : List (ReflectionGate n))
    (wires : Fin r ↪ Fin n) (c : ℝ) :
    GateCount (reflectionCompile
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C)) =
        2 * C.length + r ∧
    QueryCount (reflectionCompile
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C)) = 0 := by
  simpa [valuePhaseAngles] using computePhaseUncompute_cost C (valuePhaseAngles wires c)

theorem computed_value_phase_legal {n r : ℕ} (C : List (ReflectionGate n))
    (hC : reflectionLegal C) (wires : Fin r ↪ Fin n) (c : ℝ) :
    reflectionLegal
      (C ++ bitPhaseWord (valuePhaseAngles wires c) ++ reflectionAdjoint C) := by
  simp only [reflectionLegal_append]
  exact ⟨⟨hC, (bitPhaseWord_resources _).1⟩, reflectionAdjoint_legal C hC⟩

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
