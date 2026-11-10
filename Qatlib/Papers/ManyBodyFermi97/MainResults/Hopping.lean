/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.SecondQuantizedHubbard
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.Hopping
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical BigOperators

def hopGen (n : ℕ) (i j : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  creation i * annihilation j + creation j * annihilation i

theorem hopGen_hermitian (n : ℕ) (i j : Fin n) : (hopGen n i j).IsHermitian := by
  unfold hopGen Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : (annihilation j)ᴴ = creation j := (creation_eq_conjTranspose j).symm
  have h2 : (annihilation i)ᴴ = creation i := (creation_eq_conjTranspose i).symm
  have h3 : (creation i)ᴴ = annihilation i := by
    rw [creation_eq_conjTranspose i, Matrix.conjTranspose_conjTranspose]
  have h4 : (creation j)ᴴ = annihilation j := by
    rw [creation_eq_conjTranspose j, Matrix.conjTranspose_conjTranspose]
  rw [h1, h2, h3, h4, add_comm]

def hopEvol (n : ℕ) (i j : Fin n) (t : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  HamiltonianEvolution (hopGen n i j) t

theorem hopEvol_unitary (n : ℕ) (i j : Fin n) (t : ℝ) :
    hopEvol n i j t ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  hamiltonianEvolution_unitary (hopGen_hermitian n i j) t

def hopWord (n : ℕ) (i j : Fin n) (t : ℝ) : Circuit (Reg n) :=
  [.gate (hopEvol n i j t)]

theorem hopWord_correct (n : ℕ) (i j : Fin n) (t : ℝ) :
    IsUnitaryCircuit (hopWord n i j t) ∧
      QueryCount (hopWord n i j t) = 0 ∧
      GateCount (hopWord n i j t) = 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [hopWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact hopEvol_unitary n i j t

def pairList (m : ℕ) : List (Fin m × Fin m) := (chainPairs m).toList

theorem queryCount_map_gate {I : Type*} [Fintype I] [DecidableEq I]
    {α : Type*} (l : List α) (f : α → Matrix I I ℂ) :
    QueryCount (l.map (fun a => Step.gate (f a))) = 0 := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ih]

theorem gateCount_map_gate {I : Type*} [Fintype I] [DecidableEq I]
    {α : Type*} (l : List α) (f : α → Matrix I I ℂ) :
    GateCount (l.map (fun a => Step.gate (f a))) = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ih]

theorem isUnitaryCircuit_map_gate {I : Type*} [Fintype I] [DecidableEq I]
    {α : Type*} (l : List α) (f : α → Matrix I I ℂ)
    (h : ∀ a, f a ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (l.map (fun a => Step.gate (f a))) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, isUnitaryCircuit_gate]
    exact ⟨h a, ih⟩

def hopPassWord (m : ℕ) (t : ℝ) : Circuit (Reg m) :=
  (pairList m).map (fun p => .gate (hopEvol m p.1 p.2 t))

theorem hopPassWord_correct (m : ℕ) (t : ℝ) :
    IsUnitaryCircuit (hopPassWord m t) ∧
      QueryCount (hopPassWord m t) = 0 ∧
      GateCount (hopPassWord m t) = (chainPairs m).card := by
  refine ⟨?_, ?_, ?_⟩
  · exact isUnitaryCircuit_map_gate _ _ (fun p => hopEvol_unitary m p.1 p.2 t)
  · exact queryCount_map_gate _ _
  · rw [hopPassWord, gateCount_map_gate, pairList, Finset.length_toList]

theorem hopPass_le (m : ℕ) (t : ℝ) : GateCount (hopPassWord m t) ≤ m := by
  rw [(hopPassWord_correct m t).2.2]
  exact chainPairs_card m

def modeZ {n : ℕ} (k : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x : Reg n => (-1 : ℂ) ^ (if x k then 1 else 0))

theorem modeZ_unitary {n : ℕ} (k : Fin n) :
    modeZ k ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  rw [Complex.norm_pow]
  simp

def betweenSites (m : ℕ) (i j : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => i.val < k.val ∧ k.val < j.val)

theorem betweenSites_card_le (m : ℕ) (i j : Fin m) :
    (betweenSites m i j).card ≤ m := by
  calc (betweenSites m i j).card ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

def parityWord (m : ℕ) (i j : Fin m) : Circuit (Reg m) :=
  (betweenSites m i j).toList.map (fun k => .gate (modeZ k))

theorem parityWord_correct (m : ℕ) (i j : Fin m) :
    IsUnitaryCircuit (parityWord m i j) ∧
      QueryCount (parityWord m i j) = 0 ∧
      GateCount (parityWord m i j) = (betweenSites m i j).card ∧
      GateCount (parityWord m i j) ≤ m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isUnitaryCircuit_map_gate _ _ (fun k => modeZ_unitary k)
  · exact queryCount_map_gate _ _
  · rw [parityWord, gateCount_map_gate, Finset.length_toList]
  · rw [parityWord, gateCount_map_gate, Finset.length_toList]
    exact betweenSites_card_le m i j

theorem second_quantized_step_ledger (m : ℕ) (t : ℝ) :
    GateCount (hopPassWord m t) ≤ m :=
  hopPass_le m t

end Qatlib.Papers.ManyBodyFermi97.MainResults.Hopping
