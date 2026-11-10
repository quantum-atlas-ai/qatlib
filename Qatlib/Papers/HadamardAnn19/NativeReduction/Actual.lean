/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.QuboForms.Hadamard
import Qatlib.Foundations.BooleanEnergy.QuboForms.Hamiltonian
import Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.QuboForms
open Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain

def pair01 : ColumnPair 2 := ⟨(0,1),by decide⟩

theorem pair_two_unique (p : ColumnPair 2) : p = pair01 := by
  obtain ⟨⟨i,j⟩,h⟩ := p
  change i.val < j.val at h
  have hi : i=0 := by apply Fin.ext; omega
  have hj : j=1 := by apply Fin.ext; omega
  subst i
  subst j
  rfl

theorem pairs_two_univ : (Finset.univ : Finset (ColumnPair 2)) = {pair01} := by
  ext p
  simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
  exact pair_two_unique p

def fromSix (q : Fin 6 → Bool) : Configuration 2 2
  | .inl (r,c) => if c=0 then (if r=0 then q 0 else q 1) else (if r=0 then q 2 else q 3)
  | .inr (r,_) => if r=0 then q 4 else q 5

theorem fromSix_surjective : Function.Surjective fromSix := by
  intro x
  let q : Fin 6 → Bool := ![main x 0 0,main x 1 0,main x 0 1,main x 1 1,
    ancilla x 0 pair01,ancilla x 1 pair01]
  refine ⟨q,?_⟩
  funext v
  rcases v with ⟨r,c⟩ | ⟨r,p⟩
  · fin_cases r <;> fin_cases c <;> rfl
  · have hp := pair_two_unique p
    subst p
    fin_cases r <;> rfl

def literal20 (q : Fin 6 → Bool) : ℝ := e2Q (bit (q 0)) (bit (q 1)) (bit (q 2))
  (bit (q 3)) (bit (q 4)) (bit (q 5))

theorem literal20_eq_paperEnergy (q : Fin 6 → Bool) :
    literal20 q = paperEnergy 16 (fromSix q) := by
  unfold paperEnergy
  rw [pairs_two_univ,Finset.sum_singleton]
  unfold paperPair
  rw [pairs_two_univ,Finset.sum_singleton]
  simp only [pairPenalty,Fin.sum_univ_two,pair01,left,right,main,ancilla,fromSix]
  norm_num [literal20,e2Q,rowLinear,andPenalty]
  ring

theorem literal20_compiled (q : Fin 6 → Bool) :
    literal20 q = quadraticEval (fromSix q) (hadamardQuadratic 16) := by
  rw [hadamardQuadratic_eval,literal20_eq_paperEnergy]

theorem literal20_native_basis (q : Fin 6 → Bool) :
    expectation (hamiltonian (hadamardQuadratic 16)) (basisState (fromSix q)) = literal20 q := by
  rw [expectation_basis,← literal20_compiled]

theorem literal20_ground_iff (q : Fin 6 → Bool) :
    IsGround literal20 q ↔ Valid (fromSix q) ∧ IsGround energy (main (fromSix q)) := by
  have he : IsGround literal20 q ↔ IsGround (paperEnergy 16) (fromSix q) := by
    constructor
    · intro h x
      obtain ⟨r,rfl⟩ := fromSix_surjective x
      simpa only [← literal20_eq_paperEnergy] using h r
    · intro h r
      simpa only [← literal20_eq_paperEnergy] using h (fromSix r)
  rw [he]
  convert source_ground_iff (by decide) (fromSix q) using 1
  norm_num

theorem actual_square_ground (M : ℕ) (hM : 2 ≤ M) (x : Configuration M M) :
    IsGround (fun y => quadraticEval y (hadamardQuadratic (4*(M:ℝ)^2))) x ↔
      Valid x ∧ IsGround energy (main x) := compiled_ground_iff hM x

theorem actual_quantum_minimum {M N : ℕ} (x : Configuration M N)
    (hx : IsGround (fun y => quadraticEval y (hadamardQuadratic (4*(M:ℝ)^2))) x)
    (ψ : Configuration M N → ℂ) (hψ : Normalized ψ) :
    quadraticEval x (hadamardQuadratic (4*(M:ℝ)^2)) ≤
      expectation (hamiltonian (hadamardQuadratic (4*(M:ℝ)^2))) ψ :=
  quantum_ground_lower _ x hx ψ hψ

end Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
