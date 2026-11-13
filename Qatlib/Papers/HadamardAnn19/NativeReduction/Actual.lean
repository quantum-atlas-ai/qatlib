/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.QuboForms.Hadamard
import Qatlib.Foundations.BooleanEnergy.QuboForms.Hamiltonian
import Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain

/-!
# Native Realization of the Hadamard Reduction

This module connects the order-two scalar polynomial of [SuksmonoMinato2019] with the finite
Boolean configuration space, the compiled quadratic form, and its diagonal Hamiltonian. The
surjective map `fromSix` places four matrix bits and two ancillary bits into `Configuration 2
2`, and `literal20` evaluates the six-variable polynomial.

At the source coefficient `4 * M ^ 2`, `actual_square_ground` characterizes classical minimizers
for square matrices with at least two rows by ancillary validity and minimization of the
original Gram energy. `actual_quantum_minimum` bounds every normalized quantum expectation below
by any classical minimum of the compiled form.

## Main statements

* `literal20_eq_paperEnergy` and `literal20_compiled` identify the explicit polynomial with the
  native energies.
* `literal20_native_basis` identifies its value with a computational-basis expectation.
* `literal20_ground_iff` and `actual_square_ground` characterize the corresponding classical
  ground configurations.
* `actual_quantum_minimum` transfers a classical minimum to a lower bound for normalized quantum
  states.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.QuboForms
open Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain

/-- The increasing pair of column indices zero and one for a two-column matrix. -/
def pair01 : ColumnPair 2 := ⟨(0,1),by decide⟩

/-- Every increasing column pair for two columns equals `pair01`. -/
theorem pair_two_unique (p : ColumnPair 2) : p = pair01 := by
  obtain ⟨⟨i,j⟩,h⟩ := p
  change i.val < j.val at h
  have hi : i=0 := by apply Fin.ext; omega
  have hj : j=1 := by apply Fin.ext; omega
  subst i
  subst j
  rfl

/-- The universal finite set of increasing pairs of two columns is the singleton containing
`pair01`. -/
theorem pairs_two_univ : (Finset.univ : Finset (ColumnPair 2)) = {pair01} := by
  ext p
  simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
  exact pair_two_unique p

/-- Place six Boolean coordinates into a two-by-two configuration: the first four fill the main
matrix column by column, and the last two give its row ancillas. -/
def fromSix (q : Fin 6 → Bool) : Configuration 2 2
  | .inl (r,c) => if c=0 then (if r=0 then q 0 else q 1) else (if r=0 then q 2 else q 3)
  | .inr (r,_) => if r=0 then q 4 else q 5

/-- Every two-by-two configuration is represented by some six-bit input to `fromSix`. -/
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

/-- Evaluate the scalar quadratic expression `e2Q` from Eq. 20 of [SuksmonoMinato2019] on the
real values of six Boolean coordinates. -/
def literal20 (q : Fin 6 → Bool) : ℝ := e2Q (bit (q 0)) (bit (q 1)) (bit (q 2))
  (bit (q 3)) (bit (q 4)) (bit (q 5))

/-- The six-bit polynomial `literal20` equals the paper energy with coefficient 16 on the
configuration given by `fromSix`. -/
theorem literal20_eq_paperEnergy (q : Fin 6 → Bool) :
    literal20 q = paperEnergy 16 (fromSix q) := by
  unfold paperEnergy
  rw [pairs_two_univ,Finset.sum_singleton]
  unfold paperPair
  rw [pairs_two_univ,Finset.sum_singleton]
  simp only [pairPenalty,Fin.sum_univ_two,pair01,left,right,main,ancilla,fromSix]
  norm_num [literal20,e2Q,rowLinear,andPenalty]
  ring

/-- The value of `literal20` equals evaluation of the compiled Hadamard quadratic form with
coefficient 16 on the corresponding native configuration. -/
theorem literal20_compiled (q : Fin 6 → Bool) :
    literal20 q = quadraticEval (fromSix q) (hadamardQuadratic 16) := by
  rw [hadamardQuadratic_eval,literal20_eq_paperEnergy]

/-- The diagonal Hamiltonian of the compiled coefficient-16 quadratic form has expectation
`literal20 q` in the computational basis state indexed by `fromSix q`. -/
theorem literal20_native_basis (q : Fin 6 → Bool) :
    expectation (hamiltonian (hadamardQuadratic 16)) (basisState (fromSix q)) = literal20 q := by
  rw [expectation_basis,← literal20_compiled]

/-- A six-bit input minimizes `literal20` exactly when its native configuration has valid AND
ancillas and its main matrix minimizes the original Gram energy. -/
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

/-- For square matrices of order at least two, a configuration minimizes the compiled quadratic
form at coefficient `4 * M ^ 2` exactly when its ancillas are valid and its main matrix
minimizes Gram energy. -/
theorem actual_square_ground (M : ℕ) (hM : 2 ≤ M) (x : Configuration M M) :
    IsGround (fun y => quadraticEval y (hadamardQuadratic (4*(M:ℝ)^2))) x ↔
      Valid x ∧ IsGround energy (main x) := compiled_ground_iff hM x

/-- Any classical ground value of the compiled form at coefficient `4 * M ^ 2` is a lower bound
for the associated Hamiltonian expectation in every normalized complex state. -/
theorem actual_quantum_minimum {M N : ℕ} (x : Configuration M N)
    (hx : IsGround (fun y => quadraticEval y (hadamardQuadratic (4*(M:ℝ)^2))) x)
    (ψ : Configuration M N → ℂ) (hψ : Normalized ψ) :
    quadraticEval x (hadamardQuadratic (4*(M:ℝ)^2)) ≤
      expectation (hamiltonian (hadamardQuadratic (4*(M:ℝ)^2))) ψ :=
  quantum_ground_lower _ x hx ψ hψ

end Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
