/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.Bias

/-!
# Character diagonalization of X-program circuits

This module extends X-program circuits to arbitrary input amplitudes through `circuitOp` and
proves that binary characters are eigenfunctions of each gate and of the complete circuit. The
character identities provide the algebraic diagonalization used in the X-program and Z-network
correspondence of Lemmas 7 and 8 in [ShepherdBremner2009].

## Main statements

* `xGate_char`: computes the action of one X-gate on a binary character.
* `circuit_eq_op`: recovers the original circuit from the zero basis state.
* `circuitOp_char`: computes the product of character eigenvalues for the complete circuit.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

/-- A binary character maps addition in its second argument to multiplication. -/
theorem chi_add_right {n : ℕ} (u x y : F2Vec n) :
    chi u (x + y) = chi u x * chi u y := by
  rw [chi_comm u (x + y), chi_add_left, chi_comm x u, chi_comm y u]

/-- A binary character equals `1` for zero dot product and `-1` otherwise. -/
theorem chi_eq_sign {n : ℕ} (u x : F2Vec n) :
    chi u x = (if dot u x = 0 then (1 : ℂ) else -1) := chi_eq_sgn2 u x

/-- An X-gate commutes with multiplication of its input amplitude by a complex scalar. -/
theorem xGate_smul {n : ℕ} (θ : ℝ) (p : F2Vec n) (c : ℂ) (ψ : F2Vec n → ℂ) :
    xGate θ p (fun x => c * ψ x) = fun x => c * xGate θ p ψ x := by
  funext x
  simp only [xGate]
  ring

/-- A binary character is an eigenfunction of an X-gate, with multiplier `zCoeff θ (decide (dot
p a = 0))`. See [ShepherdBremner2009]. -/
theorem xGate_char {n : ℕ} (θ : ℝ) (p a : F2Vec n) :
    xGate θ p (fun y => chi a y) =
      fun x => zCoeff θ (decide (dot p a = 0)) * chi a x := by
  funext x
  simp only [xGate]
  have hshift : chi a (x + p) = chi a x * chi a p := chi_add_right a x p
  rw [hshift]
  have hchi : chi a p = (if dot p a = 0 then (1 : ℂ) else -1) := by
    rw [chi_comm]; exact chi_eq_sign p a
  rw [hchi]
  have heuler := cos_add_sin_mul_sign θ (decide (dot p a = 0))
  simp only [decide_eq_true_eq] at heuler
  rw [← heuler]
  ring

/-- The recursive X-program circuit operator on an arbitrary complex-valued input function. -/
def circuitOp {n : ℕ} : (k : ℕ) → (Fin k → F2Vec n) → (Fin k → ℝ) →
    (F2Vec n → ℂ) → F2Vec n → ℂ
  | 0, _, _, ψ => ψ
  | k + 1, p, θ, ψ =>
      xGate (θ 0) (p 0) (circuitOp k (fun i => p i.succ) (fun i => θ i.succ) ψ)

/-- The computational basis amplitude supported at the zero binary vector. -/
def basis0 {n : ℕ} : F2Vec n → ℂ := fun x => if x = 0 then 1 else 0

/-- The original X-program circuit is `circuitOp` applied to `basis0`. -/
theorem circuit_eq_op {n : ℕ} (k : ℕ) (p : Fin k → F2Vec n) (θ : Fin k → ℝ) :
    circuit k p θ = circuitOp k p θ basis0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext x
      simp only [circuit, circuitOp, ih]

/-- On a binary character, the circuit operator multiplies by the product of the corresponding
`zCoeff` factors. See [ShepherdBremner2009]. -/
theorem circuitOp_char {n : ℕ} (k : ℕ) (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (a : F2Vec n) :
    circuitOp k p θ (fun y => chi a y) =
      fun x => (∏ i, zCoeff (θ i) (decide (dot (p i) a = 0))) * chi a x := by
  induction k with
  | zero =>
      funext x
      simp [circuitOp]
  | succ k ih =>
      rw [show circuitOp (k + 1) p θ (fun y => chi a y) =
          xGate (θ 0) (p 0)
            (circuitOp k (fun i => p i.succ) (fun i => θ i.succ) (fun y => chi a y))
          from rfl]
      rw [ih]
      rw [xGate_smul, xGate_char]
      funext x
      rw [Fin.prod_univ_succ]
      ring

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
