/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CircuitReversal.ReversalAlgebra.CircuitReversal

/-!
# Compute copy and reverse subroutines

This module constructs `AnswerCopyGate` and analyzes a circuit followed by copying its Boolean
answer and reversing the original computation. For a self adjoint unitary oracle and a unitary
circuit, the Born probability of the restored input and a specified answer is the square of the
original answer probability, giving the cleaning identity used in [BennettEtAl1997].

## Main statements

* `answerCopyGate_unitary`: the controlled answer copy is unitary.
* `run_liftCircuit_tensorState`: a lifted execution preserves the extra tensor factor.
* `subroutine_cleaning_mass`: compute, copy, and reverse squares the answer probability at the
  restored input.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Amplification

open Matrix

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The permutation that XORs `v` of the first register into an answer bit. -/
def answerCopyPerm (v : I → Bool) : I × Bool → I × Bool :=
  fun p => (p.1, p.2 ^^ v p.1)

/-- The permutation matrix that copies the Boolean value `v` into an answer bit by XOR. -/
noncomputable def AnswerCopyGate (v : I → Bool) : Matrix (I × Bool) (I × Bool) ℂ :=
  permMatrix (answerCopyPerm v)

omit [Fintype I] [DecidableEq I] in

/-- XORing `v` of the first register into the answer bit is an involution. -/
theorem answerCopyPerm_involutive (v : I → Bool) : Function.Involutive (answerCopyPerm v) := by
  intro p
  obtain ⟨y, c⟩ := p
  simp [answerCopyPerm]

/-- The answer copy gate is unitary. -/
theorem answerCopyGate_unitary (v : I → Bool) :
    AnswerCopyGate v ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  permMatrix_unitary (answerCopyPerm_involutive v)

/-- The inner product with basis state `Ket i` in the first argument is the amplitude at `i`. -/
private theorem inner_ket_left (i : I) (φ : QState I) : Inner (Ket i) φ = φ i := by
  rw [inner_apply, Finset.sum_eq_single i]
  · simp [Ket]
  · intro k _ hk
    simp [Ket, hk]
  · simp

/-- Lifting circuits to an additional answer bit preserves concatenation. -/
private theorem liftCircuit_append (C D : Circuit I) :
    LiftCircuit (C ++ D) = LiftCircuit C ++ LiftCircuit D := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [List.cons_append, liftCircuit_gate, liftCircuit_gate, ih]; rfl
    | query => rw [List.cons_append, liftCircuit_query, liftCircuit_query, ih]; rfl

/-- Lifting a gate to an additional answer bit commutes with conjugate transposition. -/
private theorem liftGate_conjTranspose (U : Matrix I I ℂ) :
    (LiftGate U)ᴴ = LiftGate Uᴴ := by
  rw [LiftGate, tensorGate_conjTranspose, Matrix.conjTranspose_one, ← LiftGate]

/-- For a unitary gate, applying it in the first inner product argument equals applying its
conjugate transpose in the second. -/
private theorem inner_applyGate_conjTranspose {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ φ : QState I) :
    Inner (ApplyGate U ψ) φ = Inner ψ (ApplyGate Uᴴ φ) := by
  have hU' : Uᴴ ∈ Matrix.unitaryGroup I ℂ := conjTranspose_mem_unitaryGroup hU
  have hUU : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  rw [← inner_applyGate hU' (ApplyGate U ψ) φ, ← applyGate_mul, hUU, applyGate_one]

/-- For a self adjoint unitary oracle and a unitary circuit, moving the lifted execution across
an inner product gives the lifted reversed circuit. -/
private theorem inner_run_liftCircuit (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hOH : Oᴴ = O) (C : Circuit I) :
    ∀ (_ : IsUnitaryCircuit C) (χ φ : QState (I × Bool)),
      Inner (Run (LiftGate O) (LiftCircuit C) χ) φ
        = Inner χ (Run (LiftGate O) (LiftCircuit (ReverseCircuit C)) φ) := by
  induction C with
  | nil => intro _ χ φ; rfl
  | cons s C ih =>
    intro hC χ φ
    cases s with
    | gate U =>
      have hU : U ∈ Matrix.unitaryGroup I ℂ := hC U List.mem_cons_self
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have hkey : ∀ Ψ : QState (I × Bool),
          Run (LiftGate O) (LiftCircuit (ReverseCircuit (Step.gate U :: C))) Ψ
            = ApplyGate (LiftGate Uᴴ) (Run (LiftGate O) (LiftCircuit (ReverseCircuit C)) Ψ) := by
        intro Ψ
        rw [reverseCircuit_cons, liftCircuit_append, run_append]
        rfl
      rw [liftCircuit_gate, run_gate, ih hC' (ApplyGate (LiftGate U) χ) φ,
        inner_applyGate_conjTranspose (liftGate_unitary hU), liftGate_conjTranspose, hkey]
    | query =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      have hkey : ∀ Ψ : QState (I × Bool),
          Run (LiftGate O) (LiftCircuit (ReverseCircuit (Step.query :: C))) Ψ
            = ApplyGate (LiftGate O) (Run (LiftGate O) (LiftCircuit (ReverseCircuit C)) Ψ) := by
        intro Ψ
        rw [reverseCircuit_cons, liftCircuit_append, run_append]
        rfl
      rw [liftCircuit_query, run_query, ih hC' (ApplyGate (LiftGate O) χ) φ,
        inner_applyGate_conjTranspose (liftGate_unitary hO), liftGate_conjTranspose, hOH, hkey]

/-- Running a lifted circuit with a lifted oracle on a tensor state applies the original
execution to the first factor. -/
theorem run_liftCircuit_tensorState (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I)
    (χ : QState Bool) :
    Run (LiftGate O) (LiftCircuit C) (TensorState ψ χ) = TensorState (Run O C ψ) χ := by
  induction C generalizing ψ χ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => rw [liftCircuit_gate, run_gate, run_gate, applyGate_liftGate, ih]
    | query => rw [liftCircuit_query, run_query, run_query, applyGate_liftGate, ih]

/-- For a self adjoint unitary oracle and a unitary circuit, compute, copy, and reverse gives
the restored input and answer `b` with Born probability equal to the square of the original
probability of answer `b`. See [Bennett et al., Theorem 4.14][BennettEtAl1997]. -/
theorem subroutine_cleaning_mass (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (hOH : Oᴴ = O) (C : Circuit I) (hC : IsUnitaryCircuit C) (x₀ : I) (v : I → Bool)
    (b : Bool) :
    BornProb (Run (LiftGate O) (LiftCircuit C ++ [Step.gate (AnswerCopyGate v)] ++
      LiftCircuit (ReverseCircuit C)) (Ket (x₀, false))) (x₀, b) =
      (MeasureProb (Run O C (Ket x₀)) (Finset.univ.filter fun y => v y = b)) ^ 2 := by

  have hfwd : Run (LiftGate O) (LiftCircuit C) (Ket (x₀, false))
      = TensorState (Run O C (Ket x₀)) (Ket false) := by
    rw [← tensorState_ket_ket, run_liftCircuit_tensorState]

  have hstate : Run (LiftGate O) (LiftCircuit C ++ [Step.gate (AnswerCopyGate v)] ++
      LiftCircuit (ReverseCircuit C)) (Ket (x₀, false))
      = Run (LiftGate O) (LiftCircuit (ReverseCircuit C))
          (ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false))) := by
    rw [run_append, run_append, hfwd]
    rfl

  have hcopy : ∀ (y : I) (c : Bool),
      ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false)) (y, c)
        = if v y = c then (Run O C (Ket x₀)) y else 0 := by
    intro y c
    unfold AnswerCopyGate
    rw [applyGate_permMatrix (answerCopyPerm_involutive v)]
    show TensorState (Run O C (Ket x₀)) (Ket false) (y, c ^^ v y) = _
    rw [tensorState_apply]
    have hket : ∀ (c w : Bool), Ket false (c ^^ w) = if w = c then 1 else 0 := by
      intro c w
      cases c <;> cases w <;> simp [Ket]
    rw [hket c (v y)]
    by_cases hv : v y = c <;> simp [hv]

  have hinner : Inner (TensorState (Run O C (Ket x₀)) (Ket b))
      (ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false)))
      = ((MeasureProb (Run O C (Ket x₀)) (Finset.univ.filter fun y => v y = b) : ℝ) : ℂ) := by
    rw [inner_apply, Fintype.sum_prod_type]
    have expand : ∀ y : I,
        (∑ c : Bool, (starRingEnd ℂ) (TensorState (Run O C (Ket x₀)) (Ket b) (y, c))
          * ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false)) (y, c))
        = (if v y = b then (starRingEnd ℂ) ((Run O C (Ket x₀)) y) * (Run O C (Ket x₀)) y
            else 0) := by
      intro y
      rw [Finset.sum_eq_single b]
      · rw [hcopy y b]
        simp only [tensorState_apply, ket_self, mul_one]
        by_cases hv : v y = b <;> simp [hv]
      · intro c _ hc
        rw [tensorState_apply, ket_ne hc]
        simp
      · simp
    rw [Finset.sum_congr rfl fun y _ => expand y, ← Finset.sum_filter]
    unfold MeasureProb BornProb
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

  have key := inner_run_liftCircuit O hO hOH C hC (Ket (x₀, b))
    (ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false)))
  have hketstate : Run (LiftGate O) (LiftCircuit C) (Ket (x₀, b))
      = TensorState (Run O C (Ket x₀)) (Ket b) := by
    rw [← tensorState_ket_ket, run_liftCircuit_tensorState]
  have hampl : (Run (LiftGate O) (LiftCircuit (ReverseCircuit C))
        (ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false)))) (x₀, b)
      = Inner (TensorState (Run O C (Ket x₀)) (Ket b))
          (ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false))) := by
    have h1 := inner_ket_left (x₀, b)
      (Run (LiftGate O) (LiftCircuit (ReverseCircuit C))
        (ApplyGate (AnswerCopyGate v) (TensorState (Run O C (Ket x₀)) (Ket false))))
    rw [← h1, ← key, hketstate]
  unfold BornProb
  rw [hstate, hampl, hinner, Complex.norm_real,
    Real.norm_of_nonneg (measureProb_nonneg (Run O C (Ket x₀))
      (Finset.univ.filter fun y => v y = b))]

end Qatlib.Concepts.QueryComplexity.Amplification
