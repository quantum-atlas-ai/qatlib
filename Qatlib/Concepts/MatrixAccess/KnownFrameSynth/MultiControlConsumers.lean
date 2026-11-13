/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl

/-!
# Consumers of multiple-control qubit synthesis

This module applies the multiple-control construction to repeated forward and inverse operations
and to phase kickback. `multiKnownGate` preserves identity and multiplication, while the
compiled constructions restore the clean work register.

These applications use the elementary controlled-gate setting of [BarencoEtAl1995].

## Main statements

* `multi_known_control_paid_inverse_and_clean_reuse`: gives the exact cost of repeated inverse
  pairs.
* `multi_known_control_all_true_phase_kickback_consumer`: applies a phase change to the all-true
  control branch.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Controlling the identity qubit matrix on all control bits gives the identity matrix. -/
theorem multiKnownGate_one (n : ℕ) :
    multiKnownGate n (1 : Matrix Bool Bool ℂ) = 1 := by
  ext ⟨x,a⟩ ⟨y,b⟩
  by_cases h : x = y <;> simp [multiKnownGate, h, Matrix.one_apply, Prod.ext_iff]

/-- The all-true controlled construction preserves multiplication of qubit matrices. -/
theorem multiKnownGate_mul (n : ℕ) (U V : Matrix Bool Bool ℂ) :
    multiKnownGate n U * multiKnownGate n V = multiKnownGate n (U * V) := by
  ext ⟨x,a⟩ ⟨y,b⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hxy : x = y
  · subst y
    rw [Finset.sum_eq_single x]
    · by_cases hx : allControlTrue n x = true <;>
        simp [multiKnownGate, hx, Matrix.mul_apply, Matrix.one_apply]
    · intro z _ hzx
      simp [multiKnownGate, hzx, Ne.symm hzx]
    · intro h; exact (h (Finset.mem_univ x)).elim
  · have hz : ∀ z : Reg n, ∑ c : Bool,
        multiKnownGate n U (x,a) (z,c) * multiKnownGate n V (z,c) (y,b) = 0 := by
      intro z
      by_cases hxz : x = z
      · subst z; simp [multiKnownGate, hxy]
      · simp [multiKnownGate, hxz]
    calc
      _ = ∑ _z : Reg n, (0 : ℂ) := Finset.sum_congr rfl (fun z _ => hz z)
      _ = 0 := Finset.sum_const_zero
      _ = _ := by simp [multiKnownGate, hxy]

/-- Repeating a synthesized controlled gate followed by its synthesized inverse r times restores
the embedded state, uses no queries, and costs `2*r*multiKnownCost n` gates. -/
theorem multi_known_control_paid_inverse_and_clean_reuse
    (n : ℕ) (p : KnownQubitAngles) (r : ℕ) (ψ : QState (Reg n × Bool)) :
    let cs := (List.replicate r (reflectionCompile (multiKnownSteps n p) ++
      reflectionCompile (multiKnownSteps n (knownQubitAngleAdjoint p)))).flatten
    QueryCount cs = 0 ∧ GateCount cs = 2*r*multiKnownCost n ∧
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ) cs
      (multiKnownEmbed n ψ) = multiKnownEmbed n ψ := by
  (try dsimp only)
  have hf := multi_known_control_actual_local_table_and_cost n p
  have hb := multi_known_control_actual_local_table_and_cost n (knownQubitAngleAdjoint p)
  have hi : (knownQubitUnitary p)ᴴ * knownQubitUnitary p = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (knownQubitUnitary_unitary p)
  have hpair : ∀ φ : QState (Reg n × Bool),
      Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
        (reflectionCompile (multiKnownSteps n p) ++
          reflectionCompile (multiKnownSteps n (knownQubitAngleAdjoint p)))
        (multiKnownEmbed n φ) = multiKnownEmbed n φ := by
    intro φ
    rw [run_append, hf.2.2.2.2, hb.2.2.2.2, Matrix.mulVec_mulVec,
      multiKnownGate_mul, knownQubitUnitary_adjoint, hi, multiKnownGate_one, Matrix.one_mulVec]
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [List.replicate_succ, List.flatten_cons, queryCount_append,
      gateCount_append, run_append, hf.2.2.1, hb.2.2.1, hf.2.2.2.1,
      hb.2.2.2.1, hpair]
    refine ⟨by omega, ?_, ?_⟩
    · rw [ih.2.1]; ring
    · exact ih.2.2

/-- The Euler parameters (π/2, 0, π, π) represent `PauliX`. -/
theorem multiKnown_pauliX_angles :
    knownQubitUnitary ⟨Real.pi/2,0,Real.pi,Real.pi⟩ = PauliX := by
  ext a b
  cases a <;> cases b <;>
    simp [knownQubitUnitary, Matrix.smul_apply, smul_eq_mul,
      eulerPRP_ff, eulerPRP_ft, eulerPRP_tf, eulerPRP_tt,
      Complex.ofReal_div, Complex.exp_pi_div_two_mul_I, Complex.exp_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two, PauliX, permMatrix]

/-- An all-true controlled `PauliX` with target state `Minus` negates exactly the amplitudes on
the all-true control branch and preserves the target state. -/
theorem multiKnownGate_phase_minus (n : ℕ) (ψ : QState (Reg n)) :
    multiKnownGate n PauliX *ᵥ TensorState ψ Minus =
      TensorState (fun x => if allControlTrue n x then -ψ x else ψ x) Minus := by
  funext ⟨x,b⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorState]
  rw [Finset.sum_eq_single x]
  · cases h : allControlTrue n x <;> cases b <;>
      simp [multiKnownGate, h, Minus, Hadamard, Matrix.of_apply, PauliX, permMatrix,
        Matrix.one_apply]
  · intro y _ hy
    simp [multiKnownGate, Ne.symm hy]
  · intro h; exact (h (Finset.mem_univ x)).elim

/-- The explicit local synthesis of the controlled `PauliX` produces all-true phase kickback on
an arbitrary control state with target `Minus`. -/
theorem multi_known_control_all_true_phase_kickback_consumer
    (n : ℕ) (ψ : QState (Reg n)) :
    let p : KnownQubitAngles := ⟨Real.pi/2,0,Real.pi,Real.pi⟩
    knownQubitUnitary p = PauliX ∧
    Run (1 : Matrix (Reg (n+1+(n-1))) (Reg (n+1+(n-1))) ℂ)
      (reflectionCompile (multiKnownSteps n p)) (multiKnownEmbed n (TensorState ψ Minus)) =
      multiKnownEmbed n (TensorState (fun x => if allControlTrue n x then -ψ x else ψ x) Minus) := by
  (try dsimp only)
  refine ⟨multiKnown_pauliX_angles, ?_⟩
  rw [(multi_known_control_actual_local_table_and_cost n _).2.2.2.2,
    multiKnown_pauliX_angles, multiKnownGate_phase_minus]

end Qatlib.Concepts.MatrixAccess.KnownFrameSynth
