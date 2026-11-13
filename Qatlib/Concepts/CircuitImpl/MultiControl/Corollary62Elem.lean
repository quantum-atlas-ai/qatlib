/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.Corollary62Stat
import Qatlib.Concepts.CircuitImpl.SqrtApprox.UnitarySqrtChain

/-!
# Elementary synthesis of doubly controlled unitaries

The word `sourceDoubleSteps` implements a doubly controlled square of a known qubit unitary on a
target fibre. Its legality and action establish `corollary6_2`, the elementary-gate formulation
of Corollary 6.2 in [BarencoEtAl1995], with at most eight single-qubit gates and eight CNOTs.

## Main statements

* `sourceDoubleSteps_action`: Exact target-fibre semantics of the sixteen-gate word.
* `corollary6_2`: Query-free synthesis of any doubly controlled qubit unitary.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.SqrtApprox
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A CNOT on two wires distinct from the fibre target updates its background target bit and
leaves the fibre state unchanged. -/
private theorem fibre_other_cnot {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Reg N) (φ : QState Bool) :
    ApplyGate (cnotGate N a b) (multiWireState t x φ) =
      multiWireState t (Function.update x b (x b ^^ x a)) φ := by
  simp only [multiWireState, reflectionApplyGate_add, reflectionApplyGate_smul,
    applyGate_cnotGate_ket N a b hab, Function.update_of_ne hat,
    Function.update_of_ne hbt]
  rw [Function.update_comm hbt, Function.update_comm hbt]

/-- The sixteen-gate word for a doubly controlled square of the qubit unitary specified by `p`. -/
private def sourceDoubleSteps {N : ℕ} (a b t : Fin N) (p : KnownQubitAngles) :
    List (ReflectionGate N) :=
  let A : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlA p)
  let B : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlB p)
  let C : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlC p)
  let E : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlE p);
  [.inl (a,E), .inl (t,C), .inr (a,t), .inl (t,B), .inr (a,t),
   .inr (b,a), .inr (a,t), .inl (t,Bᴴ), .inr (a,t), .inl (a,Eᴴ),
   .inr (b,a), .inl (b,E), .inr (b,t), .inl (t,B), .inr (b,t), .inl (t,A)]

/-- The doubly controlled gate word is legal when its two controls and target are pairwise
distinct. -/
private theorem sourceDoubleSteps_legal {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (p : KnownQubitAngles) :
    reflectionLegal (sourceDoubleSteps a b t p) := by
  intro g hg
  simp only [sourceDoubleSteps, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact knownQubitUnitary_unitary (knownControlE p)
  · exact knownQubitUnitary_unitary (knownControlC p)
  · exact hat
  · exact knownQubitUnitary_unitary (knownControlB p)
  · exact hat
  · exact hab.symm
  · exact hat
  · exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary
      (knownQubitUnitary_unitary (knownControlB p))
  · exact hat
  · exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary
      (knownQubitUnitary_unitary (knownControlE p))
  · exact hab.symm
  · exact knownQubitUnitary_unitary (knownControlE p)
  · exact hbt
  · exact knownQubitUnitary_unitary (knownControlB p)
  · exact hbt
  · exact knownQubitUnitary_unitary (knownControlA p)

/-- The doubly controlled word applies the square of `knownQubitUnitary p` exactly when both
control bits are true. -/
private theorem sourceDoubleSteps_action {N : ℕ} (a b t : Fin N)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (p : KnownQubitAngles)
    (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourceDoubleSteps a b t p))
      (multiWireState t x φ) =
    multiWireState t x (ApplyGate
      (if x a && x b then knownQubitUnitary p * knownQubitUnitary p else 1) φ) := by
  let A : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlA p)
  let B : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlB p)
  let C : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlC p)
  let E : Matrix Bool Bool ℂ := knownQubitUnitary (knownControlE p)
  let z := Complex.exp ((p.delta : ℂ)*Complex.I)
  have hABC : A*B*C = 1 := (knownQubitControl_ABC_phase_factorization p).1
  have hV : z • (A*PauliX*B*PauliX*C) = knownQubitUnitary p :=
    (knownQubitControl_ABC_phase_factorization p).2.1
  have hE : E = diagonal (fun q : Bool => if q then z else 1) :=
    (knownQubitControl_ABC_phase_factorization p).2.2
  have hEstar : Eᴴ = diagonal (fun q : Bool => if q then star z else 1) := by
    rw [hE, Matrix.diagonal_conjTranspose]
    ext q r
    cases q <;> cases r <;> simp
  have hAA : Aᴴ*A=1 := by
    change (knownQubitUnitary (knownControlA p))ᴴ * knownQubitUnitary (knownControlA p) = 1
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (knownQubitUnitary_unitary (knownControlA p))
  have hBB : Bᴴ*B=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (knownQubitUnitary_unitary (knownControlB p))
  have hBB' : B*Bᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff.mp (knownQubitUnitary_unitary (knownControlB p))
  have hBC : B*C=Aᴴ := by
    have hh := congrArg (fun Q : Matrix Bool Bool ℂ => Aᴴ*Q) hABC
    simpa only [← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one] using! hh
  have hC : C=Bᴴ*Aᴴ := by
    have hh := congrArg (fun Q : Matrix Bool Bool ℂ => Bᴴ*Q) hBC
    simpa only [← Matrix.mul_assoc, hBB, Matrix.one_mul] using! hh
  have hCA : C*A=Bᴴ := by
    rw [hC, Matrix.mul_assoc, hAA, Matrix.mul_one]
  have hzz : z * star z = 1 := by
    have hn : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I p.delta
    rw [mul_comm]
    change (starRingEnd ℂ) z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have hzz' : star z * z = 1 := by rw [mul_comm, hzz]
  have hCA' (D : Matrix Bool Bool ℂ) : C*(A*D) = Bᴴ*D := by
    rw [← Matrix.mul_assoc, hCA]
  simp only [sourceDoubleSteps, reflectionCompile, List.map_cons, List.map_nil,
    run_gate, run_nil, reflectionGateMatrix]
  change ApplyGate (wireGate N t A) _ = _
  rw [show (knownQubitUnitary (knownControlE p))ᴴ =
    diagonal (fun q : Bool => if q then star z else 1) from hEstar]
  simp only [show knownQubitUnitary (knownControlC p) = C from rfl,
    show knownQubitUnitary (knownControlB p) = B from rfl,
    show knownQubitUnitary (knownControlE p) = E from rfl, hEstar, hE,
    multiWireState_phase a t hat, multiWireState_phase b t hbt,
    reflectionApplyGate_smul, multiWireState_single, multiWireState_cnot a t hat,
    multiWireState_cnot b t hbt, fibre_other_cnot b a t hab.symm hbt hat,
    Function.update_of_ne hab.symm, Function.update_self, Function.update_idem, Function.update_eq_self,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  cases ha : x a <;> cases hb : x b <;>
    simp only [ha, hb, Bool.false_and, Bool.true_and, Bool.xor_false, Bool.false_xor,
      Bool.xor_true, Bool.true_xor, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, one_smul, ← applyGate_mul, Matrix.one_mul, Matrix.mul_one,
      smul_smul]
  all_goals try simp only [← Matrix.mul_assoc, hBB, hBB', pauliX_mul_self,
    Matrix.one_mul, Matrix.mul_one, hABC, hzz, hzz', one_mul, one_smul]
  rw [← multiWireState_smul, ← applyGate_smul, ← hV]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hCA']

/-- Every doubly controlled qubit unitary has a legal, query-free implementation with at most
eight single-qubit gates and eight CNOTs [Barenco et al., Corollary 6.2][BarencoEtAl1995]. -/
theorem corollary6_2 : Corollary6_2 := by
  intro N c t hc hct U hU
  have hab : c 0 ≠ c 1 := fun he => by
    have hh := hc (by simp) (by simp) he
    omega
  obtain ⟨Vseq, hzero, hunit, hsquare, _⟩ := unitary_sqrt_chain_spec Bool U hU
  let p := knownQubitAnglesOfUnitary (Vseq 1)
  have hp : knownQubitUnitary p = Vseq 1 :=
    (knownQubitEuler_explicit_angles_cover_unitaries _ (hunit 1)).1
  have hs : knownQubitUnitary p * knownQubitUnitary p = U := by
    rw [hp, hsquare 0, hzero]
  refine ⟨sourceDoubleSteps (c 0) (c 1) t p,
    sourceDoubleSteps_legal _ _ _ hab (hct 0 (by omega)) (hct 1 (by omega)) p,
    queryCount_reflectionCompile _, gateCount_reflectionCompile _, ?_, ?_, ?_⟩
  · norm_num [sourceDoubleSteps]
  · norm_num [sourceDoubleSteps]
  · intro x φ
    rw [sourceDoubleSteps_action _ _ _ hab (hct 0 (by omega)) (hct 1 (by omega)), hs]
    simp [noWorkPrefixAnd, List.range_succ]

end Qatlib.Concepts.CircuitImpl.MultiControl
