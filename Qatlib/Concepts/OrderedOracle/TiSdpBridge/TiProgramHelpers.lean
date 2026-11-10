/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialTransitionKernelTran
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.HspRecovery.CyclicRecovery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped Classical BigOperators

theorem ti_permutation_mul {N : ℕ} (e f : Equiv.Perm (Fin N)) :
    permMatrix e*permMatrix f=permMatrix (e*f) := by
  ext i j
  simp only [permMatrix,Matrix.mul_apply,Matrix.of_apply]
  rw [Finset.sum_eq_single (f j)]
  · simp [Equiv.Perm.mul_apply]
  · intro k _ hk
    simp [hk]
  · simp

theorem ti_translation_pow (n r : ℕ) [NeZero n] :
    (tiTranslation n)^r=permMatrix ((finShiftEquiv (2*n))^r) := by
  induction r with
  | zero =>
    ext i j
    simp [permMatrix,Matrix.one_apply]
  | succ r ih =>
    rw [pow_succ,ih,tiTranslation,ti_permutation_mul,pow_succ]

theorem ti_shift_pow_val (N r : ℕ) [NeZero N] (i : Fin N) :
    (((finShiftEquiv N)^r) i).val=(i.val+r)%N := by
  induction r with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ r ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    change ((((finShiftEquiv N)^r) i).val+1)%N=(i.val+(r+1))%N
    rw [ih,Nat.add_mod,Nat.mod_mod,← Nat.add_mod,add_assoc]

theorem ti_oracle_shift_bit (n : ℕ) [NeZero n] (j i : Fin (2*n)) :
    ospBit n j (((finShiftEquiv (2*n))^j.val) i)=ospBit n 0 i := by
  have hi : (0:ℤ) ≤ i.val := by positivity
  have hi' : (i.val:ℤ)<(2*n:ℕ) := by exact_mod_cast i.isLt
  have hmod : (i.val:ℤ)%(2*n:ℕ)=i.val := Int.emod_eq_of_lt hi hi'
  unfold ospBit
  change decide ((((((finShiftEquiv (2*n))^j.val) i).val:ℤ)-(j.val:ℤ))%(2*n:ℕ)<(n:ℤ)) =
    decide (((i.val:ℤ)-0)%(2*n:ℕ)<(n:ℤ))
  rw [ti_shift_pow_val,Int.natCast_mod,Nat.cast_add,Int.sub_emod,
    Int.emod_emod,← Int.sub_emod,add_sub_cancel_right,sub_zero,hmod]

theorem ti_oracle_translation (n : ℕ) [NeZero n] (j : Fin (2*n)) :
    PhaseOracle (ospBit n j)*(tiTranslation n)^j.val =
      (tiTranslation n)^j.val*PhaseOracle (ospBit n 0) := by
  rw [ti_translation_pow]
  ext i k
  simp only [PhaseOracle,Matrix.diagonal_mul,Matrix.mul_diagonal,permMatrix,Matrix.of_apply]
  by_cases h : i=((finShiftEquiv (2*n))^j.val) k
  · subst i
    rw [ti_oracle_shift_bit]
    simp
  · simp [h]

theorem ti_translation_uniform (n r : ℕ) [NeZero n] :
    ApplyGate ((tiTranslation n)^r) (Uniform (Fin (2*n)))=Uniform (Fin (2*n)) := by
  rw [ti_translation_pow]
  funext i
  rw [ti_apply_permutation]
  rfl

theorem ti_invariant_gate_member (n k : ℕ)
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ) (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (h : Step.gate A ∈ tiInvariantQueryWord n k U) :
    ∃ t ∈ Finset.Icc 1 k,A=U t := by
  simp only [tiInvariantQueryWord,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at h
  obtain ⟨r,hr,h⟩ := h
  rcases h with h | h
  · cases h
  · refine ⟨r+1,?_,Step.gate.inj h⟩
    simp only [Finset.mem_Icc]
    omega

theorem ti_invariant_word_unitary (n k : ℕ)
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (hu : ∀ t ∈ Finset.Icc 1 k,U t ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ) :
    IsUnitaryCircuit (tiInvariantQueryWord n k U) := by
  intro A hA
  obtain ⟨t,ht,rfl⟩ := ti_invariant_gate_member n k U A hA
  exact hu t ht

theorem ti_polynomial_word_commutes (n k : ℕ) [NeZero n] (p : ℕ → Fin n → ℂ)
    (A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ)
    (h : Step.gate A ∈ tiPolynomialQueryWord n k p) : tiTranslation n*A=A*tiTranslation n := by
  rw [ti_polynomial_word_eq_invariant] at h
  obtain ⟨t,_ht,rfl⟩ := ti_invariant_gate_member n k _ A h
  exact ti_transition_commutes n t _ _

theorem ti_polynomial_word_unitary (n k : ℕ) [NeZero n] (p : ℕ → Fin n → ℂ)
    (hm : ∀ t ∈ Finset.Icc 1 k,∀ z : ℂ,z^n=(-1:ℂ)^t →
      ‖tiPolyEval (p t) z‖=‖tiPolyEval (p (t-1)) z‖) :
    IsUnitaryCircuit (tiPolynomialQueryWord n k p) := by
  rw [ti_polynomial_word_eq_invariant]
  apply ti_invariant_word_unitary
  intro t ht
  apply ti_transition_unitary
  intro z hz
  exact (hm t ht z hz).symm

theorem ti_polynomial_run_zero (n k : ℕ) [NeZero n] (p : ℕ → Fin n → ℂ)
    (hp0 : p 0=tiDirichletVec n)
    (hm : ∀ t ∈ Finset.Icc 1 k,∀ z : ℂ,z^n=(-1:ℂ)^t →
      ‖tiPolyEval (p t) z‖=‖tiPolyEval (p (t-1)) z‖) :
    Run (PhaseOracle (ospBit n 0)) (tiPolynomialQueryWord n k p) (Uniform (Fin (2*n))) =
      tiPolynomialState n k (p k) := by
  induction k with
  | zero => simp [tiPolynomialQueryWord,hp0,ti_state_dirichlet]
  | succ k ih =>
    have hm' : ∀ t ∈ Finset.Icc 1 k,∀ z : ℂ,z^n=(-1:ℂ)^t →
        ‖tiPolyEval (p t) z‖=‖tiPolyEval (p (t-1)) z‖ := by
      intro t ht
      apply hm t
      simp only [Finset.mem_Icc] at ht ⊢
      omega
    rw [tiPolynomialQueryWord,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change Run (PhaseOracle (ospBit n 0)) (tiPolynomialQueryWord n k p ++
      [Step.query,Step.gate (tiPolynomialTransition n (k+1) (p k) (p (k+1)))])
      (Uniform (Fin (2*n))) = _
    rw [run_append,ih hm']
    change ApplyGate (tiPolynomialTransition n (k+1) (p k) (p (k+1)))
      (ApplyGate (PhaseOracle (ospBit n 0)) (tiPolynomialState n k (p k))) = _
    apply ti_transition_run n (k+1) (by omega)
    intro z hz
    simpa only [Nat.add_sub_cancel] using (hm (k+1) (by simp) z hz).symm

theorem ti_run_covariant (n : ℕ) [NeZero n] (j : Fin (2*n))
    (C : Circuit (Fin (2*n)))
    (hc : ∀ A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ,Step.gate A ∈ C →
      tiTranslation n*A=A*tiTranslation n) (ψ : QState (Fin (2*n))) :
    Run (PhaseOracle (ospBit n j)) C (ApplyGate ((tiTranslation n)^j.val) ψ) =
      ApplyGate ((tiTranslation n)^j.val) (Run (PhaseOracle (ospBit n 0)) C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    have htail : ∀ A : Matrix (Fin (2*n)) (Fin (2*n)) ℂ,Step.gate A ∈ C →
        tiTranslation n*A=A*tiTranslation n := by
      intro A hA
      exact hc A (List.mem_cons_of_mem s hA)
    cases s with
    | query =>
      change Run (PhaseOracle (ospBit n j)) C
        (ApplyGate (PhaseOracle (ospBit n j)) (ApplyGate ((tiTranslation n)^j.val) ψ)) = _
      rw [← applyGate_mul,ti_oracle_translation,applyGate_mul]
      exact ih htail (ApplyGate (PhaseOracle (ospBit n 0)) ψ)
    | gate A =>
      have hA : Commute (tiTranslation n) A := hc A List.mem_cons_self
      have hpow := (hA.pow_left j.val).eq
      change Run (PhaseOracle (ospBit n j)) C
          (ApplyGate A (ApplyGate ((tiTranslation n)^j.val) ψ)) = _
      rw [← applyGate_mul,← hpow,applyGate_mul]
      exact ih htail (ApplyGate A ψ)

theorem ti_polynomial_run_all (n k : ℕ) [NeZero n] (p : ℕ → Fin n → ℂ)
    (hp0 : p 0=tiDirichletVec n)
    (hm : ∀ t ∈ Finset.Icc 1 k,∀ z : ℂ,z^n=(-1:ℂ)^t →
      ‖tiPolyEval (p t) z‖=‖tiPolyEval (p (t-1)) z‖) (j : Fin (2*n)) :
    Run (PhaseOracle (ospBit n j)) (tiPolynomialQueryWord n k p) (Uniform (Fin (2*n))) =
      ApplyGate ((tiTranslation n)^j.val) (tiPolynomialState n k (p k)) := by
  have h := ti_run_covariant n j (tiPolynomialQueryWord n k p)
    (ti_polynomial_word_commutes n k p) (Uniform (Fin (2*n)))
  rw [ti_translation_uniform,ti_polynomial_run_zero n k p hp0 hm] at h
  exact h

theorem ti_polynomial_prepared_run (n k : ℕ) [NeZero n] (p : ℕ → Fin n → ℂ)
    (j : Fin (2*n)) :
    Run (PhaseOracle (ospBit n j)) (tiPolynomialPreparedWord n k p) (Ket 0) =
      Run (PhaseOracle (ospBit n j)) (tiPolynomialQueryWord n k p) (Uniform (Fin (2*n))) := by
  change Run (PhaseOracle (ospBit n j)) (tiPolynomialQueryWord n k p)
    (ApplyGate (QFTMatrix (2*n)) (Ket 0)) = _
  have hN : 0<2*n := by have := NeZero.pos n; omega
  have he : (⟨0,hN⟩ : Fin (2*n))=0 := by ext; simp
  have hq := applyGate_qftMatrix_ket_zero (2*n) hN
  rw [he] at hq
  rw [hq]

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
