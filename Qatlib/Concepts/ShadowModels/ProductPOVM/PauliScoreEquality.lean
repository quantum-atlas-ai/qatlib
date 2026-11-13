/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliOrbitPOVM
import Qatlib.Foundations.FiniteStats.BornEstimator.MeasurementScore

/-!
# Pauli orbit score equality

This module proves that squared Pauli expectations are invariant under Pauli conjugation.
Together with the register and Pauli-word cardinalities, this identifies the measurement score
of `pauliOrbitPOVM` with the state's `quadraticScore`. See [XuEtAl2026] for background.

## Main statements

* `pauli_exp_sq`: Pauli conjugation preserves squared Pauli expectations.
* `pauliOrbit_measurementScore`: orbit measurements realize the state's quadratic score.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
variable {V : Type*} [Fintype V]

/-- The density state obtained by conjugating `ρ` by the Pauli unitary indexed by `q`. -/
def pauliConjugateState (n : ℕ) (q : PauliWord n) (ρ : MState (Reg n)) : MState (Reg n) where
  M := ρ.M.conj (pauliUnitary n q).val
  nonneg := HermitianMat.conj_nonneg _ ρ.nonneg
  tr := by rw [HermitianMat.trace_conj_unitary,ρ.tr]

/-- Pauli conjugation preserves the square of the expectation of every Pauli observable. -/
theorem pauli_exp_sq (n : ℕ) (q w : PauliWord n) (ρ : MState (Reg n)) :
    ((pauliConjugateState n q ρ).exp_val (pauliObservable n w))^2=(ρ.exp_val (pauliObservable n w))^2 := by
  let s : ℝ :=
      (-1:ℝ)^(symplecticForm (symplecticX q,symplecticZ q) (symplecticX w,symplecticZ w)).val
  have hs : s^2=1 := by simp [s,pow_two,← mul_pow]
  have h := HermitianMat.inner_conj_unitary ρ.M (pauliObservable n w) (pauliUnitary n q)
  rw [pauli_conjugation_sign,real_inner_smul_right] at h
  have hh := congrArg (fun x : ℝ => x^2) h
  change (s*(pauliConjugateState n q ρ).exp_val (pauliObservable n w))^2=(ρ.exp_val (pauliObservable n w))^2 at hh
  rw [mul_pow,hs,one_mul] at hh
  exact hh

/-- The cardinality of the qubit register, cast to the reals, equals `qubitDimension n`. -/
theorem card_qubitRegister (n : ℕ) : (Fintype.card (Reg n):ℝ)=qubitDimension n := by
  simp [Reg,qubitDimension]

/-- The number of `n`-qubit Pauli words, cast to the reals, equals the square of `qubitDimension
n`. -/
theorem card_pauliWords (n : ℕ) : (Fintype.card (PauliWord n):ℝ)=qubitDimension n^2 := by
  have hc : Fintype.card Pauli1=4 := rfl
  simp only [PauliWord,Fintype.card_fun,Fintype.card_fin,hc,Nat.cast_pow,Nat.cast_ofNat,qubitDimension]
  rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
  norm_num

/-- The squared inner product of an orbit effect with a Pauli observable is the squared state
expectation divided by the squared register dimension. -/
theorem pauliOrbit_inner_sq (n : ℕ) (ρ : MState (Reg n)) (q w : PauliWord n) :
    ⟪(pauliOrbitPOVM n ρ).mats q,pauliObservable n w⟫^2=
      (qubitDimension n)⁻¹^2*(ρ.exp_val (pauliObservable n w))^2 := by
  change ⟪(qubitDimension n)⁻¹ • (pauliConjugateState n q ρ).M,pauliObservable n w⟫^2=_
  rw [real_inner_smul_left,mul_pow]
  rw [show ⟪(pauliConjugateState n q ρ).M,pauliObservable n w⟫^2=(ρ.exp_val (pauliObservable n w))^2 from pauli_exp_sq n q w ρ]

/-- The Pauli orbit POVM has measurement score equal to the generating state's weighted
quadratic score, providing the score realization used in [XuEtAl2026]. -/
theorem pauliOrbit_measurementScore (n : ℕ) (words : V → PauliWord n) (w : V → ℝ) (ρ : MState (Reg n)) :
    measurementScore (fun i => pauliObservable n (words i)) w (pauliOrbitPOVM n ρ)=
      quadraticScore (fun i => pauliObservable n (words i)) w ρ := by
  unfold measurementScore quadraticScore
  simp_rw [pauliOrbit_inner_sq,pauliOrbit_trace,card_qubitRegister]
  rw [mul_inv_cancel₀ (qubitDimension_pos n).ne']
  simp only [div_one]
  have hsum : (∑ i,w i*((qubitDimension n)⁻¹^2*(ρ.exp_val (pauliObservable n (words i)))^2))=
      (qubitDimension n)⁻¹^2*(∑ i,w i*(ρ.exp_val (pauliObservable n (words i)))^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hsum]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pauliWords]
  have hd := (qubitDimension_pos n).ne'
  field_simp

end Qatlib.Concepts.ShadowModels.ProductPOVM
