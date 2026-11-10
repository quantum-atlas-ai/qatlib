/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.BlochProduct
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch

noncomputable def pairPauli {n : ℕ} (i j : Fin n) (a : Fin 3) : Matrix (Reg n) (Reg n) ℂ :=
  qubitTensor (fun h => if h=i ∨ h=j then pauliMatrix a else 1)

theorem product_trace {n : ℕ} (v : Fin n → Fin 3 → ℝ) : (productState v).trace=1 := by
  rw [productState,qubitTensor_trace]
  simp only [bloch_trace,Finset.prod_const_one]

theorem pair_product_trace {n : ℕ} (v : Fin n → Fin 3 → ℝ) (i j : Fin n) (hij : i≠j) (a : Fin 3) :
    (pairPauli i j a * productState v).trace = (v i a:ℂ)*(v j a:ℂ) := by
  rw [pairPauli,productState,qubitTensor_mul,qubitTensor_trace]
  have he : ∀ h : Fin n,
      ((if h=i ∨ h=j then pauliMatrix a else 1)*bloch (v h)).trace =
        (if h=i then (v i a:ℂ) else 1)*(if h=j then (v j a:ℂ) else 1) := by
    intro h
    by_cases hi : h=i
    · subst h
      simp only [true_or,ite_true,ite_false,hij,bloch_pauli_trace,mul_one]
    · by_cases hj : h=j
      · subst h
        simp only [or_true,ite_true,ite_false,hi,bloch_pauli_trace,one_mul]
      · simp only [hi,hj,false_or,ite_false,bloch_trace,one_mul]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

noncomputable def edgeOperator {n : ℕ} (i j : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  1-∑ a : Fin 3, pairPauli i j a

theorem edge_product_trace {n : ℕ} (v : Fin n → Fin 3 → ℝ) (i j : Fin n) (hij : i≠j) :
    (edgeOperator i j*productState v).trace =
      ((1-∑ a : Fin 3, v i a*v j a : ℝ):ℂ) := by
  rw [edgeOperator,Matrix.sub_mul,Matrix.trace_sub,Matrix.one_mul,product_trace,
    Matrix.sum_mul,Matrix.trace_sum]
  simp_rw [pair_product_trace v i j hij]
  push_cast
  rfl

noncomputable def qmcHamiltonian {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n × Fin n) (w : E → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  (-1/4:ℝ) • ∑ e, w e • edgeOperator (ends e).1 (ends e).2

noncomputable def energy {I : Type*} [Fintype I] (H ρ : Matrix I I ℂ) : ℝ := (H*ρ).trace.re

theorem qmc_product_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n × Fin n) (hends : ∀ e, (ends e).1≠(ends e).2) (w : E → ℝ)
    (v : Fin n → Fin 3 → ℝ) :
    energy (qmcHamiltonian ends w) (productState v) =
      -(1/4:ℝ)*∑ e, w e*(1-∑ a : Fin 3, v (ends e).1 a*v (ends e).2 a) := by
  simp only [energy,qmcHamiltonian,Matrix.smul_mul,Matrix.trace_smul,Matrix.sum_mul,Matrix.trace_sum]
  simp_rw [edge_product_trace v _ _ (hends _)]
  simp
  ring
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
