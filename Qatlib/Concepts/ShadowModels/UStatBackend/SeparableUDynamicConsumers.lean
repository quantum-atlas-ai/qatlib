/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.SeparableUDynamic
import Qatlib.Concepts.ShadowModels.FairBitRecords.SharpLocalPauliShadows
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.FairBitRecords
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.UStatBackend
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

private theorem sep_local_sample_cast {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (o : Fin n → Fin 3 × Bool) :
    ((localSparseSampleCounted w c o).1 : ℝ) = sparsePauliValue w c o := by
  rw [localSparseSampleCounted_spec]
  simp only [Rat.cast_sum,Rat.cast_mul,Rat.cast_prod,sparsePauliValue,tensorPauliValue]
  simp_rw [← localPauliValueQ_cast,localPauliValueQ]

theorem separable_u_actual_pauli_moment_consumer (n m r q : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin r → Fin q → Fin n → Option (Fin 3)) (c : Fin r → Fin q → ℚ)
    (hr : r ≤ m) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool, (tensorPauliLaw n ρ hρ).probOf ω *
      (separableUValue (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1) : ℝ)) =
      ∏ j : Fin r, (Matrix.trace (sparsePauliObservable (w j) (c j)*ρ)).re := by
  rw [separable_u_fresh_unbiased_consumer _ (tensorPauliLaw n ρ hρ) m r
    (fun j o => (localSparseSampleCounted (w j) (c j) o).1) hr]
  apply Finset.prod_congr rfl
  intro j _
  simp_rw [sep_local_sample_cast]
  exact (sparse_pauli_exact_energy_variance_and_bound n q ρ hρ (w j) (c j)).1

theorem separable_u_actual_pauli_second_moment (n m q : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin 2 → Fin q → Fin n → Option (Fin 3)) (c : Fin 2 → Fin q → ℚ)
    (hm : 2 ≤ m) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool, (tensorPauliLaw n ρ hρ).probOf ω *
      (separableUValue (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1) : ℝ)) =
      (Matrix.trace (sparsePauliObservable (w 0) (c 0)*ρ)).re*
      (Matrix.trace (sparsePauliObservable (w 1) (c 1)*ρ)).re := by
  simpa only [Fin.prod_univ_two] using separable_u_actual_pauli_moment_consumer n m 2 q ρ hρ w c hm

theorem separable_u_actual_pauli_third_moment (n m q : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin 3 → Fin q → Fin n → Option (Fin 3)) (c : Fin 3 → Fin q → ℚ)
    (hm : 3 ≤ m) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool, (tensorPauliLaw n ρ hρ).probOf ω *
      (separableUValue (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1) : ℝ)) =
      (Matrix.trace (sparsePauliObservable (w 0) (c 0)*ρ)).re*
      (Matrix.trace (sparsePauliObservable (w 1) (c 1)*ρ)).re*
      (Matrix.trace (sparsePauliObservable (w 2) (c 2)*ρ)).re := by
  simpa only [Fin.prod_univ_three] using
      separable_u_actual_pauli_moment_consumer n m 3 q ρ hρ w c hm

theorem separable_u_actual_pauli_variance_and_tail (n m r q : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin r → Fin q → Fin n → Option (Fin 3)) (c : Fin r → Fin q → ℚ)
    (B eps : ℝ) (hm : 0 < m) (hr : r ≤ m) (hB : 0 ≤ B) (heps : 0 < eps)
    (hb : ∀ x : Fin r → Fin n → Fin 3 × Bool,
      |∏ j : Fin r, ((localSparseSampleCounted (w j) (c j) (x j)).1 : ℝ)| ≤ B) :
    let μ := ∏ j : Fin r, (Matrix.trace (sparsePauliObservable (w j) (c j)*ρ)).re
    (∑ ω : Fin m → Fin n → Fin 3 × Bool, (tensorPauliLaw n ρ hρ).probOf ω *
      ((separableUValue (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1) : ℝ)-μ)^2) ≤
      4*(r : ℝ)^2*B^2/m ∧
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin n → Fin 3 × Bool => eps ≤
      |(separableUValue (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1) : ℝ)-μ|),
      (tensorPauliLaw n ρ hρ).probOf ω) ≤ 4*(r : ℝ)^2*B^2/(m*eps^2) := by
  have he (j : Fin r) :
      (∑ x : Fin n → Fin 3 × Bool, (tensorPauliLaw n ρ hρ).prob x *
        ((localSparseSampleCounted (w j) (c j) x).1 : ℝ)) =
        (Matrix.trace (sparsePauliObservable (w j) (c j)*ρ)).re := by
    simp_rw [sep_local_sample_cast]
    exact (sparse_pauli_exact_energy_variance_and_bound n q ρ hρ (w j) (c j)).1
  have h := separable_u_same_records_variance_and_tail _ (tensorPauliLaw n ρ hρ) m r
    (fun j x => (localSparseSampleCounted (w j) (c j) x).1) B eps hm hr hB heps hb
  simpa only [he] using h

theorem separable_u_actual_pauli_mean_and_program (n m r q : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin r → Fin q → Fin n → Option (Fin 3)) (c : Fin r → Fin q → ℚ)
    (hr : r ≤ m) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool, (tensorPauliLaw n ρ hρ).probOf ω *
      (separableUValue (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1) : ℝ)) =
      ∏ j : Fin r, (Matrix.trace (sparsePauliObservable (w j) (c j)*ρ)).re ∧
    ∀ ω : Fin m → Fin n → Fin 3 × Bool,
      (separableURun (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1)).2 = m*r*2^(r-1) ∧
      (separableURun (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1)).1.length = 2^r := by
  refine ⟨separable_u_actual_pauli_moment_consumer n m r q ρ hρ w c hr,fun ω => ?_⟩
  have hc :=
      separable_u_actual_fold_work m r (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1)
  exact ⟨hc.1.trans hc.2.1,
    (separable_u_actual_table_cells m r (fun i j => (localSparseSampleCounted (w j) (c j) (ω i)).1)).1⟩

end Qatlib.Concepts.ShadowModels.UStatBackend
