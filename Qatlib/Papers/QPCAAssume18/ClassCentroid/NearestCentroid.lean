/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SqEstimation.InnerProduct.SQInnerProductEstimation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct

variable {n d : ℕ}

def frobeniusEnergy (V : Matrix (Fin n) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ k, Complex.normSq (V i k)

def vectorEnergy (u : Fin d → ℂ) : ℝ :=
  ∑ k, Complex.normSq (u k)

def averageNormSq (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ) : ℝ :=
  vectorEnergy u + (1 / (n : ℝ)) * frobeniusEnergy V

def ncWeight (u : Fin d → ℂ) : Fin (n + 1) → ℂ :=
  fun j => Fin.cases (((Real.sqrt (vectorEnergy u) : ℝ)) : ℂ)
    (fun _ => -(((Real.sqrt (n : ℝ) : ℂ))⁻¹)) j

def ncMatrix (uhat : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ) :
    Matrix (Fin (n + 1)) (Fin d) ℂ :=
  fun j k => Fin.cases (uhat k) (fun i => ((Real.sqrt (n : ℝ) : ℂ))⁻¹ * V i k) j

theorem source_theorem6_reduction (uhat u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (hscale : ∀ k, ((Real.sqrt (vectorEnergy u) : ℝ) : ℂ) * uhat k = u k) :
    ∀ k, ∑ j, ncWeight u j * ncMatrix uhat V j k
      = u k - (n : ℂ)⁻¹ * ∑ i, V i k := by
  intro k
  rw [Fin.sum_univ_succ]
  simp only [ncWeight, ncMatrix, Fin.cases_zero, Fin.cases_succ]
  rw [hscale k]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((Real.sqrt (n : ℝ) : ℂ)) * ((Real.sqrt (n : ℝ) : ℂ)) = (n : ℂ) := by
    have h := Real.sq_sqrt (x := (n : ℝ)) hnpos.le
    calc ((Real.sqrt (n : ℝ) : ℂ)) * ((Real.sqrt (n : ℝ) : ℂ))
        = ((Real.sqrt (n : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      _ = (n : ℂ) := by rw [h]; norm_num
  have hcinv : ((Real.sqrt (n : ℝ) : ℂ))⁻¹ * ((Real.sqrt (n : ℝ) : ℂ))⁻¹ =
      ((n : ℂ))⁻¹ := by
    rw [← mul_inv, hcast]
  have hterm : ∀ i : Fin n,
      -(((Real.sqrt (n : ℝ) : ℂ))⁻¹) * (((Real.sqrt (n : ℝ) : ℂ))⁻¹ * V i k)
        = (-(((Real.sqrt (n : ℝ) : ℂ))⁻¹ * ((Real.sqrt (n : ℝ) : ℂ))⁻¹)) * V i k := by
    intro i
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hcinv]
  ring

theorem source_theorem6_objective (uhat u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (hscale : ∀ k, ((Real.sqrt (vectorEnergy u) : ℝ) : ℂ) * uhat k = u k) :
    ∑ k, Complex.normSq (∑ j, ncWeight u j * ncMatrix uhat V j k)
      = ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k) := by
  simp_rw [source_theorem6_reduction uhat u V hn hscale]

theorem source_theorem6_gram (w : Fin (n + 1) → ℂ)
    (M : Matrix (Fin (n + 1)) (Fin d) ℂ) :
    ∑ k, Complex.normSq (∑ j, w j * M j k)
      = (∑ j, ∑ j', w j * star (w j') * (∑ k, M j k * star (M j' k))).re := by
  have hoc : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = star z * z := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
  have hcomplex : ((∑ k, Complex.normSq (∑ j, w j * M j k) : ℝ) : ℂ)
      = ∑ j, ∑ j', w j * star (w j') * (∑ k, M j k * star (M j' k)) := by
    push_cast
    simp only [hoc]
    have lhs_eq : (∑ k : Fin d, star (∑ j, w j * M j k) * (∑ j, w j * M j k))
        = ∑ j : Fin (n + 1), ∑ j' : Fin (n + 1), ∑ k : Fin d,
            w j * star (w j') * (M j k * star (M j' k)) := by
      have flip : ∀ X : ℂ, star X * X = X * star X := fun X => mul_comm _ _
      have expand : (∑ k : Fin d, star (∑ j, w j * M j k) * (∑ j, w j * M j k))
          = ∑ k : Fin d, ∑ j : Fin (n + 1), ∑ j' : Fin (n + 1),
              (w j * M j k) * (star (M j' k) * star (w j')) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [flip (∑ j, w j * M j k)]
        simp only [star_sum, star_mul, Fintype.sum_mul_sum]
      have swap1 : (∑ k : Fin d, ∑ j : Fin (n + 1), ∑ j' : Fin (n + 1),
            (w j * M j k) * (star (M j' k) * star (w j')))
          = ∑ j : Fin (n + 1), ∑ k : Fin d, ∑ j' : Fin (n + 1),
              (w j * M j k) * (star (M j' k) * star (w j')) :=
        Finset.sum_comm
      have swap2 : (∑ j : Fin (n + 1), ∑ k : Fin d, ∑ j' : Fin (n + 1),
            (w j * M j k) * (star (M j' k) * star (w j')))
          = ∑ j : Fin (n + 1), ∑ j' : Fin (n + 1), ∑ k : Fin d,
              (w j * M j k) * (star (M j' k) * star (w j')) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact Finset.sum_comm
      have collapse : (∑ j : Fin (n + 1), ∑ j' : Fin (n + 1), ∑ k : Fin d,
            (w j * M j k) * (star (M j' k) * star (w j')))
          = ∑ j : Fin (n + 1), ∑ j' : Fin (n + 1), ∑ k : Fin d,
              w j * star (w j') * (M j k * star (M j' k)) := by
        refine Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun j' _ => Finset.sum_congr rfl (fun k _ => ?_)))
        ring
      exact expand.trans (swap1.trans (swap2.trans collapse))
    have rhs_eq : (∑ j : Fin (n + 1), ∑ j' : Fin (n + 1),
          w j * star (w j') * (∑ k : Fin d, M j k * star (M j' k)))
        = ∑ j : Fin (n + 1), ∑ j' : Fin (n + 1), ∑ k : Fin d,
            w j * star (w j') * (M j k * star (M j' k)) := by
      simp only [Finset.mul_sum]
    exact lhs_eq.trans rhs_eq.symm
  have := congrArg Complex.re hcomplex
  simpa using! this

theorem source_theorem6_average_norm (u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ)
    (hn : 0 < n) (hunit : ∀ i, ∑ k, Complex.normSq (V i k) = 1) :
    (∑ j : Fin (n + 1), Complex.normSq (ncWeight u j)) = averageNormSq u V := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hF : frobeniusEnergy V = (n : ℝ) := by
    unfold frobeniusEnergy
    simp [hunit]
  have hvec : 0 ≤ vectorEnergy u := by
    unfold vectorEnergy
    exact Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg (u k))
  have hS : Complex.normSq (((Real.sqrt (vectorEnergy u) : ℝ)) : ℂ) = vectorEnergy u := by
    rw [Complex.normSq_ofReal, ← sq]
    exact Real.sq_sqrt hvec
  have hnormsq : Complex.normSq (((Real.sqrt (n : ℝ) : ℂ))⁻¹) = (n : ℝ)⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hnpos.le]
  have hsum : (∑ _i : Fin n, Complex.normSq (-(((Real.sqrt (n : ℝ) : ℂ))⁻¹))) = 1 := by
    simp only [Complex.normSq_neg, hnormsq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [Fin.sum_univ_succ]
  simp only [ncWeight, Fin.cases_zero, Fin.cases_succ, hS, hsum]
  unfold averageNormSq
  rw [hF]
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  field_simp

def innerProductSamples (eps delta : ℝ) : ℝ :=
  54 / eps ^ 2 * Real.log (2 / delta)

theorem source_theorem6_block_and_sample_counts (eps delta : ℝ) :
    innerProductSamples eps delta
      = (6 * Real.log (2 / delta)) * (9 / eps ^ 2) := by
  unfold innerProductSamples
  ring

def innerProductCost (T eps delta : ℝ) : ℝ :=
  T * innerProductSamples eps delta

def algorithm4Cost (T Z eps delta : ℝ) : ℝ :=
  innerProductCost T (eps / (4 * Z)) delta

def theorem6Runtime (T Z eps delta : ℝ) : ℝ :=
  T * Z ^ 2 / eps ^ 2 * Real.log (1 / delta)

theorem source_theorem6_cost_eq (T Z eps delta : ℝ) (hZ : 0 < Z) (heps : 0 < eps) :
    algorithm4Cost T Z eps delta
      = 864 * (T * Z ^ 2 / eps ^ 2) * Real.log (2 / delta) := by
  unfold algorithm4Cost innerProductCost innerProductSamples
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hepsne : eps ≠ 0 := ne_of_gt heps
  field_simp
  ring

theorem source_theorem6_error_rescaling {eps Z normProd est target : ℝ}
    (hZ : 0 < Z) (hnorm : normProd = 4 * Z)
    (h : |est - target| ≤ (eps / (4 * Z)) * normProd) :
    |est - target| ≤ eps := by
  rw [hnorm] at h
  have h4 : (4 : ℝ) * Z ≠ 0 := by positivity
  rw [div_mul_cancel₀ eps h4] at h
  exact h

theorem source_theorem6_runtime (T Z eps delta : ℝ) (hT : 0 ≤ T) (hZ : 0 < Z)
    (heps : 0 < eps) (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2) :
    algorithm4Cost T Z eps delta ≤ 1728 * theorem6Runtime T Z eps delta := by
  rw [source_theorem6_cost_eq T Z eps delta hZ heps]
  have hlog : Real.log (2 / delta) ≤ 2 * Real.log (1 / delta) := by
    have hd : (0 : ℝ) < 1 / delta := by positivity
    have h : Real.log (2 / delta) = Real.log 2 + Real.log (1 / delta) := by
      rw [show (2 : ℝ) / delta = 2 * (1 / delta) by ring]
      rw [Real.log_mul (by norm_num) (ne_of_gt hd)]
    have hlog2 : Real.log 2 ≤ Real.log (1 / delta) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hdelta]
      nlinarith
    rw [h]
    linarith
  have hcoef : (0 : ℝ) ≤ 864 * (T * Z ^ 2 / eps ^ 2) := by positivity
  calc
    864 * (T * Z ^ 2 / eps ^ 2) * Real.log (2 / delta)
        ≤ 864 * (T * Z ^ 2 / eps ^ 2) * (2 * Real.log (1 / delta)) :=
          mul_le_mul_of_nonneg_left hlog hcoef
    _ = 1728 * theorem6Runtime T Z eps delta := by
          unfold theorem6Runtime
          ring

theorem source_inner_product_envelope_samples {X : Type} [Fintype X]
    (a : FiniteSQInput X) (v : X → ℂ) (m r : ℕ) (ω : Fin (2 * r + 1) → Fin m → X) :
    (sqRunCalls a v m r ω).count SQCall.sampleEnvelope = (2 * r + 1) * m := by
  rw [sqRunCalls_count]
  simp

def rowNorm {m d : ℕ} (M : Matrix (Fin m) (Fin d) ℂ) (k : Fin m) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (M k i))

def tensorA {n d : ℕ} (M : Matrix (Fin (n + 1)) (Fin d) ℂ) :
    Fin d → Fin (n + 1) → Fin (n + 1) → ℂ :=
  fun i j k => M j i * (((rowNorm M k : ℝ) : ℂ))

def tensorB {n d : ℕ} (w : Fin (n + 1) → ℂ) (M : Matrix (Fin (n + 1)) (Fin d) ℂ) :
    Fin d → Fin (n + 1) → Fin (n + 1) → ℂ :=
  fun i j k => star (w j) * w k * M k i / (((rowNorm M k : ℝ) : ℂ))

theorem ncMatrix_row_energy_succ {n d : ℕ} (uhat : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (i : Fin n) :
    (∑ k, Complex.normSq (ncMatrix uhat V i.succ k))
      = ((n : ℝ)⁻¹) * ∑ k, Complex.normSq (V i k) := by
  have hc : Complex.normSq (((Real.sqrt (n : ℝ) : ℝ) : ℂ)) = (n : ℝ) := by
    rw [Complex.normSq_ofReal, ← sq]
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hcinvsq : Complex.normSq (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹) = ((n : ℝ)⁻¹) := by
    rw [Complex.normSq_inv, hc]
  simp only [ncMatrix, Fin.cases_succ, Complex.normSq_mul, hcinvsq, ← Finset.mul_sum]

theorem source_theorem6_rowNorm_pos {n d : ℕ} (uhat : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (huhat : ∑ k, Complex.normSq (uhat k) = 1)
    (hunit : ∀ i, ∑ k, Complex.normSq (V i k) = 1) :
    ∀ k : Fin (n + 1), 0 < rowNorm (ncMatrix uhat V) k := by
  intro k
  refine Fin.cases (motive := fun k => 0 < rowNorm (ncMatrix uhat V) k) ?_ ?_ k
  · unfold rowNorm
    refine Real.sqrt_pos.mpr ?_
    simp only [ncMatrix, Fin.cases_zero]
    rw [huhat]
    norm_num
  · intro i
    unfold rowNorm
    refine Real.sqrt_pos.mpr ?_
    rw [ncMatrix_row_energy_succ uhat V i, hunit i]
    exact mul_pos (inv_pos.mpr (by exact_mod_cast hn)) (by norm_num)

theorem source_theorem6_tensor_inner (w : Fin (n + 1) → ℂ)
    (M : Matrix (Fin (n + 1)) (Fin d) ℂ) (hrow : ∀ k, 0 < rowNorm M k) :
    (∑ i, ∑ j, ∑ k, star (tensorA M i j k) * tensorB w M i j k)
      = ∑ j, ∑ k, w k * star (w j) * (∑ i, M k i * star (M j i)) := by
  have hterm : ∀ (i : Fin d) (j k : Fin (n + 1)),
      star (tensorA M i j k) * tensorB w M i j k
        = w k * star (w j) * (star (M j i) * M k i) := by
    intro i j k
    have hc : (((rowNorm M k : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hrow k))
    simp only [tensorA, tensorB, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem source_theorem6_tensor_energy_a (M : Matrix (Fin (n + 1)) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, Complex.normSq (tensorA M i j k)) = (frobeniusEnergy M) ^ 2 := by
  have hterm : ∀ (i : Fin d) (j k : Fin (n + 1)),
      Complex.normSq (tensorA M i j k)
        = Complex.normSq (M j i) * (rowNorm M k) ^ 2 := by
    intro i j k
    simp only [tensorA, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have hrowE : ∀ k : Fin (n + 1),
      (rowNorm M k) ^ 2 = ∑ i, Complex.normSq (M k i) := by
    intro k
    unfold rowNorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (M k i)))
  simp_rw [hterm, hrowE]
  rw [Finset.sum_comm]
  have hj : ∀ j : Fin (n + 1),
      (∑ i, ∑ k, Complex.normSq (M j i) * (∑ l, Complex.normSq (M k l)))
        = (∑ i, Complex.normSq (M j i)) * (∑ k, ∑ l, Complex.normSq (M k l)) := by
    intro j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  simp only [hj]
  rw [← Finset.sum_mul]
  unfold frobeniusEnergy
  rw [sq]

theorem source_theorem6_matrix_energy {n d : ℕ} (uhat : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (huhat : ∑ k, Complex.normSq (uhat k) = 1)
    (hunit : ∀ i, ∑ k, Complex.normSq (V i k) = 1) :
    frobeniusEnergy (ncMatrix uhat V) = 2 := by
  have hrow0 : (∑ k, Complex.normSq (ncMatrix uhat V 0 k)) = 1 := by
    simp only [ncMatrix, Fin.cases_zero]
    exact huhat
  have hrowsum : (∑ i : Fin n, ∑ k, Complex.normSq (ncMatrix uhat V i.succ k)) = 1 := by
    have h : ∀ i : Fin n, (∑ k, Complex.normSq (ncMatrix uhat V i.succ k))
        = ((n : ℝ)⁻¹) * (∑ k, Complex.normSq (V i k)) :=
      fun i => ncMatrix_row_energy_succ uhat V i
    simp only [h]
    rw [← Finset.mul_sum]
    have hV : (∑ i, ∑ k, Complex.normSq (V i k)) = (n : ℝ) := by
      simp only [hunit]
      simp
    rw [hV, inv_mul_cancel₀ (by exact_mod_cast hn.ne')]
  unfold frobeniusEnergy
  rw [Fin.sum_univ_succ]
  rw [hrow0, hrowsum]
  norm_num

theorem source_theorem6_tensor_energy_a_norm {n d : ℕ} (uhat : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (huhat : ∑ k, Complex.normSq (uhat k) = 1)
    (hunit : ∀ i, ∑ k, Complex.normSq (V i k) = 1) :
    (∑ i, ∑ j, ∑ k, Complex.normSq (tensorA (ncMatrix uhat V) i j k)) = 4 := by
  rw [source_theorem6_tensor_energy_a, source_theorem6_matrix_energy uhat V hn huhat hunit]
  norm_num

theorem source_theorem6_tensor_energy_b (w : Fin (n + 1) → ℂ)
    (M : Matrix (Fin (n + 1)) (Fin d) ℂ) (hrow : ∀ k, 0 < rowNorm M k) :
    (∑ i, ∑ j, ∑ k, Complex.normSq (tensorB w M i j k))
      = (∑ j, Complex.normSq (w j)) ^ 2 := by
  have hrowE : ∀ k : Fin (n + 1),
      (rowNorm M k) ^ 2 = ∑ i, Complex.normSq (M k i) := by
    intro k
    unfold rowNorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (M k i)))
  have hrowpos : ∀ k : Fin (n + 1), 0 < ∑ l, Complex.normSq (M k l) := by
    intro k
    have h1 := hrow k
    unfold rowNorm at h1
    have h2 : (∑ l, Complex.normSq (M k l))
        = (Real.sqrt (∑ l, Complex.normSq (M k l))) ^ 2 :=
      (Real.sq_sqrt (Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg (M k l)))).symm
    rw [h2, pow_two]
    exact mul_pos h1 h1
  have hterm : ∀ (i : Fin d) (j k : Fin (n + 1)),
      Complex.normSq (tensorB w M i j k)
        = Complex.normSq (w j) * (Complex.normSq (w k) * Complex.normSq (M k i)
            / (∑ l, Complex.normSq (M k l))) := by
    intro i j k
    have hconj : Complex.normSq (star (w j)) = Complex.normSq (w j) := by
      rw [Complex.star_def]
      exact Complex.normSq_conj (w j)
    have hE : (∑ l, Complex.normSq (M k l)) ≠ 0 := ne_of_gt (hrowpos k)
    simp only [tensorB, Complex.normSq_div, Complex.normSq_mul, hconj,
      Complex.normSq_ofReal, ← sq, hrowE]
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hj : ∀ j : Fin (n + 1),
      (∑ i, ∑ k, Complex.normSq (w j)
        * (Complex.normSq (w k) * Complex.normSq (M k i)
            / (∑ l, Complex.normSq (M k l))))
        = Complex.normSq (w j)
          * (∑ i, ∑ k, Complex.normSq (w k) * Complex.normSq (M k i)
            / (∑ l, Complex.normSq (M k l))) := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  simp only [hj]
  rw [← Finset.sum_mul]
  have hGswap : (∑ i, ∑ k, Complex.normSq (w k) * Complex.normSq (M k i)
        / (∑ l, Complex.normSq (M k l)))
      = (∑ k, ∑ i, Complex.normSq (w k) * Complex.normSq (M k i)
        / (∑ l, Complex.normSq (M k l))) := Finset.sum_comm
  rw [hGswap]
  have hk : ∀ k : Fin (n + 1),
      (∑ i, Complex.normSq (w k) * Complex.normSq (M k i)
        / (∑ l, Complex.normSq (M k l)))
        = Complex.normSq (w k) := by
    intro k
    have h1 : (∑ i, Complex.normSq (w k) * Complex.normSq (M k i)
        / (∑ l, Complex.normSq (M k l)))
        = Complex.normSq (w k)
          * ((∑ i, Complex.normSq (M k i)) / (∑ l, Complex.normSq (M k l))) := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [mul_div_assoc])
    rw [h1, div_self (ne_of_gt (hrowpos k)), mul_one]
  simp only [hk]
  rw [sq]

theorem source_theorem6_tensor_norm_product {n d : ℕ} (uhat u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (huhat : ∑ k, Complex.normSq (uhat k) = 1)
    (hunit : ∀ i, ∑ k, Complex.normSq (V i k) = 1) :
    (Real.sqrt (∑ i, ∑ j, ∑ k,
        Complex.normSq (tensorA (ncMatrix uhat V) i j k)))
      * (Real.sqrt (∑ i, ∑ j, ∑ k,
        Complex.normSq (tensorB (ncWeight u) (ncMatrix uhat V) i j k)))
      = 2 * averageNormSq u V := by
  have hrow := source_theorem6_rowNorm_pos uhat V hn huhat hunit
  have hEa := source_theorem6_tensor_energy_a_norm uhat V hn huhat hunit
  have hEb : (∑ i, ∑ j, ∑ k,
      Complex.normSq (tensorB (ncWeight u) (ncMatrix uhat V) i j k))
      = (averageNormSq u V) ^ 2 := by
    rw [source_theorem6_tensor_energy_b (ncWeight u) (ncMatrix uhat V) hrow,
      source_theorem6_average_norm u V hn hunit]
  have hZ : 0 ≤ averageNormSq u V := by
    unfold averageNormSq
    exact add_nonneg (Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg (u k)))
      (mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun i _ =>
          Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg (V i k)))))
  rw [hEa, hEb]
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt4, Real.sqrt_sq hZ]

def ncTensorA {n d : ℕ} (uhat : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ) :
    Fin d × Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun p => tensorA (ncMatrix uhat V) p.1 p.2.1 p.2.2

def ncTensorB {n d : ℕ} (u uhat : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ) :
    Fin d × Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun p => tensorB (ncWeight u) (ncMatrix uhat V) p.1 p.2.1 p.2.2

theorem source_theorem6_core_content {n d : ℕ}
    (x : FiniteSQInput (Fin d × Fin (n + 1) × Fin (n + 1)))
    (uhat u : Fin d → ℂ) (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (hscale : ∀ k, ((Real.sqrt (vectorEnergy u) : ℝ) : ℂ) * uhat k = u k)
    (huhat : ∑ k, Complex.normSq (uhat k) = 1)
    (hunit : ∀ i, ∑ k, Complex.normSq (V i k) = 1)
    (htarget : x.target = ncTensorA uhat V)
    (m r : ℕ) (eps : ℝ) (hm : 0 < m) (heps : 0 < eps)
    (hbudget : 64 * sqSquaredNorm x.envelope * sqSquaredNorm (ncTensorB u uhat V)
      ≤ (m : ℝ) * eps ^ 2) :
    (sqInnerTarget x.target (ncTensorB u uhat V)).re
      = ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)
    ∧ sqBadMass x (ncTensorB u uhat V) m r eps
      ≤ 2 * (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1)
    ∧ ∀ ω : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1)),
        ¬(eps < ‖sqMedian x (ncTensorB u uhat V) m r ω
            - sqInnerTarget x.target (ncTensorB u uhat V)‖) →
        |(sqMedian x (ncTensorB u uhat V) m r ω).re
          - ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)| ≤ eps := by
  have hrow := source_theorem6_rowNorm_pos uhat V hn huhat hunit
  have hA : (sqInnerTarget x.target (ncTensorB u uhat V)).re
      = ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k) := by
    rw [htarget]
    simp only [sqInnerTarget, ncTensorA, ncTensorB, Fintype.sum_prod_type]
    rw [source_theorem6_tensor_inner (ncWeight u) (ncMatrix uhat V) hrow]
    have hG : (∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
        ncWeight u k * star (ncWeight u j)
          * (∑ i, ncMatrix uhat V k i * star (ncMatrix uhat V j i)))
        = (∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
        ncWeight u j * star (ncWeight u k)
          * (∑ i, ncMatrix uhat V j i * star (ncMatrix uhat V k i))) := by
      rw [Finset.sum_comm]
    rw [hG]
    rw [← source_theorem6_gram (ncWeight u) (ncMatrix uhat V),
      ← source_theorem6_objective uhat u V hn hscale]
  refine ⟨hA,
    finite_sq_component_median_complex_guarantee
      (Fin d × Fin (n + 1) × Fin (n + 1)) x (ncTensorB u uhat V) m r eps
      hm heps hbudget, ?_⟩
  intro ω hω
  have h1 : ‖sqMedian x (ncTensorB u uhat V) m r ω
      - sqInnerTarget x.target (ncTensorB u uhat V)‖ ≤ eps := le_of_not_gt hω
  have h2 := (Complex.abs_re_le_norm (sqMedian x (ncTensorB u uhat V) m r ω
    - sqInnerTarget x.target (ncTensorB u uhat V))).trans h1
  rwa [Complex.sub_re, hA] at h2

end Qatlib.Papers.QPCAAssume18.ClassCentroid
