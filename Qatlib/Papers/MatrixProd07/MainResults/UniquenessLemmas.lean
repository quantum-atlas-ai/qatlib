/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.UniquenessLemmas

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Papers.MatrixProd07.MainResults
open Matrix
open scoped BigOperators ComplexConjugate

def muSeq {K : Type*} [Field K] (x : K) (lam : ℕ → K) : ℕ → K
  | 0 => 0
  | k + 1 => x * muSeq x lam k + lam k * x

theorem muSeq_closed {K : Type*} [Field K] (x : K) (lam : ℕ → K) :
    ∀ m : ℕ, muSeq x lam m = ∑ k ∈ Finset.range m, lam k * x ^ (m - k)
  | 0 => by simp [muSeq]
  | m + 1 => by
    rw [muSeq, muSeq_closed x lam m, Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < m := Finset.mem_range.mp hk
      rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
      ring
    · rw [show m + 1 - m = 1 by omega, pow_one]

theorem proposition1_linear_maps {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T S : V →ₗ[K] V) {n : ℕ} (hn : 2 ≤ n) (Y : ℕ → V) (lam : ℕ → K)
    (hstep : ∀ k, k + 1 < n → T (Y k) = S (Y (k + 1)))
    (hind : LinearIndependent K (fun k : Fin (n - 1) => Y k.val))
    (hlast : Y (n - 1) = ∑ k ∈ Finset.range (n - 1), lam k • Y k)
    (x : K) (hx : x ≠ 0)
    (hxlam : ∑ k ∈ Finset.range (n - 1), lam k * x ^ (n - 1 - k) = 1) :
    (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y k) ≠ 0 ∧
      T (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y k) =
        x⁻¹ • S (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y k) := by

  have hclast : muSeq x lam (n - 1) = 1 := by
    rw [muSeq_closed]; exact hxlam
  have hc1 : muSeq x lam 1 = lam 0 * x := by
    simp [muSeq]

  have hkey : (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y (k + 1))
      = ∑ k ∈ Finset.range (n - 1), (x⁻¹ * muSeq x lam (k + 1)) • Y k := by
    have hA : (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y (k + 1))
        = (∑ k ∈ Finset.range (n - 2), muSeq x lam (k + 1) • Y (k + 1))
          + muSeq x lam (n - 1) • Y (n - 1) := by
      rw [show n - 1 = (n - 2) + 1 by omega, Finset.sum_range_succ]
    have hB : (∑ k ∈ Finset.range (n - 1), (x⁻¹ * muSeq x lam (k + 1)) • Y k)
        = (∑ k ∈ Finset.range (n - 2), (x⁻¹ * muSeq x lam (k + 2)) • Y (k + 1))
          + (x⁻¹ * muSeq x lam 1) • Y 0 := by
      rw [show n - 1 = (n - 2) + 1 by omega, Finset.sum_range_succ']
    have hY : muSeq x lam (n - 1) • Y (n - 1)
        = (muSeq x lam (n - 1) * lam 0) • Y 0
          + ∑ k ∈ Finset.range (n - 2), (muSeq x lam (n - 1) * lam (k + 1)) • Y (k + 1) := by
      rw [hlast, Finset.smul_sum]
      simp only [smul_smul]
      rw [show n - 1 = (n - 2) + 1 by omega, Finset.sum_range_succ']
      rw [add_comm]
    have hconst : muSeq x lam (n - 1) * lam 0 = x⁻¹ * muSeq x lam 1 := by
      rw [hclast, hc1]; field_simp
    have hpt : ∀ k, muSeq x lam (k + 1) + muSeq x lam (n - 1) * lam (k + 1)
        = x⁻¹ * muSeq x lam (k + 2) := by
      intro k
      rw [hclast]
      have h2 : muSeq x lam (k + 2) = x * muSeq x lam (k + 1) + lam (k + 1) * x := by
        rw [show k + 2 = (k + 1) + 1 by omega, muSeq]
      rw [h2]
      field_simp
    have hsum : (∑ k ∈ Finset.range (n - 2), muSeq x lam (k + 1) • Y (k + 1))
          + (∑ k ∈ Finset.range (n - 2),
              (muSeq x lam (n - 1) * lam (k + 1)) • Y (k + 1))
        = ∑ k ∈ Finset.range (n - 2), (x⁻¹ * muSeq x lam (k + 2)) • Y (k + 1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← add_smul, hpt k]
    calc (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y (k + 1))
        = (∑ k ∈ Finset.range (n - 2), muSeq x lam (k + 1) • Y (k + 1))
            + ((muSeq x lam (n - 1) * lam 0) • Y 0
              + ∑ k ∈ Finset.range (n - 2),
                  (muSeq x lam (n - 1) * lam (k + 1)) • Y (k + 1)) := by
          rw [hA, hY]
      _ = ((∑ k ∈ Finset.range (n - 2), muSeq x lam (k + 1) • Y (k + 1))
            + ∑ k ∈ Finset.range (n - 2),
                (muSeq x lam (n - 1) * lam (k + 1)) • Y (k + 1))
            + (muSeq x lam (n - 1) * lam 0) • Y 0 := by abel
      _ = (∑ k ∈ Finset.range (n - 2), (x⁻¹ * muSeq x lam (k + 2)) • Y (k + 1))
            + (x⁻¹ * muSeq x lam 1) • Y 0 := by rw [hsum, hconst]
      _ = ∑ k ∈ Finset.range (n - 1), (x⁻¹ * muSeq x lam (k + 1)) • Y k := by
          rw [hB]
  refine ⟨?_, ?_⟩
  · intro hzero
    have hzero' : ∑ i : Fin (n - 1), muSeq x lam (i.val + 1) • Y i.val = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => muSeq x lam (k + 1) • Y k) (n - 1)]
      exact hzero
    have hcoef := (Fintype.linearIndependent_iff.mp hind
      (fun i : Fin (n - 1) => muSeq x lam (i.val + 1)) hzero') ⟨n - 2, by omega⟩
    rw [show (⟨n - 2, by omega⟩ : Fin (n - 1)).val = n - 2 from rfl,
      show n - 2 + 1 = n - 1 by omega, hclast] at hcoef
    exact one_ne_zero hcoef
  · have hTY : T (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y k)
        = S (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y (k + 1)) := by
      rw [map_sum, map_sum (f := fun k => muSeq x lam (k + 1) • Y (k + 1))]
      exact Finset.sum_congr rfl fun k hk => by
        rw [map_smul, hstep k (by simp only [Finset.mem_range] at hk; omega), ← map_smul]
    have hSc : x⁻¹ • S (∑ k ∈ Finset.range (n - 1), muSeq x lam (k + 1) • Y k)
        = S (∑ k ∈ Finset.range (n - 1), (x⁻¹ * muSeq x lam (k + 1)) • Y k) := by
      rw [← map_smul]
      congr 1
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
    rw [hTY, hSc, hkey]

def kronOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun i j => A i.1 j.1 * (if i.2 = j.2 then 1 else 0)

theorem mul_kronOne_apply {n : ℕ} (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (a c b d : Fin n) :
    (W * kronOne C) (a, c) (b, d) = ∑ k, W (a, c) (k, d) * C k b := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hterm : ∀ k2 : Fin n, W (a, c) (k, k2) * kronOne C (k, k2) (b, d)
      = if k2 = d then W (a, c) (k, d) * C k b else 0 := by
    intro k2
    by_cases hk2 : k2 = d
    · subst hk2; simp [kronOne]
    · simp [kronOne, hk2]
  simp only [hterm]
  rw [Finset.sum_ite_eq']
  simp

theorem kronOne_mul_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (a c b d : Fin n) :
    (kronOne B * W) (a, c) (b, d) = ∑ k, B a k * W (k, c) (b, d) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hterm : ∀ k2 : Fin n, kronOne B (a, c) (k, k2) * W (k, k2) (b, d)
      = if k2 = c then B a k * W (k, c) (b, d) else 0 := by
    intro k2
    by_cases hk2 : k2 = c
    · subst hk2; simp [kronOne]
    · have hk2' : c ≠ k2 := fun h => hk2 h.symm
      simp [kronOne, hk2, hk2']
  simp only [hterm]
  rw [Finset.sum_ite_eq']
  simp

theorem proposition2_kronecker_solutions {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ)
    (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    W * kronOne C = kronOne B * W ↔
      ∃ (m : ℕ) (X : Fin m → Matrix (Fin n) (Fin n) ℂ) (M : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ i, X i * C = B * X i) ∧
          ∀ (a c b d : Fin n), W (a, c) (b, d) = ∑ i, X i a b * M i c d := by
  let e : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv
  constructor
  · intro h
    refine ⟨n * n,
      fun i a b => W (a, (e.symm i).1) (b, (e.symm i).2),
      fun i => Matrix.single (e.symm i).1 (e.symm i).2 1, ?_, ?_⟩
    · intro i
      ext a b
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hh := congrFun (congrFun h (a, (e.symm i).1)) (b, (e.symm i).2)
      rw [mul_kronOne_apply, kronOne_mul_apply] at hh
      exact hh
    · intro a c b d
      have hsingle : ∀ i : Fin (n * n), Matrix.single (e.symm i).1 (e.symm i).2 (1 : ℂ) c d
          = if i = e (c, d) then 1 else 0 := by
        intro i
        rw [Matrix.single_apply]
        by_cases hi : i = e (c, d)
        · subst hi; simp
        · have hne : (e.symm i).1 = c ∧ (e.symm i).2 = d → False := by
            rintro ⟨h1, h2⟩
            apply hi
            have : e.symm i = (c, d) := Prod.ext h1 h2
            calc i = e (e.symm i) := (e.apply_symm_apply i).symm
              _ = e (c, d) := by rw [this]
          by_cases hcond : (e.symm i).1 = c ∧ (e.symm i).2 = d
          · exact absurd hcond hne
          · simp [hcond, hi]
      simp only [hsingle, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp [e]
  · rintro ⟨m, X, M, hX, hW⟩
    have hWmat : W = ∑ i, Matrix.of (fun (p q : Fin n × Fin n) =>
        X i p.1 q.1 * M i p.2 q.2) := by
      ext p q
      obtain ⟨a, c⟩ := p
      obtain ⟨b, d⟩ := q
      rw [Matrix.sum_apply]
      simp only [Matrix.of_apply]
      exact hW a c b d
    have hterm : ∀ i, (Matrix.of (fun (p q : Fin n × Fin n) =>
        X i p.1 q.1 * M i p.2 q.2) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) * kronOne C
        = kronOne B * Matrix.of (fun (p q : Fin n × Fin n) => X i p.1 q.1 * M i p.2 q.2) := by
      intro i
      ext p q
      obtain ⟨a, c⟩ := p
      obtain ⟨b, d⟩ := q
      rw [mul_kronOne_apply, kronOne_mul_apply]
      simp only [Matrix.of_apply]
      have hmul : (X i * C) a b = (B * X i) a b := by rw [hX i]
      rw [Matrix.mul_apply, Matrix.mul_apply] at hmul
      calc ∑ k, (X i a k * M i c d) * C k b
          = M i c d * ∑ k, X i a k * C k b := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = M i c d * ∑ k, B a k * X i k b := by rw [hmul]
        _ = ∑ k, B a k * (X i k b * M i c d) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hWmat, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i

end Qatlib.Papers.MatrixProd07.MainResults.UniquenessLemmas
