/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSingValue19.AlgorithmApps.LcuQsvtStackDefs

/-!
# LCU approximation and compilation

This module develops Bernstein approximation estimates and connects polynomial responses to
singular transforms in the setting of [GilyenSuLowWiebe2019]. The results `lcu_cor10_solver` and
`lcu_machine_ledger` complement the approximation bounds with phase synthesis and machine
accounting; the module also verifies phase table recovery, source recurrence parity, degree zero
behavior, and the resource counts of a concrete dynamic machine word.

## Main statements

* `lcu_bernstein_error_le`: Bounds the approximation error using a modulus of continuity.
* `lcu_application_chain`: Constructs an approximate block encoding with exact query and gate
  counts.
* `lcu_cor10_solver`: Produces phases and a real table with a synthesis cost bound.
* `lcu_machine_ledger`: Computes the dynamic machine word resource counters.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open Matrix Polynomial
open Qatlib SignalProcessing Encoding
open scoped BigOperators Matrix.Norms.L2Operator

/-- Splits a weighted binomial sum of order n + 1 into two order n sums by Pascal's identity. -/
private theorem lcu_pascal (w : ℝ → ℝ) (u v : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * (w i * u ^ i * v ^ (n + 1 - i)))
      = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (w i * u ^ i * v ^ (n - i))) * v
        + u * (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ i * v ^ (n - i))) := by
  have hrec := Finset.sum_choose_succ_mul (R := ℝ) (fun i j => w i * u ^ i * v ^ j) n
  have key : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (w i * u ^ i * v ^ (n + 1 - i))
        = ((n.choose i : ℝ) * (w i * u ^ i * v ^ (n - i))) * v := by
    intro i hi
    have hle : i ≤ n := by
      have hlt : i < n + 1 := Finset.mem_range.mp hi
      omega
    have hshift : n + 1 - i = n - i + 1 := by omega
    rw [hshift, pow_succ]
    ring
  have key2 : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ (i + 1) * v ^ (n - i))
        = u * ((n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ i * v ^ (n - i))) := by
    intro i _hi
    rw [pow_succ]
    ring
  calc
    (∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * (w i * u ^ i * v ^ (n + 1 - i)))
        = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (w i * u ^ i * v ^ (n + 1 - i)))
          + (∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ (i + 1) * v ^ (n - i))) := by
          rw [hrec]
    _ = ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (w i * u ^ i * v ^ (n - i))) * v)
          + (∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ (i + 1) * v ^ (n - i))) := by
          rw [Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
            (f := fun i => (n.choose i : ℝ) * (w i * u ^ i * v ^ (n + 1 - i)))
            (g := fun i => ((n.choose i : ℝ) * (w i * u ^ i * v ^ (n - i))) * v) rfl key]
          rw [← Finset.sum_mul]
    _ = ((∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (w i * u ^ i * v ^ (n - i))) * v)
          + (u * (∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ i * v ^ (n - i)))) := by
          rw [Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
            (f := fun i => (n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ (i + 1) * v ^ (n - i)))
            (g := fun i => u * ((n.choose i : ℝ) * (w (i + 1 : ℕ) * u ^ i * v ^ (n - i)))) rfl key2]
          rw [Finset.mul_sum]

/-- The binomial sum with parameters u and v equals (u + v)^n. -/
theorem lcu_binomial_sum (u v : ℝ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (u ^ k * v ^ (n - k))) = (u + v) ^ n := by
  intro n
  induction n with
  | zero =>
      have h : (∑ k ∈ Finset.range (0 + 1), (Nat.choose 0 k : ℝ) * (u ^ k * v ^ (0 - k))) = 1 := by
        simp
      simpa using! h
  | succ m ih =>
      have hp := lcu_pascal (fun _ => (1 : ℝ)) u v m
      have hmain : (∑ k ∈ Finset.range (m + 2),
          ((m + 1).choose k : ℝ) * (1 * u ^ k * v ^ (m + 1 - k))) = (u + v) ^ (m + 1) := by
        rw [hp]
        simp only [one_mul]
        rw [ih]
        rw [pow_succ]
        ring
      simpa only [one_mul] using! hmain

/-- If u + v = 1, the binomial sum of order n is one. -/
theorem lcu_binomial_sum_one (u v : ℝ) (huv : u + v = 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (u ^ k * v ^ (n - k)) = 1 := by
  have h := lcu_binomial_sum u v n
  rw [huv, one_pow] at h
  exact h

/-- If u + v = 1 and n ≥ 1, the first weighted binomial moment equals nu. -/
theorem lcu_binomial_moment1_one (u v : ℝ) (huv : u + v = 1) :
    ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((k : ℝ) * u ^ k * v ^ (n - k))) = n * u := by
  intro n
  induction n with
  | zero => omega
  | succ m ih =>
      intro hn
      by_cases hm : m = 0
      · subst hm
        have hb : (∑ k ∈ Finset.range (1 + 1),
              (Nat.choose 1 k : ℝ) * ((k : ℝ) * u ^ k * v ^ (1 - k))) = u := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp only [Nat.choose_one_right, Nat.choose_zero_right, Finset.sum_range_zero,
            mul_one, one_mul, zero_mul, mul_zero, one_pow, zero_pow]
          ring
        rw [hb]
        ring
      · have hm1 : 1 ≤ m := by omega
        have hp := lcu_pascal (fun i => (i : ℝ)) u v m
        have hsplit : (∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ((i + 1 : ℕ) * u ^ i * v ^ (m - i)))
            = (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i)))
              + (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) := by
          calc
            (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ((i + 1 : ℕ) * u ^ i * v ^ (m - i)))
                = ∑ i ∈ Finset.range (m + 1),
                    ((m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i))
                      + (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) := by
                  refine Finset.sum_congr (s₁ := Finset.range (m + 1))
                    (s₂ := Finset.range (m + 1))
                    (f := fun i => (m.choose i : ℝ) * ((i + 1 : ℕ) * u ^ i * v ^ (m - i)))
                    (g := fun i => (m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i))
                      + (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) rfl ?_
                  intro i _
                  simp only [Nat.cast_add, Nat.cast_one]
                  ring
            _ = _ := Finset.sum_add_distrib
        rw [hsplit] at hp
        simp only [one_mul] at hp
        have hS := lcu_binomial_sum_one u v huv m
        rw [ih hm1, hS] at hp
        calc
          (∑ k ∈ Finset.range (m + 2),
              ((m + 1).choose k : ℝ) * ((k : ℝ) * u ^ k * v ^ (m + 1 - k)))
              = (m * u) * v + u * ((m * u) + 1) := hp
          _ = ↑(m + 1) * u := by
            rw [show (m * u) * v + u * ((m * u) + 1) = m * u * (u + v) + u by ring]
            rw [huv]
            simp only [Nat.cast_add, Nat.cast_one]
            ring

/-- If u + v = 1 and n ≥ 1, the second weighted binomial moment equals nu + n(n − 1)u². -/
theorem lcu_binomial_moment2_one (u v : ℝ) (huv : u + v = 1) :
    ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((k : ℝ) ^ 2 * u ^ k * v ^ (n - k)))
        = n * u + n * (n - 1) * u ^ 2 := by
  intro n
  induction n with
  | zero => omega
  | succ m ih =>
      intro hn
      by_cases hm : m = 0
      · subst hm
        have hb : (∑ k ∈ Finset.range (1 + 1),
              (Nat.choose 1 k : ℝ) * ((k : ℝ) ^ 2 * u ^ k * v ^ (1 - k))) = u := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp only [Nat.choose_one_right, Nat.choose_zero_right, Finset.sum_range_zero,
            mul_one, one_mul, zero_mul, mul_zero, one_pow, zero_pow]
          ring
        rw [hb]
        ring
      · have hm1 : 1 ≤ m := by omega
        have hp := lcu_pascal (fun i => (i : ℝ) ^ 2) u v m
        have hsplit : (∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ((i + 1 : ℕ) ^ 2 * u ^ i * v ^ (m - i)))
            = (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ((i : ℝ) ^ 2 * u ^ i * v ^ (m - i)))
              + 2 * (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i)))
              + (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) := by
          calc
            (∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * ((i + 1 : ℕ) ^ 2 * u ^ i * v ^ (m - i)))
                = ∑ i ∈ Finset.range (m + 1),
                    ((m.choose i : ℝ) * ((i : ℝ) ^ 2 * u ^ i * v ^ (m - i))
                      + 2 * ((m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i)))
                      + (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) := by
                  refine Finset.sum_congr (s₁ := Finset.range (m + 1))
                    (s₂ := Finset.range (m + 1))
                    (f := fun i => (m.choose i : ℝ) * ((i + 1 : ℕ) ^ 2 * u ^ i * v ^ (m - i)))
                    (g := fun i => (m.choose i : ℝ) * ((i : ℝ) ^ 2 * u ^ i * v ^ (m - i))
                      + 2 * ((m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i)))
                      + (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) rfl ?_
                  intro i _
                  simp only [Nat.cast_add, Nat.cast_one]
                  ring
            _ = (∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * ((i : ℝ) ^ 2 * u ^ i * v ^ (m - i)))
                + 2 * (∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * ((i : ℝ) * u ^ i * v ^ (m - i)))
                + (∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * (1 * u ^ i * v ^ (m - i))) := by
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  rw [← Finset.mul_sum]
            _ = _ := rfl
        rw [hsplit] at hp
        simp only [one_mul] at hp
        have hS := lcu_binomial_sum_one u v huv m
        have hM1 := lcu_binomial_moment1_one u v huv m hm1
        rw [ih hm1, hM1, hS] at hp
        calc
          (∑ k ∈ Finset.range (m + 2),
              ((m + 1).choose k : ℝ) * ((k : ℝ) ^ 2 * u ^ k * v ^ (m + 1 - k)))
              = (m * u + m * (m - 1) * u ^ 2) * v
                + u * ((m * u + m * (m - 1) * u ^ 2) + 2 * (m * u) + 1) := hp
          _ = ↑(m + 1) * u + ↑(m + 1) * (↑(m + 1) - 1) * u ^ 2 := by
            rw [show (m * u + m * (m - 1) * u ^ 2) * v
                + u * ((m * u + m * (m - 1) * u ^ 2) + 2 * (m * u) + 1)
                = m * u * (u + v) + m * (m - 1) * u ^ 2 * (u + v) + 2 * m * u ^ 2 + u by ring]
            rw [huv]
            simp only [Nat.cast_add, Nat.cast_one]
            ring

/-- The Bernstein weights at indices zero through n sum to one. -/
theorem lcu_weight_sum (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k = 1 := by
  have huv : (x + 1) / 2 + (1 - x) / 2 = 1 := by ring
  have h := lcu_binomial_sum_one ((x + 1) / 2) ((1 - x) / 2) huv n
  calc
    (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k)
        = ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)) := by
          refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
            (f := fun k => lcuBernsteinWeight n x k)
            (g := fun k => (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k))) rfl ?_
          intro k _
          rfl
    _ = 1 := h

/-- Every Bernstein weight is nonnegative for x ∈ [−1, 1]. -/
theorem lcu_weight_nonneg (n : ℕ) (x : ℝ) (k : ℕ) (hx : -1 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ lcuBernsteinWeight n x k := by
  unfold lcuBernsteinWeight
  have hc : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg (n.choose k)
  have hu : (0 : ℝ) ≤ (x + 1) / 2 := by linarith
  have hv : (0 : ℝ) ≤ (1 - x) / 2 := by linarith
  exact mul_nonneg hc (mul_nonneg (pow_nonneg hu _) (pow_nonneg hv _))

/-- For positive n, the Bernstein weighted squared distance of the nodes from x is (1 − x²)/n. -/
theorem lcu_weight_sq_moment (n : ℕ) (x : ℝ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2
      = (1 - x ^ 2) / n := by
  have huv : (x + 1) / 2 + (1 - x) / 2 = 1 := by ring
  have hS0 := lcu_binomial_sum_one ((x + 1) / 2) ((1 - x) / 2) huv n
  have hM10 := lcu_binomial_moment1_one ((x + 1) / 2) ((1 - x) / 2) huv n (Nat.succ_le_of_lt hn)
  have hM20 := lcu_binomial_moment2_one ((x + 1) / 2) ((1 - x) / 2) huv n (Nat.succ_le_of_lt hn)
  have hconv0 : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k)
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)) := by
    refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
      (f := fun k => lcuBernsteinWeight n x k)
      (g := fun k => (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k))) rfl ?_
    intro k _
    rfl
  have hconv1 : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k * (k : ℝ))
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * ((k : ℝ) * ((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)) := by
    refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
      (f := fun k => lcuBernsteinWeight n x k * (k : ℝ))
      (g := fun k => (n.choose k : ℝ) * ((k : ℝ) * ((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)))
        rfl ?_
    intro k _
    unfold lcuBernsteinWeight
    ring
  have hconv2 : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k * (k : ℝ) ^ 2)
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * ((k : ℝ) ^ 2 * ((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)) := by
    refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
      (f := fun k => lcuBernsteinWeight n x k * (k : ℝ) ^ 2)
      (g := fun k => (n.choose k : ℝ) * ((k : ℝ) ^ 2 * ((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)))
        rfl ?_
    intro k _
    unfold lcuBernsteinWeight
    ring
  have hconv0 : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k)
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k)) := by
    refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
      (f := fun k => lcuBernsteinWeight n x k)
      (g := fun k => (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k))) rfl ?_
    intro k _
    unfold lcuBernsteinWeight
    ring
  have hS : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k) = 1 := by
    rw [hconv0]
    exact hS0
  have hM1 : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k * (k : ℝ))
      = (n : ℝ) * ((x + 1) / 2) := by
    rw [hconv1]
    exact hM10
  have hM2 : (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k * (k : ℝ) ^ 2)
      = (n : ℝ) * ((x + 1) / 2) + (n : ℝ) * ((n : ℕ) - 1) * ((x + 1) / 2) ^ 2 := by
    rw [hconv2]
    exact hM20
  have hnode : ∀ k ∈ Finset.range (n + 1),
      lcuBernsteinNode n k - x = 2 * ((k : ℝ) / (n : ℝ) - (x + 1) / 2) := by
    intro k _hk
    unfold lcuBernsteinNode
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
    ring
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hexp : (∑ k ∈ Finset.range (n + 1),
        lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2)
      = (4 / (n : ℝ) ^ 2) * (∑ k ∈ Finset.range (n + 1),
            lcuBernsteinWeight n x k * (k : ℝ) ^ 2)
        - (8 * ((x + 1) / 2) / (n : ℝ)) * (∑ k ∈ Finset.range (n + 1),
            lcuBernsteinWeight n x k * (k : ℝ))
        + (4 * ((x + 1) / 2) ^ 2) * (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k) := by
    calc
      (∑ k ∈ Finset.range (n + 1),
          lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2)
          = ∑ k ∈ Finset.range (n + 1),
              ((4 / (n : ℝ) ^ 2) * (lcuBernsteinWeight n x k * (k : ℝ) ^ 2)
                - (8 * ((x + 1) / 2) / (n : ℝ)) * (lcuBernsteinWeight n x k * (k : ℝ))
                + (4 * ((x + 1) / 2) ^ 2) * lcuBernsteinWeight n x k) := by
            refine Finset.sum_congr (s₁ := Finset.range (n + 1))
              (s₂ := Finset.range (n + 1))
              (f := fun k => lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2)
              (g := fun k => (4 / (n : ℝ) ^ 2) * (lcuBernsteinWeight n x k * (k : ℝ) ^ 2)
                - (8 * ((x + 1) / 2) / (n : ℝ)) * (lcuBernsteinWeight n x k * (k : ℝ))
                + (4 * ((x + 1) / 2) ^ 2) * lcuBernsteinWeight n x k) rfl ?_
            intro k hk
            simp only [hnode k hk]
            field_simp [hn0]
            ring
      _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp, hM2, hM1, hS]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

/-- Evaluating the Bernstein polynomial gives the weighted sum of the target function values at
its nodes. -/
theorem lcu_bernstein_eval (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (lcuBernsteinPoly n f).eval (x : ℂ)
      = ∑ k ∈ Finset.range (n + 1), (lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k) := by
  have hkey : ∀ k ∈ Finset.range (n + 1),
      (((n.choose k : ℕ) : ℂ) * f (lcuBernsteinNode n k))
          * ((1 / 2 : ℂ) * (x + 1 : ℂ)) ^ k * ((1 / 2 : ℂ) * (1 - x : ℂ)) ^ (n - k)
        = (lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k) := by
    intro k _
    simp only [lcuBernsteinWeight]
    push_cast
    rw [mul_pow, div_pow]
    rw [div_pow]
    simp only [one_pow]
    ring
  simp only [lcuBernsteinPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one]
  refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
    (f := fun k => (((n.choose k : ℕ) : ℂ) * f (lcuBernsteinNode n k))
        * ((1 / 2 : ℂ) * (x + 1 : ℂ)) ^ k * ((1 / 2 : ℂ) * (1 - x : ℂ)) ^ (n - k))
    (g := fun k => (lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k)) rfl ?_
  intro k hk
  exact hkey k hk

/-- The Bernstein grid contains n + 1 entries. -/
theorem lcuBernsteinGrid_length (n : ℕ) : (lcuBernsteinGrid n).length = n + 1 := by
  simp [lcuBernsteinGrid]

/-- For positive degree n and scale s, the Bernstein approximation error on [−1, 1] is at most
ω(s) + ω(2)/(ns²) when ω is a modulus of continuity. -/
theorem lcu_bernstein_error_le {f : ℝ → ℂ} {ω : ℝ → ℝ}
    (hmod : ModulusOfContinuity f ω) (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(lcuBernsteinPoly n f).eval (x : ℂ) - f x‖
      ≤ ω s + ω 2 / (n * s ^ 2) := by
  have hωs : 0 ≤ ω s := by
    have h1 : 0 ≤ s := le_of_lt hs
    have h := hmod.mono h1
    rw [hmod.at_zero] at h
    exact h
  have hω2 : 0 ≤ ω 2 := by
    have h1 : (0 : ℝ) ≤ 2 := by norm_num
    have h := hmod.mono h1
    rw [hmod.at_zero] at h
    exact h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnode : ∀ k ∈ Finset.range (n + 1), lcuBernsteinNode n k ∈ Set.Icc (-1 : ℝ) 1 := by
    intro k hk
    have hle : k ≤ n := by
      have hlt : k < n + 1 := Finset.mem_range.mp hk
      omega
    have hkn0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
    have hkn1 : (k : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hle
    have hform : lcuBernsteinNode n k = -1 + 2 * ((k : ℝ) / (n : ℝ)) := by
      unfold lcuBernsteinNode
      field_simp [hn0]
    constructor
    · rw [hform]
      linarith
    · rw [hform]
      linarith
  have hbound : ∀ k ∈ Finset.range (n + 1),
      ω |lcuBernsteinNode n k - x| ≤ ω s + ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2 := by
    intro k hk
    have hnode' := hnode k hk
    have hdist : |lcuBernsteinNode n k - x| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hnode'.1, hnode'.2, hx.1, hx.2]
    by_cases hle : |lcuBernsteinNode n k - x| ≤ s
    · have hmono : ω |lcuBernsteinNode n k - x| ≤ ω s := hmod.mono hle
      have hsq : (0 : ℝ) ≤ (lcuBernsteinNode n k - x) ^ 2 := by positivity
      have hterm : (0 : ℝ) ≤ ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2 := by
        positivity
      linarith
    · have hgt : s < |lcuBernsteinNode n k - x| := lt_of_not_ge hle
      have hsq : s ^ 2 ≤ (lcuBernsteinNode n k - x) ^ 2 := by
        have h1 : s ≤ |lcuBernsteinNode n k - x| := le_of_lt hgt
        have habs : |s| ≤ |lcuBernsteinNode n k - x| := by
          rw [abs_of_nonneg (le_of_lt hs)]
          exact h1
        have h2 := (sq_le_sq₀ (abs_nonneg s) (abs_nonneg _)).mpr habs
        simpa [sq_abs] using! h2
      have hterm : ω 2 ≤ ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have hmul : ω 2 * s ^ 2 ≤ ω 2 * (lcuBernsteinNode n k - x) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hω2
        nlinarith
      have hmono : ω |lcuBernsteinNode n k - x| ≤ ω 2 := hmod.mono hdist
      linarith
  have hdom : ∀ k ∈ Finset.range (n + 1),
      ‖f (lcuBernsteinNode n k) - f x‖ ≤ ω |lcuBernsteinNode n k - x| := by
    intro k hk
    have hnode' := hnode k hk
    have h := hmod.dominates (lcuBernsteinNode n k) x hnode' hx
    simpa [norm_sub_rev] using! h
  have hstep : ∀ k ∈ Finset.range (n + 1),
      lcuBernsteinWeight n x k * ‖f (lcuBernsteinNode n k) - f x‖
        ≤ lcuBernsteinWeight n x k
          * (ω s + ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2) := by
    intro k hk
    have hw := lcu_weight_nonneg n x k hx.1 hx.2
    exact mul_le_mul_of_nonneg_left (by linarith [hdom k hk, hbound k hk]) hw
  have hnorm : ‖∑ k ∈ Finset.range (n + 1),
        (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x)‖
      ≤ ∑ k ∈ Finset.range (n + 1),
        lcuBernsteinWeight n x k * ‖f (lcuBernsteinNode n k) - f x‖ := by
    have h1 := norm_sum_le (Finset.range (n + 1))
      (fun k => (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x))
    refine h1.trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Complex.norm_mul, Complex.norm_of_nonneg (lcu_weight_nonneg n x k hx.1 hx.2)]
  have hW := lcu_weight_sum n x
  have hsq := lcu_weight_sq_moment n x hn
  have hsum : ∑ k ∈ Finset.range (n + 1),
        lcuBernsteinWeight n x k * ‖f (lcuBernsteinNode n k) - f x‖
      ≤ ω s + ω 2 / (n * s ^ 2) := by
    calc
      (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k * ‖f (lcuBernsteinNode n k) - f x‖)
          ≤ ∑ k ∈ Finset.range (n + 1),
              lcuBernsteinWeight n x k
                * (ω s + ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2) := by
            exact Finset.sum_le_sum fun k hk => hstep k hk
      _ = ω s * (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k)
          + (ω 2 / s ^ 2) * (∑ k ∈ Finset.range (n + 1),
            lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2) := by
            calc
              (∑ k ∈ Finset.range (n + 1),
                  lcuBernsteinWeight n x k
                    * (ω s + ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2))
                  = ∑ k ∈ Finset.range (n + 1),
                      (ω s * lcuBernsteinWeight n x k
                        + (ω 2 / s ^ 2)
                          * (lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2)) := by
                    refine Finset.sum_congr (s₁ := Finset.range (n + 1))
                      (s₂ := Finset.range (n + 1))
                      (f := fun k => lcuBernsteinWeight n x k
                        * (ω s + ω 2 * (lcuBernsteinNode n k - x) ^ 2 / s ^ 2))
                      (g := fun k => ω s * lcuBernsteinWeight n x k
                        + (ω 2 / s ^ 2)
                          * (lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2)) rfl ?_
                    intro k _
                    ring
              _ = ω s * (∑ k ∈ Finset.range (n + 1), lcuBernsteinWeight n x k)
                  + (ω 2 / s ^ 2) * (∑ k ∈ Finset.range (n + 1),
                    lcuBernsteinWeight n x k * (lcuBernsteinNode n k - x) ^ 2) := by
                    rw [Finset.sum_add_distrib]
                    rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = ω s * 1 + (ω 2 / s ^ 2) * ((1 - x ^ 2) / n) := by rw [hW, hsq]
      _ ≤ ω s + ω 2 / (n * s ^ 2) := by
        have h1 : 0 ≤ 1 - x ^ 2 := by
          have h1a : (0 : ℝ) ≤ 1 - x := sub_nonneg.mpr hx.2
          have h1b : (0 : ℝ) ≤ x + 1 := by linarith [hx.1]
          nlinarith [mul_nonneg h1a h1b]
        have hle : (1 - x ^ 2) / n ≤ 1 / n := by
          have hle' : (1 - x ^ 2 : ℝ) ≤ 1 := by nlinarith [sq_nonneg x]
          exact div_le_div_of_nonneg_right hle' (by positivity)
        have h2 : (ω 2 / s ^ 2) * ((1 - x ^ 2) / n) ≤ (ω 2 / s ^ 2) * (1 / n) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
        have h3 : (ω 2 / s ^ 2) * (1 / n) = ω 2 / (n * s ^ 2) := by ring
        calc
          ω s * 1 + (ω 2 / s ^ 2) * ((1 - x ^ 2) / n)
              ≤ ω s * 1 + (ω 2 / s ^ 2) * (1 / n) := by linarith [h2]
          _ = ω s + ω 2 / (n * s ^ 2) := by rw [h3]; ring
  have hWc : (∑ k ∈ Finset.range (n + 1), (lcuBernsteinWeight n x k : ℂ)) = 1 := by
    norm_cast
  have hident : (lcuBernsteinPoly n f).eval (x : ℂ) - f x
      = ∑ k ∈ Finset.range (n + 1),
          (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x) := by
    have hexpand : (∑ k ∈ Finset.range (n + 1),
          (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x))
        = ∑ k ∈ Finset.range (n + 1),
            (lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k)
            - f x * (∑ k ∈ Finset.range (n + 1), (lcuBernsteinWeight n x k : ℂ)) := by
      have hfx : (∑ k ∈ Finset.range (n + 1), (lcuBernsteinWeight n x k : ℂ) * f x)
          = f x * (∑ k ∈ Finset.range (n + 1), (lcuBernsteinWeight n x k : ℂ)) := by
        rw [← Finset.sum_mul]
        ring
      have hsplit : (∑ k ∈ Finset.range (n + 1),
            (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x))
          = ∑ k ∈ Finset.range (n + 1),
              ((lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k)
                - (lcuBernsteinWeight n x k : ℂ) * f x) := by
        refine Finset.sum_congr (s₁ := Finset.range (n + 1)) (s₂ := Finset.range (n + 1))
          (f := fun k => (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x))
          (g := fun k => (lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k)
            - (lcuBernsteinWeight n x k : ℂ) * f x) rfl ?_
        intro k _
        ring
      rw [hsplit, Finset.sum_sub_distrib, hfx]
    calc
      (lcuBernsteinPoly n f).eval (x : ℂ) - f x
          = ∑ k ∈ Finset.range (n + 1),
              (lcuBernsteinWeight n x k : ℂ) * f (lcuBernsteinNode n k) - f x := by
            rw [lcu_bernstein_eval]
      _ = ∑ k ∈ Finset.range (n + 1),
            (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x) := by
            rw [hexpand, hWc]
            ring
  rw [hident]
  calc
    ‖∑ k ∈ Finset.range (n + 1),
        (lcuBernsteinWeight n x k : ℂ) * (f (lcuBernsteinNode n k) - f x)‖
        ≤ ∑ k ∈ Finset.range (n + 1),
            lcuBernsteinWeight n x k * ‖f (lcuBernsteinNode n k) - f x‖ := hnorm
    _ ≤ ω s + ω 2 / (n * s ^ 2) := hsum

/-- Packages the Bernstein error estimate into a positive degree plan with n + 1 evaluation
reads and two modulus reads. -/
theorem lcu_bernstein_plan {f : ℝ → ℂ} {ω : ℝ → ℝ}
    (hmod : ModulusOfContinuity f ω) (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ plan : LcuApproxPlan,
      plan.degree = n ∧
      plan.evalReads = n + 1 ∧
      plan.modulusReads = 2 ∧
      plan.error = ω s + ω 2 / (n * s ^ 2) ∧
      ‖(lcuBernsteinPoly n f).eval (x : ℂ) - f x‖ ≤ plan.error := by
  refine ⟨{ degree := n, evalReads := n + 1, modulusReads := 2,
            error := ω s + ω 2 / (n * s ^ 2), degree_pos := hn },
    rfl, rfl, rfl, rfl, ?_⟩
  exact lcu_bernstein_error_le hmod n hn s hs x hx

/-- An odd positive length phase response approximating f on [0, 1] yields an ε approximate
block encoding of the odd singular transform, with n adjoint model queries and n + 1 gates. -/
theorem lcu_application_chain {I O H : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] [Fintype H] [DecidableEq H]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (henc : ProjectedUnitaryEncoding A U L R) (P : Polynomial ℂ) (Φ : List ℝ) (n : ℕ)
    (hΦ : Φ.length = n) (hn : 0 < n) (hnodd : n % 2 = 1)
    (hP : sourcePhaseResponse Φ = P)
    (f : ℝ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → ‖(P.eval (x : ℂ)) - f x‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      BlockEncoding (oddSingularTransform A f) (evaluate U cs) L R 1 ε ∧
      adjointQueryCount cs = n ∧ adjointGateCount cs = n + 1 := by
  have hodd : (Φ.map anglePhase).length % 2 = 1 := by
    rw [List.length_map, hΦ]
    exact hnodd
  have happrox' : ∀ i : Fin (Fintype.card I),
      ‖(responseP (1 : ℂ) (Φ.map anglePhase)).eval (matrixSingularValues A i : ℂ)
        - f (matrixSingularValues A i)‖ ≤ ε := by
    intro i
    have hmem := encoded_singularValues_mem_unitInterval henc i
    have hresp : responseP (1 : ℂ) (Φ.map anglePhase) = P := by
      have hdef : sourcePhaseResponse Φ = responseP (1 : ℂ) (Φ.map anglePhase) := rfl
      rw [← hdef, hP]
    rw [hresp]
    exact happrox _ hmem
  obtain ⟨cs, hblock, hq, hg⟩ :=
    qsvt_odd_counted_approximation henc (base := (1 : ℂ)) (by simp [IsPhase])
      (Φ.map anglePhase) (anglePhaseTable_isPhase Φ) hodd f hε happrox'
  refine ⟨cs, hblock, ?_, ?_⟩
  · rw [hq, List.length_map, hΦ]
  · rw [hg, List.length_map, hΦ]

/-- Compiling the source real phase family produces the source resource quadruple at its phase
list length. -/
theorem lcu_cpp_quadruple (Φ : List ℝ) :
    cppCounts (cppCompile (sourceRealFamily Φ)) = sourceCppQuadruple Φ.length := by
  rw [cppCompile_counts]
  have hlen : (sourceRealFamily Φ).length = Φ.length := by simp [sourceRealFamily]
  rw [hlen]
  rfl

/-- For a unit modulus constant c other than one, a two angle word realizes the constant
response, and every realizing word has even length at least two. -/
theorem lcu_degreeZero_range (c : ℂ) (hc : Complex.normSq c = 1) :
    (c = 1 ∨ sourcePhaseResponse [Complex.arg c, 0] = Polynomial.C c) ∧
    (c ≠ 1 →
      sourcePhaseResponse [Complex.arg c, 0] = Polynomial.C c ∧
      (∀ Ψ : List ℝ, sourcePhaseResponse Ψ = Polynomial.C c → 2 ≤ Ψ.length) ∧
      (∀ Ψ : List ℝ, sourcePhaseResponse Ψ = Polynomial.C c → Ψ.length % 2 = 0)) := by
  refine ⟨?_, ?_⟩
  · by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact Or.inr (sourcePhaseResponse_arg_pair c hc)
  · intro hc1
    refine ⟨sourcePhaseResponse_arg_pair c hc, ?_, ?_⟩
    · intro Ψ hΨ
      exact length_two_le_of_sourcePhaseResponse_const hΨ hc hc1
    · intro Ψ hΨ
      exact length_even_of_sourcePhaseResponse_const hΨ hc

/-- An admissible degree zero polynomial is a unit modulus constant whose right singular
transform is the same scalar identity for all input matrices, giving zero perturbation. -/
theorem lcu_degreeZero_transform_sharp {I O : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (P : Polynomial ℂ)
    (hdeg : P.natDegree = 0) (hadm : Cor8Admissible P 0) :
    (∃ c : ℂ, P = Polynomial.C c ∧ Complex.normSq c = 1 ∧
      rightSingularTransform A (polynomialResponse P) = c • (1 : Matrix I I ℂ) ∧
      rightSingularTransform B (polynomialResponse P) = c • (1 : Matrix I I ℂ) ∧
      ‖rightSingularTransform A (polynomialResponse P)
        - rightSingularTransform B (polynomialResponse P)‖ = 0) := by
  obtain ⟨c, hPc, hnorm⟩ := unitConstant_of_cor8_degreeZero hdeg hadm
  subst hPc
  have hconst : polynomialResponse (Polynomial.C c) = fun _ : ℝ => c := by
    funext x
    simp [polynomialResponse]
  refine ⟨c, rfl, hnorm, ?_, ?_, ?_⟩
  · rw [hconst]
    exact rightSingularTransform_const A c
  · rw [hconst]
    exact rightSingularTransform_const B c
  · rw [hconst]
    simp [rightSingularTransform_const]

/-- Both response polynomials depend on the initial base by multiplication by the corresponding
constant polynomial. -/
private theorem lcu_response_base_linear (base : ℂ) (zs : List ℂ) :
    responseP base zs = Polynomial.C base * responseP 1 zs ∧
    responseQ base zs = Polynomial.C base * responseQ 1 zs := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [responseP_cons, responseQ_cons, ih.1, ih.2]
    constructor <;> ring

/-- For a unit modulus base, multiplying the response pair by its conjugate recovers the
response pair with base one. -/
private theorem lcu_response_one_of_phase {z0 : ℂ} (hz0 : IsPhase z0) (zs : List ℂ) :
    responseP 1 zs = Polynomial.C (star z0) * responseP z0 zs ∧
    responseQ 1 zs = Polynomial.C (star z0) * responseQ z0 zs := by
  have h := lcu_response_base_linear z0 zs
  constructor
  · rw [h.1]
    calc responseP 1 zs = Polynomial.C 1 * responseP 1 zs := by simp
      _ = Polynomial.C (star z0 * z0) * responseP 1 zs := by rw [hz0]
      _ = Polynomial.C (star z0) * (Polynomial.C z0 * responseP 1 zs) := by
        rw [Polynomial.C_mul]; ring
  · rw [h.2]
    calc responseQ 1 zs = Polynomial.C 1 * responseQ 1 zs := by simp
      _ = Polynomial.C (star z0 * z0) * responseQ 1 zs := by rw [hz0]
      _ = Polynomial.C (star z0) * (Polynomial.C z0 * responseQ 1 zs) := by
        rw [Polynomial.C_mul]; ring

/-- Taking arguments of unit modulus phase entries and applying `anglePhase` recovers the
original phase list. -/
theorem lcu_source_table_recovery {zs : List ℂ} (hzs : ∀ z ∈ zs, IsPhase z) :
    (zs.map Complex.arg).map anglePhase = zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have hzs' : ∀ w ∈ zs, IsPhase w := fun w hw => hzs w (List.mem_cons_of_mem z hw)
    rw [List.map_cons, List.map_cons, ih hzs']
    simp [anglePhase_arg_of_isPhase (hzs z (List.mem_cons_self))]

/-- A completed polynomial pair has synthesis count bounded by `lqSynthOpCount` at its degree
parameter. -/
private theorem lcu_synth_count_le : ∀ (n : ℕ) (P Q : Polynomial ℂ),
    CompletedPair n P Q → lqSynthCount n P Q ≤ lqSynthOpCount n := by
  intro n
  induction n with
  | zero =>
      intro P Q h
      have h0 : lqSynthCount 0 P Q = 0 := by rfl
      have hop : lqSynthOpCount 0 = 0 := by rfl
      rw [h0, hop]
  | succ n ih =>
      intro P Q h
      have hstep := CompletedPair.inverse_step (n := n) (P := P) (Q := Q) h
      have hPnd : P.natDegree ≤ n + 1 := Polynomial.natDegree_le_of_degree_le h.degreeP
      have hQnd : Q.natDegree ≤ n := by
        rcases eq_or_ne Q 0 with rfl | hQ0
        · simp
        · have hk := (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr h.degreeQ
          omega
      have hopEq : lqSynthOpCount n = n * (8 * n + 28) := by rfl
      have hcount_eq : lqSynthCount (n + 1) P Q
          = 12 + 8 * (max P.natDegree Q.natDegree + 1) +
            lqSynthCount n
              (inverseResponseP (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q)
              (inverseResponseQ (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q) := by
        simp [lqSynthCount]
      rw [hcount_eq]
      have hrec := (ih _ _ hstep.2).trans_eq hopEq
      have htermle : max P.natDegree Q.natDegree + 1 ≤ n + 2 := by omega
      have hA : 12 + 8 * (max P.natDegree Q.natDegree + 1) +
          lqSynthCount n
            (inverseResponseP (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q)
            (inverseResponseQ (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q)
          ≤ 12 + 8 * (n + 2) + n * (8 * n + 28) := by omega
      have hB : (12 : ℕ) + 8 * (n + 2) + n * (8 * n + 28) ≤ lqSynthOpCount (n + 1) := by
        have hdef : lqSynthOpCount (n + 1) = (n + 1) * (8 * (n + 1) + 28) := by rfl
        rw [hdef]
        have e1 : (12 : ℕ) + 8 * (n + 2) + n * (8 * n + 28) = 8 * n * n + 36 * n + 28 := by ring
        have e2 : (n + 1) * (8 * (n + 1) + 28) = 8 * n * n + 44 * n + 36 := by ring
        omega
      exact hA.trans hB

/-- An admissible Theorem 3 pair possesses a phase list and real angle table of length n with
exact responses, the stated base normalization, and synthesis cost at most `lqSynthOpCount`
n. -/
theorem lcu_cor10_solver {n : ℕ} {P Q : Polynomial ℂ} (h : Th3Pair n P Q) :
    ∃ s : LcuSynthesizedPair,
      s.phases.length = n ∧
      s.table.length = n ∧
      s.table.map anglePhase = s.phases ∧
      IsPhase s.base ∧
      (∀ z ∈ s.phases, IsPhase z) ∧
      responseP s.base s.phases = P ∧
      responseQ s.base s.phases = Q ∧
      sourcePhaseResponse s.table = Polynomial.C (star s.base) * P ∧
      responseQ 1 (s.table.map anglePhase) = Polynomial.C (star s.base) * Q ∧
      s.cost ≤ lqSynthOpCount n := by
  obtain ⟨hbase, hphases, hP, hQ⟩ := synthesizePair_correct h
  have hconv := lcu_response_one_of_phase hbase (synthesizePair n P Q).2
  have htab := lcu_source_table_recovery hphases
  refine ⟨{ base := (synthesizePair n P Q).1,
            phases := (synthesizePair n P Q).2,
            table := (synthesizePair n P Q).2.map Complex.arg,
            cost := lqSynthCount n P Q }, ?_⟩
  (try dsimp only)
  refine ⟨synthesizePair_length n P Q, ?_, htab, hbase, hphases, hP, hQ, ?_, ?_,
    lcu_synth_count_le n P Q h⟩
  · rw [List.length_map]
    exact synthesizePair_length n P Q
  · rw [sourcePhaseResponse, htab, hconv.1, hP]
  · rw [htab, hconv.2, hQ]

/-- The Equation 3 recurrence step agrees with the response recurrence after negating its second
input polynomial. -/
theorem lcu_eq3_step_eq (z : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    lcuEq3Step z pq = lcuResponseStep z (pq.1, -pq.2) := by
  show (Polynomial.C z * (Polynomial.X * pq.1 - (1 - Polynomial.X ^ 2) * pq.2),
      Polynomial.C (star z) * (pq.1 + Polynomial.X * pq.2))
      = (Polynomial.C z * (Polynomial.X * pq.1 + (1 - Polynomial.X ^ 2) * (-pq.2)),
        Polynomial.C (star z) * (pq.1 - Polynomial.X * (-pq.2)))
  apply Prod.ext
  · ring
  · ring

/-- One Equation 3 recurrence step increases the parity exponent of the first polynomial by one
while preserving the opposite parity of the second. -/
private theorem lcu_eq3Step_sign (z : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) (x : ℂ) (k : ℕ)
    (h : pq.1.eval (-x) = (-1 : ℂ) ^ k * pq.1.eval x ∧
      pq.2.eval (-x) = -((-1 : ℂ) ^ k) * pq.2.eval x) :
    (lcuEq3Step z pq).1.eval (-x) = (-1 : ℂ) ^ (k + 1) * (lcuEq3Step z pq).1.eval x ∧
    (lcuEq3Step z pq).2.eval (-x) = -((-1 : ℂ) ^ (k + 1)) * (lcuEq3Step z pq).2.eval x := by
  have hz : (-1 : ℂ) ^ (k + 1) = -((-1 : ℂ) ^ k) := by
    rw [pow_succ]
    ring
  constructor <;>
    simp only [lcuEq3Step, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow] <;>
    rw [h.1, h.2, hz] <;> ring

/-- The two Equation 3 response polynomials have opposite parities determined by the phase list
length. -/
theorem lcu_eq3_parity (z0 : ℂ) (zs : List ℂ) (x : ℂ) :
    (lqEq3Pair z0 zs).1.eval (-x) = (-1 : ℂ) ^ zs.length * (lqEq3Pair z0 zs).1.eval x ∧
    (lqEq3Pair z0 zs).2.eval (-x) =
      -((-1 : ℂ) ^ zs.length) * (lqEq3Pair z0 zs).2.eval x := by
  have hfold : ∀ (acc : Polynomial ℂ × Polynomial ℂ) (k : ℕ) (zs : List ℂ),
      (acc.1.eval (-x) = (-1 : ℂ) ^ k * acc.1.eval x ∧
        acc.2.eval (-x) = -((-1 : ℂ) ^ k) * acc.2.eval x) →
      (zs.foldl lcuEq3Fold acc).1.eval (-x) =
          (-1 : ℂ) ^ (k + zs.length) * (zs.foldl lcuEq3Fold acc).1.eval x ∧
        (zs.foldl lcuEq3Fold acc).2.eval (-x) =
          -((-1 : ℂ) ^ (k + zs.length)) * (zs.foldl lcuEq3Fold acc).2.eval x := by
    intro acc k zs
    induction zs generalizing acc k with
    | nil =>
      intro hacc
      simpa using! hacc
    | cons w ws ih =>
      intro hacc
      rw [List.foldl_cons]
      have hstep := lcu_eq3Step_sign w acc x k hacc
      have hres := ih (lcuEq3Step w acc) (k + 1) hstep
      simp only [List.length_cons, lcuEq3Fold] at hres ⊢
      have heq : k + 1 + ws.length = k + (ws.length + 1) := by omega
      refine ⟨?_, ?_⟩
      · rw [hres.1, heq]
      · rw [hres.2, heq]
  have hbase : (Polynomial.C z0).eval (-x) = (-1 : ℂ) ^ 0 * (Polynomial.C z0).eval x ∧
      (0 : Polynomial ℂ).eval (-x) = -((-1 : ℂ) ^ 0) * (0 : Polynomial ℂ).eval x := by
    simp
  have h := hfold (Polynomial.C z0, 0) 0 zs hbase
  rw [show lqEq3Pair z0 zs = zs.foldl lcuEq3Fold (Polynomial.C z0, 0) by
    show lqEq3Pair z0 zs = zs.foldl (fun pq z => lqEq3PairStep z pq) (Polynomial.C z0, 0)
    rfl]
  simpa using! h

/-- A nonempty real phase list splits into a head phase and tail phase list with the stated
length and Equation 3 pair identities. -/
theorem lcu_eq3_word_parameters {Φ : List ℝ} (hΦ : Φ ≠ []) :
    ∃ z0 : ℂ, ∃ zs : List ℂ,
      z0 = anglePhase Φ.headI ∧
      zs = Φ.tail.map anglePhase ∧
      (Φ.map anglePhase) = z0 :: zs ∧
      zs.length + 1 = Φ.length ∧
      lqEq3Pair z0 zs = lqEq3Pair (anglePhase Φ.headI) (Φ.tail.map anglePhase) := by
  refine ⟨anglePhase Φ.headI, Φ.tail.map anglePhase, rfl, rfl, ?_, ?_, rfl⟩
  · cases Φ with
    | nil => simp at hΦ
    | cons a t =>
      simp only [List.headI_cons, List.tail_cons]
      rfl
  · cases Φ with
    | nil => simp at hΦ
    | cons a t =>
      simp only [List.length_cons, List.tail_cons]
      simp [List.length_map]

/-- Sequential addition of two resource accounts is commutative. -/
private theorem account_seq_comm (a b : Account) : Account.seq a b = Account.seq b a := by
  ext <;> simp only [Account.seq] <;> omega

/-- The counters of k repetitions of a dynamic step equal k repetitions of its step account. -/
private theorem counters_replicate (s : DynStep) (k : ℕ) :
    counters (List.replicate k s) = Account.repeat s.stepAccount k := by
  induction k with
  | zero => simp [counters_nil, repeat_zero]
  | succ k ih =>
    have hrep : List.replicate (Nat.succ k) s = s :: List.replicate k s := by
      simp [List.replicate_succ]
    rw [hrep, counters_cons, ih]
    exact (repeat_succ s.stepAccount k).symm

/-- The dynamic instruction list with one allocation, n adjoint oracle calls, n + 1 phase
macros, the specified evolution steps, and final reset, release, and classical work. -/
noncomputable def lcuMachineWord (n pauli ticks bits : ℕ) : List DynStep :=
  DynStep.alloc 1 :: (List.replicate n (DynStep.oracle true [1]) ++
    List.replicate (n + 1) (DynStep.macro (.t 1)) ++
    List.replicate pauli (DynStep.evolve ticks) ++
    [DynStep.reset 1, DynStep.releaseDirty 1, DynStep.classical bits])

/-- Computes the machine word counters: zero forward queries, n adjoint queries, the specified
evolution counts and ticks, n + 1 macro and basic gates, depth 2n + pauli + 5, and bits + 8
classical bits. -/
theorem lcu_machine_ledger (n pauli ticks bits : ℕ) :
    let a :=
        Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs.account 1
        (lcuMachineWord n pauli ticks bits)
    a.queries = 0 ∧
    a.adjointQueries = n ∧
    a.hamiltonianCount = pauli ∧
    a.hamiltonianTicks = pauli * ticks ∧
    a.macroGates = n + 1 ∧
    a.basicGates = n + 1 ∧
    a.depth = 2 * n + pauli + 5 ∧
    a.classicalBits = bits + 8 := by
  have hq : (counters (lcuMachineWord n pauli ticks bits)).queries = 0 := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_queries, repeat_queries, Account.zero, DynStep.stepAccount] <;> omega
  have hqa : (counters (lcuMachineWord n pauli ticks bits)).adjointQueries = n := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_adjointQueries, repeat_adjointQueries, Account.zero, DynStep.stepAccount]
    <;> omega
  have hhc : (counters (lcuMachineWord n pauli ticks bits)).hamiltonianCount = pauli := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_hamiltonianCount, repeat_hamiltonianCount, Account.zero,
      DynStep.stepAccount] <;> omega
  have hht : (counters (lcuMachineWord n pauli ticks bits)).hamiltonianTicks
      = pauli * ticks := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_hamiltonianTicks, repeat_hamiltonianTicks, Account.zero,
      DynStep.stepAccount] <;> rfl
  have hmg : (counters (lcuMachineWord n pauli ticks bits)).macroGates = n + 1 := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_macroGates, repeat_macroGates, Account.zero, DynStep.stepAccount] <;> omega
  have hbg : (counters (lcuMachineWord n pauli ticks bits)).basicGates = n + 1 := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_basicGates, repeat_basicGates, Account.zero, DynStep.stepAccount] <;> omega
  have hd : (counters (lcuMachineWord n pauli ticks bits)).depth = 2 * n + pauli + 5 := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_depth, repeat_depth, Account.zero, DynStep.stepAccount] <;> omega
  have hcb : (counters (lcuMachineWord n pauli ticks bits)).classicalBits = bits + 8 := by
    simp only [lcuMachineWord, counters_cons, counters_append, counters_replicate,
      counters_nil]
    simp [seq_classicalBits, repeat_classicalBits, Account.zero, DynStep.stepAccount,
      DynStep.bitCharge] <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_queries, hq]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_adjointQueries, hqa]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_hamiltonianCount, hhc]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_hamiltonianTicks, hht]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_macroGates, hmg]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_basicGates, hbg]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_depth, hd]
    simp [initState, Account.initAccount, Account.zero]
  · rw [show account 1 (lcuMachineWord n pauli ticks bits)
      = (runFrom 1 (initState 1) (lcuMachineWord n pauli ticks bits)).acc from rfl,
      runFrom_classicalBits, hcb]
    simp [initState, Account.initAccount, Account.zero]

end Qatlib.Papers.QSingValue19.AlgorithmApps
