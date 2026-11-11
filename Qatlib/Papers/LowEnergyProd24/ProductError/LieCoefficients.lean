/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.LieTerms
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.FactorialWeights
import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Finite Lie coefficients and their absolute mass

The recursive expansion `lieTerms` constructs degree-indexed nested commutator terms for a
real-weighted stage list. The quantity `lieMass` sums their coefficient norms, and
`lieMass_bound` controls it using the total absolute stage weight `timeBudget` and a factorial
denominator. See [HejaziZiniArrazola2024].

## Main statements

* `lieTerms_degree`: Every Lie term generated at degree `n` has an outer commutator list of
  length `n`.
* `lieMass_cons`: Prepending a stage adds its absolute weight at degree zero and convolves the
  remaining masses with powers of its absolute weight divided by factorials.
* `lieMass_bound`: The degree-`n` Lie coefficient mass is at most `timeBudget stages *
  (timeBudget stages)^n / n!`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The sum of the absolute values of the real stage weights. -/
def timeBudget (stages : List (ℝ × Fin M)) : ℝ := (stages.map (fun stage => |stage.1|)).sum

/-- The total absolute stage weight is nonnegative. -/
theorem timeBudget_nonneg (stages : List (ℝ × Fin M)) : 0 ≤ timeBudget stages := by
  induction stages with
  | nil => simp only [timeBudget, List.map_nil, List.sum_nil, le_refl]
  | cons stage stages ih => simpa only [timeBudget, List.map_cons, List.sum_cons] using add_nonneg (abs_nonneg stage.1) ih

/-- The finite Lie terms of each degree, built recursively from stage generators and their
repeated commutators with reciprocal factorial weights. -/
def lieTerms : List (ℝ × Fin M) → ℕ → List (LieTerm M)
  | [], _ => []
  | stage :: stages, n =>
      (if n=0 then [⟨((-stage.1 : ℂ)*Complex.I), stage.2, []⟩] else []) ++
      (Finset.HasAntidiagonal.antidiagonal n).toList.flatMap (fun ij =>
        (lieTerms stages ij.2).map (fun term => (term.raise stage ij.1).scale (1/(ij.1.factorial : ℝ))))

/-- The sum of the complex coefficient norms of all Lie terms at degree `n`. -/
def lieMass (stages : List (ℝ × Fin M)) (n : ℕ) : ℝ :=
  ((lieTerms stages n).map (fun term => ‖term.coefficient‖)).sum

/-- Every Lie term generated at degree `n` has an outer commutator list of length `n`. -/
theorem lieTerms_degree (stages : List (ℝ × Fin M)) (n : ℕ) (term : LieTerm M)
    (ht : term ∈ lieTerms stages n) : term.outer.length = n := by
  induction stages generalizing n term with
  | nil => simp only [lieTerms, List.not_mem_nil] at ht
  | cons stage stages ih =>
    rw [lieTerms, List.mem_append] at ht
    rcases ht with ht | ht
    · split_ifs at ht with hn
      · simp only [List.mem_singleton] at ht
        subst term
        simp only [List.length_nil]
        exact hn.symm
      · exact (List.not_mem_nil ht).elim
    · obtain ⟨ij, hij, ht'⟩ := List.mem_flatMap.mp ht
      obtain ⟨base, hb, he⟩ := List.mem_map.mp ht'
      subst term
      have hsum : ij.1+ij.2=n :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_toList.mp hij)
      simpa only [LieTerm.scale, LieTerm.raise, List.length_append, List.length_replicate,
        ih ij.2 base hb] using hsum

/-- Prepending a stage adds its absolute weight at degree zero and convolves the remaining
masses with powers of its absolute weight divided by factorials. -/
theorem lieMass_cons (stage : ℝ × Fin M) (stages : List (ℝ × Fin M)) (n : ℕ) :
    lieMass (stage::stages) n = (if n=0 then |stage.1| else 0) +
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (|stage.1|^ij.1/(ij.1.factorial : ℝ))*lieMass stages ij.2 := by
  simp only [lieMass, lieTerms, List.map_append, List.sum_append, Hamiltonian.flatMap_sum,
    List.map_map, Function.comp_def]
  congr 1
  · split_ifs <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  · have hp (i : ℕ) : |1/(i.factorial : ℝ)| = 1/(i.factorial : ℝ) := abs_of_nonneg (by positivity)
    simp only [LieTerm.scale_mass, LieTerm.raise_mass, hp, ← mul_assoc, List.sum_map_mul_left]
    have he (i : ℕ) : (1/(i.factorial : ℝ))*|stage.1|^i = |stage.1|^i/(i.factorial : ℝ) := by ring
    simp_rw [he]
    simpa only [Finset.toList_toFinset] using!
      (List.sum_toFinset (fun ij : ℕ × ℕ =>
        (|stage.1|^ij.1/(ij.1.factorial : ℝ))*lieMass stages ij.2)
        (Finset.nodup_toList (Finset.HasAntidiagonal.antidiagonal n))).symm

/-- The degree-`n` Lie coefficient mass is at most `timeBudget stages * (timeBudget stages)^n /
n!`. -/
theorem lieMass_bound (stages : List (ℝ × Fin M)) (n : ℕ) :
    lieMass stages n ≤ timeBudget stages * timeBudget stages^n/(n.factorial : ℝ) := by
  induction stages generalizing n with
  | nil => simp only [lieMass, lieTerms, List.map_nil, List.sum_nil, timeBudget, zero_mul, zero_div, le_refl]
  | cons stage stages ih =>
    have hb := timeBudget_nonneg stages
    rw [lieMass_cons]
    change _ ≤ (|stage.1|+timeBudget stages)*(|stage.1|+timeBudget stages)^n/(n.factorial : ℝ)
    by_cases hn : n=0
    · subst n
      simpa only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, if_true, mul_one, add_comm] using add_le_add_left (ih 0) |stage.1|
    · rw [if_neg hn]
      calc
        _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            (|stage.1|^ij.1/(ij.1.factorial : ℝ)) *
              (timeBudget stages*timeBudget stages^ij.2/(ij.2.factorial : ℝ)) := by
          simp only [zero_add]
          gcongr with ij hij
          exact ih ij.2
        _ = timeBudget stages * (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            (|stage.1|^ij.1/(ij.1.factorial : ℝ))*(timeBudget stages^ij.2/(ij.2.factorial : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ij hij
          ring
        _ = timeBudget stages*((|stage.1|+timeBudget stages)^n/(n.factorial : ℝ)) := by
          rw [factorial_convolution]
        _ ≤ (|stage.1|+timeBudget stages)*(|stage.1|+timeBudget stages)^n/(n.factorial : ℝ) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg stage.1))
              (by positivity)
end Qatlib.Papers.LowEnergyProd24.ProductError
