/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TimeDependent.Equation28Stat
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Error bounds for a discrete ordered segment

This module bounds layers of sublist products by binomial weights and then by factorial weights.
`equation28` combines the resulting truncation estimate with a time-grid discretization estimate
for continuous Lipschitz Hamiltonians, in the time-dependent simulation setting
[BerryEtAl2015Taylor].

## Main statements

* `equation28_choose_weight_bound`: A factorial upper bound for the binomial layer weight.
* `equation28`: The combined truncation and time-grid error bound.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Foundations.OperatorErrors.OperatorError

set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.CoherentSim.TimeDependent
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The sum of products of all length-`k` sublists of a matrix list. -/
private noncomputable def layer {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) (k : ℕ) : Matrix I I ℂ :=
  ((l.sublistsLen k).map List.prod).sum

/-- The sum of a function mapped over `List.range n` equals its finite sum over `Finset.range
n`. -/
private theorem map_range_sum {G : Type*} [AddCommMonoid G] (f : ℕ → G) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

/-- The sum of products over all sublists equals the sum of its fixed-length layers from zero
through the list length. -/
private theorem layers_full {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) :
    (l.sublists.map List.prod).sum = ∑ k ∈ Finset.range (l.length + 1), layer l k := by
  have hf (ns : List ℕ) :
      ((ns.flatMap (fun k => l.sublistsLen k)).map List.prod).sum =
        (ns.map (layer l)).sum := by
    induction ns with
    | nil => simp
    | cons n ns ih => simp [List.flatMap_cons, List.map_append, List.sum_append, layer, ih]
  have hp := (List.range_bind_sublistsLen_perm l).trans (List.sublists_perm_sublists' l).symm
  rw [← (hp.map List.prod).sum_eq, hf, map_range_sum]

/-- If every matrix in a list has norm at most a nonnegative `q`, the product norm is at most
`q` to the list length. -/
private theorem norm_prod_bound {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) (q : ℝ) (hq : 0 ≤ q)
    (h : ∀ A ∈ l, ‖A‖ ≤ q) : ‖l.prod‖ ≤ q ^ l.length := by
  induction l with
  | nil => simpa using! (l2_norm_one_le (I := I))
  | cons A l ih =>
    have ha := h A (by simp)
    have hl := ih (fun B hB => h B (by simp [hB]))
    calc
      _ ≤ ‖A‖ * ‖l.prod‖ := norm_mul_le _ _
      _ ≤ q * q ^ l.length := mul_le_mul ha hl (norm_nonneg _) hq
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- A uniform norm bound `C` on the matrices in a list bounds their sum norm by the list length
times `C`. -/
private theorem norm_sum_length {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) (C : ℝ) (h : ∀ A ∈ l, ‖A‖ ≤ C) :
    ‖l.sum‖ ≤ (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons A l ih =>
    have hl := ih (fun B hB => h B (by simp [hB]))
    have ha := h A (by simp)
    calc
      _ ≤ ‖A‖ + ‖l.sum‖ := norm_add_le _ _
      _ ≤ C + (l.length : ℝ) * C := add_le_add ha hl
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- If each matrix has norm at most nonnegative `q`, the order-`k` sublist-product layer has
norm at most `choose l.length k * q^k`. -/
private theorem layer_bound {I : Type} [Fintype I] [DecidableEq I]
    (l : List (Matrix I I ℂ)) (q : ℝ) (hq : 0 ≤ q)
    (h : ∀ A ∈ l, ‖A‖ ≤ q) (k : ℕ) :
    ‖layer l k‖ ≤ (l.length.choose k : ℝ) * q ^ k := by
  have he := norm_sum_length ((l.sublistsLen k).map List.prod) (q^k) (by
    intro A hA
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hA
    obtain ⟨hsub,hlen⟩ := List.mem_sublistsLen.mp hw
    simpa [hlen] using! norm_prod_bound w q hq (fun B hB => h B (hsub.subset hB)))
  simpa [List.length_sublistsLen] using! he

/-- For positive `M` and nonnegative `a`, the binomial weight `choose M k * (a / M)^k` is at
most `a^k / k!`. -/
theorem equation28_choose_weight_bound (M k : ℕ) (a : ℝ) (hM : 0 < M) (ha : 0 ≤ a) :
    (M.choose k : ℝ) * (a / M) ^ k ≤ a ^ k / (k.factorial : ℝ) := by
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  calc
    _ ≤ ((M : ℝ) ^ k / (k.factorial : ℝ)) * (a / M) ^ k :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k M) (pow_nonneg (by positivity) _)
    _ = _ := by rw [div_pow]; field_simp

/-- For the stated continuous Hermitian Hamiltonian with norm bound `Λ` and Lipschitz constant
`L`, the discrete ordered segment differs from ordered evolution by at most `exp (Λ * τ) *
((Λ * τ)^(K + 1) / (K + 1)! + (Λ² + L) * τ² / (2 * M))`. See [BerryEtAl2015Taylor]. -/
theorem equation28 : Equation28 := by
  intro I _ _ H τ Λ L M K hH ht hΛ hL hM hbound hLip
  let l := gridIncrements H τ M
  let a := Λ * τ
  let k := K + 1
  have ha : 0 ≤ a := mul_nonneg hΛ ht
  have hq : 0 ≤ a / M := div_nonneg ha (Nat.cast_nonneg _)
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hlen : l.length = M := by simp [l, gridIncrements]
  have hinc : ∀ A ∈ l, ‖A‖ ≤ a / M := by
    intro A hA
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hA)
    have hj : (j.val : ℝ) ≤ M := by exact_mod_cast j.isLt.le
    have hu : τ * (j.val : ℝ) / M ∈ Set.Icc 0 τ := by
      refine ⟨by positivity, ?_⟩
      calc
        _ ≤ τ * (M : ℝ) / M := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj ht)
          (Nat.cast_nonneg _)
        _ = τ := by field_simp
    calc
      _ = (τ / M) * ‖H (τ * (j.val : ℝ) / M)‖ := by
        simp [norm_smul, abs_of_nonneg ht]
      _ ≤ (τ / M) * Λ := mul_le_mul_of_nonneg_left (hbound _ hu).2 (by positivity)
      _ = _ := by dsimp [a]; ring
  have hfull : dysonGridRun H τ M = ∑ j ∈ Finset.range (M+1), layer l j := by
    rw [dyson_grid_strict_subset_expansion]
    simpa [l, gridIncrements, hlen] using! layers_full l
  have hz (n : ℕ) : layer l (M+1+n) = 0 := by
    simp [layer, List.sublistsLen_of_length_lt (by omega : l.length < M+1+n)]
  have hlarge : (∑ j ∈ Finset.range (k+(M+1)), layer l j) = dysonGridRun H τ M := by
    rw [Nat.add_comm k (M+1), Finset.sum_range_add, ← hfull]
    simp [hz]
  have htail : equation28Segment H τ M K - dysonGridRun H τ M =
      -(∑ n ∈ Finset.range (M+1), layer l (k+n)) := by
    rw [Finset.sum_range_add] at hlarge
    change (∑ j ∈ Finset.range k, layer l j) - dysonGridRun H τ M = _
    rw [← hlarge]
    abel
  have hmajorant (n : ℕ) : ‖layer l (k+n)‖ ≤
      (a^k / (k.factorial : ℝ)) * (a^n / (n.factorial : ℝ)) := by
    have hd : (k.factorial : ℝ) * (n.factorial : ℝ) ≤ ((k+n).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (k+n))
        (Nat.factorial_mul_factorial_dvd_factorial_add k n)
    calc
      _ ≤ (M.choose (k+n) : ℝ) * (a/M)^(k+n) := by
        simpa [hlen] using! layer_bound l (a/M) hq hinc (k+n)
      _ ≤ a^(k+n) / ((k+n).factorial : ℝ) := equation28_choose_weight_bound M (k+n) a hM ha
      _ ≤ a^(k+n) / ((k.factorial : ℝ)*(n.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) hd
      _ = _ := by rw [pow_add]; ring
  have hs : Summable (fun n : ℕ => (a^k / (k.factorial : ℝ)) * (a^n / (n.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial a).mul_left _
  have hc : ‖equation28Segment H τ M K - dysonGridRun H τ M‖ ≤
      Real.exp a * a^k / (k.factorial : ℝ) := by
    rw [htail, norm_neg]
    calc
      _ ≤ ∑ n ∈ Finset.range (M+1), ‖layer l (k+n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (M+1), (a^k / (k.factorial : ℝ)) *
          (a^n / (n.factorial : ℝ)) := Finset.sum_le_sum (fun n _ => hmajorant n)
      _ ≤ ∑' n : ℕ, (a^k / (k.factorial : ℝ)) * (a^n / (n.factorial : ℝ)) :=
        hs.sum_le_tsum _ (fun _ _ => by positivity)
      _ = _ := by
        rw [tsum_mul_left, ← congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) a, ← Real.exp_eq_exp_ℝ]
        ring
  have hg := (dyson_sorted_grid_actual_error_and_cost I H τ Λ L M hH ht hΛ hL hM hbound hLip).1
  calc
    _ ≤ ‖equation28Segment H τ M K - dysonGridRun H τ M‖ +
        ‖dysonGridRun H τ M - orderedEvolution (fun u => Complex.I • H u) 0 τ‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.exp a * a^k / (k.factorial : ℝ) +
        Real.exp (Λ*τ) * (Λ^2+L)*τ^2/(2*M) := add_le_add hc hg
    _ = _ := by dsimp [a,k]; ring

end Qatlib.Concepts.CoherentSim.TimeDependent
