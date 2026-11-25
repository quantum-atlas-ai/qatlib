/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WeighMatrix00.MainResults.Corollary1TensorFamily
public import Qatlib.Papers.WeighMatrix00.MainResults.Lemma2ClassicalLowerBounds
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Depth lower bound for the tensor family of weighing matrices

Squaring the known query-scale identity rewrites the order-to-weight
ratio in [VanDam2002], Corollary 1. Its finite correction vanishes
for weights strictly greater than one.
-/

set_option autoImplicit false

namespace Qatlib.Papers.WeighMatrix00.MainResults

open Qatlib.Papers.WeighMatrix00.MainResults
open Qatlib.Papers.WeighMatrix00.MainResults.WeighingMatrix
open Filter
open scoped Topology

/-- Classical depth for the tensor-power matrix is bounded below by the order power
with the explicit finite weight correction. -/
theorem tensor_depth {n k : ℕ} (M : WeighingMatrix n k) (hk : 0 < k) (hkn : k < n)
    (t : ℕ) (tree : QueryTree (tPow n t)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcorrect : (1 - ε) * (tPow n t : ℝ) ≤ ((tensorPow M t).correctSet tree).card) :
    (1 - ε) * (((n : ℝ) ^ t) ^ (1 - Real.log (k : ℝ) / Real.log (n : ℝ))) -
      ((k : ℝ) ^ t)⁻¹ ≤ (tree.depth : ℝ) := by
  have hK : (0 : ℝ) < (k : ℝ) ^ t := pow_pos (by exact_mod_cast hk) t
  have hn : 1 < n := by omega
  have hn0 : 0 ≤ (n : ℝ) ^ t := by positivity
  have hratio : (n : ℝ) ^ t / (k : ℝ) ^ t =
      ((n : ℝ) ^ t) ^ (1 - Real.log (k : ℝ) / Real.log (n : ℝ)) := by
    let γ := 1 - Real.log (k : ℝ) / Real.log (n : ℝ)
    calc
      _ = (Real.sqrt ((n : ℝ) ^ t / (k : ℝ) ^ t)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ = ((((n : ℝ) ^ t) ^ (γ / 2))) ^ 2 :=
        congrArg (fun u : ℝ => u ^ 2) (queryBound_rpow hn hk t)
      _ = ((n : ℝ) ^ t) ^ γ := by
        rw [← Real.rpow_two, ← Real.rpow_mul hn0]
        congr 1
        ring
  have hd := (source_lemma2_classicalLowerBounds (tensorPow M t) tree ε hε0 hε1
    (tPow_le hkn.le t) (tPow_pos hk t) hcorrect).2.1
  simp only [tPow_eq_pow, Nat.cast_pow] at hd
  have hdiv : ((1 - ε) * (n : ℝ) ^ t - 1) / (k : ℝ) ^ t ≤ (tree.depth : ℝ) :=
    (div_le_iff₀ hK).2 (by linarith)
  rw [sub_div, mul_div_assoc, hratio, one_div] at hdiv
  exact hdiv

/-- The reciprocal weight correction tends to zero for a base weight greater than one. -/
theorem weight_tail {k : ℕ} (hk : 1 < k) :
    Tendsto (fun t : ℕ => ((k : ℝ) ^ t)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hk))

end Qatlib.Papers.WeighMatrix00.MainResults
