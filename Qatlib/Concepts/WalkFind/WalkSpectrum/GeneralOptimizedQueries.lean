/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.UniqueCollision.GeneralQueryMemory
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Choosing the optimized collision-search memory scale

This module chooses an integer subset size whose memory size and `queryScale` are both bounded
by `(k+2)*N^(k/(k+1))`. It then derives the general optimized-query contract from the general
query-memory tradeoff, following the scale balancing used in collision search
[Ambainis2007ElementDistinctness].

## Main statements

* `optimizedMemory_choice`: simultaneous bounds on the chosen subset size and query scale.
* `generalOptimizedQueries_of_generalQueryMemory`: the optimized endpoint from the memory
  tradeoff.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.WalkSpectrum
open scoped Classical

/-- For `2 ≤ k ≤ N`, there is `r` with `k ≤ r ≤ N` such that both `queryScale k N r` and `r` are
at most `(k+2)*N^(k/(k+1))`. -/
theorem optimizedMemory_choice (k N : ℕ) (hk : 2 ≤ k) (hNk : k ≤ N) :
    ∃ r : ℕ, k ≤ r ∧ r ≤ N ∧
      queryScale k N r ≤ ((k : ℝ)+2)*(N : ℝ)^((k : ℝ)/(k+1)) ∧
      (r : ℝ) ≤ ((k : ℝ)+2)*(N : ℝ)^((k : ℝ)/(k+1)) := by
  let a : ℝ := (k : ℝ)/(k+1)
  let R : ℝ := (N : ℝ)^a
  let r := max k (Nat.ceil R)
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : 0 < (N : ℝ) := by linarith
  have ha : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hR1 : 1 ≤ R := Real.one_le_rpow hN ha
  have hRN : R ≤ (N : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN ha1
    simpa [R] using! hh
  have hrN : r ≤ N := max_le hNk (Nat.ceil_le.mpr hRN)
  have hkr : k ≤ r := le_max_left _ _
  have hRr : R ≤ (r : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast (le_max_right k (Nat.ceil R)))
  have hru : (r : ℝ) ≤ ((k : ℝ)+1)*R := by
    change ((max k (Nat.ceil R) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    apply max_le
    · nlinarith
    · have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ R)
      nlinarith
  have hβ : 0 ≤ ((k : ℝ)-1)/2 := by linarith
  have hpow : R^(((k : ℝ)-1)/2) ≤ (r : ℝ)^(((k : ℝ)-1)/2) :=
    Real.rpow_le_rpow (by linarith) hRr hβ
  have hdiv : (N : ℝ)^((k : ℝ)/2)/(r : ℝ)^(((k : ℝ)-1)/2) ≤ R := by
    calc
      _ ≤ (N : ℝ)^((k : ℝ)/2)/R^(((k : ℝ)-1)/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = R := by
        dsimp only [R]
        rw [← Real.rpow_mul hNp.le,← Real.rpow_sub hNp]
        congr 1
        dsimp [a]
        field_simp
        ring
  refine ⟨r,hkr,hrN,?_,?_⟩
  · unfold queryScale
    change (r : ℝ)+(N : ℝ)^((k : ℝ)/2)/(r : ℝ)^(((k : ℝ)-1)/2) ≤ ((k : ℝ)+2)*R
    nlinarith
  · nlinarith

/-- The general query-memory contract implies the general optimized-query contract. -/
theorem generalOptimizedQueries_of_generalQueryMemory
    (hgeneral : GeneralQueryMemoryContract) : GeneralOptimizedQueriesContract := by
  intro k hk
  obtain ⟨C,hC,hA⟩ := hgeneral k hk
  refine ⟨C*((k : ℝ)+2),by positivity,?_⟩
  intro N M _ hN hM
  by_cases hNk : k ≤ N
  · obtain ⟨r,hkr,hrN,hscale,hr⟩ := optimizedMemory_choice k N hk hNk
    obtain ⟨A,hcorr,hq,hw⟩ := hA N M r hM hkr hrN
    refine ⟨A,hcorr,?_,?_⟩
    · intro s
      exact (hq s).trans (by nlinarith [mul_le_mul_of_nonneg_left hscale hC.le])
    · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hC.le) (Nat.cast_nonneg (dataBits N M))
      nlinarith
  · refine ⟨nativeReject N M k hN,nativeReject_correct N M k hN (by omega),?_,?_⟩
    · intro s
      rw [nativeReject_queries]
      simp only [Nat.cast_zero]
      positivity
    · dsimp only [nativeReject]
      simp only [Nat.cast_zero]
      positivity

end Qatlib.Concepts.WalkFind.WalkSpectrum
