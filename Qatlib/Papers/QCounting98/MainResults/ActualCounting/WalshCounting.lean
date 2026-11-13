/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.ActualCounting.ActualWindows

/-!
# Walsh preparation for quantum counting

`walsh_marked_mass` identifies the marked probability of a Walsh-prepared register with the
marked fraction. `walsh_standard_theorem5` combines the actual XOR-oracle program, its exact
query count, and the strict approximate-counting error window. The mathematical context is
[BrassardHoyerTapp1998Counting].

## Main statements

* `source_sqrt_scale`: For nonnegative `t` and positive `N`, scaling `sqrt (t/N)` by `N` gives
  `sqrt (t*N)`.
* `walsh_standard_theorem5`: For `P ≥ 4`, the padded Walsh counting circuit uses exactly `P`
  queries and places probability at least `8/π²` in the stated strict counting window.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open scoped Classical BigOperators

/-- The Walsh-prepared zero state has marked probability equal to the number of marked strings
divided by `2^n`. -/
theorem walsh_marked_mass (n : ℕ) (F : Reg n → Bool) :
    MeasureProb (preparedAAState (HadamardN n) (ZeroStr n)) (sourceMarked F) =
      ((sourceMarked F).card : ℝ)/(2 : ℝ)^n := by
  rw [preparedAAState,applyGate_hadamardN_ket_zero]
  have hcard : (0 : ℝ) < Fintype.card (Reg n) := by rw [card_reg]; positivity
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card (Reg n)) := Real.sqrt_pos.mpr hcard
  have hn : ‖((Real.sqrt (Fintype.card (Reg n)) : ℂ))⁻¹‖ =
      (Real.sqrt (Fintype.card (Reg n)))⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hsqrt.le]
  simp only [MeasureProb,BornProb,Uniform,Finset.sum_const,nsmul_eq_mul]
  rw [hn,inv_pow,Real.sq_sqrt hcard.le]
  simp only [card_reg,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv]

/-- For nonnegative `t` and positive `N`, scaling `sqrt (t/N)` by `N` gives `sqrt (t*N)`. -/
theorem source_sqrt_scale (t N : ℝ) (ht : 0 ≤ t) (hN : 0 < N) :
    N*Real.sqrt (t/N) = Real.sqrt (t*N) := by
  calc
    N*Real.sqrt (t/N) = Real.sqrt (t/N)*Real.sqrt (N^2) := by rw [Real.sqrt_sq hN.le]; ring
    _ = Real.sqrt ((t/N)*N^2) := (Real.sqrt_mul (by positivity) _).symm
    _ = Real.sqrt (t*N) := by congr 1; field_simp

/-- For `P ≥ 4`, the padded Walsh counting circuit uses exactly `P` queries and places
probability at least `8/π²` in the stated strict counting window. See
[BrassardHoyerTapp1998Counting]. -/
theorem walsh_standard_theorem5 (n P : ℕ) (F : Reg n → Bool) (hP : 4 ≤ P) :
    QueryCount (standardPaddedAEWord P (HadamardN n) (ZeroStr n)) = P ∧
      8/Real.pi^2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
        |(2 : ℝ)^n*foldedEstimate P z-((sourceMarked F).card : ℝ)| <
          2*Real.pi/(P : ℝ)*Real.sqrt (((sourceMarked F).card : ℝ)*(2 : ℝ)^n)+
            Real.pi^2/(P : ℝ)^2*(2 : ℝ)^n),
        MeasureProb (Run (workspaceBitOracle F) (standardPaddedAEWord P (HadamardN n) (ZeroStr n))
          (standardInput P (by omega) (ZeroStr n))) (Finset.univ.filter (fun p => p.2 = z)) := by
  refine ⟨(standardPaddedAE_resources P (by omega) (HadamardN n) (ZeroStr n)).1,?_⟩
  have h := (standard_theorem6 P (HadamardN n) (ZeroStr n) F (hadamardN_unitary n) hP).2
  rw [walsh_marked_mass] at h
  refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    have hN : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have he : (2 : ℝ)^n*(foldedEstimate P z-((sourceMarked F).card : ℝ)/(2 : ℝ)^n) =
        (2 : ℝ)^n*foldedEstimate P z-((sourceMarked F).card : ℝ) := by field_simp
    rw [← he,abs_mul,abs_of_pos hN]
    calc
      _ < (2 : ℝ)^n*(2*Real.pi/(P : ℝ)*Real.sqrt (((sourceMarked F).card : ℝ)/(2 : ℝ)^n)+
          Real.pi^2/(P : ℝ)^2) := mul_lt_mul_of_pos_left hz hN
      _ = (2*Real.pi/(P : ℝ))*((2 : ℝ)^n*Real.sqrt (((sourceMarked F).card : ℝ)/(2 : ℝ)^n))+
          Real.pi^2/(P : ℝ)^2*(2 : ℝ)^n := by ring
      _ = _ := by rw [source_sqrt_scale _ _ (Nat.cast_nonneg _) hN]
  · intro z _ _
    exact measureProb_nonneg _ _

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
