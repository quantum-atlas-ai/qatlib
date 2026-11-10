/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalQueryBounds
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalConsumers
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LchsSimulation.Quadrature
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Concepts.QsvtCore.QueryLowerBound

open Matrix Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

private theorem chord_inner_sqrt_ge_of_le (x y : ℝ)
    (hx1 : -1 ≤ x) (_hx2 : x ≤ 1) (_hy1 : -1 ≤ y) (hy2 : y ≤ 1) (hxy : x ≤ y) :
    (1 - y) * (1 + x) ≤ Real.sqrt ((1 - x ^ 2) * (1 - y ^ 2)) := by
  have hnn : 0 ≤ (1 - y) * (1 + x) := by nlinarith
  have hfac : (1 - x ^ 2) * (1 - y ^ 2) - ((1 - y) * (1 + x)) ^ 2 =
      (1 + x) * (1 - y) * 2 * (y - x) := by ring
  have hpos : 0 ≤ (1 + x) * (1 - y) * 2 * (y - x) := by nlinarith
  have hsq : ((1 - y) * (1 + x)) ^ 2 ≤ (1 - x ^ 2) * (1 - y ^ 2) := by
    linarith [hfac, hpos]
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsq

theorem scalar_signal_inner_ge_one_sub_abs (x y : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    1 - |x - y| ≤ x * y + Real.sqrt ((1 - x ^ 2) * (1 - y ^ 2)) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rcases le_total x y with h | h
  · have hkey := chord_inner_sqrt_ge_of_le x y hx1 hx2 hy1 hy2 h
    have hrew : (1 - y) * (1 + x) = 1 + x - y - x * y := by ring
    rw [hrew] at hkey
    rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ y - x)]
    linarith
  · have hkey := chord_inner_sqrt_ge_of_le y x hy1 hy2 hx1 hx2 h
    have hrew : (1 - x) * (1 + y) = 1 + y - x - x * y := by ring
    rw [hrew, mul_comm (1 - y ^ 2) (1 - x ^ 2)] at hkey
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith

private theorem scalar_chord_sq_eq (x y : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    scalarSignalDistance x y ^ 2 =
      2 * (1 - x * y - Real.sqrt ((1 - x ^ 2) * (1 - y ^ 2))) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hpx : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hpy : 0 ≤ 1 - y ^ 2 := by nlinarith
  have h1 := Real.sq_sqrt hpx
  have h2 := Real.sq_sqrt hpy
  rw [scalarSignalDistance_sq, Real.sqrt_mul hpx]
  nlinarith only [h1, h2]

private theorem scalar_chord_sq_le_two_abs (x y : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    scalarSignalDistance x y ^ 2 ≤ 2 * |x - y| := by
  have hinner := scalar_signal_inner_ge_one_sub_abs x y hx hy
  have hsq := scalar_chord_sq_eq x y hx hy
  linarith

theorem scalarSignalDistance_le_sqrt_two_mul_abs (x y : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    scalarSignalDistance x y ≤ Real.sqrt 2 * Real.sqrt |x - y| := by
  apply (sq_le_sq₀ (scalarSignalDistance_nonneg x y)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (abs_nonneg (x - y))]
  exact scalar_chord_sq_le_two_abs x y hx hy

theorem scalarSignalDistance_le_sqrt_two_mul_of_abs_le (x y ε : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1)
    (hε : 0 ≤ ε) (hle : |x - y| ≤ ε) :
    scalarSignalDistance x y ≤ Real.sqrt (2 * ε) := by
  apply (sq_le_sq₀ (scalarSignalDistance_nonneg x y) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by nlinarith : 0 ≤ 2 * ε)]
  exact (scalar_chord_sq_le_two_abs x y hx hy).trans (by linarith)

theorem scalarSignalDistance_le_abs_div_window (m x y : ℝ)
    (hm : 0 ≤ m) (hm1 : m < 1) (hx : |x| ≤ m) (hy : |y| ≤ m) :
    scalarSignalDistance x y ≤ |x - y| / Real.sqrt (1 - m ^ 2) := by
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith
  have hx2 : x ^ 2 ≤ m ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs x] at h
  have hy2 : y ^ 2 ≤ m ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rwa [sq_abs y] at h
  have hpx : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hpy : 0 ≤ 1 - y ^ 2 := by nlinarith
  have h1 := Real.sq_sqrt hpx
  have h2 := Real.sq_sqrt hpy
  set t := Real.sqrt (1 - x ^ 2) with htdef
  set s := Real.sqrt (1 - y ^ 2) with hsdef
  have ht : Real.sqrt (1 - m ^ 2) ≤ t := Real.sqrt_le_sqrt (by nlinarith)
  have hs : Real.sqrt (1 - m ^ 2) ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have hsum2 : 2 * Real.sqrt (1 - m ^ 2) ≤ t + s := by linarith
  have hcross : (t + s) * (t - s) = (y - x) * (x + y) := by
    nlinarith [h1, h2]
  have habs : (t + s) * |t - s| = |x - y| * |x + y| := by
    have h := congrArg abs hcross
    simp only [abs_mul] at h
    have htsnn : 0 ≤ t + s := by
      simp only [htdef, hsdef]
      positivity
    rw [abs_sub_comm y x, abs_of_nonneg htsnn] at h
    exact h
  have hxyp : |x + y| ≤ 2 * m := by
    have h := abs_add_le x y
    nlinarith [h, hx, hy]
  have hts : |t - s| * Real.sqrt (1 - m ^ 2) ≤ m * |x - y| := by
    have h1' : |t - s| * (2 * Real.sqrt (1 - m ^ 2)) ≤ |t - s| * (t + s) :=
      mul_le_mul_of_nonneg_left hsum2 (abs_nonneg _)
    have h2' : |t - s| * (t + s) ≤ |x - y| * (2 * m) := by
      rw [mul_comm (|t - s|) (t + s), habs]
      exact mul_le_mul_of_nonneg_left hxyp (abs_nonneg _)
    nlinarith [h1', h2']
  have htsq : (t - s) ^ 2 * (1 - m ^ 2) ≤ m ^ 2 * (x - y) ^ 2 := by
    have hnnL : 0 ≤ |t - s| * Real.sqrt (1 - m ^ 2) :=
      mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have hmono := mul_self_le_mul_self hnnL hts
    have heq1 : |t - s| * Real.sqrt (1 - m ^ 2) * (|t - s| * Real.sqrt (1 - m ^ 2)) =
        (t - s) ^ 2 * (1 - m ^ 2) := by
      rw [← pow_two, mul_pow, sq_abs, Real.sq_sqrt hm2.le]
    have heq2 : m * |x - y| * (m * |x - y|) = m ^ 2 * (x - y) ^ 2 := by
      rw [← pow_two, mul_pow, sq_abs]
    rw [heq1, heq2] at hmono
    exact hmono
  have hd := scalarSignalDistance_sq x y
  apply (sq_le_sq₀ (scalarSignalDistance_nonneg x y)
    (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [div_pow, Real.sq_sqrt hm2.le, sq_abs]
  apply (le_div_iff₀ hm2).mpr
  nlinarith [hd, htsq, hm2.le]

theorem frontier1 : ∀ (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (m ε : ℝ),
    WellFormedAdjointCircuit word → 0 ≤ ε → 0 ≤ m → m < 1 →
    (∀ x y : ℝ, x ∈ Set.Icc (-m) m → y ∈ Set.Icc (-m) m → |x - y| ≤ ε →
      ‖evaluate (scalarSignalLift W x) word - evaluate (scalarSignalLift W y) word‖ ≤
        (adjointQueryCount word : ℝ) * ε / Real.sqrt (1 - m ^ 2)) ∧
    (∀ x y : ℝ, x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → |x - y| ≤ ε →
      ‖evaluate (scalarSignalLift W x) word - evaluate (scalarSignalLift W y) word‖ ≤
        (adjointQueryCount word : ℝ) * Real.sqrt (2 * ε)) := by
  intro W _ _ word m ε hw hε hm hm1
  refine ⟨?_, ?_⟩
  · intro x y hxw hyw hxy
    obtain ⟨hxw1, hxw2⟩ := hxw
    obtain ⟨hyw1, hyw2⟩ := hyw
    have hm2 : 0 < 1 - m ^ 2 := by nlinarith
    have hxa : |x| ≤ m := abs_le.mpr ⟨hxw1, hxw2⟩
    have hya : |y| ≤ m := abs_le.mpr ⟨hyw1, hyw2⟩
    have hIccx : x ∈ Set.Icc (-1) 1 := ⟨by linarith, by linarith⟩
    have hIccy : y ∈ Set.Icc (-1) 1 := ⟨by linarith, by linarith⟩
    have hb := scalar_signal_fixed_word_hybrid_bound W word x y hw hIccx hIccy
    have hd := scalarSignalDistance_le_abs_div_window m x y hm hm1 hxa hya
    have hdiv : (adjointQueryCount word : ℝ) * (|x - y| / Real.sqrt (1 - m ^ 2)) ≤
        (adjointQueryCount word : ℝ) * ε / Real.sqrt (1 - m ^ 2) := by
      rw [← mul_div_assoc]
      exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hm2) (Real.sqrt_pos.mpr hm2)).mpr
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
    exact (hb.trans (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _))).trans hdiv
  · intro x y hx hy hxy
    exact (scalar_signal_fixed_word_hybrid_bound W word x y hw hx hy).trans
      (mul_le_mul_of_nonneg_left
        (scalarSignalDistance_le_sqrt_two_mul_of_abs_le x y ε hx hy hε hxy)
        (Nat.cast_nonneg _))

theorem uniform_approx_signal_transport (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (m ε : ℝ) (approx : ℝ → ℝ)
    (hw : WellFormedAdjointCircuit word) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hm1 : m < 1)
    (huni : ∀ x : ℝ, x ∈ Set.Icc (-m) m → approx x ∈ Set.Icc (-m) m → |approx x - x| ≤ ε) :
    ∀ x : ℝ, x ∈ Set.Icc (-m) m → approx x ∈ Set.Icc (-m) m →
      ‖evaluate (scalarSignalLift W (approx x)) word - evaluate (scalarSignalLift W x) word‖ ≤
        (adjointQueryCount word : ℝ) * ε / Real.sqrt (1 - m ^ 2) :=
  fun x hx hax => (frontier1 W word m ε hw hε hm hm1).1 (approx x) x hax hx (huni x hx hax)

theorem polynomial_pair_word_transport (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (m δ : ℝ) (p q : Polynomial ℝ)
    (hw : WellFormedAdjointCircuit word) (hδ : 0 ≤ δ) (hm : 0 ≤ m) (hm1 : m < 1)
    (hwinp : ∀ t : ℝ, t ∈ Set.Icc (-m) m → p.eval t ∈ Set.Icc (-m) m)
    (hwinq : ∀ t : ℝ, t ∈ Set.Icc (-m) m → q.eval t ∈ Set.Icc (-m) m)
    (huni : ∀ t : ℝ, t ∈ Set.Icc (-m) m → |p.eval t - q.eval t| ≤ δ) :
    (∀ t : ℝ, t ∈ Set.Icc (-m) m →
      ‖evaluate (scalarSignalLift W (p.eval t)) word -
          evaluate (scalarSignalLift W (q.eval t)) word‖ ≤
        (adjointQueryCount word : ℝ) * δ / Real.sqrt (1 - m ^ 2)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (-m) m →
      ‖evaluate (scalarSignalLift W (p.eval t)) word -
          evaluate (scalarSignalLift W (q.eval t)) word‖ ≤
        (adjointQueryCount word : ℝ) * Real.sqrt (2 * δ)) := by
  refine ⟨fun t ht =>
    (frontier1 W word m δ hw hδ hm hm1).1 (p.eval t) (q.eval t)
      (hwinp t ht) (hwinq t ht) (huni t ht), ?_⟩
  intro t ht
  have hp : p.eval t ∈ Set.Icc (-1) 1 := by
    obtain ⟨h1, h2⟩ := hwinp t ht
    exact ⟨by linarith, by linarith⟩
  have hq : q.eval t ∈ Set.Icc (-1) 1 := by
    obtain ⟨h1, h2⟩ := hwinq t ht
    exact ⟨by linarith, by linarith⟩
  exact (frontier1 W word m δ hw hδ hm hm1).2 (p.eval t) (q.eval t) hp hq (huni t ht)

noncomputable def chebTrunc (N : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (c k) * Polynomial.Chebyshev.T ℝ (k : ℤ)

theorem chebTrunc_eval (N : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (chebTrunc N c).eval x =
      ∑ k ∈ Finset.range (N + 1), c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x := by
  rw [chebTrunc, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]

private theorem abs_cheb_sum_le (s : Finset ℕ) (c : ℕ → ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |∑ k ∈ s, c k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x| ≤ ∑ k ∈ s, |c k| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (k : ℤ) hx
  have hc := abs_nonneg (c k)
  nlinarith

theorem chebTrunc_abs_eval_le (N : ℕ) (c : ℕ → ℝ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebTrunc N c).eval x| ≤ ∑ k ∈ Finset.range (N + 1), |c k| := by
  rw [chebTrunc_eval]
  exact abs_cheb_sum_le _ c (abs_le.mpr ⟨hx.1, hx.2⟩)

private theorem range_union_Icc_of_le (N N' : ℕ) (h : N ≤ N') :
    Finset.range (N' + 1) = Finset.range (N + 1) ∪ Finset.Icc (N + 1) N' := by
  ext k
  simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
  omega

theorem chebTrunc_add_tail (N N' : ℕ) (c : ℕ → ℝ) (h : N ≤ N') :
    chebTrunc N' c = chebTrunc N c +
      ∑ k ∈ Finset.Icc (N + 1) N',
        Polynomial.C (c k) * Polynomial.Chebyshev.T ℝ (k : ℤ) := by
  have hdisj : Disjoint (Finset.range (N + 1)) (Finset.Icc (N + 1) N') := by
    rw [Finset.disjoint_right]
    intro k hk hks
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range] at hks
    omega
  simp only [chebTrunc]
  rw [range_union_Icc_of_le N N' h, Finset.sum_union hdisj]

theorem chebTrunc_tail_abs_eval_le (N N' : ℕ) (c : ℕ → ℝ) (h : N ≤ N') {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    |(chebTrunc N' c).eval x - (chebTrunc N c).eval x| ≤
      ∑ k ∈ Finset.Icc (N + 1) N', |c k| := by
  rw [chebTrunc_add_tail N N' c h, Polynomial.eval_add, add_sub_cancel_left,
    Polynomial.eval_finsetSum, Finset.sum_congr rfl fun k _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C]]
  exact abs_cheb_sum_le _ c (abs_le.mpr ⟨hx.1, hx.2⟩)

theorem chebyshev_truncation_word_transport (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (m δ : ℝ) (N N' : ℕ) (c : ℕ → ℝ)
    (hw : WellFormedAdjointCircuit word) (hδ : 0 ≤ δ) (hm : 0 ≤ m) (hm1 : m < 1)
    (hNN' : N ≤ N') (hcoeff : ∑ k ∈ Finset.range (N' + 1), |c k| ≤ m)
    (htail : ∑ k ∈ Finset.Icc (N + 1) N', |c k| ≤ δ) :
    (∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      ‖evaluate (scalarSignalLift W ((chebTrunc N c).eval t)) word -
          evaluate (scalarSignalLift W ((chebTrunc N' c).eval t)) word‖ ≤
        (adjointQueryCount word : ℝ) * δ / Real.sqrt (1 - m ^ 2)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      ‖evaluate (scalarSignalLift W ((chebTrunc N c).eval t)) word -
          evaluate (scalarSignalLift W ((chebTrunc N' c).eval t)) word‖ ≤
        (adjointQueryCount word : ℝ) * Real.sqrt (2 * δ)) := by
  have hm1' : m ≤ 1 := hm1.le
  have hwin : ∀ N'' : ℕ, N'' ≤ N' → ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      (chebTrunc N'' c).eval t ∈ Set.Icc (-m) m := by
    intro N'' hN'' t ht
    have hsub : Finset.range (N'' + 1) ⊆ Finset.range (N' + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have hle : ∑ k ∈ Finset.range (N'' + 1), |c k| ≤ m :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => abs_nonneg (c k))).trans hcoeff
    obtain ⟨h1, h2⟩ := abs_le.mp ((chebTrunc_abs_eval_le N'' c ht).trans hle)
    exact ⟨h1, h2⟩
  have hwinN : ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      (chebTrunc N c).eval t ∈ Set.Icc (-m) m := hwin N hNN'
  have hwinN' : ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      (chebTrunc N' c).eval t ∈ Set.Icc (-m) m := hwin N' le_rfl
  have hgN : ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      (chebTrunc N c).eval t ∈ Set.Icc (-1) 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hwinN t ht
    exact ⟨by linarith, by linarith⟩
  have hgN' : ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      (chebTrunc N' c).eval t ∈ Set.Icc (-1) 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hwinN' t ht
    exact ⟨by linarith, by linarith⟩
  have huni : ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      |(chebTrunc N c).eval t - (chebTrunc N' c).eval t| ≤ δ := by
    intro t ht
    have h := chebTrunc_tail_abs_eval_le N N' c hNN' ht
    rw [abs_sub_comm] at h
    exact h.trans htail
  exact ⟨fun t ht =>
    (frontier1 W word m δ hw hδ hm hm1).1 _ _ (hwinN t ht) (hwinN' t ht) (huni t ht),
    fun t ht =>
      (frontier1 W word m δ hw hδ hm hm1).2 _ _ (hgN t ht) (hgN' t ht) (huni t ht)⟩

theorem chebT_natDegree_eq (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).natDegree = n := by
  rw [Polynomial.Chebyshev.natDegree_T ℝ ((n : ℕ) : ℤ), Int.natAbs_natCast]

theorem chebT_leadingCoeff_eq (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
  rw [Polynomial.Chebyshev.leadingCoeff_T ℝ ((n : ℕ) : ℤ), Int.natAbs_natCast]

theorem chebTRecurrenceEntry :
    (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)) = 1 ∧
    (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)) = Polynomial.X ∧
    (∀ n : ℕ, 0 < n →
      Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) =
        2 * Polynomial.X * Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ) -
          Polynomial.Chebyshev.T ℝ ((n - 1 : ℕ) : ℤ)) ∧
    (∀ n : ℕ,
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).natDegree = n ∧
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).leadingCoeff = 2 ^ (n - 1)) := by
  refine ⟨Polynomial.Chebyshev.T_zero ℝ, Polynomial.Chebyshev.T_one ℝ, ?_,
    fun n => ⟨chebT_natDegree_eq n, chebT_leadingCoeff_eq n⟩⟩
  intro n hn
  have h1 : (((n + 1 : ℕ) : ℤ)) = ((n : ℤ) + 1 : ℤ) := by omega
  have h2 : (((n - 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 : ℤ) := by omega
  rw [h1, h2]
  exact Polynomial.Chebyshev.T_add_one ℝ ((n : ℤ))

theorem chebTOrthogonalityEntry (n m : ℕ) :
    ∫ x in (-1 : ℝ)..1,
        (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x *
        (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x *
        Real.sqrt ((1 - x ^ 2)⁻¹) =
      if n = m then (if n = 0 then Real.pi else Real.pi / 2) else 0 := by
  rw [← Polynomial.Chebyshev.integral_measureT
      (fun x => (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x *
        (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)]
  by_cases h : n = m
  · subst h
    by_cases h0 : n = 0
    · subst h0
      simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    · simpa [h0] using
        Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero h0
  · simpa [h] using Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne h

theorem chebTNodesEntry (N : ℕ) (hN : 0 < N) :
    (∀ j : ℕ, j < N →
      (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval
        (Real.cos ((2 * j + 1) * Real.pi / (2 * N))) = 0) ∧
    (∀ x : ℝ, (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval x = 0 ↔
      ∃ j : ℕ, j < N ∧ x = Real.cos ((2 * j + 1) * Real.pi / (2 * N))) ∧
    (∀ j j' : ℕ, j < N → j' < N →
      Real.cos ((2 * j + 1) * Real.pi / (2 * N)) =
        Real.cos ((2 * j' + 1) * Real.pi / (2 * N)) → j = j') ∧
    (∀ j : ℕ, j < N → Real.cos ((2 * j + 1) * Real.pi / (2 * N)) ∈ Set.Ioo (-1) 1) := by
  have hne : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)) ≠ 0 := by
    intro h
    have h1 : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval 1 = 1 := by simp
    rw [h] at h1
    simp at h1
  have hval : ∀ j : ℕ, j < N →
      (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval
        (Real.cos ((2 * j + 1) * Real.pi / (2 * N))) = 0 := by
    intro j _
    rw [Polynomial.Chebyshev.T_real_cos, Real.cos_eq_zero_iff]
    refine ⟨(j : ℤ), ?_⟩
    push_cast
    field_simp
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hmem : x ∈ (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).roots :=
        (Polynomial.mem_roots hne).mpr hx
      rw [Polynomial.Chebyshev.roots_T_real N, Finset.mem_val, Finset.mem_image] at hmem
      obtain ⟨j, hj, hxj⟩ := hmem
      exact ⟨j, Finset.mem_range.mp hj, hxj.symm⟩
    · rintro ⟨j, hj, hxj⟩
      rw [hxj]
      exact hval j hj
  · intro j j' hj hj' heq
    have hinj : Set.InjOn
        (fun k : ℕ => Real.cos ((2 * k + 1) * Real.pi / (2 * N))) (Finset.range N) :=
      (Finset.range N).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_T_real_nodup N)
    exact hinj (Finset.mem_coe.2 <| Finset.mem_range.mpr hj)
      (Finset.mem_coe.2 <| Finset.mem_range.mpr hj') heq
  · intro j hj
    have hθ0 : (0 : ℝ) < (2 * j + 1) * Real.pi / (2 * N) :=
      div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)
    have hθπ : (2 * j + 1) * Real.pi / (2 * N) < Real.pi := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * N), mul_comm Real.pi (2 * N)]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast by omega) Real.pi_pos
    have hmemθ : (2 * j + 1) * Real.pi / (2 * N) ∈ Set.Icc 0 Real.pi :=
      ⟨hθ0.le, hθπ.le⟩
    have hlt1 : Real.cos ((2 * j + 1) * Real.pi / (2 * N)) < Real.cos (0 : ℝ) :=
      Real.strictAntiOn_cos (Set.mem_Icc.2 ⟨le_refl _, Real.pi_nonneg⟩) hmemθ hθ0
    have hgt1 : Real.cos Real.pi <
        Real.cos ((2 * j + 1) * Real.pi / (2 * N)) :=
      Real.strictAntiOn_cos hmemθ (Set.mem_Icc.2 ⟨Real.pi_nonneg, le_refl _⟩) hθπ
    rw [Real.cos_pi] at hgt1
    rw [Real.cos_zero] at hlt1
    exact ⟨hgt1, hlt1⟩

theorem chebTTrigEntry (n : ℕ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (Real.cos θ) = Real.cos ((n : ℝ) * θ) ∧
    (∀ x : ℝ, x ∈ Set.Icc (-1) 1 → ∃ φ : ℝ, φ ∈ Set.Icc 0 Real.pi ∧ x = Real.cos φ) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Polynomial.Chebyshev.T_real_cos θ ((n : ℕ) : ℤ)]
    push_cast
    rfl
  · obtain ⟨φ, hφ, hcos⟩ := Real.surjOn_cos hx
    exact ⟨φ, hφ, hcos.symm⟩

theorem chebTrunc_natDegree_le (N : ℕ) (c : ℕ → ℝ) :
    (chebTrunc N c).natDegree ≤ N := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (Polynomial.natDegree_C_mul_le (c k) _).trans ?_
  rw [chebT_natDegree_eq]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

noncomputable def unitLiftStep (c : AdjointStep Bool) : AdjointStep (Bool × Unit) :=
  match c with
  | .gate V => .gate (TensorGate V (1 : Matrix Unit Unit ℂ))
  | .forward => .forward
  | .backward => .backward

theorem signalChebyshevUnitWord_eq (n : ℕ) :
    signalChebyshevUnitWord n = (signalChebyshevWord n).map unitLiftStep := rfl

private theorem unitLiftStep_counts (word : List (AdjointStep Bool)) :
    adjointQueryCount (word.map unitLiftStep) = adjointQueryCount word ∧
      adjointGateCount (word.map unitLiftStep) = adjointGateCount word := by
  induction word with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c with
    | gate V => simpa [unitLiftStep, adjointQueryCount, adjointGateCount] using ih
    | forward => simpa [unitLiftStep, adjointQueryCount, adjointGateCount] using ih
    | backward => simpa [unitLiftStep, adjointQueryCount, adjointGateCount] using ih

private theorem unitLiftStep_wellFormed {word : List (AdjointStep Bool)}
    (hw : WellFormedAdjointCircuit word) :
    WellFormedAdjointCircuit (word.map unitLiftStep) := by
  induction word with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons c cs ih =>
    cases c with
    | gate V =>
      simp only [List.map_cons, unitLiftStep, WellFormedAdjointCircuit.gate_cons_iff] at hw ⊢
      exact ⟨tensorGate_unitary hw.1 (Matrix.unitaryGroup Unit ℂ).one_mem, ih hw.2⟩
    | forward =>
      simp only [List.map_cons, unitLiftStep, WellFormedAdjointCircuit.forward_cons_iff] at hw ⊢
      exact ih hw
    | backward =>
      simp only [List.map_cons, unitLiftStep, WellFormedAdjointCircuit.backward_cons_iff] at hw ⊢
      exact ih hw

theorem signalChebyshevUnitWord_cost (n : ℕ) :
    WellFormedAdjointCircuit (signalChebyshevUnitWord n) ∧
      adjointQueryCount (signalChebyshevUnitWord n) = n ∧
      adjointGateCount (signalChebyshevUnitWord n) = n := by
  have hc := scalar_signal_chebyshev_actual_word n 0 (by norm_num)
  rw [signalChebyshevUnitWord_eq]
  exact ⟨unitLiftStep_wellFormed hc.1,
    (unitLiftStep_counts _).1.trans hc.2.1, (unitLiftStep_counts _).2.trans hc.2.2.1⟩

theorem norm_entry_le_l2_norm {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (a b : I) : ‖M a b‖ ≤ ‖M‖ := by
  have hket : ‖toEuclidean_fromVec (Ket b)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket b)
  have hv := l2_norm_mulVec_fromVec_le M (Ket b)
  rw [hket, mul_one] at hv
  have hentry : (M *ᵥ Ket b) a = M a b := by
    simp [Matrix.mulVec, dotProduct, Ket]
  have hle : ‖(M *ᵥ Ket b) a‖ ≤ ‖toEuclidean_fromVec (M *ᵥ Ket b)‖ := by
    have h1 : ‖(M *ᵥ Ket b) a‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ Ket b) i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖(M *ᵥ Ket b) i‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ a)
    have h2 := norm_toEuclidean_fromVec_sq (M *ᵥ Ket b)
    have h4 : 0 ≤ ‖toEuclidean_fromVec (M *ᵥ Ket b)‖ := norm_nonneg _
    have h5 : 0 ≤ ‖(M *ᵥ Ket b) a‖ := norm_nonneg _
    nlinarith [h1, h2]
  rw [hentry] at hle
  exact hle.trans hv

theorem chebyshev_word_output_transport : ∀ (n : ℕ) (x y ε : ℝ),
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → 0 ≤ ε → |x - y| ≤ ε →
    ‖evaluate (scalarSignalLift Unit x) (signalChebyshevUnitWord n) -
        evaluate (scalarSignalLift Unit y) (signalChebyshevUnitWord n)‖ ≤
      (n : ℝ) * Real.sqrt (2 * ε) ∧
    ‖evaluate (scalarSignalLift Unit x) (signalChebyshevUnitWord n) -
        evaluate (scalarSignalLift Unit y) (signalChebyshevUnitWord n)‖ ≤
      (n : ℝ) * scalarSignalDistance x y ∧
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x - (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval y| ≤
      (n : ℝ) * Real.sqrt (2 * ε) := by
  intro n x y ε hx hy hε hxy
  have hcost := signalChebyshevUnitWord_cost n
  have hmain := (frontier1 Unit (signalChebyshevUnitWord n) (1 / 2) ε
    hcost.1 hε (by norm_num) (by norm_num)).2 x y hx hy hxy
  rw [hcost.2.1] at hmain
  have hb := scalar_signal_fixed_word_hybrid_bound Unit (signalChebyshevUnitWord n) x y
    hcost.1 hx hy
  rw [hcost.2.1] at hb
  have hLx := (scalar_signal_chebyshev_actual_word n x hx).2.2.2.2.2
  have hLy := (scalar_signal_chebyshev_actual_word n y hy).2.2.2.2.2
  have hTx := (scalar_signal_chebyshev_actual_word n x hx).2.2.2.2.1
  have hTy := (scalar_signal_chebyshev_actual_word n y hy).2.2.2.2.1
  have hentry :
      (evaluate (scalarSignalLift Unit x) (signalChebyshevUnitWord n) -
          evaluate (scalarSignalLift Unit y) (signalChebyshevUnitWord n)) (false, ()) (false, ()) =
        ((Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x - (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval y :
          ℝ) := by
    rw [hLx, hLy, Matrix.sub_apply, tensorGate_apply, tensorGate_apply,
      Matrix.one_apply_eq, mul_one, mul_one, hTx, hTy, Complex.ofReal_sub]
  refine ⟨hmain, hb, ?_⟩
  have hnorm : ‖(evaluate (scalarSignalLift Unit x) (signalChebyshevUnitWord n) -
        evaluate (scalarSignalLift Unit y) (signalChebyshevUnitWord n)) (false, ()) (false, ())‖ =
      |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x - (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval y| := by
    rw [hentry]
    exact Complex.norm_real _
  rw [← hnorm]
  exact (norm_entry_le_l2_norm _ (false, ()) (false, ())).trans hmain

open Complex in

private theorem cexp_re (φ : ℝ) : (cexp (φ * I)).re = Real.cos φ := by
  rw [Complex.exp_mul_I, Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
  simp

open Complex in

private theorem cexp_im (φ : ℝ) : (cexp (φ * I)).im = Real.sin φ := by
  rw [Complex.exp_mul_I, Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.I_im, Complex.I_re]
  simp

open Complex in

private theorem re_pow_cexp_mul (q φ : ℝ) (k : ℕ) :
    (((q : ℂ) * cexp (φ * I)) ^ k).re = q ^ k * Real.cos (↑k * φ) := by
  have hpow : ((q : ℂ) * cexp (φ * I)) ^ k = ↑(q ^ k) * cexp (↑(↑k * φ) * I) := by
    rw [mul_pow, Complex.ofReal_pow, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, Complex.mul_re, cexp_re, Complex.ofReal_re, Complex.ofReal_im]
  simp

open Complex in

private theorem norm_cexp_mul (q φ : ℝ) : ‖((q : ℂ) * cexp (φ * I))‖ = |q| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, mul_one]
  exact Real.norm_eq_abs q

open Complex in

private theorem poisson_dev_gen (z : ℂ) (hz1 : ‖z‖ < 1) (n : ℕ) :
    |(1 - Complex.normSq z) / Complex.normSq (1 - z) -
      (2 * (∑ k ∈ Finset.range (n + 1), z ^ k).re - 1)| ≤ 2 * ‖z‖ ^ (n + 1) / (1 - ‖z‖) := by
  have hzne : z ≠ 1 := by
    intro h
    rw [h] at hz1
    exact absurd hz1 (by norm_num)
  have hone : (1 : ℂ) - z ≠ 0 := by
    rw [sub_ne_zero]
    exact Ne.symm hzne
  have hNpos : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hone
  have hznn : 0 ≤ ‖z‖ := norm_nonneg z
  have h1z : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    have hle : ‖(1 : ℂ)‖ ≤ ‖1 - z‖ + ‖z‖ := by
      have h := norm_add_le (1 - z) z
      rwa [sub_add_cancel] at h
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    linarith
  have hgs : ∑ k ∈ Finset.range (n + 1), z ^ k = (1 - z ^ (n + 1)) / (1 - z) := by
    have h := geom_sum_eq hzne (n + 1)
    rw [← neg_sub 1 (z ^ (n + 1)), ← neg_sub 1 z, neg_div_neg_eq] at h
    exact h
  have hsplit : 1 / (1 - z) - ∑ k ∈ Finset.range (n + 1), z ^ k = z ^ (n + 1) / (1 - z) := by
    rw [hgs, div_sub_div_same, sub_sub_cancel]
  have hpoi : 2 * (1 / (1 - z)).re - 1 = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [one_div, Complex.inv_re]
    field_simp
    rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  have hkey : (1 - Complex.normSq z) / Complex.normSq (1 - z) -
      (2 * (∑ k ∈ Finset.range (n + 1), z ^ k).re - 1) =
      2 * ((z ^ (n + 1) / (1 - z)) : ℂ).re := by
    have e1 : (1 - Complex.normSq z) / Complex.normSq (1 - z) = 2 * (1 / (1 - z)).re - 1 :=
      hpoi.symm
    have e2 : (1 / (1 - z)).re - (∑ k ∈ Finset.range (n + 1), z ^ k).re =
        (z ^ (n + 1) / (1 - z)).re := by
      rw [← Complex.sub_re, hsplit]
    rw [e1,
      show (2 * (1 / (1 - z)).re - 1) - (2 * (∑ k ∈ Finset.range (n + 1), z ^ k).re - 1) =
        2 * ((1 / (1 - z)).re - (∑ k ∈ Finset.range (n + 1), z ^ k).re) from by ring,
      e2]
  rw [hkey]
  have hre : |2 * ((z ^ (n + 1) / (1 - z)) : ℂ).re| ≤ 2 * ‖z ^ (n + 1) / (1 - z)‖ := by
    have h1 := Complex.re_le_norm (z ^ (n + 1) / (1 - z))
    have h2 := Complex.re_le_norm (-(z ^ (n + 1) / (1 - z)))
    rw [Complex.neg_re, norm_neg] at h2
    rw [abs_le]
    constructor <;> linarith
  refine hre.trans ?_
  rw [norm_div, norm_pow]
  have hpos1 : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hpos2 : (0 : ℝ) < ‖1 - z‖ := lt_of_lt_of_le hpos1 h1z
  have e : 2 * (‖z‖ ^ (n + 1) / ‖1 - z‖) = 2 * ‖z‖ ^ (n + 1) / ‖1 - z‖ := by ring
  rw [e, div_le_div_iff₀ hpos2 hpos1]
  have hP : (0 : ℝ) ≤ 2 * ‖z‖ ^ (n + 1) := by positivity
  exact mul_le_mul_of_nonneg_left h1z hP

open Complex in

private theorem poisson_dev (q φ : ℝ) (hq1 : |q| < 1) (n : ℕ) :
    |(1 - q ^ 2) / (1 - 2 * q * Real.cos φ + q ^ 2) -
      (2 * (∑ k ∈ Finset.range (n + 1), ((q : ℂ) * cexp (φ * I)) ^ k).re - 1)| ≤
      2 * |q| ^ (n + 1) / (1 - |q|) := by
  have hz1 : ‖((q : ℂ) * cexp (φ * I))‖ < 1 := by
    rw [norm_cexp_mul]
    exact hq1
  have hpy : Complex.normSq ((q : ℂ) * cexp (φ * I)) = q ^ 2 := by
    rw [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, cexp_re, cexp_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h := Real.sin_sq_add_cos_sq φ
    nlinarith [h]
  have hK : Complex.normSq (1 - (q : ℂ) * cexp (φ * I)) =
      1 - 2 * q * Real.cos φ + q ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, cexp_re, cexp_im, Complex.ofReal_re, Complex.ofReal_im]
    have h := Real.sin_sq_add_cos_sq φ
    nlinarith [h]
  have hmain := poisson_dev_gen ((q : ℂ) * cexp (φ * I)) hz1 n
  rw [hpy, hK, norm_cexp_mul] at hmain
  exact hmain

noncomputable def recipChebRatio (δ : ℝ) : ℝ := (1 - Real.sqrt δ) / (1 + Real.sqrt δ)

noncomputable def recipChebCoeff (δ : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 1 / Real.sqrt δ else (2 / Real.sqrt δ) * (-(recipChebRatio δ)) ^ k

private theorem recipChebRatio_bounds (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ recipChebRatio δ ∧ recipChebRatio δ < 1 ∧
      1 - recipChebRatio δ = 2 * Real.sqrt δ / (1 + Real.sqrt δ) := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hs1 : Real.sqrt δ ≤ 1 := (Real.sqrt_le_one).mpr hδ1
  refine ⟨?_, ?_, ?_⟩
  · unfold recipChebRatio
    exact div_nonneg (by nlinarith) (by nlinarith)
  · unfold recipChebRatio
    rw [div_lt_iff₀ (by nlinarith : (0 : ℝ) < 1 + Real.sqrt δ)]
    nlinarith
  · unfold recipChebRatio
    field_simp
    ring

private theorem geom_sum_le_inv (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ k ≤ 1 / (1 - r) := by
  have hrne : r ≠ 1 := ne_of_lt hr1
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have h : ∑ k ∈ Finset.range n, r ^ k = (1 - r ^ n) / (1 - r) := by
    have h2 := geom_sum_eq (x := r) hrne n
    rw [← neg_sub 1 (r ^ n), ← neg_sub 1 r, neg_div_neg_eq] at h2
    exact h2
  rw [h, div_le_iff₀ hpos]
  field_simp
  linarith [pow_nonneg hr0 n]

private theorem recip_affine_poisson (s cφ : ℝ) (hs : 0 < s) :
    (1 + s ^ 2) / 2 + (1 - s ^ 2) / 2 * cφ =
      s / (1 - ((1 - s) / (1 + s)) ^ 2) *
        (1 + 2 * ((1 - s) / (1 + s)) * cφ + ((1 - s) / (1 + s)) ^ 2) := by
  have h1 : (1 + s : ℝ) ≠ 0 := by linarith
  have h2 : (1 : ℝ) - ((1 - s) / (1 + s)) ^ 2 = 4 * s / (1 + s) ^ 2 := by
    field_simp
    ring
  have h4 : s / (1 - ((1 - s) / (1 + s)) ^ 2) = (1 + s) ^ 2 / 4 := by
    rw [h2]
    field_simp
  rw [h4]
  field_simp
  ring

private theorem chebTrunc_eval_cos (n : ℕ) (c : ℕ → ℝ) (φ : ℝ) :
    (chebTrunc n c).eval (Real.cos φ) =
      ∑ k ∈ Finset.range (n + 1), c k * Real.cos ((k : ℝ) * φ) := by
  rw [chebTrunc_eval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.T_real_cos φ ((k : ℕ) : ℤ)]
  push_cast
  ring_nf

theorem recipWindowIcc (δ : ℝ) (hδ1 : δ ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    (1 + δ) / 2 + (1 - δ) / 2 * t ∈ Set.Icc δ 1 := by
  have hb : (0 : ℝ) ≤ (1 - δ) / 2 := by
    field_simp
    nlinarith
  have hlow : (1 - δ) / 2 * (-1) ≤ (1 - δ) / 2 * t :=
    mul_le_mul_of_nonneg_left ht.1 hb
  have hhigh : (1 - δ) / 2 * t ≤ (1 - δ) / 2 * 1 :=
    mul_le_mul_of_nonneg_left ht.2 hb
  have heq1 : (1 + δ) / 2 + (1 - δ) / 2 * (-1) = δ := by ring
  have heq2 : (1 + δ) / 2 + (1 - δ) / 2 * 1 = 1 := by ring
  constructor
  · linarith
  · linarith

theorem recipChebCoeff_abs_sum_le (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), |recipChebCoeff δ k| ≤ 1 / δ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hrb := recipChebRatio_bounds δ hδ hδ1
  have hrw : recipChebRatio δ = (1 - Real.sqrt δ) / (1 + Real.sqrt δ) := rfl
  have h0 : |recipChebCoeff δ 0| = 1 / Real.sqrt δ := by
    simp only [recipChebCoeff]
    exact abs_of_pos (div_pos (by positivity) hs)
  have hrest : ∀ k : ℕ, |recipChebCoeff δ (k + 1)| =
      (2 / Real.sqrt δ) * recipChebRatio δ ^ (k + 1) := by
    intro k
    simp only [recipChebCoeff, if_neg (Nat.succ_ne_zero k)]
    rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg hrb.1, abs_of_pos (by positivity)]
  have hsum : ∑ k ∈ Finset.range (n + 1), |recipChebCoeff δ k| =
      1 / Real.sqrt δ + ∑ k ∈ Finset.range n, (2 / Real.sqrt δ) * recipChebRatio δ ^ (k + 1) := by
    rw [Finset.sum_range_succ', h0, Finset.sum_congr rfl (fun k _ => hrest k)]
    ring
  have hscale : ∑ k ∈ Finset.range n, (2 / Real.sqrt δ) * recipChebRatio δ ^ (k + 1) =
      (2 / Real.sqrt δ) * recipChebRatio δ * ∑ k ∈ Finset.range n, recipChebRatio δ ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
  have hgeom := geom_sum_le_inv (recipChebRatio δ) hrb.1 hrb.2.1 n
  have hfinal : 1 / Real.sqrt δ +
      (2 / Real.sqrt δ) * recipChebRatio δ * (1 / (1 - recipChebRatio δ)) =
      1 / (Real.sqrt δ) ^ 2 := by
    rw [hrb.2.2, hrw]
    field_simp
    ring
  have hlast : 1 / (Real.sqrt δ) ^ 2 = 1 / δ := by
    rw [Real.sq_sqrt (le_of_lt hδ)]
  have hmul : (2 / Real.sqrt δ) * recipChebRatio δ * ∑ k ∈ Finset.range n, recipChebRatio δ ^ k ≤
      (2 / Real.sqrt δ) * recipChebRatio δ * (1 / (1 - recipChebRatio δ)) :=
    mul_le_mul_of_nonneg_left hgeom (mul_nonneg (by positivity) hrb.1)
  rw [hsum, hscale]
  exact (add_le_add (le_refl _) hmul).trans ((le_of_eq hfinal).trans (le_of_eq hlast))

theorem recipChebTruncAbsEvalLe (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    |(chebTrunc n (recipChebCoeff δ)).eval t| ≤ 1 / δ :=
  (chebTrunc_abs_eval_le n (recipChebCoeff δ) ht).trans (recipChebCoeff_abs_sum_le δ hδ hδ1 n)

open Complex in

theorem recipChebTruncError (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    |1 / ((1 + δ) / 2 + (1 - δ) / 2 * t) - (chebTrunc n (recipChebCoeff δ)).eval t| ≤
      (1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / δ := by
  have hrb := recipChebRatio_bounds δ hδ hδ1
  set s := Real.sqrt δ with hsdef
  set r := recipChebRatio δ with hrdef
  have hs : 0 < s := Real.sqrt_pos.mpr hδ
  have hs2 : s ^ 2 = δ := Real.sq_sqrt (le_of_lt hδ)
  set φ := Real.arccos t with hφdef
  have hφ : Real.cos φ = t := Real.cos_arccos ht.1 ht.2
  have hcosb : |Real.cos φ| ≤ 1 := by rw [hφ]; exact abs_le.mpr ⟨ht.1, ht.2⟩
  have hKpos : (0 : ℝ) < 1 + 2 * r * Real.cos φ + r ^ 2 := by
    have hc := abs_le.mp hcosb
    nlinarith [hrb.1, hrb.2.1, hc.1, hc.2]
  have h2 : 1 / ((1 + δ) / 2 + (1 - δ) / 2 * t) =
      (1 - r ^ 2) / (s * (1 + 2 * r * Real.cos φ + r ^ 2)) := by
    have hrw : r = (1 - s) / (1 + s) := by
      rw [hrdef]
      unfold recipChebRatio
      rw [← hsdef]
    have haff := recip_affine_poisson s (Real.cos φ) hs
    have hr2ne : (1 : ℝ) - ((1 - s) / (1 + s)) ^ 2 ≠ 0 := by
      have hq : (1 : ℝ) - ((1 - s) / (1 + s)) ^ 2 = 4 * s / (1 + s) ^ 2 := by
        field_simp
        ring
      rw [hq]
      positivity
    have hKne : (1 : ℝ) + 2 * ((1 - s) / (1 + s)) * Real.cos φ + ((1 - s) / (1 + s)) ^ 2 ≠ 0 := by
      rw [← hrw]
      exact ne_of_gt hKpos
    have hsne : s ≠ 0 := ne_of_gt hs
    have h1ne : (1 + s : ℝ) ≠ 0 := by linarith
    have hq2 : s / (1 - ((1 - s) / (1 + s)) ^ 2) = (1 + s) ^ 2 / 4 := by
      have hq : (1 : ℝ) - ((1 - s) / (1 + s)) ^ 2 = 4 * s / (1 + s) ^ 2 := by
        field_simp
        ring
      rw [hq]
      field_simp
    rw [← hs2, hrw, ← hφ, haff, hq2]
    field_simp
    ring
  have htr : (chebTrunc n (recipChebCoeff δ)).eval t =
      (1 / s) * (2 * (∑ k ∈ Finset.range (n + 1),
        ((-(r : ℝ) : ℂ) * cexp (φ * I)) ^ k).re - 1) := by
    have hsum : ∑ k ∈ Finset.range n, (((-(r : ℝ) : ℂ) * cexp (φ * I)) ^ (k + 1)).re =
        ∑ k ∈ Finset.range n, (-(r : ℝ)) ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * φ) :=
      Finset.sum_congr rfl fun k _ => by
        have h := re_pow_cexp_mul (-(r : ℝ)) φ (k + 1)
        rw [Complex.ofReal_neg] at h
        exact h
    rw [← hφ, chebTrunc_eval_cos, Complex.re_sum, Finset.sum_range_succ', Finset.sum_range_succ',
      pow_zero, Complex.one_re, hsum]
    simp only [recipChebCoeff, Nat.succ_ne_zero, if_true, if_false, ← hrdef, ← hsdef,
      Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [show (∑ k ∈ Finset.range n, (2 / s) * (-(r : ℝ)) ^ (k + 1) * Real.cos (↑(k + 1) * φ)) =
        (2 / s) * ∑ k ∈ Finset.range n, (-(r : ℝ)) ^ (k + 1) * Real.cos (↑(k + 1) * φ) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  have hdev := poisson_dev (-(r : ℝ)) φ
    (by rw [abs_neg, abs_of_nonneg hrb.1]; exact hrb.2.1) n
  have hKe : (1 : ℝ) - 2 * (-(r : ℝ)) * Real.cos φ + (-(r : ℝ)) ^ 2 =
      1 + 2 * r * Real.cos φ + r ^ 2 := by ring
  have hKe2 : (1 : ℝ) - (-(r : ℝ)) ^ 2 = 1 - r ^ 2 := by ring
  rw [hKe, hKe2, abs_neg, abs_of_nonneg hrb.1] at hdev
  simp only [Complex.ofReal_neg] at hdev
  rw [h2, htr]
  have hsplit : (1 - r ^ 2) / (s * (1 + 2 * r * Real.cos φ + r ^ 2)) -
      (1 / s) * (2 * (∑ k ∈ Finset.range (n + 1),
        ((-(r : ℝ) : ℂ) * cexp (φ * I)) ^ k).re - 1) =
      (1 / s) * ((1 - r ^ 2) / (1 + 2 * r * Real.cos φ + r ^ 2) -
        (2 * (∑ k ∈ Finset.range (n + 1),
          ((-(r : ℝ) : ℂ) * cexp (φ * I)) ^ k).re - 1)) := by
    have hKne : (1 : ℝ) + 2 * r * Real.cos φ + r ^ 2 ≠ 0 := ne_of_gt hKpos
    field_simp
  rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / s)]
  have hconst : (1 / s) * (2 * r ^ (n + 1) / (1 - r)) = (1 + s) * r ^ (n + 1) / s ^ 2 := by
    rw [hrb.2.2]
    field_simp
  rw [hs2] at hconst
  exact (mul_le_mul_of_nonneg_left hdev (by positivity : (0 : ℝ) ≤ 1 / s)).trans
    (le_of_eq hconst)

theorem recipChebTruncWordTransport (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (δ : ℝ) (n : ℕ) (m : ℝ)
    (hw : WellFormedAdjointCircuit word) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 1 / 2 ≤ m) (hm1 : m < 1) :
    (∀ t ∈ Set.Icc (-1) 1,
      ‖evaluate (scalarSignalLift W ((δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t)) word -
          evaluate (scalarSignalLift W (δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)))) word‖ ≤
        (adjointQueryCount word : ℝ) * ((1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / 2) /
          Real.sqrt (1 - m ^ 2)) ∧
    (∀ t ∈ Set.Icc (-1) 1,
      ‖evaluate (scalarSignalLift W ((δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t)) word -
          evaluate (scalarSignalLift W (δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)))) word‖ ≤
        (adjointQueryCount word : ℝ) * Real.sqrt (2 * ((1 + Real.sqrt δ) *
          (recipChebRatio δ) ^ (n + 1) / 2))) := by
  have hrb := recipChebRatio_bounds δ hδ hδ1
  have hε : (0 : ℝ) ≤ (1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / 2 :=
    div_nonneg (mul_nonneg (by positivity) (pow_nonneg hrb.1 _)) (by norm_num)
  have hmain := frontier1 W word m _ hw hε (by nlinarith) hm1
  have hu : ∀ t : ℝ, t ∈ Set.Icc (-1) 1 →
      (0 : ℝ) < 2 * ((1 + δ) / 2 + (1 - δ) / 2 * t) := by
    intro t ht
    obtain ⟨hw1, hw2⟩ := recipWindowIcc δ hδ1 ht
    exact mul_pos (by norm_num) (by linarith)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨hw1, hw2⟩ := recipWindowIcc δ hδ1 ht
    have hupos : (0 : ℝ) < (1 + δ) / 2 + (1 - δ) / 2 * t := by linarith
    have hxabs : |(δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t| ≤ 1 / 2 := by
      have h1 := recipChebTruncAbsEvalLe δ hδ hδ1 n ht
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
      have hcalc : (δ / 2) * (1 / δ) = 1 / 2 := by field_simp
      exact (mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ δ / 2)).trans_eq hcalc
    have hx : (δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t ∈ Set.Icc (-m) m := by
      obtain ⟨h1, h2⟩ := abs_le.mp hxabs
      exact ⟨by linarith, by linarith⟩
    have hyu : δ / 2 ≤ δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) := by
      rw [le_div_iff₀ (hu t ht)]
      have hrew : (δ / 2) * (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) =
          δ * ((1 + δ) / 2 + (1 - δ) / 2 * t) := by ring
      rw [hrew]
      have hkey : δ * ((1 + δ) / 2 + (1 - δ) / 2 * t) ≤ δ * 1 :=
        mul_le_mul_of_nonneg_left hw2 (le_of_lt hδ)
      linarith
    have hyo : δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (hu t ht)]
      have hrew : (1 / 2) * (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) =
          (1 + δ) / 2 + (1 - δ) / 2 * t := by ring
      linarith
    have hy : δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) ∈ Set.Icc (-m) m :=
      ⟨by linarith, by linarith⟩
    have herr : |(δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t -
        δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t))| ≤
        (1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / 2 := by
      have h1 := recipChebTruncError δ hδ hδ1 n ht
      rw [abs_sub_comm] at h1
      have hsplit : (δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t -
          δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) =
          (δ / 2) * ((chebTrunc n (recipChebCoeff δ)).eval t -
            1 / ((1 + δ) / 2 + (1 - δ) / 2 * t)) := by
        field_simp
      rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
      have hcalc : (δ / 2) * ((1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / δ) =
          (1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / 2 := by
        field_simp
      exact (mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ δ / 2)).trans_eq hcalc
    exact hmain.1 _ _ hx hy herr
  · obtain ⟨hw1, hw2⟩ := recipWindowIcc δ hδ1 ht
    have habs : |(δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t| ≤ 1 := by
      have h1 := recipChebTruncAbsEvalLe δ hδ hδ1 n ht
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
      have h2 : (δ / 2) * (1 / δ) ≤ 1 := by
        field_simp
        nlinarith
      exact (mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ δ / 2)).trans h2
    have hx : (δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t ∈ Set.Icc (-1) 1 := by
      obtain ⟨h1, h2⟩ := abs_le.mp habs
      exact ⟨by linarith, by linarith⟩
    have hyu : (0 : ℝ) < δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) :=
      div_pos hδ (hu t ht)
    have hyo : δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (hu t ht)]
      have hrew : (1 / 2) * (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) =
          (1 + δ) / 2 + (1 - δ) / 2 * t := by ring
      linarith
    have hy : δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) ∈ Set.Icc (-1) 1 :=
      ⟨by linarith, by linarith⟩
    have herr : |(δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t -
        δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t))| ≤
        (1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / 2 := by
      have h1 := recipChebTruncError δ hδ hδ1 n ht
      rw [abs_sub_comm] at h1
      have hsplit : (δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t -
          δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)) =
          (δ / 2) * ((chebTrunc n (recipChebCoeff δ)).eval t -
            1 / ((1 + δ) / 2 + (1 - δ) / 2 * t)) := by
        field_simp
      rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
      have hcalc : (δ / 2) * ((1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / δ) =
          (1 + Real.sqrt δ) * (recipChebRatio δ) ^ (n + 1) / 2 := by
        field_simp
      exact (mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ δ / 2)).trans_eq hcalc
    exact hmain.2 _ _ hx hy herr

private theorem arctan_add_inv_eq_pi_div_two (u : ℝ) (hu : 0 < u) :
    Real.arctan u + Real.arctan u⁻¹ = Real.pi / 2 := by
  have hu' : 0 < u⁻¹ := inv_pos.mpr hu
  have ha : 0 < Real.arctan u := Real.arctan_pos.mpr hu
  have hb : 0 < Real.arctan u⁻¹ := Real.arctan_pos.mpr hu'
  have hab : Real.arctan u < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hab' : Real.arctan u⁻¹ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hsin : Real.sin (Real.arctan u + Real.arctan u⁻¹) = 1 := by
    have h1 : Real.sin (Real.arctan u) = u * Real.cos (Real.arctan u) := by
      rw [Real.sin_arctan, Real.cos_arctan]
      field_simp
    have h2 : Real.sin (Real.arctan u⁻¹) = u⁻¹ * Real.cos (Real.arctan u⁻¹) := by
      rw [Real.sin_arctan, Real.cos_arctan]
      field_simp
    have hsqrt : Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + u⁻¹ ^ 2) = u + u⁻¹ := by
      rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 1 + u ^ 2),
        show (1 + u ^ 2) * (1 + u⁻¹ ^ 2) = (u + u⁻¹) ^ 2 from by
          field_simp
          ring,
        Real.sqrt_sq (by positivity : (0:ℝ) ≤ u + u⁻¹)]
    have hprod : Real.cos (Real.arctan u) * Real.cos (Real.arctan u⁻¹) = 1 / (u + u⁻¹) := by
      rw [Real.cos_arctan, Real.cos_arctan, ← hsqrt]
      field_simp
    rw [Real.sin_add, h1, h2]
    have hrw : u * Real.cos (Real.arctan u) * Real.cos (Real.arctan u⁻¹) +
        Real.cos (Real.arctan u) * (u⁻¹ * Real.cos (Real.arctan u⁻¹)) =
        (u + u⁻¹) * (Real.cos (Real.arctan u) * Real.cos (Real.arctan u⁻¹)) := by
      ring
    rw [hrw, hprod]
    field_simp
  have hcos : Real.cos (Real.arctan u + Real.arctan u⁻¹) = 0 := by
    have h := Real.sin_sq_add_cos_sq (Real.arctan u + Real.arctan u⁻¹)
    rw [hsin] at h
    have hp : Real.cos (Real.arctan u + Real.arctan u⁻¹) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp hp
  have hzero : Real.sin (Real.arctan u + Real.arctan u⁻¹ - Real.pi / 2) = 0 := by
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, hcos]
    simp
  have heq : Real.arctan u + Real.arctan u⁻¹ - Real.pi / 2 = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos, ha, hab])
      (by nlinarith [Real.pi_pos, hb, hab'])).mp hzero
  linarith

open Complex in

private theorem cexp_sq (θ : ℝ) : (cexp (θ * I)) ^ 2 = cexp ((2 * θ : ℝ) * I) := by
  have h : (2 * θ : ℝ) * I = θ * I + θ * I := by
    push_cast
    ring
  rw [sq, ← Complex.exp_add, h]

open Complex in

private theorem sq_wave_denom_re (θ t : ℝ) :
    (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2).re = 1 + t ^ 2 * Real.cos (2 * θ) := by
  rw [cexp_sq θ, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, cexp_re]

open Complex in

private theorem sq_wave_denom_im (θ t : ℝ) :
    (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2).im = t ^ 2 * Real.sin (2 * θ) := by
  rw [cexp_sq θ, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, cexp_im]
  ring

open Complex in

private theorem sq_wave_denom_ne {θ : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) (t : ℝ) :
    1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2 ≠ 0 := by
  intro h0
  have hre : 1 + t ^ 2 * Real.cos (2 * θ) = 0 := by
    have hx := (Complex.ext_iff.mp h0).1
    rw [sq_wave_denom_re θ t] at hx
    simpa using hx
  have him : t ^ 2 * Real.sin (2 * θ) = 0 := by
    have hx := (Complex.ext_iff.mp h0).2
    rw [sq_wave_denom_im θ t] at hx
    simpa using hx
  by_cases ht : t = 0
  · subst ht
    norm_num at him hre
  · have hsin : Real.sin (2 * θ) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) ht
      · exact h
    have h2θ : 2 * θ = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])).mp hsin
    have hcos2 : Real.cos (2 * θ) = 1 := by
      rw [h2θ]
      norm_num
    rw [hcos2] at hre
    nlinarith [sq_nonneg t]

open Complex in

private theorem sq_wave_denom_normSq (θ t : ℝ) :
    Complex.normSq (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2) =
      (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 := by
  have e1 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 :=
    Real.cos_two_mul' θ
  have e3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have e4 : Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * θ)
  rw [Complex.normSq_apply, sq_wave_denom_re, sq_wave_denom_im]
  linear_combination (2 * t ^ 2) * e1 + (t ^ 4) * e4 - (1 + t ^ 4) * e3

open Complex in

private theorem sq_wave_integrand_re (θ t : ℝ) (hc : 0 < Real.cos θ) :
    ((cexp (θ * I)) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)).re =
      (1 + t ^ 2) * Real.cos θ /
        ((1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2) := by
  have hzre : (cexp (θ * I)).re = Real.cos θ := cexp_re θ
  have hzim : (cexp (θ * I)).im = Real.sin θ := cexp_im θ
  have hwre : (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2).re =
      1 + t ^ 2 * Real.cos (2 * θ) := sq_wave_denom_re θ t
  have hwim : (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2).im =
      t ^ 2 * Real.sin (2 * θ) := sq_wave_denom_im θ t
  have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hc)
  have hD : 0 < (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 := by
    have hpos : (0:ℝ) < (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 :=
      mul_pos (by positivity) hc2
    have hnn : (0:ℝ) ≤ (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 :=
      mul_nonneg (sq_nonneg (1 - t ^ 2)) (sq_nonneg _)
    linarith
  have hzne : 1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2 ≠ 0 := by
    intro h0
    have hns := Complex.normSq_eq_norm_sq (z := 1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)
    rw [sq_wave_denom_normSq, h0] at hns
    norm_num at hns
    linarith
  rw [div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    hwre, hwim, hzre, hzim, sq_wave_denom_normSq]
  have e4 : Real.cos θ * Real.cos (2 * θ) + Real.sin θ * Real.sin (2 * θ) =
      Real.cos θ := by
    have hcsub : Real.cos θ =
        Real.cos (2 * θ) * Real.cos θ + Real.sin (2 * θ) * Real.sin θ := by
      have h := Real.cos_sub (2 * θ) θ
      rw [show 2 * θ - θ = θ from by ring] at h
      exact h
    linear_combination (-1) * hcsub
  have hnum : Real.cos θ * (1 + t ^ 2 * Real.cos (2 * θ)) +
      Real.sin θ * (t ^ 2 * Real.sin (2 * θ)) = (1 + t ^ 2) * Real.cos θ := by
    linear_combination t ^ 2 * e4
  have hDne : (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 ≠ 0 :=
    ne_of_gt hD
  field_simp
  linarith [hnum]

open Complex in

private theorem sq_wave_value_re (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    (∫ t in (0 : ℝ)..1, ((cexp (θ * I)) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)).re) =
      Real.pi / 4 := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hθ2⟩
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (by nlinarith [Real.pi_pos, hθ2])
  have heq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [intervalIntegral.integral_congr (a := (0 : ℝ)) (b := 1)
    (fun t _ => sq_wave_integrand_re θ t hc)]
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => (Real.arctan ((t - Real.sin θ) / Real.cos θ) +
        Real.arctan ((t + Real.sin θ) / Real.cos θ)) / 2)
        ((1 + t ^ 2) * Real.cos θ /
          ((1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2)) t := by
    intro t _
    have hcne : Real.cos θ ≠ 0 := ne_of_gt hc
    have hDne : (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 ≠ 0 := by
      have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_ne_zero hcne
      have hpos : (0 : ℝ) < (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 := mul_pos (by positivity) hc2
      have hnn : (0 : ℝ) ≤ (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 :=
        mul_nonneg (sq_nonneg (1 - t ^ 2)) (sq_nonneg _)
      exact ne_of_gt (by linarith)
    have h1 : HasDerivAt (fun t => (t - Real.sin θ) / Real.cos θ) (1 / Real.cos θ) t := by
      refine (((hasDerivAt_id t).sub (hasDerivAt_const _ _)).div
        (hasDerivAt_const _ _) (ne_of_gt hc)).congr_deriv ?_
      simp only [sub_zero, mul_zero]
      field_simp
      try ring
    have h2 : HasDerivAt (fun t => (t + Real.sin θ) / Real.cos θ) (1 / Real.cos θ) t := by
      refine (((hasDerivAt_id t).add (hasDerivAt_const _ _)).div
        (hasDerivAt_const _ _) (ne_of_gt hc)).congr_deriv ?_
      simp only [add_zero, mul_zero]
      field_simp
      try ring
    have hA : HasDerivAt (fun t => Real.arctan ((t - Real.sin θ) / Real.cos θ))
        ((1 / (1 + ((t - Real.sin θ) / Real.cos θ) ^ 2)) * (1 / Real.cos θ)) t :=
      (Real.hasDerivAt_arctan _).comp t h1
    have hB : HasDerivAt (fun t => Real.arctan ((t + Real.sin θ) / Real.cos θ))
        ((1 / (1 + ((t + Real.sin θ) / Real.cos θ) ^ 2)) * (1 / Real.cos θ)) t :=
      (Real.hasDerivAt_arctan _).comp t h2
    have hval : ((1 / (1 + ((t - Real.sin θ) / Real.cos θ) ^ 2)) * (1 / Real.cos θ) +
        (1 / (1 + ((t + Real.sin θ) / Real.cos θ) ^ 2)) * (1 / Real.cos θ)) / 2 =
        (1 + t ^ 2) * Real.cos θ /
          ((1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2) := by
      field_simp
      linear_combination (2 * t ^ 2 * ((1 + t ^ 2) * (t ^ 2 + Real.sin θ ^ 2 +
        Real.cos θ ^ 2) - 4 * Real.sin θ ^ 2)) * heq
    exact (hA.add hB).div_const 2 |>.congr_deriv hval
  have hint : IntervalIntegrable
      (fun t : ℝ => (1 + t ^ 2) * Real.cos θ /
        ((1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hc)
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro x
    have hp : (0 : ℝ) < (1 + x ^ 2) ^ 2 * Real.cos θ ^ 2 :=
      mul_pos (by positivity) hc2
    have hnn : (0 : ℝ) ≤ (1 - x ^ 2) ^ 2 * Real.sin θ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact ne_of_gt (by linarith)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1) hder hint
  have hinv : (1 - Real.sin θ) / Real.cos θ = ((1 + Real.sin θ) / Real.cos θ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    field_simp
    linarith [heq]
  have hpair : Real.arctan ((1 + Real.sin θ) / Real.cos θ) +
      Real.arctan ((1 - Real.sin θ) / Real.cos θ) = Real.pi / 2 := by
    rw [hinv]
    exact arctan_add_inv_eq_pi_div_two _
      (div_pos (by linarith : (0 : ℝ) < 1 + Real.sin θ) hc)
  rw [hFTC, zero_sub, zero_add, neg_div, Real.arctan_neg, neg_add_cancel, zero_div,
    sub_zero,
    add_comm (Real.arctan ((1 - Real.sin θ) / Real.cos θ))
      (Real.arctan ((1 + Real.sin θ) / Real.cos θ)),
    hpair]
  ring

private theorem interval_integrable_finset_sum (f : ℕ → ℝ → ℂ) (s : Finset ℕ) (a b : ℝ)
    (hf : ∀ k ∈ s, IntervalIntegrable (f k) MeasureTheory.volume a b) :
    IntervalIntegrable (fun t => ∑ k ∈ s, f k t) MeasureTheory.volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact intervalIntegrable_const
  | insert k s hk ih =>
    have hf' : ∀ j ∈ s, IntervalIntegrable (f j) MeasureTheory.volume a b := fun j hj =>
      hf j (Finset.mem_insert_of_mem hj)
    have h := (hf k (Finset.mem_insert_self k s)).add (ih hf')
    simp only [Finset.sum_insert hk] at h ⊢
    exact h

private theorem integral_finset_sum_interval (f : ℕ → ℝ → ℂ) (s : Finset ℕ) (a b : ℝ)
    (hf : ∀ k ∈ s, IntervalIntegrable (f k) MeasureTheory.volume a b) :
    ∫ t in a..b, ∑ k ∈ s, f k t = ∑ k ∈ s, ∫ t in a..b, f k t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have hf' : ∀ j ∈ s, IntervalIntegrable (f j) MeasureTheory.volume a b := fun j hj =>
      hf j (Finset.mem_insert_of_mem hj)
    have hsum : IntervalIntegrable (fun t => ∑ j ∈ s, f j t) MeasureTheory.volume a b :=
      interval_integrable_finset_sum f s a b hf'
    simp only [Finset.sum_insert hk]
    rw [intervalIntegral.integral_add (hf k (Finset.mem_insert_self k s)) hsum, ih hf']

private theorem sq_wave_pow_int (n : ℕ) : ∫ t in (0 : ℝ)..1, t ^ n = 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => t ^ (n + 1) / ((n : ℝ) + 1)) (t ^ n) t := by
    intro t _
    have h := (hasDerivAt_pow (n + 1) t).div_const ((n : ℝ) + 1)
    refine h.congr_deriv ?_
    push_cast
    rw [mul_div_cancel_left₀ _ (by positivity : ((n : ℝ) + 1) ≠ 0)]
  have hint : IntervalIntegrable (fun t : ℝ => t ^ n) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1) hder hint
  rw [hFTC]
  norm_num

open Complex in

private theorem sq_wave_W_eq (θ t : ℝ) :
    1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2 =
      1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) := by
  push_cast
  ring

open Complex in

private theorem sq_wave_x_ne_one {θ : ℝ} (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) (t : ℝ) :
    (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ≠ 1 := by
  intro h
  have hwx := sq_wave_W_eq θ t
  rw [h, sub_self] at hwx
  exact sq_wave_denom_ne hθ hθ2 t hwx

private theorem sq_wave_geom_sum (x : ℂ) (hx : x ≠ 1) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), x ^ k = (1 - x ^ (K + 1)) / (1 - x) := by
  have hden : (1 : ℂ) - x ≠ 0 := sub_ne_zero_of_ne (Ne.symm hx)
  rw [eq_div_iff hden]
  clear hden
  induction K with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring

open Complex in

private theorem sq_wave_geom (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) (K : ℕ) (t : ℝ) :
    cexp (θ * I) * (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1)) /
        (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ)) =
      ∑ k ∈ Finset.range (K + 1),
        cexp (θ * I) * ((-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ k) := by
  have hxn : (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ≠ 1 := sq_wave_x_ne_one hθ hθ2 t
  rw [← Finset.mul_sum, sq_wave_geom_sum _ hxn K]
  ring

open Complex in

private theorem sq_wave_pow_expand (θ : ℝ) (t : ℝ) (k : ℕ) :
    ((-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ)) ^ k =
      (((-(1 : ℝ)) ^ k : ℂ)) * (((t ^ (2 * k) : ℝ) : ℂ)) * (cexp (θ * I)) ^ (2 * k) := by
  have h1 : (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) =
      (((-1 : ℝ) : ℂ)) * ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2 := by
    push_cast
    ring
  rw [h1, mul_pow, mul_pow, Complex.ofReal_pow, Complex.ofReal_pow, pow_mul, pow_mul]
  simp only [Complex.ofReal_neg]

open Complex in

private theorem sq_wave_term_eq (θ : ℝ) (t : ℝ) (k : ℕ) :
    cexp (θ * I) * ((-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ k) =
      (((-(1 : ℝ)) ^ k : ℂ)) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I) *
        (((t ^ (2 * k) : ℝ) : ℂ)) := by
  have hzk : (cexp (θ * I)) ^ (2 * k + 1) = cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I) := by
    rw [← Complex.exp_nat_mul (θ * I) (2 * k + 1)]
    congr 1
    push_cast
    ring
  have hz2 : (cexp (θ * I)) * (cexp (θ * I)) ^ (2 * k) = (cexp (θ * I)) ^ (2 * k + 1) := by
    rw [mul_comm, ← pow_succ]
  rw [sq_wave_pow_expand θ t k,
    show (cexp (θ * I)) * ((((-(1 : ℝ)) ^ k : ℂ)) * (((t ^ (2 * k) : ℝ) : ℂ)) *
      (cexp (θ * I)) ^ (2 * k)) =
      (((-(1 : ℝ)) ^ k : ℂ)) * (((t ^ (2 * k) : ℝ) : ℂ)) *
      ((cexp (θ * I)) * (cexp (θ * I)) ^ (2 * k)) from by
      ring,
    hz2, hzk]
  ring

open Complex in

private theorem sq_wave_partial (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1),
        (((-(1 : ℝ)) ^ k : ℂ) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I)) /
          (((2 * k + 1 : ℕ) : ℝ)) =
      ∫ t in (0 : ℝ)..1,
        cexp (θ * I) * (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1)) /
          (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ)) := by
  have hcont : ∀ k : ℕ, IntervalIntegrable
      (fun t => (((-(1 : ℝ)) ^ k : ℂ) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I)) *
        (((t ^ (2 * k) : ℝ) : ℂ))) MeasureTheory.volume 0 1 := by
    intro k
    apply Continuous.intervalIntegrable
    fun_prop
  have hint : IntervalIntegrable
      (fun t => cexp (θ * I) * (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1)) /
          (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ))) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro x
    exact sub_ne_zero_of_ne (Ne.symm (sq_wave_x_ne_one hθ hθ2 x))
  have h1 : (∫ t in (0 : ℝ)..1,
      cexp (θ * I) * (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1)) /
        (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ))) =
      ∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range (K + 1),
        (((-(1 : ℝ)) ^ k : ℂ) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I)) *
          (((t ^ (2 * k) : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr (a := (0 : ℝ)) (b := 1) fun t _ => ?_
    rw [sq_wave_geom θ hθ hθ2 K t]
    exact Finset.sum_congr rfl fun k _ => sq_wave_term_eq θ t k
  rw [h1, integral_finset_sum_interval _ _ 0 1 fun k _ => hcont k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    sq_wave_pow_int]
  push_cast
  field_simp

open Complex in

private theorem sq_wave_re_of_integral {f : ℝ → ℂ} (a b : ℝ) (hfc : Continuous f) :
    (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re := by
  have hre : Continuous fun x : ℝ => ((f x).re : ℂ) := by fun_prop
  have him : Continuous fun x : ℝ => ((f x).im * I : ℂ) := by fun_prop
  have hintre : IntervalIntegrable (fun x => ((f x).re : ℂ)) MeasureTheory.volume a b :=
    hre.intervalIntegrable a b
  have hintim : IntervalIntegrable (fun x => ((f x).im * I : ℂ)) MeasureTheory.volume a b :=
    him.intervalIntegrable a b
  have hcongr : ∀ x ∈ Set.uIcc a b,
      f x = ((f x).re + (f x).im * I : ℂ) := fun x _ => (Complex.re_add_im (f x)).symm
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_add hintre hintim,
    intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  simp

open Complex in

private theorem sq_wave_integral_re (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    (∫ t in (0 : ℝ)..1, cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)).re =
      Real.pi / 4 := by
  have hcont : Continuous
      (fun t => cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun x => sq_wave_denom_ne hθ hθ2 x)
  rw [sq_wave_re_of_integral 0 1 hcont, sq_wave_value_re θ hθ hθ2]

open Complex in

private theorem sq_wave_tail_abs (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) (K : ℕ) :
    ‖(∫ t in (0 : ℝ)..1, cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)) -
      ∑ k ∈ Finset.range (K + 1),
        (((-(1 : ℝ)) ^ k : ℂ) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I)) /
          (((2 * k + 1 : ℕ) : ℝ))‖ ≤
      1 / (4 * ((K + 1 : ℕ) : ℝ) * Real.cos θ) := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hθ2⟩
  have hintA : IntervalIntegrable
      (fun t => cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => sq_wave_denom_ne hθ hθ2 x)
  have hintB : IntervalIntegrable
      (fun t => cexp (θ * I) * (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1)) /
        (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ))) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro x
    exact sub_ne_zero_of_ne (Ne.symm (sq_wave_x_ne_one hθ hθ2 x))
  have hident : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2) -
        (cexp (θ * I) * (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1)) /
          (1 - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ))) =
      cexp (θ * I) * (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1) /
        (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2) := by
    intro t _
    have hWne : 1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2 ≠ 0 := sq_wave_denom_ne hθ hθ2 t
    rw [sq_wave_W_eq θ t]
    have hden : (1 : ℂ) - (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ≠ 0 := by
      rw [← sq_wave_W_eq θ t]
      exact hWne
    field_simp
    ring
  have hnormx : ∀ t : ℝ, ‖((-(t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)‖ = t ^ 2 := by
    intro t
    rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_pow,
      Complex.norm_exp_ofReal_mul_I,
      one_pow, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  have hpw : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ‖cexp (θ * I) * (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1) /
        (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)‖ ≤
        t ^ (2 * K + 1) / (2 * Real.cos θ) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hWlb : 2 * t * Real.cos θ ≤
        ‖1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2‖ := by
      have hns : ‖1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2‖ ^ 2 =
          (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, sq_wave_denom_normSq]
      have key : (1 + t ^ 2) ^ 2 * Real.cos θ ^ 2 + (1 - t ^ 2) ^ 2 * Real.sin θ ^ 2 -
          (2 * t * Real.cos θ) ^ 2 = (1 - t ^ 2) ^ 2 :=
        by linear_combination (1 - t ^ 2) ^ 2 * Real.sin_sq_add_cos_sq θ
      have h2 : (2 * t * Real.cos θ) ^ 2 ≤
          ‖1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2‖ ^ 2 := by
        rw [hns]
        have hsq : (0 : ℝ) ≤ (1 - t ^ 2) ^ 2 := sq_nonneg _
        linarith
      have habs := sq_le_sq.mp h2
      rwa [abs_of_pos (show (0 : ℝ) < 2 * t * Real.cos θ by positivity),
        abs_of_nonneg (norm_nonneg _)] at habs
    have hWpos : 0 < ‖1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2‖ :=
      norm_pos_iff.mpr (sq_wave_denom_ne hθ hθ2 t)
    rw [norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow, hnormx t,
      ← pow_mul, div_le_div_iff₀ hWpos
        (show (0 : ℝ) < 2 * Real.cos θ by positivity)]
    have hu : (0 : ℝ) ≤ t ^ (2 * K + 1) := pow_nonneg (le_of_lt ht0) _
    have hstep1 : t ^ (2 * K + 1) * t * (2 * Real.cos θ) ≤
        t ^ (2 * K + 1) * (2 * t * Real.cos θ) :=
      le_of_eq (by ring)
    have hstep2 : t ^ (2 * K + 1) * (2 * t * Real.cos θ) ≤
        t ^ (2 * K + 1) * ‖1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2‖ :=
      mul_le_mul_of_nonneg_left hWlb hu
    have hexp : (2 : ℕ) * (K + 1) = 2 * K + 1 + 1 := by omega
    rw [hexp, pow_succ]
    linarith
  have hintC : IntervalIntegrable
      (fun t => ‖cexp (θ * I) * (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1) /
        (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)‖) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact Continuous.norm
      (Continuous.div (by fun_prop) (by fun_prop) (fun x => sq_wave_denom_ne hθ hθ2 x))
  have hintT : IntervalIntegrable (fun t => t ^ (2 * K + 1) / (2 * Real.cos θ))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) continuous_const
      (fun _ => ne_of_gt (show (0 : ℝ) < 2 * Real.cos θ by positivity))
  have hscale : ∫ t in (0 : ℝ)..1, t ^ (2 * K + 1) / (2 * Real.cos θ) =
      (∫ t in (0 : ℝ)..1, t ^ (2 * K + 1)) * (1 / (2 * Real.cos θ)) := by
    have hcongr2 : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        t ^ (2 * K + 1) / (2 * Real.cos θ) = t ^ (2 * K + 1) * (1 / (2 * Real.cos θ)) :=
      fun t _ => div_eq_mul_one_div _ _
    rw [intervalIntegral.integral_congr hcongr2, intervalIntegral.integral_mul_const]
  have hlast : ∫ t in (0 : ℝ)..1, t ^ (2 * K + 1) / (2 * Real.cos θ) =
      1 / (4 * ((K + 1 : ℕ) : ℝ) * Real.cos θ) := by
    rw [hscale, sq_wave_pow_int,
      show (((2 * K + 1 : ℕ) : ℝ) + 1) = 2 * ((K + 1 : ℕ) : ℝ) from by push_cast; ring]
    field_simp
    ring
  calc ‖(∫ t in (0 : ℝ)..1,
        cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)) -
      ∑ k ∈ Finset.range (K + 1),
        (((-(1 : ℝ)) ^ k : ℂ) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I)) /
          (((2 * k + 1 : ℕ) : ℝ))‖ =
      ‖∫ t in (0 : ℝ)..1,
        cexp (θ * I) * (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1) /
          (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)‖ := by
        rw [sq_wave_partial θ hθ hθ2 K, ← intervalIntegral.integral_sub hintA hintB,
          intervalIntegral.integral_congr hident]
    _ ≤ ∫ t in (0 : ℝ)..1,
        ‖cexp (θ * I) * (-(t ^ 2 : ℝ) * (cexp (θ * I)) ^ 2 : ℂ) ^ (K + 1) /
          (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, t ^ (2 * K + 1) / (2 * Real.cos θ) :=
        intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hintC hintT hpw
    _ = 1 / (4 * ((K + 1 : ℕ) : ℝ) * Real.cos θ) := hlast

open Complex in

private theorem sq_wave_tail (θ : ℝ) (hθ : 0 ≤ θ) (hθ2 : θ < Real.pi / 2) (K : ℕ) :
    |Real.pi / 4 - ∑ k ∈ Finset.range (K + 1),
        ((-(1 : ℝ)) ^ k * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)) /
          (((2 * k + 1 : ℕ) : ℝ))| ≤
      1 / (4 * ((K + 1 : ℕ) : ℝ) * Real.cos θ) := by
  have hreA : (∫ t in (0 : ℝ)..1,
      cexp (θ * I) / (1 + ((t ^ 2 : ℝ) : ℂ) * (cexp (θ * I)) ^ 2)).re = Real.pi / 4 :=
    sq_wave_integral_re θ hθ hθ2
  have hreS : (∑ k ∈ Finset.range (K + 1),
      (((-(1 : ℝ)) ^ k : ℂ) * cexp (((2 * k + 1 : ℕ) : ℝ) * θ * I)) /
        (((2 * k + 1 : ℕ) : ℝ))).re =
      ∑ k ∈ Finset.range (K + 1),
        ((-(1 : ℝ)) ^ k * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)) /
          (((2 * k + 1 : ℕ) : ℝ)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hA : (-(1 : ℝ) : ℂ) ^ k = (((-(1 : ℝ)) ^ k : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_pow]
    have hcast : ((((2 * k + 1 : ℕ) : ℝ) : ℂ) * (θ : ℂ)) * I =
        Complex.ofReal ((((2 * k + 1 : ℕ) : ℝ) * θ)) * I := by
      push_cast
      ring
    have hc1 : (cexp ((((2 * k + 1 : ℕ) : ℝ) * θ * I))).re =
        Real.cos ((((2 * k + 1 : ℕ) : ℝ) * θ)) := by
      rw [hcast]
      exact cexp_re _
    have hc2 : (cexp ((((2 * k + 1 : ℕ) : ℝ) * θ * I))).im =
        Real.sin ((((2 * k + 1 : ℕ) : ℝ) * θ)) := by
      rw [hcast]
      exact cexp_im _
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_re,
      Complex.mul_im, hA, hc1, hc2, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [← hreA, ← hreS, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (sq_wave_tail_abs θ hθ hθ2 K)

noncomputable def signChebCoeff : ℕ → ℝ :=
  fun k => if k % 2 = 1 then (4 / Real.pi) * (-(1 : ℝ)) ^ (k / 2) / ((k : ℝ)) else 0

theorem signChebCoeff_even (j : ℕ) : signChebCoeff (2 * j) = 0 := by
  simp only [signChebCoeff, if_neg (show (2 * j) % 2 ≠ 1 by omega)]

theorem signChebCoeff_odd (j : ℕ) :
    signChebCoeff (2 * j + 1) =
      (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) := by
  simp only [signChebCoeff, if_pos (show (2 * j + 1) % 2 = 1 by omega),
    show (2 * j + 1) / 2 = j from by omega]

theorem chebT_eval_neg (k : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval (-x) =
      (-(1 : ℝ)) ^ k * (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval x := by
  rw [Polynomial.Chebyshev.T_eval_neg ℝ ((k : ℕ) : ℤ) x,
    Int.cast_negOnePow_natCast]

theorem signChebTrunc_eval_eq (K : ℕ) (x : ℝ) :
    (chebTrunc (2 * K + 1) signChebCoeff).eval x =
      ∑ j ∈ Finset.range (K + 1),
        (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
          (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x := by
  induction K with
  | zero =>
      rw [chebTrunc_eval]
      norm_num
      have hc0 : signChebCoeff 0 = 0 := by
        have h := signChebCoeff_even 0
        simpa using h
      have hc1 : signChebCoeff 1 = 4 / Real.pi := by
        have h := signChebCoeff_odd 0
        simpa using h
      rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1]
      norm_num
  | succ n ih =>
      rw [chebTrunc_eval, Finset.sum_range_succ (n := 2 * (n + 1) + 1),
        Finset.sum_range_succ (n := 2 * (n + 1)), signChebCoeff_even (n + 1),
        signChebCoeff_odd (n + 1),
        show 2 * (n + 1) = 2 * n + 1 + 1 from by omega,
        ← chebTrunc_eval (2 * n + 1) signChebCoeff x, ih,
        Finset.sum_range_succ (n := n + 1)]
      ring

theorem signChebTrunc_odd (K : ℕ) (x : ℝ) :
    (chebTrunc (2 * K + 1) signChebCoeff).eval (-x) =
      -((chebTrunc (2 * K + 1) signChebCoeff).eval x) := by
  have hterm : ∀ j ∈ Finset.range (K + 1),
      (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
          (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval (-x) =
        -((4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
          (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x) := by
    intro j _
    rw [chebT_eval_neg, Odd.neg_one_pow ⟨j, rfl⟩]
    ring
  rw [signChebTrunc_eval_eq, signChebTrunc_eval_eq,
    Finset.sum_congr rfl (fun j hj => hterm j hj), Finset.sum_neg_distrib]

theorem signChebTruncErrorPos (K : ℕ) {x : ℝ} (hx1 : (0 : ℝ) < x) (hx2 : x ≤ 1) :
    |1 - (chebTrunc (2 * K + 1) signChebCoeff).eval x| ≤
      1 / (((K + 1 : ℕ) : ℝ) * Real.pi * x) := by
  have hθ : 0 ≤ Real.arccos x := Real.arccos_nonneg x
  have hθ2 : Real.arccos x < Real.pi / 2 := (Real.arccos_lt_pi_div_two).mpr hx1
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith) (by linarith)
  rw [signChebTrunc_eval_eq]
  have hT : ∀ j ∈ Finset.range (K + 1),
      (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x =
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * Real.arccos x) := by
    intro j _
    have hTeval := Polynomial.Chebyshev.T_real_cos (Real.arccos x)
      ((2 * j + 1 : ℕ) : ℤ)
    rw [hcos] at hTeval
    rw [hTeval, Int.cast_natCast]
  have hsum : ∑ j ∈ Finset.range (K + 1),
      (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
        (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x =
      ∑ j ∈ Finset.range (K + 1),
        (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * Real.arccos x) :=
    Finset.sum_congr rfl fun j hj => by rw [hT j hj]
  rw [hsum]
  have hsplit : 1 - ∑ j ∈ Finset.range (K + 1),
      (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
        Real.cos (((2 * j + 1 : ℕ) : ℝ) * Real.arccos x) =
      (4 / Real.pi) * (Real.pi / 4 - ∑ j ∈ Finset.range (K + 1),
        ((-(1 : ℝ)) ^ j * Real.cos (((2 * j + 1 : ℕ) : ℝ) * Real.arccos x)) /
          (((2 * j + 1 : ℕ) : ℝ))) := by
    have hS : ∑ j ∈ Finset.range (K + 1),
        (4 / Real.pi) * (-(1 : ℝ)) ^ j / (((2 * j + 1 : ℕ) : ℝ)) *
          Real.cos (((2 * j + 1 : ℕ) : ℝ) * Real.arccos x) =
        (4 / Real.pi) * ∑ j ∈ Finset.range (K + 1),
        ((-(1 : ℝ)) ^ j * Real.cos (((2 * j + 1 : ℕ) : ℝ) * Real.arccos x)) /
          (((2 * j + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hS, mul_sub]
    have hpi : (4 / Real.pi) * (Real.pi / 4) = 1 := by field_simp
    rw [hpi]
  rw [hsplit, abs_mul, abs_of_pos (show (0 : ℝ) < 4 / Real.pi by positivity)]
  have hcalc : (4 / Real.pi) * (1 / (4 * ((K + 1 : ℕ) : ℝ) * Real.cos (Real.arccos x))) =
      1 / (((K + 1 : ℕ) : ℝ) * Real.pi * x) := by
    rw [hcos]
    field_simp
  exact le_trans (mul_le_mul_of_nonneg_left (sq_wave_tail (Real.arccos x) hθ hθ2 K)
    (show (0 : ℝ) ≤ 4 / Real.pi by positivity)) (le_of_eq hcalc)

theorem signChebTruncErrorNeg (K : ℕ) {x : ℝ} (hx1 : (-1 : ℝ) ≤ x) (hx2 : x < 0) :
    |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval x| ≤
      1 / (((K + 1 : ℕ) : ℝ) * Real.pi * (-x)) := by
  have hy1 : (0 : ℝ) < -x := by linarith
  have hy2 : -x ≤ 1 := by linarith
  have hp := signChebTrunc_odd K (-x)
  rw [neg_neg] at hp
  rw [hp,
    show (-1 : ℝ) - (-(chebTrunc (2 * K + 1) signChebCoeff).eval (-x)) =
      -((1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval (-x)) from by ring,
    abs_neg]
  exact signChebTruncErrorPos K hy1 hy2

theorem signChebTruncAbsEvalLe (K : ℕ) {x δ : ℝ} (hδ : (0 : ℝ) < δ)
    (hx1 : δ ≤ |x|) (hx2 : |x| ≤ 1) :
    |(chebTrunc (2 * K + 1) signChebCoeff).eval x| ≤
      1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
  have hmono : ∀ y : ℝ, δ ≤ |y| → ((K + 1 : ℕ) : ℝ) * Real.pi * δ ≤
      ((K + 1 : ℕ) : ℝ) * Real.pi * |y| := fun y hy =>
    mul_le_mul_of_nonneg_left hy
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos))
  rcases le_or_gt 0 x with hx0 | hx0
  · have hx1' : δ ≤ x := by rwa [abs_of_nonneg hx0] at hx1
    have hpos : (0 : ℝ) < x := lt_of_lt_of_le hδ hx1'
    have hb := signChebTruncErrorPos K hpos ((abs_le.mp hx2).2)
    have hmono' : ((K + 1 : ℕ) : ℝ) * Real.pi * δ ≤ ((K + 1 : ℕ) : ℝ) * Real.pi * x :=
      mul_le_mul_of_nonneg_left hx1'
        (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos))
    have hb' := le_trans hb (one_div_le_one_div_of_le (by positivity) hmono')
    calc |(chebTrunc (2 * K + 1) signChebCoeff).eval x|
        = |((chebTrunc (2 * K + 1) signChebCoeff).eval x - 1) + 1| := by ring
      _ ≤ |(chebTrunc (2 * K + 1) signChebCoeff).eval x - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |1 - (chebTrunc (2 * K + 1) signChebCoeff).eval x| + 1 := by
          rw [abs_sub_comm]
          norm_num
      _ ≤ 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) + 1 := by linarith
      _ = 1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring
  · have hx1' : δ ≤ -x := by rwa [abs_of_nonpos (le_of_lt hx0)] at hx1
    have hb := signChebTruncErrorNeg K ((abs_le.mp hx2).1) hx0
    have hmono' : ((K + 1 : ℕ) : ℝ) * Real.pi * δ ≤ ((K + 1 : ℕ) : ℝ) * Real.pi * (-x) :=
      mul_le_mul_of_nonneg_left hx1'
        (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos))
    have hb' := le_trans hb (one_div_le_one_div_of_le (by positivity) hmono')
    calc |(chebTrunc (2 * K + 1) signChebCoeff).eval x|
        = |((chebTrunc (2 * K + 1) signChebCoeff).eval x - (-1 : ℝ)) + (-1 : ℝ)| := by ring
      _ ≤ |(chebTrunc (2 * K + 1) signChebCoeff).eval x - (-1 : ℝ)| + |(-1 : ℝ)| := abs_add_le _ _
      _ = |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval x| + 1 := by
          rw [abs_sub_comm]
          norm_num
      _ ≤ 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) + 1 := by linarith
      _ = 1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring

theorem signChebTruncWordTransport (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (K : ℕ) (δ m : ℝ)
    (hw : WellFormedAdjointCircuit word) (hδ : (0 : ℝ) < δ)
    (hm : (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 ≤ m) (hm1 : m < 1) :
    (∀ t ∈ Set.Icc (-1) 1, δ ≤ |t| →
      ‖evaluate (scalarSignalLift W ((1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t)) word -
          evaluate (scalarSignalLift W (t / (2 * |t|))) word‖ ≤
        (adjointQueryCount word : ℝ) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2) /
          Real.sqrt (1 - m ^ 2)) ∧
    (∀ t ∈ Set.Icc (-1) 1, δ ≤ |t| →
      ‖evaluate (scalarSignalLift W ((1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t)) word -
          evaluate (scalarSignalLift W (t / (2 * |t|))) word‖ ≤
        (adjointQueryCount word : ℝ) * Real.sqrt (2 * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)))) := by
  have hε : (0 : ℝ) ≤ 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by positivity
  have hε1 : 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) < 1 := by
    have h2 : (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 < 1 :=
      lt_of_le_of_lt hm hm1
    linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hmain1 := frontier1 W word m (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2) hw
    (by positivity) hm0 hm1
  have hmain2 := frontier1 W word m (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) hw hε hm0 hm1
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmhalf : (1 : ℝ) / 2 ≤ m := by
    have h3 : (1 : ℝ) / 2 ≤ (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      have h4 := add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hε
      linarith
    linarith
  have htn0 : ∀ t : ℝ, δ ≤ |t| → t ≠ 0 := by
    intro t htδ h
    rw [h, abs_zero] at htδ
    exact absurd htδ (not_le.mpr hδ)
  have hyvpos : ∀ t : ℝ, (0 : ℝ) ≤ t → t ≠ 0 → t / (2 * |t|) = 1 / 2 := by
    intro t htp htne
    have htpos : (0 : ℝ) < t := lt_of_le_of_ne htp (Ne.symm htne)
    rw [abs_of_nonneg htp,
      div_eq_iff (ne_of_gt (mul_pos two_pos htpos)),
      show (1 / 2) * (2 * t) = t from by ring]
  have hyvneg : ∀ t : ℝ, t < 0 → t / (2 * |t|) = -(1 / 2) := by
    intro t htn
    rw [abs_of_nonpos (le_of_lt htn),
      div_eq_iff (ne_of_gt (mul_pos two_pos (neg_pos.mpr htn))),
      show -(1 / 2) * (2 * (-t)) = t from by ring]
  have hmonoerr : ∀ y : ℝ, δ ≤ |y| →
      1 / (((K + 1 : ℕ) : ℝ) * Real.pi * |y|) ≤
        1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := fun y hy =>
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hy
        (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos)))
  refine ⟨fun t ht htδ => ?_, fun t ht htδ => ?_⟩
  · have htabs : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hδ1 : δ ≤ 1 := le_trans htδ htabs
    have habs := signChebTruncAbsEvalLe K hδ htδ htabs
    have hxe : |(1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t| ≤
        (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hcalc : (1 / 2) * (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) =
          (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by ring
      exact (mul_le_mul_of_nonneg_left habs hhalf).trans_eq hcalc
    have hx : (1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t ∈ Set.Icc (-m) m := by
      have := abs_le.mp hxe
      exact ⟨by linarith, by linarith⟩
    have hy : t / (2 * |t|) ∈ Set.Icc (-m) m := by
      rcases le_or_gt 0 t with htp | htn
      · rw [hyvpos t htp (htn0 t htδ)]
        exact ⟨by linarith, by linarith⟩
      · rw [hyvneg t htn]
        constructor <;> linarith
    have herr : |(1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - t / (2 * |t|)| ≤
        1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by
      rcases le_or_gt 0 t with htp | htn
      · have hxd : δ ≤ t := by rwa [abs_of_nonneg htp] at htδ
        have hpos : (0 : ℝ) < t := lt_of_lt_of_le hδ hxd
        have h1 := signChebTruncErrorPos K hpos ((abs_le.mp htabs).2)
        rw [hyvpos t htp (htn0 t htδ),
          show (1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - 1 / 2 =
            (1 / 2) * ((chebTrunc (2 * K + 1) signChebCoeff).eval t - 1) from by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_sub_comm]
        have hmerr : 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * t) ≤
            1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_left hxd
              (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos)))
        have h2 : (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * t)) ≤
            (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
          mul_le_mul_of_nonneg_left hmerr hhalf
        have h3 : (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) =
            1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by ring
        exact (mul_le_mul_of_nonneg_left h1 hhalf).trans (h2.trans_eq h3)
      · have hxd : δ ≤ -t := by rwa [abs_of_nonpos (le_of_lt htn)] at htδ
        have h1 := signChebTruncErrorNeg K ((abs_le.mp htabs).1) htn
        rw [hyvneg t htn,
          show (1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - -(1 / 2) =
            -((1 / 2) * ((-(1 : ℝ)) - (chebTrunc (2 * K + 1) signChebCoeff).eval t)) from by
            ring,
          abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have hmerr : 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * (-t)) ≤
            1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_left hxd
              (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos)))
        have h2 : (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * (-t))) ≤
            (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
          mul_le_mul_of_nonneg_left hmerr hhalf
        have h3 : (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) =
            1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by ring
        exact (mul_le_mul_of_nonneg_left h1 hhalf).trans (h2.trans_eq h3)
    exact hmain1.1 _ _ hx hy herr
  · have htabs : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hδ1 : δ ≤ 1 := le_trans htδ htabs
    have habs := signChebTruncAbsEvalLe K hδ htδ htabs
    have hx : (1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t ∈ Set.Icc (-1) 1 := by
      have h1 : |(1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t| ≤ 1 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have h2 : (1 / 2) * (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) ≤ 1 := by
          linarith
        exact (mul_le_mul_of_nonneg_left habs hhalf).trans h2
      have := abs_le.mp h1
      exact ⟨by linarith, by linarith⟩
    have hy : t / (2 * |t|) ∈ Set.Icc (-1) 1 := by
      rcases le_or_gt 0 t with htp | htn
      · rw [hyvpos t htp (htn0 t htδ)]
        norm_num
      · rw [hyvneg t htn]
        norm_num
    have herr : |(1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - t / (2 * |t|)| ≤
        1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
      have hhalfpos : (0 : ℝ) ≤ 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by positivity
      have hkey : |(1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - t / (2 * |t|)| ≤
          1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by
        rcases le_or_gt 0 t with htp | htn
        · have hxd : δ ≤ t := by rwa [abs_of_nonneg htp] at htδ
          have hpos : (0 : ℝ) < t := lt_of_lt_of_le hδ hxd
          have h1 := signChebTruncErrorPos K hpos ((abs_le.mp htabs).2)
          rw [hyvpos t htp (htn0 t htδ),
            show (1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - 1 / 2 =
              (1 / 2) * ((chebTrunc (2 * K + 1) signChebCoeff).eval t - 1) from by ring,
            abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_sub_comm]
          have hmerr : 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * t) ≤
              1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) :=
            one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_left hxd
                (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos)))
          have h3 : (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) =
              1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by ring
          exact ((mul_le_mul_of_nonneg_left h1 hhalf).trans
            (mul_le_mul_of_nonneg_left hmerr hhalf)).trans_eq h3
        · have hxd : δ ≤ -t := by rwa [abs_of_nonpos (le_of_lt htn)] at htδ
          have h1 := signChebTruncErrorNeg K ((abs_le.mp htabs).1) htn
          rw [hyvneg t htn,
            show (1 / 2) * (chebTrunc (2 * K + 1) signChebCoeff).eval t - -(1 / 2) =
              -((1 / 2) * ((-(1 : ℝ)) - (chebTrunc (2 * K + 1) signChebCoeff).eval t)) from by
              ring,
            abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          have hmerr : 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * (-t)) ≤
              1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) :=
            one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_left hxd
                (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos)))
          have h3 : (1 / 2) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) =
              1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2 := by ring
          exact ((mul_le_mul_of_nonneg_left h1 hhalf).trans
            (mul_le_mul_of_nonneg_left hmerr hhalf)).trans_eq h3
      linarith
    exact hmain2.2 _ _ hx hy herr

noncomputable def shiftScale (c : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * (Polynomial.X - Polynomial.C c)

theorem shiftScale_eval (c t : ℝ) : (shiftScale c).eval t = (t - c) / 2 := by
  rw [shiftScale, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

noncomputable def windowTrunc (a b : ℝ) (K : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) * ((chebTrunc (2 * K + 1) signChebCoeff).comp (shiftScale a) -
    (chebTrunc (2 * K + 1) signChebCoeff).comp (shiftScale b))

theorem windowTrunc_eval (a b : ℝ) (K : ℕ) (t : ℝ) :
    (windowTrunc a b K).eval t =
      (1 / 2) * ((chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2) -
        (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) := by
  rw [windowTrunc, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
  rw [Polynomial.eval_comp, shiftScale_eval, Polynomial.eval_comp, shiftScale_eval]

private theorem window_half_mono {x y : ℝ} (h : x ≤ y) : x / 2 ≤ y / 2 := by
  nlinarith [h]

private theorem window_half_pos {x : ℝ} (h : 0 < x) : 0 < x / 2 := by
  nlinarith [h]

private theorem window_half_lt {x : ℝ} (h : x < 0) : x / 2 < 0 := by
  nlinarith [h]

private theorem window_half_le_one {x : ℝ} (h : x ≤ 2) : x / 2 ≤ 1 := by
  have h2 := window_half_mono h
  rwa [div_self two_ne_zero] at h2

private theorem window_half_ge_neg_one {x : ℝ} (h : -2 ≤ x) : -1 ≤ x / 2 := by
  have h2 := window_half_mono h
  rw [neg_div, div_self two_ne_zero] at h2
  exact h2

private theorem window_err_mono (K : ℕ) {u δ : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hu0 : 0 < u) (hu : δ ≤ 2 * u) :
    1 / (((K : ℕ) : ℝ) * Real.pi * u) ≤ 2 / (((K : ℕ) : ℝ) * Real.pi * δ) := by
  have hKu : (0 : ℝ) < ((K : ℕ) : ℝ) * Real.pi * u :=
    mul_pos (mul_pos (Nat.cast_pos.mpr hK) Real.pi_pos) hu0
  have hKδ : (0 : ℝ) < ((K : ℕ) : ℝ) * Real.pi * δ :=
    mul_pos (mul_pos (Nat.cast_pos.mpr hK) Real.pi_pos) hδ
  have hmul : ((K : ℕ) : ℝ) * Real.pi * δ ≤ ((K : ℕ) : ℝ) * Real.pi * (2 * u) :=
    mul_le_mul_of_nonneg_left hu (mul_nonneg (Nat.cast_nonneg _) (le_of_lt Real.pi_pos))
  have hrw : ((K : ℕ) : ℝ) * Real.pi * (2 * u) = 2 * (((K : ℕ) : ℝ) * Real.pi * u) := by
    ring
  rw [hrw] at hmul
  rw [div_le_div_iff₀ hKu hKδ]
  nlinarith [hmul]

theorem windowTruncErrorInside (K : ℕ) {a b δ t : ℝ}
    (ha : -1 ≤ a) (hb : b ≤ 1) (hδ : 0 < δ)
    (h1 : a + δ ≤ t) (h2 : t ≤ b - δ) :
    |1 - (windowTrunc a b K).eval t| ≤ 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
  have hua1 : (0 : ℝ) < (t - a) / 2 := window_half_pos (by linarith)
  have hua2 : (t - a) / 2 ≤ 1 := window_half_le_one (by
    have : t - a ≤ b - a := by linarith
    have h2 : b - a ≤ 2 := by
      have : b - a ≤ 1 - a := by linarith
      linarith
    linarith)
  have hub1 : -1 ≤ (t - b) / 2 := window_half_ge_neg_one (by
    have : t - b ≥ a - b := by linarith
    have h2 : a - b ≥ -2 := by
      have : a - b ≥ -1 - b := by linarith
      linarith
    linarith)
  have hub2 : (t - b) / 2 < 0 := window_half_lt (by linarith)
  have e1 := signChebTruncErrorPos K hua1 hua2
  have e1' := e1.trans (window_err_mono (K + 1) (by omega) hδ hua1
    (show δ ≤ 2 * ((t - a) / 2) from by nlinarith [h1]))
  have e2 := signChebTruncErrorNeg K hub1 hub2
  have e2' := e2.trans (window_err_mono (K + 1) (by omega) hδ (show (0 : ℝ) < -((t - b) / 2) from by
      have hb2 : 0 < b - t := by linarith
      nlinarith [hb2])
    (show δ ≤ 2 * -((t - b) / 2) from by
      have hb2 : δ ≤ b - t := by linarith
      nlinarith [hb2]))
  have hpw : 1 - (windowTrunc a b K).eval t =
      (1 / 2) * ((1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) +
        (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))) := by
    rw [windowTrunc_eval]
    ring
  have hnegb : |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| =
      |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| := by
    have : 1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2) =
        -((-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) := by
      ring
    rw [this, abs_neg]
  have hsum : |(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) +
      (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))| ≤
      |1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| +
      |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| :=
    abs_add_le _ _
  rw [hpw, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
  rw [hnegb] at hsum
  calc (1 / 2) * |(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) +
        (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))| ≤
      (1 / 2) * (|(1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| +
        |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)|) :=
        mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    _ ≤ (1 / 2) * (2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) +
        2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1' e2') (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    _ = 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring

theorem windowTruncErrorOutsideLeft (K : ℕ) {a b δ t : ℝ}
    (hb1 : b ≤ 1) (hab : a < b) (hδ : 0 < δ)
    (ht1 : -1 ≤ t) (ht : t ≤ a - δ) :
    |(windowTrunc a b K).eval t| ≤ 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
  have hta : t ≤ a - δ := ht
  have hua1 : -1 ≤ (t - a) / 2 := window_half_ge_neg_one (by
    have : t - a ≥ -1 - a := by linarith
    have h2 : -1 - a ≥ -2 := by linarith
    linarith)
  have hua2 : (t - a) / 2 < 0 := window_half_lt (by linarith)
  have hub1 : -1 ≤ (t - b) / 2 := window_half_ge_neg_one (by
    have : t - b ≥ -1 - b := by linarith
    have h2 : -1 - b ≥ -2 := by linarith
    linarith)
  have hub2 : (t - b) / 2 < 0 := window_half_lt (by linarith)
  have e1 := signChebTruncErrorNeg K hua1 hua2
  have e1' := e1.trans (window_err_mono (K + 1) (by omega) hδ
    (show (0 : ℝ) < -((t - a) / 2) from by
      have hta2 : 0 < a - t := by linarith
      nlinarith [hta2])
    (show δ ≤ 2 * -((t - a) / 2) from by
      have hta2 : δ ≤ a - t := by linarith
      nlinarith [hta2]))
  have e2 := signChebTruncErrorNeg K hub1 hub2
  have e2' := e2.trans (window_err_mono (K + 1) (by omega) hδ
    (show (0 : ℝ) < -((t - b) / 2) from by
      have htb2 : 0 < b - t := by linarith
      nlinarith [htb2])
    (show δ ≤ 2 * -((t - b) / 2) from by
      have htb2 : δ ≤ b - t := by linarith
      nlinarith [htb2]))
  have hpw : (windowTrunc a b K).eval t =
      (1 / 2) * ((1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) -
        (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))) := by
    rw [windowTrunc_eval]
    ring
  have hnega : |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| =
      |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| := by
    have : 1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2) =
        -((-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) := by
      ring
    rw [this, abs_neg]
  have hnegb : |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| =
      |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| := by
    have : 1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2) =
        -((-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) := by
      ring
    rw [this, abs_neg]
  have hsum0 : |(1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) +
      (-(1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)))| ≤
      |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| +
      |-(1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))| :=
    abs_add_le _ _
  rw [abs_neg] at hsum0
  have hsum : |(1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) -
      (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))| ≤
      |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| +
      |1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| := by
    have hrw : (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) -
        (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) =
        (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) +
        (-(1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))) := by
      ring
    rw [hrw]
    exact hsum0
  rw [hpw, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
  rw [hnega, hnegb] at hsum
  calc (1 / 2) * |(1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) -
        (1 + (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2))| ≤
      (1 / 2) * (|(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| +
        |(-1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)|) :=
        mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    _ ≤ (1 / 2) * (2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) +
        2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1' e2') (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    _ = 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring

theorem windowTruncErrorOutsideRight (K : ℕ) {a b δ t : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hδ : 0 < δ)
    (ht : b + δ ≤ t) (ht2 : t ≤ 1) :
    |(windowTrunc a b K).eval t| ≤ 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
  have hua1 : (0 : ℝ) < (t - a) / 2 := window_half_pos (by linarith)
  have hua2 : (t - a) / 2 ≤ 1 := window_half_le_one (by
    have : t - a ≤ 1 - a := by linarith
    have h2 : 1 - a ≤ 2 := by linarith
    linarith)
  have hub1 : (0 : ℝ) < (t - b) / 2 := window_half_pos (by linarith)
  have hub2 : (t - b) / 2 ≤ 1 := window_half_le_one (by
    have : t - b ≤ 1 - b := by linarith
    have h2 : 1 - b ≤ 2 := by linarith
    linarith)
  have e1 := signChebTruncErrorPos K hua1 hua2
  have e1' := e1.trans (window_err_mono (K + 1) (by omega) hδ hua1
    (show δ ≤ 2 * ((t - a) / 2) from by nlinarith [ht]))
  have e2 := signChebTruncErrorPos K hub1 hub2
  have e2' := e2.trans (window_err_mono (K + 1) (by omega) hδ hub1
    (show δ ≤ 2 * ((t - b) / 2) from by nlinarith [ht]))
  have hpw : (windowTrunc a b K).eval t =
      (1 / 2) * ((1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) -
        (1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2))) := by
    rw [windowTrunc_eval]
    ring
  have hsum0 : |(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) +
      (-(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)))| ≤
      |1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| +
      |-(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2))| :=
    abs_add_le _ _
  rw [abs_neg] at hsum0
  have hsum : |(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) -
      (1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2))| ≤
      |1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| +
      |1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)| := by
    have hrw : (1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) -
        (1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)) =
        (1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) +
        (-(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2))) := by
      ring
    rw [hrw]
    exact hsum0
  rw [hpw, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
  calc (1 / 2) * |(1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)) -
        (1 - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2))| ≤
      (1 / 2) * (|(1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - b) / 2)| +
        |(1 : ℝ) - (chebTrunc (2 * K + 1) signChebCoeff).eval ((t - a) / 2)|) :=
        mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    _ ≤ (1 / 2) * (2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) +
        2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add e2' e1') (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    _ = 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring

theorem windowTruncAbsEvalLe (K : ℕ) {a b δ t : ℝ}
    (ha : -1 ≤ a) (hb1 : b ≤ 1) (hab : a < b)
    (hδ : (0 : ℝ) < δ) (ht1 : -1 ≤ t) (ht2 : t ≤ 1)
    (hdista : δ ≤ |t - a|) (hdistb : δ ≤ |t - b|) :
    |(windowTrunc a b K).eval t| ≤ 1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
  have hpos : (0 : ℝ) ≤ 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by positivity
  rcases lt_trichotomy t a with hta | hta | hta
  · have hle : t ≤ a - δ := by
      rw [abs_of_nonpos (show (t : ℝ) - a ≤ 0 by linarith)] at hdista
      linarith
    have h := windowTruncErrorOutsideLeft K hb1 hab hδ ht1 hle
    linarith
  · rw [hta, sub_self, abs_zero] at hdista
    exact absurd hdista (not_le.mpr hδ)
  · rcases lt_trichotomy t b with htb | htb | htb
    · have hin1 : a + δ ≤ t := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ t - a by linarith)] at hdista
        linarith
      have hin2 : t ≤ b - δ := by
        rw [abs_of_nonpos (show (t : ℝ) - b ≤ 0 by linarith)] at hdistb
        linarith
      have h := windowTruncErrorInside K ha hb1 hδ hin1 hin2
      have hle : |(windowTrunc a b K).eval t| ≤
          |(1 : ℝ) - (windowTrunc a b K).eval t| + 1 := by
        calc |(windowTrunc a b K).eval t| =
            |((windowTrunc a b K).eval t - 1) + 1| := by ring
          _ ≤ |(windowTrunc a b K).eval t - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ = |(1 : ℝ) - (windowTrunc a b K).eval t| + 1 := by
              rw [abs_sub_comm]
              norm_num
          _ = |(1 : ℝ) - (windowTrunc a b K).eval t| + 1 := by ring
      linarith
    · rw [htb, sub_self, abs_zero] at hdistb
      exact absurd hdistb (not_le.mpr hδ)
    · have hle : b + δ ≤ t := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ t - b by linarith)] at hdistb
        linarith
      have h := windowTruncErrorOutsideRight K ha hab hδ hle ht2
      linarith

theorem windowTruncWordTransport (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (K : ℕ) (a b δ m : ℝ)
    (ha : -1 ≤ a) (hb1 : b ≤ 1) (hab : a < b)
    (hw : WellFormedAdjointCircuit word) (hδ : (0 : ℝ) < δ)
    (hm : (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 ≤ m) (hm1 : m < 1) :
    (∀ t ∈ Set.Icc (-1) 1, δ ≤ |t - a| → δ ≤ |t - b| →
      ‖evaluate (scalarSignalLift W ((1 / 2) * (windowTrunc a b K).eval t)) word -
        evaluate (scalarSignalLift W ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)) word‖ ≤
        (adjointQueryCount word : ℝ) * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) /
          Real.sqrt (1 - m ^ 2)) ∧
    (∀ t ∈ Set.Icc (-1) 1, δ ≤ |t - a| → δ ≤ |t - b| →
      ‖evaluate (scalarSignalLift W ((1 / 2) * (windowTrunc a b K).eval t)) word -
        evaluate (scalarSignalLift W ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)) word‖ ≤
        (adjointQueryCount word : ℝ) *
          Real.sqrt (2 * (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)))) := by
  have hε : (0 : ℝ) ≤ 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by positivity
  have h2ε1 : 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) < 1 := by
    have h2 : (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 < 1 :=
      lt_of_le_of_lt hm hm1
    linarith
  have hm0 : (0 : ℝ) ≤ m := by
    have h2 : (0 : ℝ) < (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      have h3 := add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hε
      positivity
    linarith
  have hmhalf : (1 : ℝ) / 2 ≤ m := by
    have hposx : (0 : ℝ) ≤ 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by positivity
    have h4 : (1 : ℝ) / 2 ≤ (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  have hmain := frontier1 W word m (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) hw hε hm0 hm1
  have hpt : ∀ t ∈ Set.Icc (-1) 1, δ ≤ |t - a| → δ ≤ |t - b| →
      ((1 / 2) * (windowTrunc a b K).eval t ∈ Set.Icc (-m) m ∧
        (1 / 2) * (windowTrunc a b K).eval t ∈ Set.Icc (-1) 1 ∧
        ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2) ∈ Set.Icc (-m) m ∧
        ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2) ∈ Set.Icc (-1) 1 ∧
        |(1 / 2) * (windowTrunc a b K).eval t -
          ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)| ≤
          1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) := by
    intro t ht hdista hdistb
    have hposx : (0 : ℝ) ≤ 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by positivity
    have habs := windowTruncAbsEvalLe K ha hb1 hab hδ ht.1 ht.2 hdista hdistb
    have hxe : |(1 / 2) * (windowTrunc a b K).eval t| ≤
        (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      have hcalc : (1 / 2) * (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) =
          (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by ring
      exact (mul_le_mul_of_nonneg_left habs (show (0 : ℝ) ≤ 1 / 2 by norm_num)).trans_eq hcalc
    have hx : (1 / 2) * (windowTrunc a b K).eval t ∈ Set.Icc (-m) m := by
      have hmem := abs_le.mp hxe
      exact ⟨by linarith, by linarith⟩
    have hM1 : (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 ≤ 1 := by
      have hle : 1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) ≤ 2 := by linarith
      nlinarith [hle]
    have hx1 : (1 / 2) * (windowTrunc a b K).eval t ∈ Set.Icc (-1) 1 := by
      have h1 : |(1 / 2) * (windowTrunc a b K).eval t| ≤ 1 := hxe.trans hM1
      have hmem := abs_le.mp h1
      exact ⟨by linarith, by linarith⟩
    have hyhalf1 : (1 : ℝ) / 2 ∈ Set.Icc (-m) m := ⟨by linarith, by linarith⟩
    have hyhalf2 : (1 : ℝ) / 2 ∈ Set.Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
    have hyzero1 : (0 : ℝ) ∈ Set.Icc (-m) m := ⟨by linarith, by linarith⟩
    have hyzero2 : (0 : ℝ) ∈ Set.Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
    by_cases hioo : t ∈ Set.Ioo a b
    · have hioo1 : a < t := hioo.1
      have hioo2 : t < b := hioo.2
      have hin1 : a + δ ≤ t := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ t - a by linarith)] at hdista
        linarith
      have hin2 : t ≤ b - δ := by
        rw [abs_of_nonpos (show (t : ℝ) - b ≤ 0 by linarith)] at hdistb
        linarith
      have h := windowTruncErrorInside K ha hb1 hδ hin1 hin2
      have herr : |(1 / 2) * (windowTrunc a b K).eval t -
          ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)| ≤
          1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
        rw [if_pos hioo,
          show (1 / 2) * (windowTrunc a b K).eval t - (1 : ℝ) / 2 =
            (1 / 2) * ((windowTrunc a b K).eval t - 1) from by ring,
          abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num), abs_sub_comm]
        calc (1 / 2) * |(1 : ℝ) - (windowTrunc a b K).eval t| ≤
            (1 / 2) * (2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
              mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          _ = 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring
      refine ⟨hx, hx1, ?_, ?_, herr⟩
      · rw [if_pos hioo]; exact hyhalf1
      · rw [if_pos hioo]; exact hyhalf2
    · rcases lt_trichotomy t a with hta | hta | hta
      · have hle : t ≤ a - δ := by
          rw [abs_of_nonpos (show (t : ℝ) - a ≤ 0 by linarith)] at hdista
          linarith
        have h := windowTruncErrorOutsideLeft K hb1 hab hδ ht.1 hle
        have hy1 : ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2) ∈ Set.Icc (-m) m := by
          rw [if_neg hioo, zero_div]
          exact hyzero1
        have hy2 : ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2) ∈ Set.Icc (-1) 1 := by
          rw [if_neg hioo, zero_div]
          exact hyzero2
        have herr : |(1 / 2) * (windowTrunc a b K).eval t -
            ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)| ≤
            1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
          rw [if_neg hioo, zero_div, sub_zero, abs_mul,
            abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
          calc (1 / 2) * |(windowTrunc a b K).eval t| ≤
              (1 / 2) * (2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
                mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
            _ = 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring
        exact ⟨hx, hx1, hy1, hy2, herr⟩
      · rw [hta, sub_self, abs_zero] at hdista
        exact absurd hdista (not_le.mpr hδ)
      · rcases lt_trichotomy t b with htb | htb | htb
        · exact absurd ⟨hta, htb⟩ hioo
        · rw [htb, sub_self, abs_zero] at hdistb
          exact absurd hdistb (not_le.mpr hδ)
        · have hle : b + δ ≤ t := by
            rw [abs_of_nonneg (show (0 : ℝ) ≤ t - b by linarith)] at hdistb
            linarith
          have h := windowTruncErrorOutsideRight K ha hab hδ hle ht.2
          have hy1 : ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2) ∈ Set.Icc (-m) m := by
            rw [if_neg hioo, zero_div]
            exact hyzero1
          have hy2 : ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2) ∈ Set.Icc (-1) 1 := by
            rw [if_neg hioo, zero_div]
            exact hyzero2
          have herr : |(1 / 2) * (windowTrunc a b K).eval t -
              ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)| ≤
              1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by
            rw [if_neg hioo, zero_div, sub_zero, abs_mul,
              abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
            calc (1 / 2) * |(windowTrunc a b K).eval t| ≤
                (1 / 2) * (2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) :=
                  mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
              _ = 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) := by ring
          exact ⟨hx, hx1, hy1, hy2, herr⟩
  refine ⟨fun t ht hdista hdistb => ?_, fun t ht hdista hdistb => ?_⟩
  · obtain ⟨hx, hx1, hy, hy1, herr⟩ := hpt t ht hdista hdistb
    exact hmain.1 _ _ hx hy herr
  · obtain ⟨hx, hx1, hy, hy1, herr⟩ := hpt t ht hdista hdistb
    exact hmain.2 _ _ hx1 hy1 herr

noncomputable def chebGaussNode (N : ℕ) (j : Fin N) : ℝ :=
  Real.cos ((2 * (j : ℕ) + 1) * Real.pi / (2 * N))

theorem chebGaussNode_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (chebGaussNode N) := by
  intro i j hij
  exact Fin.val_injective
    ((chebTNodesEntry N hN).2.2.1 (i : ℕ) (j : ℕ) i.isLt j.isLt hij)

theorem chebT_eval_chebGaussNode {N : ℕ} (hN : 0 < N) (j : Fin N) :
    (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval (chebGaussNode N j) = 0 :=
  (chebTNodesEntry N hN).1 (j : ℕ) j.isLt

theorem chebGaussNode_mem_Icc {N : ℕ} (hN : 0 < N) (j : Fin N) :
    chebGaussNode N j ∈ Set.Icc (-1) 1 :=
  ⟨((chebTNodesEntry N hN).2.2.2 j j.isLt).1.le,
    ((chebTNodesEntry N hN).2.2.2 j j.isLt).2.le⟩

noncomputable def chebNodeProd (N : ℕ) : Polynomial ℝ :=
  ∏ j : Fin N, (Polynomial.X - Polynomial.C (chebGaussNode N j))

theorem chebNodeProd_monic (N : ℕ) : (chebNodeProd N).Monic := by
  rw [chebNodeProd]
  exact Polynomial.monic_prod_X_sub_C _ _

theorem chebNodeProd_natDegree (N : ℕ) : (chebNodeProd N).natDegree = N := by
  rw [chebNodeProd, Polynomial.natDegree_prod_of_monic Finset.univ
    (fun j => Polynomial.X - Polynomial.C (chebGaussNode N j))
    (fun j _ => Polynomial.monic_X_sub_C _)]
  simp

theorem chebNodeProd_eval (N : ℕ) (x : ℝ) :
    (chebNodeProd N).eval x = ∏ j : Fin N, (x - chebGaussNode N j) := by
  rw [chebNodeProd, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem chebT_eq_scale_nodeProd {N : ℕ} (hN : 0 < N) :
    Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ) =
      Polynomial.C (2 ^ (N - 1)) * chebNodeProd N := by
  have hTne : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)) ≠ 0 := by
    intro h
    have h1 : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval 1 = 1 := by simp
    rw [h] at h1
    simp at h1
  have hnpne : chebNodeProd N ≠ 0 := (chebNodeProd_monic N).ne_zero
  have hlcne : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
  have hlcmul : (Polynomial.C (2 ^ (N - 1))).leadingCoeff * (chebNodeProd N).leadingCoeff
      ≠ 0 := by
    rw [Polynomial.leadingCoeff_C, (chebNodeProd_monic N).leadingCoeff, mul_one]
    exact hlcne
  have hlcnp : (Polynomial.C (2 ^ (N - 1)) * chebNodeProd N).leadingCoeff ≠ 0 := by
    rwa [Polynomial.leadingCoeff_mul' hlcmul]
  have hmulne : Polynomial.C (2 ^ (N - 1)) * chebNodeProd N ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp hlcnp
  have hdegeq : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).degree =
      (Polynomial.C (2 ^ (N - 1)) * chebNodeProd N).degree := by
    rw [Polynomial.degree_eq_natDegree hTne, Polynomial.degree_eq_natDegree hmulne,
      chebT_natDegree_eq, Polynomial.natDegree_mul' hlcmul, Polynomial.natDegree_C,
      zero_add, chebNodeProd_natDegree]
  have hlc : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).leadingCoeff =
      (Polynomial.C (2 ^ (N - 1)) * chebNodeProd N).leadingCoeff := by
    rw [chebT_leadingCoeff_eq, Polynomial.leadingCoeff_mul' hlcmul,
      Polynomial.leadingCoeff_C, (chebNodeProd_monic N).leadingCoeff, mul_one]
  have hdeglt : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ) -
      Polynomial.C (2 ^ (N - 1)) * chebNodeProd N).natDegree < N := by
    by_cases hd0 : Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ) -
        Polynomial.C (2 ^ (N - 1)) * chebNodeProd N = 0
    · rw [hd0, Polynomial.natDegree_zero]
      omega
    · have hTdeg : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).degree = (N : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hTne, chebT_natDegree_eq]
      rw [Polynomial.natDegree_lt_iff_degree_lt hd0, ← hTdeg]
      exact Polynomial.degree_sub_lt hdegeq hTne hlc
  have hzero : Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ) -
      Polynomial.C (2 ^ (N - 1)) * chebNodeProd N = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (chebGaussNode_injective hN) (fun j => ?_) (by simpa using hdeglt)
    rw [Polynomial.eval_sub, chebT_eval_chebGaussNode hN j, zero_sub,
      Polynomial.eval_mul, Polynomial.eval_C, chebNodeProd_eval,
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [sub_self])]
    ring
  exact sub_eq_zero.mp hzero

theorem chebNodeProd_abs_eval_le {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    ∏ j : Fin N, |x - chebGaussNode N j| ≤ 2 / (2 : ℝ) ^ N := by
  have hcx : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hpos : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have hpow : (2 : ℝ) ^ N = 2 ^ (N - 1) * 2 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, N = k + 1 := ⟨N - 1, by omega⟩
    subst hk
    rw [Nat.add_sub_cancel, pow_succ]
  have h2 : (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval x
      = 2 ^ (N - 1) * (chebNodeProd N).eval x := by
    rw [chebT_eq_scale_nodeProd hN, Polynomial.eval_mul, Polynomial.eval_C]
  have hdiv : (chebNodeProd N).eval x
      = (Polynomial.Chebyshev.T ℝ ((N : ℕ) : ℤ)).eval x / 2 ^ (N - 1) := by
    rw [h2, mul_div_cancel_left₀ _ hpos.ne']
  have hkey : (1 : ℝ) / 2 ^ (N - 1) = 2 / (2 : ℝ) ^ N := by
    rw [hpow]
    field_simp
  rw [← Finset.abs_prod, ← chebNodeProd_eval, hdiv, abs_div, abs_of_pos hpos, ← hkey,
    div_le_div_iff₀ hpos hpos, one_mul]
  exact (mul_le_mul_of_nonneg_right
    (Polynomial.Chebyshev.abs_eval_T_real_le_one ((N : ℕ) : ℤ) hcx) hpos.le).trans_eq
    (one_mul (2 ^ (N - 1)))

noncomputable def lagrangeInterpPoly {N : ℕ} (node : Fin N → ℝ) (f : ℝ → ℝ) :
    Polynomial ℝ :=
  ∑ i, Polynomial.C (f (node i)) * Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node i

theorem lagrangeInterpPoly_eval_node {N : ℕ} (node : Fin N → ℝ)
    (hinj : Function.Injective node) (f : ℝ → ℝ) (j : Fin N) :
    (lagrangeInterpPoly node f).eval (node j) = f (node j) := by
  rw [lagrangeInterpPoly, Polynomial.eval_finsetSum,
    Finset.sum_eq_single j (fun i _ hne => by
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_of_ne node (Ne.symm hne), mul_zero])
    (by simp)]
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_self node hinj j, mul_one]

theorem lagrangeInterpPoly_natDegree_lt {N : ℕ} (node : Fin N → ℝ) (f : ℝ → ℝ)
    (hN : 0 < N) : (lagrangeInterpPoly node f).natDegree < N := by
  have hsup : (Finset.univ.sup fun i : Fin N =>
      (Polynomial.C (f (node i)) *
        Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node i).natDegree) ≤ N - 1 := by
    refine Finset.sup_le fun i _ => ?_
    exact Nat.le_trans (Polynomial.natDegree_mul_le.trans (by simp))
      (Qatlib.Concepts.LchsSimulation.Quadrature.natDegree_lagrangeBasis_le node i)
  exact (Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun i => Polynomial.C (f (node i)) * Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node i)
    (fun i _ => (Finset.le_sup (Finset.mem_univ i)).trans hsup)).trans_lt
    (Nat.sub_lt hN (by omega))

noncomputable def chebInterpWeight (N : ℕ) (j : Fin N) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) j).eval x

noncomputable def chebQuadRule (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, chebInterpWeight N j * f (chebGaussNode N j)

private theorem integral_finset_sum_real {ι : Type} [DecidableEq ι] (s : Finset ι)
    (g : ι → ℝ → ℝ) (a b : ℝ)
    (hg : ∀ i ∈ s, IntervalIntegrable (g i) MeasureTheory.volume a b) :
    (∫ x in a..b, ∑ i ∈ s, g i x) = ∑ i ∈ s, ∫ x in a..b, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have h1 : IntervalIntegrable (g i) MeasureTheory.volume a b :=
        hg i (Finset.mem_insert_self i s)
      have h2 : ∀ j ∈ s, IntervalIntegrable (g j) MeasureTheory.volume a b :=
        fun j hj => hg j (Finset.mem_insert_of_mem hj)
      have h3 : IntervalIntegrable (fun x => ∑ j ∈ s, g j x) MeasureTheory.volume a b := by
        have h := IntervalIntegrable.sum s h2
        have hfun : (fun x => ∑ j ∈ s, g j x) = ∑ i ∈ s, g i := by
          funext x
          exact (Finset.sum_apply x s g).symm
        rw [hfun]
        exact h
      simp only [Finset.sum_insert hi]
      rw [intervalIntegral.integral_add h1 h3, ih h2]

theorem chebQuadExact {N : ℕ} (hN : 0 < N) (p : Polynomial ℝ) (hp : p.natDegree < N) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = chebQuadRule N p.eval := by
  have hinj := chebGaussNode_injective hN
  have hlag :=
      Qatlib.Concepts.LchsSimulation.Quadrature.lagrange_interpolation (chebGaussNode N) hinj p hp
  have hev : ∀ x : ℝ, p.eval x = ∑ i : Fin N,
      (Polynomial.C (p.eval (chebGaussNode N i)) *
        Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) i).eval x := by
    intro x
    conv_lhs => rw [hlag]
    rw [Polynomial.eval_finsetSum]
  calc (∫ x in (-1 : ℝ)..1, p.eval x)
      = ∫ x in (-1 : ℝ)..1, ∑ i : Fin N,
          (Polynomial.C (p.eval (chebGaussNode N i)) *
            Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) i).eval x :=
        intervalIntegral.integral_congr (fun x _ => hev x)
    _ = ∑ i : Fin N, ∫ x in (-1 : ℝ)..1,
          (Polynomial.C (p.eval (chebGaussNode N i)) *
            Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) i).eval x :=
        integral_finset_sum_real Finset.univ
          (fun i => fun x => (Polynomial.C (p.eval (chebGaussNode N i)) *
            Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) i).eval x) (-1) 1
          (fun i _ => Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _)
    _ = chebQuadRule N p.eval := by
        have hint : ∀ i : Fin N,
            (∫ x in (-1 : ℝ)..1,
              (Polynomial.C (p.eval (chebGaussNode N i)) *
                Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) i).eval x)
              = p.eval (chebGaussNode N i) * chebInterpWeight N i := by
          intro i
          rw [intervalIntegral.integral_congr (fun x _ => by
              rw [Polynomial.eval_mul, Polynomial.eval_C]),
            intervalIntegral.integral_const_mul, chebInterpWeight]
        simp only [hint]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem chebQuadWeightSum {N : ℕ} (hN : 0 < N) :
    ∑ j, chebInterpWeight N j = 2 := by
  have h := chebQuadExact hN 1 (by simp; omega)
  have h1 : (fun x : ℝ => (1 : Polynomial ℝ).eval x) = fun _ => (1 : ℝ) := by
    funext x; simp
  rw [h1, intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  have h2 : ((1 : ℝ) - (-1 : ℝ)) * 1 = 2 := by norm_num
  rw [h2] at h
  simpa only [chebQuadRule, mul_one] using h.symm

noncomputable def chebGaussAngle (N : ℕ) (j : Fin N) : ℝ :=
  (2 * ((j : ℕ) : ℝ) + 1) * Real.pi / (2 * (N : ℝ))

theorem chebGaussNode_eq_cos (N : ℕ) (j : Fin N) :
    chebGaussNode N j = Real.cos (chebGaussAngle N j) := by
  rw [chebGaussNode, chebGaussAngle]

noncomputable def cosNodeSum (N : ℕ) (r : ℤ) : ℝ :=
  ∑ j : Fin N, Real.cos (((r : ℤ) : ℝ) * chebGaussAngle N j)

theorem cosNodeSum_zero (N : ℕ) : cosNodeSum N 0 = (N : ℝ) := by
  simp [cosNodeSum, chebGaussAngle]

theorem chebNodeEvalSum_zero (N : ℕ) :
    ∑ j : Fin N, (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval (chebGaussNode N j)
      = (N : ℝ) := by
  simp [Polynomial.Chebyshev.T_zero]

theorem chebNodeEvalSum_eq_zero {N : ℕ} (hN : 0 < N) {r : ℤ} (hr0 : r ≠ 0)
    (hrN : |r| < 2 * N) :
    ∑ j : Fin N, (Polynomial.Chebyshev.T ℝ r).eval (chebGaussNode N j) = 0 := by
  have hndvd : ¬((2 * (N : ℤ)) ∣ r) := by
    rintro ⟨q, hq⟩
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hr0 hq
    have hq1 : (1 : ℤ) ≤ |q| := Int.one_le_abs hq0
    have hpos2 : (0 : ℤ) < 2 * (N : ℤ) := by omega
    rw [hq, abs_mul, abs_of_pos hpos2] at hrN
    have hge : (2 * (N : ℤ)) ≤ (2 * (N : ℤ)) * |q| := by
      have hle := mul_le_mul_of_nonneg_left hq1 hpos2.le
      rwa [mul_one] at hle
    linarith
  have h := Polynomial.Chebyshev.sumZeroes_T_of_not_dvd (n := N) (k := r) hndvd
  rw [Polynomial.Chebyshev.sumZeroes, mul_eq_zero_iff_left
    (div_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hN.ne'))] at h
  have hterm : ∀ j : Fin N, (Polynomial.Chebyshev.T ℝ r).eval (chebGaussNode N j)
      = (Polynomial.Chebyshev.T ℝ r).eval
        (Real.cos ((2 * ((j : ℕ) : ℝ) + 1) / (2 * ((N : ℕ) : ℝ)) * Real.pi)) := by
    intro j
    rw [chebGaussNode_eq_cos]
    congr 2
    rw [chebGaussAngle, div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range
      (f := fun i => (Polynomial.Chebyshev.T ℝ r).eval
        (Real.cos ((2 * ((i : ℕ) : ℝ) + 1) / (2 * ((N : ℕ) : ℝ)) * Real.pi)))]
  exact h

theorem cosNodeSum_eq_zero {N : ℕ} (hN : 0 < N) {r : ℤ} (hr0 : r ≠ 0)
    (hrN : |r| < 2 * N) :
    cosNodeSum N r = 0 := by
  have h := chebNodeEvalSum_eq_zero hN hr0 hrN
  simp only [cosNodeSum]
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [show Real.cos (((r : ℤ) : ℝ) * chebGaussAngle N j)
        = (Polynomial.Chebyshev.T ℝ r).eval (chebGaussNode N j) from by
        rw [chebGaussNode_eq_cos, Polynomial.Chebyshev.T_real_cos]])]
  exact h

theorem cosNodeSum_natCast_eq_zero {N : ℕ} (hN0 : 0 < N) {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n < 2 * N) :
    cosNodeSum N ((n : ℕ) : ℤ) = 0 :=
  cosNodeSum_eq_zero hN0 (by exact_mod_cast hn0) (by exact_mod_cast hnN)

theorem cosNodeSum_sub_eq_zero {N : ℕ} (hN0 : 0 < N) {k m : ℕ}
    (hne : 2 * k ≠ m) (hkN : 2 * k < 2 * N) (hmN : m < 2 * N) :
    cosNodeSum N (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)) = 0 := by
  have hr0 : ((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((2 * k : ℕ) : ℤ) = ((m : ℕ) : ℤ) := sub_eq_zero.mp h0
    exact_mod_cast h1
  have hrN : |((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)| < 2 * N := by
    rw [abs_lt]
    constructor <;> (push_cast; omega)
  exact cosNodeSum_eq_zero hN0 hr0 hrN

theorem chebT_eval_chebGaussNode_eq_cos (N : ℕ) (m : ℕ) (j : Fin N) :
    (Polynomial.Chebyshev.T ℝ m).eval (chebGaussNode N j)
      = Real.cos ((m : ℝ) * chebGaussAngle N j) := by
  rw [chebGaussNode_eq_cos,
    Polynomial.Chebyshev.T_real_cos (chebGaussAngle N j) ((m : ℕ) : ℤ)]
  push_cast
  ring

private theorem derivative_two_mul_X (p : Polynomial ℝ) :
    (2 * Polynomial.X * p).derivative = 2 * p + 2 * Polynomial.X * p.derivative := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_ofNat, zero_mul, mul_one, zero_add]

private theorem natCast_two : ((2 : Polynomial ℝ)) = Polynomial.C (2 : ℝ) :=
  (Polynomial.C_eq_natCast 2).symm

private theorem chebT_derivative_succ (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (((n : ℕ) : ℤ) + 1)).derivative
      = ((n : ℝ) + 1) • Polynomial.Chebyshev.U ℝ ((n : ℕ) : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
      have hE1 : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
      have hE : (((1 : ℕ) : ℤ) + 1) = (2 : ℤ) := by norm_num
      have hE' : (((1 : ℕ) : ℝ) + 1) = (2 : ℝ) := by norm_num
      rw [hE, hE', hE1, Polynomial.Chebyshev.T_two ℝ, two_mul,
        Polynomial.Chebyshev.U_one ℝ,
        Polynomial.derivative_sub, Polynomial.derivative_add,
        Polynomial.derivative_X_sq,
        Polynomial.derivative_one, sub_zero]
      simp only [natCast_two, ← Polynomial.algebraMap_eq, ← Algebra.smul_def, smul_smul]
      module
  | more n ih1 ih2 =>
      have hi2a : (((n + 1 : ℕ) : ℤ) + 1) = (((n : ℕ) : ℤ) + 2) := by push_cast; ring
      have hi2b : (((n + 1 : ℕ) : ℝ) + 1) = (((n : ℕ) : ℝ) + 2) := by push_cast; ring
      have hi2c : ((n + 1 : ℕ) : ℤ) = (((n : ℕ) : ℤ) + 1) := by push_cast; ring
      rw [hi2a, hi2b, hi2c] at ih2
      have hga : (((n + 2 : ℕ) : ℤ) + 1) = (((n : ℕ) : ℤ) + 3) := by push_cast; ring
      have hgb : (((n + 2 : ℕ) : ℝ) + 1) = (((n : ℕ) : ℝ) + 3) := by push_cast; ring
      have hgc : ((n + 2 : ℕ) : ℤ) = (((n : ℕ) : ℤ) + 2) := by push_cast; ring
      rw [hga, hgb, hgc]
      have hrec : Polynomial.Chebyshev.T ℝ (((n : ℕ) : ℤ) + 3)
          = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ (((n : ℕ) : ℤ) + 2)
            - Polynomial.Chebyshev.T ℝ (((n : ℕ) : ℤ) + 1) := by
        have h := Polynomial.Chebyshev.T_add_two ℝ (((n : ℕ) : ℤ) + 1)
        rw [show (((n : ℕ) : ℤ) + 1 + 2) = (((n : ℕ) : ℤ) + 3) from by ring] at h
        exact h
      have h2T : (2 : Polynomial ℝ) * Polynomial.Chebyshev.T ℝ (((n : ℕ) : ℤ) + 2)
          = Polynomial.Chebyshev.U ℝ (((n : ℕ) : ℤ) + 2)
            - Polynomial.Chebyshev.U ℝ ((n : ℕ) : ℤ) :=
        Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ ((n : ℕ) : ℤ)
      have hU : Polynomial.Chebyshev.U ℝ (((n : ℕ) : ℤ) + 2)
          = 2 * Polynomial.X * Polynomial.Chebyshev.U ℝ (((n : ℕ) : ℤ) + 1)
            - Polynomial.Chebyshev.U ℝ ((n : ℕ) : ℤ) :=
        Polynomial.Chebyshev.U_add_two ℝ ((n : ℕ) : ℤ)
      rw [hrec, Polynomial.derivative_sub, derivative_two_mul_X, ih2, ih1, h2T, hU]
      simp only [natCast_two, ← Polynomial.algebraMap_eq, ← Algebra.smul_def,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
      module

theorem chebT_integral_zero :
    (∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x) = 2 := by
  simp only [show ((0 : ℕ) : ℤ) = 0 from rfl, Polynomial.Chebyshev.T_zero,
    Polynomial.eval_one, intervalIntegral.integral_const]
  norm_num

private theorem chebT_antiderivative_derivative (m : ℕ) (hm : 2 ≤ m) :
    (Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1)))
        * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) + 1)
      - Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1)))
        * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) - 1)).derivative
      = Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ) := by
  have hcast2 : ((m : ℕ) : ℤ) - 1 = (((m - 2 : ℕ) : ℤ)) + 1 := by
    have h2 : (((m - 2 : ℕ) : ℤ)) + 2 = ((m : ℕ) : ℤ) := by
      have hsub : (m - 2 : ℕ) + 2 = m := by omega
      exact_mod_cast hsub
    linarith
  have hbr : (2 : Polynomial ℝ) * Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)
      = Polynomial.Chebyshev.U ℝ ((m : ℕ) : ℤ)
        - Polynomial.Chebyshev.U ℝ (((m - 2 : ℕ) : ℤ)) := by
    have h := Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ (((m - 2 : ℕ) : ℤ))
    rw [show (((m - 2 : ℕ) : ℤ)) + 2 = ((m : ℕ) : ℤ) from by omega] at h
    exact h
  rw [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
    chebT_derivative_succ m, hcast2, chebT_derivative_succ (m - 2)]
  simp only [zero_add]
  have hcoef : (((m - 2 : ℕ) : ℝ)) + 1 = (((m : ℕ) : ℝ)) - 1 := by
    have h2 : (((m - 2 : ℕ) : ℝ)) + 2 = ((m : ℕ) : ℝ) := by
      have hsub : (m - 2 : ℕ) + 2 = m := by omega
      exact_mod_cast hsub
    linarith
  have hgoal : (2 : Polynomial ℝ) * (Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1)))
        * (((m : ℝ) + 1) • Polynomial.Chebyshev.U ℝ ((m : ℕ) : ℤ))
      - Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1)))
        * ((((m - 2 : ℕ) : ℝ) + 1) • Polynomial.Chebyshev.U ℝ (((m - 2 : ℕ) : ℤ))))
      = (2 : Polynomial ℝ) * Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ) := by
    rw [mul_sub, hbr, hcoef]
    have hne1 : (((m : ℕ) : ℝ)) + 1 ≠ 0 := by
      have h0 : (0 : ℝ) < ((m : ℕ) : ℝ) + 1 := by exact_mod_cast Nat.succ_pos m
      exact ne_of_gt h0
    have hne2 : (((m : ℕ) : ℝ)) - 1 ≠ 0 := by
      have h2 : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm
      linarith
    have key1 : (((m : ℕ) : ℝ) + 1) * ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1))) * 2 = 1 := by
      field_simp
    have key2 : (((m : ℕ) : ℝ) - 1) * ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1))) * 2 = 1 := by
      field_simp
    simp only [natCast_two, ← Polynomial.algebraMap_eq, ← Algebra.smul_def,
      Algebra.mul_smul_comm, smul_smul]
    rw [key1, key2, one_smul, one_smul]
  exact mul_left_cancel₀ (two_ne_zero) hgoal

private theorem chebT_integral_succ_sub (m : ℕ) (hm : 2 ≤ m) :
    (∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)
      = (1 - (-1 : ℝ) ^ (m + 1)) / (2 * (((m : ℕ) : ℝ) + 1))
        - (1 - (-1 : ℝ) ^ (m - 1)) / (2 * (((m : ℕ) : ℝ) - 1)) := by
  have hint : IntervalIntegrable
      (fun x : ℝ => (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)
      MeasureTheory.volume (-1) 1 :=
    Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _
  have hder := chebT_antiderivative_derivative m hm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ =>
      (Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1)))
          * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) + 1)
        - Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1)))
          * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) - 1)).eval x)
    (f' := fun x : ℝ => (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)
    (fun x _ => by
      have hq := (Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1)))
          * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) + 1)
        - Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1)))
          * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) - 1)).hasDerivAt x
      rwa [hder] at hq)
    hint
  calc (∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)
      = (Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1)))
            * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) + 1)
          - Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1)))
            * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) - 1)).eval 1
        - (Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) + 1)))
            * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) + 1)
          - Polynomial.C ((1 : ℝ) / (2 * (((m : ℕ) : ℝ) - 1)))
            * Polynomial.Chebyshev.T ℝ (((m : ℕ) : ℤ) - 1)).eval (-1) := hftc
    _ = (1 - (((Int.negOnePow (((m : ℕ) : ℤ) + 1) : ℤ) : ℝ)))
          / (2 * (((m : ℕ) : ℝ) + 1))
        - (1 - (((Int.negOnePow (((m : ℕ) : ℤ) - 1) : ℤ) : ℝ)))
          / (2 * (((m : ℕ) : ℝ) - 1)) := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.Chebyshev.T_eval_one, Polynomial.Chebyshev.T_eval_neg_one]
        ring_nf
    _ = (1 - (-1 : ℝ) ^ (m + 1)) / (2 * (((m : ℕ) : ℝ) + 1))
        - (1 - (-1 : ℝ) ^ (m - 1)) / (2 * (((m : ℕ) : ℝ) - 1)) := by
        have hc1 : ((m : ℕ) : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
        have hc2 : ((m : ℕ) : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) := by
          have hsub : (m - 1 : ℕ) + 1 = m := by omega
          push_cast at hsub ⊢
          omega
        rw [hc1, hc2, Int.cast_negOnePow ℝ, Int.cast_negOnePow ℝ, zpow_natCast,
          zpow_natCast]

theorem chebT_integral_of_odd {m : ℕ} (hm : Odd m) :
    (∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x) = 0 := by
  obtain ⟨t, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · have hred : ((2 * 0 + 1 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
    have hT1 : ∀ x : ℝ, (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)).eval x = x := by
      intro x; simp
    rw [hred, intervalIntegral.integral_congr (fun x _ => hT1 x)]
    have hint : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume (-1) 1 :=
      (continuous_id).intervalIntegrable (-1) 1
    have hftc1 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => x ^ 2 / 2) (f' := fun x : ℝ => x)
      (fun x _ => by
        have h2 := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
        simpa using h2)
      hint
    rw [hftc1]
    norm_num
  · have hm2 : 2 ≤ 2 * t + 1 := by omega
    have hnp1 : (-1 : ℝ) ^ ((2 * t + 1) + 1) = 1 :=
      Even.neg_one_pow ⟨t + 1, by omega⟩
    have hnp2 : (-1 : ℝ) ^ ((2 * t + 1) - 1) = 1 :=
      Even.neg_one_pow ⟨t, by omega⟩
    rw [chebT_integral_succ_sub (2 * t + 1) hm2, hnp1, hnp2]
    norm_num

private theorem even_integral_identity (x : ℝ) (h1 : x + 1 ≠ 0) (h2 : x - 1 ≠ 0)
    (h3 : 1 - x ^ 2 ≠ 0) :
    (1 - (-1 : ℝ)) / (2 * (x + 1)) - (1 - (-1 : ℝ)) / (2 * (x - 1))
      = 2 / (1 - x ^ 2) := by
  field_simp
  ring

theorem chebT_integral_of_even {m : ℕ} (hm2 : 2 ≤ m) (hme : Even m) :
    (∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)
      = 2 / (1 - ((m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨t, ht⟩ := hme
  have hm2t : m = 2 * t := by omega
  subst hm2t
  have hnp1 : (-1 : ℝ) ^ ((2 * t) + 1) = -1 :=
    Odd.neg_one_pow ⟨t, by omega⟩
  have hnp2 : (-1 : ℝ) ^ ((2 * t) - 1) = -1 :=
    Odd.neg_one_pow ⟨t - 1, by omega⟩
  rw [chebT_integral_succ_sub (2 * t) (by omega), hnp1, hnp2]
  refine even_integral_identity _ (by positivity) ?_ ?_
  · have h1 : (1 : ℝ) < ((2 * t : ℕ) : ℝ) := by
      exact_mod_cast (show (1 : ℕ) < 2 * t by omega)
    linarith
  · have htwo : (2 : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by
      exact_mod_cast (show (2 : ℕ) ≤ 2 * t by omega)
    nlinarith [htwo]

noncomputable def fejerWeight (N : ℕ) (j : Fin N) : ℝ :=
  (2 / ((N : ℝ))) * (1 - 2 * ∑ k ∈ Finset.Icc 1 (N / 2),
    Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j) / (4 * ((k : ℕ) : ℝ) ^ 2 - 1))

noncomputable def fejerQuad (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, fejerWeight N j * f (chebGaussNode N j)

private theorem fejerQuad_sum {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) :
    fejerQuad N (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, fejerQuad N (f i) := by
  simp only [fejerQuad, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem fejerQuad_const_mul {N : ℕ} (c : ℝ) (f : ℝ → ℝ) :
    fejerQuad N (fun x => c * f x) = c * fejerQuad N f := by
  simp only [fejerQuad, mul_left_comm, ← Finset.mul_sum]

private theorem fejerQuad_expand {N : ℕ} (f : ℝ → ℝ) :
    fejerQuad N f = (2 / ((N : ℝ))) * ∑ j : Fin N, f (chebGaussNode N j)
      - (4 / ((N : ℝ))) * ∑ k ∈ Finset.Icc 1 (N / 2),
        (∑ j : Fin N, Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
          * f (chebGaussNode N j)) / (4 * ((k : ℕ) : ℝ) ^ 2 - 1) := by
  have hterm : ∀ j : Fin N, fejerWeight N j * f (chebGaussNode N j)
      = (2 / ((N : ℝ))) * f (chebGaussNode N j)
        - (4 / ((N : ℝ))) * ∑ k ∈ Finset.Icc 1 (N / 2),
          Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
            * f (chebGaussNode N j) / (4 * ((k : ℕ) : ℝ) ^ 2 - 1) := by
    intro j
    simp only [fejerWeight]
    have hmul : (∑ k ∈ Finset.Icc 1 (N / 2),
        Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
          / (4 * ((k : ℕ) : ℝ) ^ 2 - 1)) * f (chebGaussNode N j)
      = ∑ k ∈ Finset.Icc 1 (N / 2),
        Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
          * f (chebGaussNode N j) / (4 * ((k : ℕ) : ℝ) ^ 2 - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← hmul]
    ring
  simp only [fejerQuad]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  refine congrArg (fun t => 2 / ((N : ℝ)) * ∑ j : Fin N, f (chebGaussNode N j)
    - 4 / ((N : ℝ)) * t) ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  exact (Finset.sum_div (Finset.univ)
    (fun x : Fin N => Real.cos (2 * ((y : ℕ) : ℝ) * chebGaussAngle N x)
      * f (chebGaussNode N x)) (4 * ((y : ℕ) : ℝ) ^ 2 - 1)).symm

private theorem fejerCrossSum_eq {N : ℕ} (hN : 0 < N) {k m : ℕ}
    (hk1 : 1 ≤ k) (hkN : 2 * k ≤ N) (hmN : m < N) :
    ∑ j : Fin N, Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
        * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval (chebGaussNode N j)
      = if 2 * k = m then ((N : ℝ)) / 2 else 0 := by
  have hcosT : ∀ j : Fin N, Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
      = (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval (chebGaussNode N j) := by
    intro j
    rw [chebT_eval_chebGaussNode_eq_cos]
    congr 1
    push_cast
    ring
  have h2 := Polynomial.Chebyshev.T_mul_T ℝ ((2 * k : ℕ) : ℤ) ((m : ℕ) : ℤ)
  have hprod : ∀ j : Fin N,
      (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval (chebGaussNode N j)
        * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval (chebGaussNode N j)
      = ((Polynomial.Chebyshev.T ℝ (((2 * k : ℕ) : ℤ) + ((m : ℕ) : ℤ))).eval
          (chebGaussNode N j)
        + (Polynomial.Chebyshev.T ℝ (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ))).eval
          (chebGaussNode N j)) / 2 := by
    intro j
    have hev : ((2 : Polynomial ℝ)
        * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ))
        * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ))).eval (chebGaussNode N j)
      = ((Polynomial.Chebyshev.T ℝ (((2 * k : ℕ) : ℤ) + ((m : ℕ) : ℤ)))
        + (Polynomial.Chebyshev.T ℝ (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)))).eval
          (chebGaussNode N j) := by
      rw [h2]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat] at hev
    rw [eq_div_iff two_ne_zero]
    linear_combination hev
  have hSp : ∑ j : Fin N, (Polynomial.Chebyshev.T ℝ
      (((2 * k : ℕ) : ℤ) + ((m : ℕ) : ℤ))).eval (chebGaussNode N j) = 0 :=
    chebNodeEvalSum_eq_zero hN (by exact_mod_cast (by omega))
      (by exact_mod_cast (by omega))
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcosT j, hprod j])]
  simp_rw [add_div]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hSp, zero_div,
    zero_add]
  by_cases h2k : 2 * k = m
  · rw [if_pos h2k]
    have hSm : ∑ j : Fin N, (Polynomial.Chebyshev.T ℝ
        (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ))).eval (chebGaussNode N j)
        = ((N : ℝ)) := by
      rw [show (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)) = ((0 : ℕ) : ℤ) from by
          push_cast; omega,
        chebNodeEvalSum_zero]
    rw [hSm]
  · rw [if_neg h2k]
    have hSm : ∑ j : Fin N, (Polynomial.Chebyshev.T ℝ
        (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ))).eval (chebGaussNode N j) = 0 := by
      refine chebNodeEvalSum_eq_zero hN ?_ ?_
      · intro h0
        refine h2k ?_
        have h1 : ((2 * k : ℕ) : ℤ) = ((m : ℕ) : ℤ) := sub_eq_zero.mp h0
        exact_mod_cast h1
      · rw [abs_lt]
        push_cast
        omega
    rw [hSm]
    ring

theorem fejerQuad_T_zero {N : ℕ} (hN : 0 < N) :
    fejerQuad N (fun x => (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x) = 2 := by
  rw [fejerQuad_expand, chebNodeEvalSum_zero]
  have hk : ∀ k ∈ Finset.Icc 1 (N / 2),
      (∑ j : Fin N, Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
        * (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval (chebGaussNode N j))
        / (4 * ((k : ℕ) : ℝ) ^ 2 - 1) = 0 := by
    intro k hkmem
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hkmem
    have hc := fejerCrossSum_eq hN hk1 (by omega) (by omega)
    rw [hc, if_neg (by omega : ¬(2 * k = 0)), zero_div]
  have hN0 : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [Finset.sum_congr rfl hk, Finset.sum_const_zero, mul_zero, sub_zero,
    div_mul_cancel₀ _ hN0]

theorem fejerQuad_T_of_odd {N : ℕ} (hN : 0 < N) {m : ℕ} (hmN : m < N) (hm : Odd m) :
    fejerQuad N (fun x => (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x) = 0 := by
  have hmne : m ≠ 0 := by
    obtain ⟨t, rfl⟩ := hm
    omega
  rw [fejerQuad_expand, chebNodeEvalSum_eq_zero hN (by exact_mod_cast hmne)
    (by exact_mod_cast (by omega))]
  have hk : ∀ k ∈ Finset.Icc 1 (N / 2),
      (∑ j : Fin N, Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
        * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval (chebGaussNode N j))
        / (4 * ((k : ℕ) : ℝ) ^ 2 - 1) = 0 := by
    intro k hkmem
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hkmem
    have hc := fejerCrossSum_eq hN hk1 (by omega) hmN
    rw [hc, if_neg (by rcases hm with ⟨t, rfl⟩; omega), zero_div]
  rw [Finset.sum_congr rfl hk, Finset.sum_const_zero, mul_zero, mul_zero]
  norm_num

theorem fejerQuad_T_of_even {N : ℕ} (hN : 0 < N) {m : ℕ} (hm2 : 2 ≤ m)
    (hme : Even m) (hmN : m < N) :
    fejerQuad N (fun x => (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x)
      = 2 / (1 - ((m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨t, ht⟩ := hme
  have hm2t : m = 2 * t := by omega
  subst hm2t
  have hpos : 1 ≤ t := by omega
  have hm0 : (2 * t : ℕ) ≠ 0 := by omega
  rw [fejerQuad_expand, chebNodeEvalSum_eq_zero hN (by exact_mod_cast hm0)
    (by exact_mod_cast (by omega))]
  have hmem : (2 * t / 2 : ℕ) ∈ Finset.Icc 1 (N / 2) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hk : ∑ k ∈ Finset.Icc 1 (N / 2),
      (∑ j : Fin N, Real.cos (2 * ((k : ℕ) : ℝ) * chebGaussAngle N j)
        * (Polynomial.Chebyshev.T ℝ ((2 * t : ℕ) : ℤ)).eval (chebGaussNode N j))
        / (4 * ((k : ℕ) : ℝ) ^ 2 - 1)
      = (((N : ℝ)) / 2) / (4 * ((((2 * t / 2 : ℕ) : ℝ)) ^ 2) - 1) := by
    rw [Finset.sum_eq_single (2 * t / 2)]
    · rw [fejerCrossSum_eq hN (by omega) (by omega) (by omega),
        if_pos (by omega : 2 * (2 * t / 2) = 2 * t)]
    · intro k hkmem hkne
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hkmem
      rw [fejerCrossSum_eq hN hk1 (by omega) (by omega),
        if_neg (by omega : ¬(2 * k = 2 * t)), zero_div]
    · intro hnm
      exact absurd hmem hnm
  have hhalf : ((((2 * t / 2 : ℕ) : ℝ)) ^ 2) = (((t : ℕ) : ℝ)) ^ 2 := by
    congr 1
    exact_mod_cast (show (2 * t / 2 : ℕ) = t by omega)
  have hsq : 4 * (((t : ℕ) : ℝ)) ^ 2 - 1 = ((2 * t : ℕ) : ℝ) ^ 2 - 1 := by
    push_cast
    ring
  have hden : (((2 * t : ℕ) : ℝ) ^ 2 - 1) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ ((t : ℕ) : ℝ) := by exact_mod_cast hpos
    nlinarith
  have hN0 : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [hk, mul_zero, zero_sub, hhalf, hsq]
  have key : (4 / ((N : ℝ))) * ((((N : ℝ)) / 2) / (((2 * t : ℕ) : ℝ) ^ 2 - 1))
      = -(2 / (1 - ((2 * t : ℕ) : ℝ) ^ 2)) := by
    have e3 : (1 : ℝ) - ((2 * t : ℕ) : ℝ) ^ 2 ≠ 0 := by
      intro h0
      apply hden
      linarith
    field_simp
    ring
  rw [key]
  ring

theorem chebT_span {N : ℕ} (p : Polynomial ℝ) (hp : p.natDegree < N) :
    ∃ c : ℕ → ℝ, p = ∑ m ∈ Finset.range N,
      c m • Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · refine ⟨fun _ => 0, ?_⟩
    simp
  · have hmem : p ∈ Polynomial.degreeLT ℝ N := by
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mp hp
    rw [← Polynomial.Sequence.span_degreeLT
        (Polynomial.Chebyshev.chebyshevTsequence ℝ) (by simp),
      show (Set.Iio N) = (Finset.range N : Set ℕ) by simp,
      Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
    obtain ⟨c, rfl⟩ := hmem
    exact ⟨fun m => c m, rfl⟩

theorem fejerQuad_exact {N : ℕ} (hN : 0 < N) (p : Polynomial ℝ) (hp : p.natDegree < N) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = fejerQuad N p.eval := by
  obtain ⟨c, hc⟩ := chebT_span p hp
  have hfev : ∀ x : ℝ, p.eval x
      = ∑ m ∈ Finset.range N, c m * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x := by
    intro x
    rw [hc, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun m _ => by
      rw [Polynomial.eval_smul, smul_eq_mul]
  have hfun : p.eval = fun x => ∑ m ∈ Finset.range N,
      c m * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x := funext hfev
  have hR : fejerQuad N p.eval
      = ∑ m ∈ Finset.range N,
        c m * fejerQuad N (fun x => (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x) := by
    rw [hfun, fejerQuad_sum]
    exact Finset.sum_congr rfl fun m _ => fejerQuad_const_mul (c m) _
  rw [hR, hfun, integral_finset_sum_real (Finset.range N)
      (fun m x => c m * (Polynomial.Chebyshev.T ℝ ((m : ℕ) : ℤ)).eval x) (-1) 1
      (fun m _ => (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _).const_mul (c m))]
  have hsplit : ∀ i ∈ Finset.range N,
      (∫ x in (-1 : ℝ)..1, c i * (Polynomial.Chebyshev.T ℝ ((i : ℕ) : ℤ)).eval x)
      = c i * (∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ ((i : ℕ) : ℤ)).eval x) :=
    fun i _ => intervalIntegral.integral_const_mul _ _
  rw [Finset.sum_congr rfl hsplit]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m < N := Finset.mem_range.mp hm
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [fejerQuad_T_zero hN, chebT_integral_zero]
  · rcases Nat.even_or_odd' m with ⟨t, hm | hm⟩
    · rw [fejerQuad_T_of_even hN (by omega) ⟨t, by omega⟩ hmN,
        chebT_integral_of_even (by omega) ⟨t, by omega⟩]
    · rw [fejerQuad_T_of_odd hN hmN ⟨t, hm⟩, chebT_integral_of_odd ⟨t, hm⟩]

theorem chebQuadRule_eq_fejerQuad {N : ℕ} (hN : 0 < N) (p : Polynomial ℝ)
    (hp : p.natDegree < N) :
    chebQuadRule N p.eval = fejerQuad N p.eval :=
  (chebQuadExact hN p hp).symm.trans (fejerQuad_exact hN p hp)

theorem fejerWeightSum {N : ℕ} (hN : 0 < N) :
    ∑ j : Fin N, fejerWeight N j = 2 := by
  have h := fejerQuad_T_zero hN
  simp only [fejerQuad, show ((0 : ℕ) : ℤ) = 0 from rfl, Polynomial.Chebyshev.T_zero,
    Polynomial.eval_one, mul_one] at h
  exact h

theorem chebInterpWeight_eq_fejerWeight {N : ℕ} (hN : 0 < N) (j : Fin N) :
    chebInterpWeight N j = fejerWeight N j := by
  have hinj := chebGaussNode_injective hN
  set L : Polynomial ℝ :=
    Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis (chebGaussNode N) j with hLdef
  have hdeg : L.natDegree < N :=
    lt_of_le_of_lt (Qatlib.Concepts.LchsSimulation.Quadrature.natDegree_lagrangeBasis_le (chebGaussNode N) j)
      (by omega)
  have hexact := fejerQuad_exact hN L hdeg
  rw [hLdef, ← chebInterpWeight] at hexact
  rw [hexact, fejerQuad, Finset.sum_eq_single j]
  · rw [Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_self (chebGaussNode N) hinj j,
      mul_one]
  · intro i _ hne
    rw [Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_of_ne (chebGaussNode N) hne,
        mul_zero]
  · intro hnm
    exact absurd (Finset.mem_univ j) hnm

private theorem iterSup_nonneg {n : ℕ} {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) f) :
    (0 : ℝ) ≤ ⨆ k ∈ Set.Icc a b, |iteratedDeriv n f k| := by
  have hcont : Continuous (fun k => iteratedDeriv n f k) :=
    hf.continuous_iteratedDeriv n (by exact_mod_cast le_refl n)
  have hbdd : BddAbove ((fun k => |iteratedDeriv n f k|) '' Set.Icc a b) :=
    isCompact_Icc.bddAbove_image hcont.abs.continuousOn
  have htrange : (⋃ i, Set.range (fun (_ : i ∈ Set.Icc a b) =>
      |iteratedDeriv n f i|)) ⊆
      (fun k => |iteratedDeriv n f k|) '' Set.Icc a b := by
    intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hi⟩ := hy
    rw [Set.mem_range] at hi
    obtain ⟨z, hz⟩ := hi
    exact ⟨i, z, hz⟩
  obtain ⟨z, hz⟩ : (Set.Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  have hle := le_ciSup₂ (f := fun (k : ℝ) (_ : k ∈ Set.Icc a b) =>
    |iteratedDeriv n f k|) (hbdd.mono htrange) z hz
  linarith [abs_nonneg (iteratedDeriv n f z)]

theorem lagrangeInterpRemainderAbs {N : ℕ} (hN : 0 < N) (a b : ℝ) (hab : a ≤ b)
    (node : Fin N → ℝ) (hinj : Function.Injective node) (hmem : ∀ i, node i ∈ Set.Icc a b)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    |f x - (lagrangeInterpPoly node f).eval x| ≤
      ((⨆ k ∈ Set.Icc a b, |iteratedDeriv N f k|) / (N.factorial : ℝ)) *
        ∏ i, |x - node i| := by
  set P : Polynomial ℝ := lagrangeInterpPoly node f with hPdef
  set ω : Polynomial ℝ := ∏ i : Fin N, (Polynomial.X - Polynomial.C (node i)) with hωdef
  have hωmonic : ω.Monic := by
    rw [hωdef]
    exact Polynomial.monic_prod_X_sub_C _ _
  have hωne : ω ≠ 0 := hωmonic.ne_zero
  have hωdeg : ω.natDegree = N := by
    rw [hωdef, Polynomial.natDegree_prod_of_monic Finset.univ
      (fun i => Polynomial.X - Polynomial.C (node i))
      (fun i _ => Polynomial.monic_X_sub_C _)]
    simp
  have hωval : ∀ y : ℝ, ω.eval y = ∏ i : Fin N, (y - node i) := by
    intro y
    rw [hωdef, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hPnode : ∀ i, P.eval (node i) = f (node i) :=
    fun i => lagrangeInterpPoly_eval_node node hinj f i
  by_cases hxω : ω.eval x = 0
  · obtain ⟨q, hq⟩ : ∃ q : Fin N, x = node q := by
      have hzero : ∏ i : Fin N, (x - node i) = 0 := by rw [← hωval x, hxω]
      obtain ⟨i, _, hi⟩ := (Finset.prod_eq_zero_iff (s := Finset.univ)
        (f := fun i => x - node i)).mp hzero
      exact ⟨i, sub_eq_zero.mp hi⟩
    subst hq
    rw [hPnode q, sub_self, abs_zero]
    have hfac : ∏ i : Fin N, |node q - node i| = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by rw [sub_self, abs_zero])
    rw [hfac, mul_zero]
  · have hnx : ∀ i : Fin N, node i ≠ x := by
      intro i hi
      refine hxω ?_
      rw [hωval x, ← hi,
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [sub_self])]
    set K : ℝ := (f x - P.eval x) / ω.eval x with hKdef
    set G : ℝ → ℝ := fun y => f y - P.eval y - K * ω.eval y with hGdef
    have hGcd : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) G :=
      ((hf.sub (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ P)).sub
        (contDiff_const.mul (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ ω)))
    have hGnode : ∀ i : Fin N, G (node i) = 0 := by
      intro i
      show f (node i) - P.eval (node i) - K * ω.eval (node i) = 0
      rw [hPnode i, hωval (node i),
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [sub_self])]
      ring
    have hGx : G x = 0 := by
      show f x - P.eval x - K * ω.eval x = 0
      rw [hKdef, div_mul_cancel₀ _ hxω, sub_self]
    set node' : Fin (N + 1) → ℝ :=
      fun i => if hi : (i : ℕ) < N then node ⟨(i : ℕ), hi⟩ else x with hnode'def
    have hnodeinj : Function.Injective node' := by
      intro i j hij
      have hiB := i.isLt
      have hjB := j.isLt
      by_cases hi : (i : ℕ) < N
      · have hii : node' i = node ⟨(i : ℕ), hi⟩ := dif_pos hi
        rw [hii] at hij
        by_cases hj : (j : ℕ) < N
        · have hjj : node' j = node ⟨(j : ℕ), hj⟩ := dif_pos hj
          rw [hjj] at hij
          refine Fin.ext ?_
          simpa using congrArg Fin.val (hinj hij)
        · have hjj : node' j = x := dif_neg hj
          rw [hjj] at hij
          exact absurd hij (hnx ⟨(i : ℕ), hi⟩)
      · have hii : node' i = x := dif_neg hi
        rw [hii] at hij
        by_cases hj : (j : ℕ) < N
        · have hjj : node' j = node ⟨(j : ℕ), hj⟩ := dif_pos hj
          rw [hjj] at hij
          exact absurd hij.symm (hnx ⟨(j : ℕ), hj⟩)
        · exact Fin.val_injective (show (i : ℕ) = (j : ℕ) by omega)
    have hnodemem : ∀ i : Fin (N + 1), node' i ∈ Set.Icc a b := by
      intro i
      by_cases hi : (i : ℕ) < N
      · show (if hi : (i : ℕ) < N then node ⟨(i : ℕ), hi⟩ else x) ∈ Set.Icc a b
        rw [dif_pos hi]
        exact hmem _
      · show (if hi : (i : ℕ) < N then node ⟨(i : ℕ), hi⟩ else x) ∈ Set.Icc a b
        rw [dif_neg hi]
        exact hx
    have hzeros : ∀ i (j : ℕ), j < 1 → iteratedDeriv j G (node' i) = 0 := by
      intro i j hjlt
      have hj : j = 0 := by omega
      rw [hj, iteratedDeriv_zero]
      by_cases hi : (i : ℕ) < N
      · show G (if hi : (i : ℕ) < N then node ⟨(i : ℕ), hi⟩ else x) = 0
        rw [dif_pos hi]
        exact hGnode _
      · show G (if hi : (i : ℕ) < N then node ⟨(i : ℕ), hi⟩ else x) = 0
        rw [dif_neg hi]
        exact hGx
    have hsum : N + 1 ≤ ∑ i : Fin (N + 1), 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp
    obtain ⟨ξ, hξmem, hξ⟩ := Qatlib.Concepts.LchsSimulation.Quadrature.counted_zero_rolle N (N + 1) a b G node'
      (fun _ => 1) hab hnodeinj hnodemem (fun _ => le_refl 1) hsum hGcd hzeros
    have hcdF : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) (fun y => f y - P.eval y) :=
      hf.sub (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ P)
    have hdouter : iteratedDeriv N G ξ
        = iteratedDeriv N (fun y => f y - P.eval y) ξ
          - iteratedDeriv N (fun y => K * ω.eval y) ξ :=
      iteratedDeriv_sub (hcdF.contDiffAt)
        ((contDiff_const.mul (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ ω)).contDiffAt)
    have hdinner : iteratedDeriv N (fun y => f y - P.eval y) ξ
        = iteratedDeriv N f ξ - iteratedDeriv N (fun t => P.eval t) ξ :=
      iteratedDeriv_sub hf.contDiffAt (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ P).contDiffAt
    have hdP : iteratedDeriv N (fun t => P.eval t) ξ = 0 :=
      Qatlib.Concepts.LchsSimulation.Quadrature.iteratedDeriv_eval_eq_zero
        (lagrangeInterpPoly_natDegree_lt node f hN) ξ
    have hdK : iteratedDeriv N (fun y => K * ω.eval y) ξ
        = K * iteratedDeriv N (fun t => ω.eval t) ξ :=
      iteratedDeriv_const_mul_field K _
    have hdωξ : iteratedDeriv N (fun t => ω.eval t) ξ = (N.factorial : ℝ) := by
      rw [Qatlib.Concepts.LchsSimulation.Quadrature.iteratedDeriv_eval,
        Qatlib.Concepts.LchsSimulation.Quadrature.iterate_derivative_eq_C hωne hωdeg, hωmonic.leadingCoeff,
        mul_one, Polynomial.eval_C]
    rw [hdouter, hdinner, hdP, sub_zero, hdK, hdωξ] at hξ
    have hKeq : K * (N.factorial : ℝ) = iteratedDeriv N f ξ := by linarith
    have hcont : Continuous (fun k => iteratedDeriv N f k) :=
      hf.continuous_iteratedDeriv N (by exact_mod_cast le_refl N)
    have hbddimg : BddAbove ((fun k => |iteratedDeriv N f k|) '' Set.Icc a b) :=
      isCompact_Icc.bddAbove_image hcont.abs.continuousOn
    have htrange : (⋃ i, Set.range (fun (_ : i ∈ Set.Icc a b) =>
        |iteratedDeriv N f i|)) ⊆
        (fun k => |iteratedDeriv N f k|) '' Set.Icc a b := by
      intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨i, hi⟩ := hy
      rw [Set.mem_range] at hi
      obtain ⟨z, hz⟩ := hi
      exact ⟨i, z, hz⟩
    have habsξ : |iteratedDeriv N f ξ| ≤ (⨆ k ∈ Set.Icc a b, |iteratedDeriv N f k|) :=
      le_ciSup₂ (f := fun (k : ℝ) (_ : k ∈ Set.Icc a b) => |iteratedDeriv N f k|)
        (hbddimg.mono htrange) ξ hξmem
    have hfpos : (0 : ℝ) < (N.factorial : ℝ) := by positivity
    have hKb : |K| * (N.factorial : ℝ) ≤ (⨆ k ∈ Set.Icc a b, |iteratedDeriv N f k|) := by
      rw [show |K| * (N.factorial : ℝ) = |K * (N.factorial : ℝ)| from by
        rw [abs_mul, abs_of_nonneg hfpos.le], hKeq]
      exact habsξ
    have hfH : f x - P.eval x = K * ω.eval x := by
      rw [hKdef, div_mul_cancel₀ _ hxω]
    rw [hfH, abs_mul, hωval x, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => abs_nonneg _)
    have hsuppos : (0 : ℝ) ≤ ⨆ k ∈ Set.Icc a b, |iteratedDeriv N f k| := by
      have := abs_nonneg (iteratedDeriv N f ξ)
      linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N.factorial : ℝ))]
    exact hKb

noncomputable def glErrorConst (Q : ℕ) : ℝ :=
  ((Q.factorial : ℝ) ^ 4 * (2 : ℝ) ^ (2 * Q + 1)) /
    (((2 * Q + 1 : ℕ) : ℝ) * ((2 * Q).factorial : ℝ) ^ 3)

noncomputable def chebErrorConst (N : ℕ) : ℝ := (4 : ℝ) / ((2 : ℝ) ^ N * (N.factorial : ℝ))

theorem chebQuadErrorBound {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f) :
    |(∫ x in (-1 : ℝ)..1, f x) - chebQuadRule N f| ≤
      chebErrorConst N * (⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv N f k|) := by
  have hinj := chebGaussNode_injective hN
  set P : Polynomial ℝ := lagrangeInterpPoly (chebGaussNode N) f with hPdef
  have hPnode : ∀ j, P.eval (chebGaussNode N j) = f (chebGaussNode N j) :=
    fun j => lagrangeInterpPoly_eval_node _ hinj f j
  have hrule : chebQuadRule N f = ∫ x in (-1 : ℝ)..1, P.eval x := by
    rw [chebQuadExact hN P (lagrangeInterpPoly_natDegree_lt _ f hN)]
    show ∑ j : Fin N, chebInterpWeight N j * f (chebGaussNode N j)
        = ∑ j : Fin N, chebInterpWeight N j * P.eval (chebGaussNode N j)
    exact Finset.sum_congr rfl fun j _ => by rw [hPnode j]
  have hcontf : Continuous f := hf.continuous
  have hif : IntervalIntegrable f MeasureTheory.volume (-1) 1 :=
    hcontf.intervalIntegrable _ _
  have hiP : IntervalIntegrable (fun x : ℝ => P.eval x) MeasureTheory.volume (-1) 1 :=
    Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval _ _ _
  have hiabs : IntervalIntegrable (fun x : ℝ => |f x - P.eval x|) MeasureTheory.volume (-1) 1 :=
    ((hcontf.sub (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval P)).abs).intervalIntegrable _ _
  have hpb : ∀ x ∈ Set.Icc (-1) 1, |f x - P.eval x| ≤
      ((⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv N f k|) / (N.factorial : ℝ)) *
        (2 / (2 : ℝ) ^ N) := by
    intro x hx
    have h1 := lagrangeInterpRemainderAbs hN (-1) 1 (by norm_num) (chebGaussNode N) hinj
      (fun i => chebGaussNode_mem_Icc hN i) f hf x hx
    refine h1.trans ?_
    have hsuppos : (0 : ℝ) ≤ ⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv N f k| :=
      iterSup_nonneg (by norm_num) f hf
    exact mul_le_mul_of_nonneg_left (chebNodeProd_abs_eval_le hN hx)
      (div_nonneg hsuppos (by positivity))
  calc |(∫ x in (-1 : ℝ)..1, f x) - chebQuadRule N f|
      = |∫ x in (-1 : ℝ)..1, f x - P.eval x| := by
        rw [hrule, ← intervalIntegral.integral_sub hif hiP]
    _ ≤ ∫ x in (-1 : ℝ)..1, |f x - P.eval x| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ x in (-1 : ℝ)..1,
          ((⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv N f k|) / (N.factorial : ℝ)) *
            (2 / (2 : ℝ) ^ N) :=
        intervalIntegral.integral_mono_on (by norm_num) hiabs
          (continuous_const.intervalIntegrable (-1) 1) (fun z hz => hpb z hz)
    _ = chebErrorConst N * (⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv N f k|) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add]
        have hnum : ((1 : ℝ) + 1) = 2 := by norm_num
        rw [hnum]
        have hfpos : (0 : ℝ) < (N.factorial : ℝ) := by positivity
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
        unfold chebErrorConst
        field_simp
        ring

theorem gaussLegendreUnitError (Q : ℕ) (hQ : 0 < Q) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) f) :
    ∃ node weight : Fin Q → ℝ,
      (∀ q, node q ∈ Set.Ioo (-1) 1) ∧ Function.Injective node ∧ (∀ q, 0 < weight q) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
        (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ q, weight q * p.eval (node q)) ∧
      |(∫ x in (-1 : ℝ)..1, f x) - ∑ q, weight q * f (node q)| ≤
        glErrorConst Q * (⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv (2 * Q) f k|) := by
  obtain ⟨node, weight, hIoo, hinj, hwpos, hexact, homega⟩ :=
    gauss_legendre_rule_exists Q (by omega)
  refine ⟨node, weight, hIoo, hinj, hwpos, hexact, ?_⟩
  have hexact' := gauss_cell_rule_affine_exact Q (-1) 2 node weight hexact
  have homega' := gauss_cell_omega Q (-1) 2 node (by norm_num) homega
  have hcell := gauss_legendre_cell_error_bound Q (-1) 2 node weight f (by omega)
    (by norm_num) (fun p hp => hexact' p hp) homega' hf
  have hrpow : (2 : ℝ) ^ ((2 : ℝ) * Q + 1) = (2 : ℝ) ^ (2 * Q + 1) := by
    have hc : ((2 : ℝ) * Q + 1) = ((2 * Q + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hc, Real.rpow_natCast]
  have h1 : (-1 : ℝ) + 2 = 1 := by norm_num
  have h2 : ∀ q : Fin Q, (-1 : ℝ) + 2 * (node q + 1) / 2 = node q := fun q => by ring
  have h3 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [h1, h2, h3, one_mul] at hcell
  rw [hrpow] at hcell
  simpa only [glErrorConst] using hcell

theorem chebErrorConst_pos (N : ℕ) : 0 < chebErrorConst N := by
  unfold chebErrorConst
  positivity

private theorem glErrorConst_succ (N : ℕ) :
    glErrorConst (N + 1) * (2 * ((2 * N + 3 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ^ 2)
      = glErrorConst N * ((N + 1 : ℕ) : ℝ) := by
  have e1 : (((N + 1 : ℕ).factorial : ℝ))
      = ((N + 1 : ℕ) : ℝ) * (((N : ℕ)).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e2 : (((2 * (N + 1) : ℕ).factorial : ℝ))
      = ((2 * N + 2 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) * (((2 * N : ℕ)).factorial : ℝ) := by
    rw [show (2 * (N + 1) : ℕ) = 2 * N + 2 from by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  have e3 : ((2 * (N + 1) + 1 : ℕ) : ℝ) = ((2 * N + 3 : ℕ) : ℝ) := by
    push_cast
    ring
  have e4 : (2 : ℝ) ^ (2 * (N + 1) + 1) = 2 * (2 : ℝ) ^ (2 * N + 2) := by
    rw [show (2 * (N + 1) + 1 : ℕ) = 2 * N + 2 + 1 from by ring, pow_succ, mul_comm]
  unfold glErrorConst
  rw [e1, e2, e3, e4]
  push_cast
  have hfN : ((N : ℕ).factorial : ℝ) ≠ 0 := by positivity
  have hf2N : (((2 * N : ℕ)).factorial : ℝ) ≠ 0 := by positivity
  have hn1 : ((2 * N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn2 : ((2 * N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn3 : ((2 * N + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem chebErrorConst_succ (N : ℕ) :
    chebErrorConst (N + 1) * (2 * ((N + 1 : ℕ) : ℝ)) = chebErrorConst N := by
  unfold chebErrorConst
  rw [Nat.factorial_succ, pow_succ]
  have hpos : (0 : ℝ) < 2 ^ N * (((N : ℕ)).factorial : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < 2 ^ (N + 1) * (((N + 1 : ℕ)).factorial : ℝ) := by positivity
  field_simp
  push_cast
  ring

theorem glErrorConst_le_chebErrorConst (N : ℕ) (hN : 1 ≤ N) :
    glErrorConst N ≤ chebErrorConst N := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN1 : 1 ≤ N
    · have hstep := glErrorConst_succ N
      have hstep2 := chebErrorConst_succ N
      have hkey : 2 * ((N + 1 : ℕ) : ℝ) ^ 2
          ≤ 2 * ((2 * N + 3 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ^ 2 := by
        have hinner : ((N + 1 : ℕ) : ℝ) ^ 2
            ≤ ((2 * N + 3 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ^ 2 := by
          have hN0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le N
          push_cast
          nlinarith [hN0, sq_nonneg ((N : ℕ) : ℝ)]
        nlinarith [hinner]
      have hApos : (0 : ℝ) < 2 * ((2 * N + 3 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ^ 2 := by
        positivity
      have hchpos := chebErrorConst_pos (N + 1)
      have hN1nn : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
      have hchain : glErrorConst (N + 1) * (2 * ((2 * N + 3 : ℕ) : ℝ)
          * ((2 * N + 1 : ℕ) : ℝ) ^ 2)
          ≤ chebErrorConst (N + 1) * (2 * ((2 * N + 3 : ℕ) : ℝ)
            * ((2 * N + 1 : ℕ) : ℝ) ^ 2) := by
        calc glErrorConst (N + 1) * (2 * ((2 * N + 3 : ℕ) : ℝ)
            * ((2 * N + 1 : ℕ) : ℝ) ^ 2)
            = glErrorConst N * ((N + 1 : ℕ) : ℝ) := hstep
          _ ≤ chebErrorConst N * ((N + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right (ih hN1) hN1nn
          _ = chebErrorConst (N + 1) * (2 * ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ) := by
              rw [mul_assoc, ← hstep2]
              ring
          _ = chebErrorConst (N + 1) * (2 * ((N + 1 : ℕ) : ℝ) ^ 2) := by ring
          _ ≤ chebErrorConst (N + 1) * (2 * ((2 * N + 3 : ℕ) : ℝ)
              * ((2 * N + 1 : ℕ) : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey hchpos.le
      exact le_of_mul_le_mul_right hchain hApos
    · have hN0 : N = 0 := by omega
      subst hN0
      norm_num [glErrorConst, chebErrorConst, Nat.factorial]

theorem quadratureComparisonEntry (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ)
    (hfN : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f)
    (hf2N : ContDiff ℝ ((2 * N : ℕ) : WithTop ℕ∞) f) :
    (∃ node weight : Fin N → ℝ,
      (∀ q, node q ∈ Set.Ioo (-1) 1) ∧ Function.Injective node ∧ (∀ q, 0 < weight q) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * N - 1 →
        (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ q, weight q * p.eval (node q)) ∧
      |(∫ x in (-1 : ℝ)..1, f x) - ∑ q, weight q * f (node q)| ≤
        glErrorConst N * (⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv (2 * N) f k|)) ∧
    |(∫ x in (-1 : ℝ)..1, f x) - chebQuadRule N f| ≤
      chebErrorConst N * (⨆ k ∈ Set.Icc (-1) 1, |iteratedDeriv N f k|) ∧
    glErrorConst N ≤ chebErrorConst N :=
  ⟨gaussLegendreUnitError N hN f hf2N, chebQuadErrorBound hN f hfN,
    glErrorConst_le_chebErrorConst N (by omega)⟩

theorem chebTruncChebQuadExact {N : ℕ} (hN : 0 < N) {K : ℕ} (hK : K < N) (c : ℕ → ℝ) :
    (∫ x in (-1 : ℝ)..1, (chebTrunc K c).eval x) = chebQuadRule N (chebTrunc K c).eval :=
  chebQuadExact hN _ ((chebTrunc_natDegree_le K c).trans_lt hK)

theorem chebTruncGLExact {Q : ℕ} (hQ : 0 < Q) {K : ℕ} (hK : K ≤ 2 * Q - 1) (c : ℕ → ℝ) :
    ∃ node weight : Fin Q → ℝ,
      (∀ q, node q ∈ Set.Ioo (-1) 1) ∧ Function.Injective node ∧ (∀ q, 0 < weight q) ∧
      (∫ x in (-1 : ℝ)..1, (chebTrunc K c).eval x)
        = ∑ q, weight q * (chebTrunc K c).eval (node q) := by
  obtain ⟨node, weight, hIoo, hinj, hwpos, hexact, _⟩ :=
    gauss_legendre_rule_exists Q (by omega)
  exact ⟨node, weight, hIoo, hinj, hwpos,
    hexact _ ((chebTrunc_natDegree_le K c).trans hK)⟩

theorem iSup_mem_le {s : Set ℝ} {u : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hpt : ∀ k ∈ s, u k ≤ C) : (⨆ k ∈ s, u k) ≤ C :=
  Real.iSup_le (fun k => Real.iSup_le (fun hk => hpt k hk) hC) hC

private theorem iteratedDeriv_comp_affine {N : ℕ} (f : ℝ → ℝ)
    (hf : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f) (c d : ℝ) (k : ℕ) (hk : k ≤ N) :
    ∀ t : ℝ, iteratedDeriv k (fun s => f (c * s + d)) t
      = c ^ k * iteratedDeriv k f (c * t + d) := by
  induction k with
  | zero => intro t; simp [iteratedDeriv_zero]
  | succ k ih =>
    intro t
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    have hfk : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f :=
      hf.of_le (by exact_mod_cast hk)
    have hgeq : iteratedDeriv k (fun s => f (c * s + d))
        = fun s : ℝ => c ^ k * iteratedDeriv k f (c * s + d) := funext fun s => ih hkN s
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hgeq]
    have hφ : HasDerivAt (fun s : ℝ => c * s + d) c t := by
      simpa using ((hasDerivAt_id t).const_mul c).add_const d
    have hF : DifferentiableAt ℝ (iteratedDeriv k f) (c * t + d) :=
      (hfk.differentiable_iteratedDeriv' k).differentiableAt
    have hd : HasDerivAt (fun s : ℝ => c ^ k * iteratedDeriv k f (c * s + d))
        (c ^ k * (deriv (iteratedDeriv k f) (c * t + d) * c)) t := by
      have h := ((hF.hasDerivAt).comp t hφ).const_mul (c ^ k)
      simpa only [Function.comp_def] using h
    rw [hd.deriv, pow_succ]
    ring

private theorem integral_partition_eq_sum (f : ℝ → ℝ) (hf : Continuous f) (δ : ℝ)
    (n : ℕ) :
    (∫ x in (-1 : ℝ)..(-1 : ℝ) + ((n : ℕ) : ℝ) * δ, f x)
      = ∑ i ∈ Finset.range n, ∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * δ..
          (-1 : ℝ) + ((i : ℕ) : ℝ) * δ + δ, f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hf.intervalIntegrable (-1 : ℝ) ((-1 : ℝ) + ((n : ℕ) : ℝ) * δ))
      (hf.intervalIntegrable ((-1 : ℝ) + ((n : ℕ) : ℝ) * δ)
        ((-1 : ℝ) + ((n : ℕ) : ℝ) * δ + δ))
    have hc : (-1 : ℝ) + ((n + 1 : ℕ) : ℝ) * δ
        = (-1 : ℝ) + ((n : ℕ) : ℝ) * δ + δ := by
      push_cast
      ring
    rw [hc, Finset.sum_range_succ, ← hsplit, ih]

noncomputable def chebCellQuad (N : ℕ) (f : ℝ → ℝ) (a h : ℝ) : ℝ :=
  ∑ j, (h / 2) * chebInterpWeight N j * f (a + h * (chebGaussNode N j + 1) / 2)

theorem chebCellQuadExact {N : ℕ} (hN : 0 < N) (a h : ℝ) (p : Polynomial ℝ)
    (hp : p.natDegree < N) :
    (∫ x in a..a + h, p.eval x) = chebCellQuad N p.eval a h := by
  let u : Polynomial ℝ := Polynomial.C (h / 2) * Polynomial.X + Polynomial.C (a + h / 2)
  have hu : u.natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact le_trans Polynomial.natDegree_mul_le (by simp)
    · simp
  have hc : (p.comp u).natDegree < N := by
    refine lt_of_le_of_lt ?_ hp
    calc (p.comp u).natDegree ≤ p.natDegree * u.natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hu
      _ = p.natDegree := Nat.mul_one _
  have he := chebQuadExact hN (p.comp u) hc
  simp only [Polynomial.eval_comp, u, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at he
  have ht := intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    p.eval (h / 2) (a + h / 2)
  simp only [smul_eq_mul] at ht
  rw [show h / 2 * (-1 : ℝ) + (a + h / 2) = a from by ring,
    show h / 2 * (1 : ℝ) + (a + h / 2) = a + h from by ring] at ht
  rw [← ht, he]
  simp only [chebQuadRule]
  rw [Finset.mul_sum]
  simp only [chebCellQuad]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show a + h * (chebGaussNode N j + 1) / 2
      = h / 2 * chebGaussNode N j + (a + h / 2) from by ring]
  ring

theorem chebCellQuadErrorBound {N : ℕ} (hN : 0 < N) (a h : ℝ) (hpos : 0 < h)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f) :
    |(∫ x in a..a + h, f x) - chebCellQuad N f a h| ≤
      chebErrorConst N * (h / 2) ^ (N + 1) *
        (⨆ k ∈ Set.Icc a (a + h), |iteratedDeriv N f k|) := by
  have hhp : 0 ≤ h / 2 := by positivity
  have htr := intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    f (h / 2) (a + h / 2)
  simp only [smul_eq_mul] at htr
  rw [show h / 2 * (-1 : ℝ) + (a + h / 2) = a from by ring,
    show h / 2 * (1 : ℝ) + (a + h / 2) = a + h from by ring] at htr
  have hrule : chebCellQuad N f a h = (h / 2) * chebQuadRule N
      (fun t => f (h / 2 * t + (a + h / 2))) := by
    simp only [chebCellQuad, chebQuadRule]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a + h * (chebGaussNode N j + 1) / 2
        = h / 2 * chebGaussNode N j + (a + h / 2) from by ring]
    ring
  have hgcd : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞)
      (fun t => f (h / 2 * t + (a + h / 2))) :=
    hf.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hub := chebQuadErrorBound hN (fun t => f (h / 2 * t + (a + h / 2))) hgcd
  have hcontN : Continuous (fun k => iteratedDeriv N f k) :=
    hf.continuous_iteratedDeriv N (by exact_mod_cast le_refl N)
  have hbddimg : BddAbove ((fun k => |iteratedDeriv N f k|) '' Set.Icc a (a + h)) :=
    isCompact_Icc.bddAbove_image hcontN.abs.continuousOn
  have htrange : (⋃ i, Set.range (fun _ : i ∈ Set.Icc a (a + h) =>
      |iteratedDeriv N f i|)) ⊆ (fun k => |iteratedDeriv N f k|) '' Set.Icc a (a + h) := by
    intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hi⟩ := hy
    rw [Set.mem_range] at hi
    obtain ⟨x, hx⟩ := hi
    exact ⟨i, x, hx⟩
  have hbdd := hbddimg.mono htrange
  have hsup : (⨆ t ∈ Set.Icc (-1 : ℝ) 1,
      |iteratedDeriv N (fun s => f (h / 2 * s + (a + h / 2))) t|)
      ≤ (h / 2) ^ N * (⨆ k ∈ Set.Icc a (a + h), |iteratedDeriv N f k|) := by
    refine iSup_mem_le (mul_nonneg (pow_nonneg hhp N)
      (iterSup_nonneg (by linarith) f hf)) fun t ht => ?_
    rw [iteratedDeriv_comp_affine f hf (h / 2) (a + h / 2) N (le_refl N) t,
      abs_mul, abs_of_nonneg (pow_nonneg hhp N)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hhp N)
    obtain ⟨ht1, ht2⟩ := ht
    have hlo : a ≤ h / 2 * t + (a + h / 2) := by
      have hp1 : h / 2 * (-1 : ℝ) ≤ h / 2 * t :=
        mul_le_mul_of_nonneg_left ht1 hhp
      linarith
    have hhi : h / 2 * t + (a + h / 2) ≤ a + h := by
      have hp2 : h / 2 * t ≤ h / 2 * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left ht2 hhp
      have hp3 : h / 2 * (1 : ℝ) = h / 2 := by ring
      linarith
    exact le_ciSup₂ (f := fun k (_ : k ∈ Set.Icc a (a + h)) => |iteratedDeriv N f k|)
      hbdd (h / 2 * t + (a + h / 2)) ⟨hlo, hhi⟩
  calc |(∫ x in a..a + h, f x) - chebCellQuad N f a h|
      = (h / 2) * |(∫ t in (-1 : ℝ)..1, f (h / 2 * t + (a + h / 2)))
          - chebQuadRule N (fun t => f (h / 2 * t + (a + h / 2)))| := by
        rw [hrule, ← htr, ← mul_sub, abs_mul, abs_of_nonneg hhp]
    _ ≤ (h / 2) * (chebErrorConst N *
        (⨆ t ∈ Set.Icc (-1 : ℝ) 1,
          |iteratedDeriv N (fun s => f (h / 2 * s + (a + h / 2))) t|)) :=
        mul_le_mul_of_nonneg_left hub hhp
    _ ≤ (h / 2) * (chebErrorConst N * ((h / 2) ^ N *
        (⨆ k ∈ Set.Icc a (a + h), |iteratedDeriv N f k|))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsup (chebErrorConst_pos N).le) hhp
    _ = chebErrorConst N * (h / 2) ^ (N + 1) *
        (⨆ k ∈ Set.Icc a (a + h), |iteratedDeriv N f k|) := by
        rw [pow_succ]
        ring

noncomputable def chebCompositeQuad (N M : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, chebCellQuad N f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
    (2 / ((M : ℕ) : ℝ))

theorem compositeQuadNodeCount (N M : ℕ) :
    (∑ _i : Fin M, ∑ _j : Fin N, (1 : ℝ)) = ((M * N : ℕ) : ℝ) := by
  simp

theorem chebCompositeQuadExact {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (p : Polynomial ℝ) (hp : p.natDegree < N) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = chebCompositeQuad N M p.eval := by
  have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := Nat.cast_pos.mpr hM
  have hMne : ((M : ℕ) : ℝ) ≠ 0 := ne_of_gt hMpos
  have hpart := integral_partition_eq_sum p.eval
    (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval p) (2 / ((M : ℕ) : ℝ)) M
  rw [show (-1 : ℝ) + ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 1 from by
      rw [show ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 2 from by field_simp]; ring] at hpart
  rw [hpart, chebCompositeQuad]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact chebCellQuadExact hN _ _ p hp

theorem chebCompositeQuadErrorBound {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f) :
    |(∫ x in (-1 : ℝ)..1, f x) - chebCompositeQuad N M f| ≤
      (chebErrorConst N / ((M : ℕ) : ℝ) ^ N) *
        (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|) := by
  have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := Nat.cast_pos.mpr hM
  have hMne : ((M : ℕ) : ℝ) ≠ 0 := ne_of_gt hMpos
  have hcontN : Continuous (fun k => iteratedDeriv N f k) :=
    hf.continuous_iteratedDeriv N (by exact_mod_cast le_refl N)
  have hbddimg : BddAbove ((fun k => |iteratedDeriv N f k|) '' Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hcontN.abs.continuousOn
  have htrange : (⋃ i, Set.range (fun _ : i ∈ Set.Icc (-1 : ℝ) 1 =>
      |iteratedDeriv N f i|)) ⊆ (fun k => |iteratedDeriv N f k|) '' Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hi⟩ := hy
    rw [Set.mem_range] at hi
    obtain ⟨x, hx⟩ := hi
    exact ⟨i, x, hx⟩
  have hbdd := hbddimg.mono htrange
  have hsupglob : ∀ i : ℕ, i + 1 ≤ M →
      (⨆ k ∈ Set.Icc (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
          (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ)),
        |iteratedDeriv N f k|)
        ≤ (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|) := by
    intro i hi
    have hile : (((i : ℕ) : ℝ) + 1) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hi
    have hfrac : (2 * (((i : ℕ) : ℝ) + 1)) / ((M : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hMpos]
      linarith
    have hX : (0 : ℝ) ≤ ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) hMpos.le)
    refine iSup_mem_le (iterSup_nonneg (by norm_num) f hf) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := hk
    have hconv : (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ)
        = -1 + (2 * (((i : ℕ) : ℝ) + 1)) / ((M : ℕ) : ℝ) := by
      rw [mul_div_assoc]
      ring
    rw [hconv] at hk2
    exact le_ciSup₂ (f := fun k (_ : k ∈ Set.Icc (-1 : ℝ) 1) => |iteratedDeriv N f k|)
      hbdd k ⟨by linarith, by linarith⟩
  have hpart := integral_partition_eq_sum f hf.continuous (2 / ((M : ℕ) : ℝ)) M
  rw [show (-1 : ℝ) + ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 1 from by
      rw [show ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 2 from by field_simp]; ring] at hpart
  have hcell : ∀ i ∈ Finset.range M,
      |(∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
          (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
        - chebCellQuad N f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
          (2 / ((M : ℕ) : ℝ))|
        ≤ chebErrorConst N * (1 / ((M : ℕ) : ℝ)) ^ (N + 1)
          * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|) := by
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hb := chebCellQuadErrorBound hN (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
      (2 / ((M : ℕ) : ℝ)) (by positivity) f hf
    rw [show (2 / ((M : ℕ) : ℝ)) / 2 = 1 / ((M : ℕ) : ℝ) from by ring] at hb
    refine hb.trans ?_
    refine mul_le_mul_of_nonneg_left (hsupglob i (by omega)) ?_
    exact mul_nonneg (chebErrorConst_pos N).le
      (pow_nonneg (div_nonneg (by norm_num) hMpos.le) _)
  have hkey : ((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) ^ (N + 1)
      = 1 / ((M : ℕ) : ℝ) ^ N := by
    have h1 : (1 / ((M : ℕ) : ℝ)) ^ (N + 1)
        = (1 / ((M : ℕ) : ℝ)) ^ N * (1 / ((M : ℕ) : ℝ)) := pow_succ _ N
    have h2 : ((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) = 1 := by field_simp
    have h3 : (1 / ((M : ℕ) : ℝ)) ^ N = 1 / ((M : ℕ) : ℝ) ^ N := by
      rw [div_pow, one_pow]
    have hre : ((M : ℕ) : ℝ) * ((1 / ((M : ℕ) : ℝ)) ^ N * (1 / ((M : ℕ) : ℝ)))
        = ((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) * (1 / ((M : ℕ) : ℝ)) ^ N := by
      ring
    rw [h1, hre, h2, one_mul, h3]
  calc |(∫ x in (-1 : ℝ)..1, f x) - chebCompositeQuad N M f|
      = |∑ i ∈ Finset.range M,
          ((∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
              (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
            - chebCellQuad N f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
              (2 / ((M : ℕ) : ℝ)))| := by
        rw [chebCompositeQuad, hpart, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range M,
          |(∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
              (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
            - chebCellQuad N f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
              (2 / ((M : ℕ) : ℝ))| := by
        exact Finset.abs_sum_le_sum_abs (fun i : ℕ =>
          (∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
            (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
          - chebCellQuad N f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
            (2 / ((M : ℕ) : ℝ))) (Finset.range M)
    _ ≤ ∑ i ∈ Finset.range M, chebErrorConst N * (1 / ((M : ℕ) : ℝ)) ^ (N + 1)
          * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|) :=
        Finset.sum_le_sum hcell
    _ = chebErrorConst N / ((M : ℕ) : ℝ) ^ N *
        (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hL : ((M : ℕ) : ℝ) * (chebErrorConst N * (1 / ((M : ℕ) : ℝ)) ^ (N + 1)
            * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|))
            = (((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) ^ (N + 1)) * (chebErrorConst N
              * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|)) := by
          ring
        rw [hL, hkey, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]

noncomputable def glCompositeQuad (Q M : ℕ) (node weight : Fin Q → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, ∑ q, (1 / ((M : ℕ) : ℝ)) * weight q
    * f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))
      + (2 / ((M : ℕ) : ℝ)) * (node q + 1) / 2)

theorem glCompositeQuadExact (Q M : ℕ) (hM : 0 < M) {node weight : Fin Q → ℝ}
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ q, weight q * p.eval (node q))
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 2 * Q - 1) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = glCompositeQuad Q M node weight p.eval := by
  have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := Nat.cast_pos.mpr hM
  have hMne : ((M : ℕ) : ℝ) ≠ 0 := ne_of_gt hMpos
  have hpart := integral_partition_eq_sum p.eval
    (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval p) (2 / ((M : ℕ) : ℝ)) M
  rw [show (-1 : ℝ) + ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 1 from by
      rw [show ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 2 from by field_simp]; ring] at hpart
  rw [hpart, glCompositeQuad]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gauss_cell_rule_affine_exact Q (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
    (2 / ((M : ℕ) : ℝ)) node weight hexact p hp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [show (2 / ((M : ℕ) : ℝ)) / 2 = 1 / ((M : ℕ) : ℝ) from by ring]

private theorem gl_cell_const_eq (Q : ℕ) (h : ℝ) :
    (((Q.factorial : ℕ) : ℝ) ^ 4 * h ^ ((2 : ℝ) * Q + 1))
        / ((((2 * Q + 1 : ℕ) : ℝ)) * ((((2 * Q).factorial : ℕ) : ℝ) ^ 3))
      = glErrorConst Q * (h / 2) ^ (2 * Q + 1) := by
  have hexp : ((2 : ℝ) * Q + 1) = ((2 * Q + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_natCast, div_pow]
  unfold glErrorConst
  field_simp

theorem glErrorConst_pos (Q : ℕ) : 0 < glErrorConst Q := by
  unfold glErrorConst
  positivity

theorem glCompositeQuadErrorBound (Q M : ℕ) (hQ : 0 < Q) (hM : 0 < M)
    (node weight : Fin Q → ℝ)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ q, weight q * p.eval (node q))
    (homega : (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2)
      = ((2 : ℝ) ^ (2 * Q + 1) * ((Q.factorial : ℕ) : ℝ) ^ 4)
        / ((((2 * Q + 1 : ℕ) : ℝ)) * ((((2 * Q).factorial : ℕ) : ℝ) ^ 2)))
    (f : ℝ → ℝ) (hf : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) f) :
    |(∫ x in (-1 : ℝ)..1, f x) - glCompositeQuad Q M node weight f| ≤
      (glErrorConst Q / ((M : ℕ) : ℝ) ^ (2 * Q))
        * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|) := by
  have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := Nat.cast_pos.mpr hM
  have hMne : ((M : ℕ) : ℝ) ≠ 0 := ne_of_gt hMpos
  have hcontN : Continuous (fun k => iteratedDeriv (2 * Q) f k) :=
    hf.continuous_iteratedDeriv (2 * Q) (by exact_mod_cast le_refl (2 * Q))
  have hbddimg : BddAbove ((fun k => |iteratedDeriv (2 * Q) f k|) '' Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hcontN.abs.continuousOn
  have htrange : (⋃ i, Set.range (fun _ : i ∈ Set.Icc (-1 : ℝ) 1 =>
      |iteratedDeriv (2 * Q) f i|)) ⊆ (fun k => |iteratedDeriv (2 * Q) f k|) ''
      Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, hi⟩ := hy
    rw [Set.mem_range] at hi
    obtain ⟨x, hx⟩ := hi
    exact ⟨i, x, hx⟩
  have hbdd := hbddimg.mono htrange
  have hsupglob : ∀ i : ℕ, i + 1 ≤ M →
      (⨆ k ∈ Set.Icc (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)))
          (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ)),
        |iteratedDeriv (2 * Q) f k|)
        ≤ (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|) := by
    intro i hi
    have hile : (((i : ℕ) : ℝ) + 1) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hi
    have hfrac : (2 * (((i : ℕ) : ℝ) + 1)) / ((M : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hMpos]
      linarith
    have hX : (0 : ℝ) ≤ ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) hMpos.le)
    refine iSup_mem_le (iterSup_nonneg (by norm_num) f hf) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := hk
    have hconv : (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ)
        = -1 + (2 * (((i : ℕ) : ℝ) + 1)) / ((M : ℕ) : ℝ) := by
      rw [mul_div_assoc]
      ring
    rw [hconv] at hk2
    exact le_ciSup₂ (f := fun k (_ : k ∈ Set.Icc (-1 : ℝ) 1) =>
        |iteratedDeriv (2 * Q) f k|) hbdd k ⟨by linarith, by linarith⟩
  have hpart := integral_partition_eq_sum f hf.continuous (2 / ((M : ℕ) : ℝ)) M
  rw [show (-1 : ℝ) + ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 1 from by
      rw [show ((M : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) = 2 from by field_simp]; ring] at hpart
  have hcell : ∀ i ∈ Finset.range M,
      |(∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
          (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
        - ∑ q, (1 / ((M : ℕ) : ℝ)) * weight q
          * f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))
            + (2 / ((M : ℕ) : ℝ)) * (node q + 1) / 2)|
        ≤ glErrorConst Q * (1 / ((M : ℕ) : ℝ)) ^ (2 * Q + 1)
          * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|) := by
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hce := gauss_cell_rule_affine_exact Q
      (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))) (2 / ((M : ℕ) : ℝ)) node weight hexact
    have homunit := gauss_cell_omega Q
      (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))) (2 / ((M : ℕ) : ℝ)) node
      (by positivity) homega
    have hb := gauss_legendre_cell_error_bound Q
      (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))) (2 / ((M : ℕ) : ℝ)) node weight f
      (by omega) (by positivity) (fun p hp => hce p hp) homunit hf
    rw [gl_cell_const_eq] at hb
    rw [show (2 / ((M : ℕ) : ℝ)) / 2 = 1 / ((M : ℕ) : ℝ) from by ring] at hb
    refine hb.trans ?_
    refine mul_le_mul_of_nonneg_left (hsupglob i (by omega)) ?_
    exact mul_nonneg (glErrorConst_pos Q).le
      (pow_nonneg (div_nonneg (by norm_num) hMpos.le) _)
  have hkey : ((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) ^ (2 * Q + 1)
      = 1 / ((M : ℕ) : ℝ) ^ (2 * Q) := by
    have h1 : (1 / ((M : ℕ) : ℝ)) ^ (2 * Q + 1)
        = (1 / ((M : ℕ) : ℝ)) ^ (2 * Q) * (1 / ((M : ℕ) : ℝ)) := pow_succ _ (2 * Q)
    have h2 : ((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) = 1 := by field_simp
    have h3 : (1 / ((M : ℕ) : ℝ)) ^ (2 * Q) = 1 / ((M : ℕ) : ℝ) ^ (2 * Q) := by
      rw [div_pow, one_pow]
    have hre : ((M : ℕ) : ℝ) * ((1 / ((M : ℕ) : ℝ)) ^ (2 * Q) * (1 / ((M : ℕ) : ℝ)))
        = ((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) * (1 / ((M : ℕ) : ℝ)) ^ (2 * Q) := by
      ring
    rw [h1, hre, h2, one_mul, h3]
  calc |(∫ x in (-1 : ℝ)..1, f x) - glCompositeQuad Q M node weight f|
      = |∑ i ∈ Finset.range M,
          ((∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
              (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
            - ∑ q, (1 / ((M : ℕ) : ℝ)) * weight q
              * f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))
                + (2 / ((M : ℕ) : ℝ)) * (node q + 1) / 2))| := by
        rw [glCompositeQuad, hpart, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range M,
          |(∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
              (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
            - ∑ q, (1 / ((M : ℕ) : ℝ)) * weight q
              * f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))
                + (2 / ((M : ℕ) : ℝ)) * (node q + 1) / 2)| := by
        exact Finset.abs_sum_le_sum_abs (fun i : ℕ =>
          (∫ x in (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))..
            (-1 : ℝ) + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ)) + 2 / ((M : ℕ) : ℝ), f x)
          - ∑ q, (1 / ((M : ℕ) : ℝ)) * weight q
            * f (-1 + ((i : ℕ) : ℝ) * (2 / ((M : ℕ) : ℝ))
              + (2 / ((M : ℕ) : ℝ)) * (node q + 1) / 2)) (Finset.range M)
    _ ≤ ∑ i ∈ Finset.range M, glErrorConst Q * (1 / ((M : ℕ) : ℝ)) ^ (2 * Q + 1)
          * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|) :=
        Finset.sum_le_sum hcell
    _ = glErrorConst Q / ((M : ℕ) : ℝ) ^ (2 * Q)
        * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hL : ((M : ℕ) : ℝ) * (glErrorConst Q * (1 / ((M : ℕ) : ℝ)) ^ (2 * Q + 1)
            * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|))
            = (((M : ℕ) : ℝ) * (1 / ((M : ℕ) : ℝ)) ^ (2 * Q + 1)) * (glErrorConst Q
              * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * Q) f k|)) := by
          ring
        rw [hL, hkey, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]

theorem glCompositeErrorConst_le_chebCompositeErrorConst (N M : ℕ) (hN : 1 ≤ N)
    (hM : 1 ≤ M) :
    glErrorConst N / ((M : ℕ) : ℝ) ^ (2 * N)
      ≤ chebErrorConst N / ((M : ℕ) : ℝ) ^ N := by
  have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos : (0 : ℝ) < ((M : ℕ) : ℝ) ^ N := pow_pos hMpos N
  have hpos2 : (0 : ℝ) < ((M : ℕ) : ℝ) ^ (2 * N) := pow_pos hMpos (2 * N)
  have hMpown : ((M : ℕ) : ℝ) ^ N ≤ ((M : ℕ) : ℝ) ^ (2 * N) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < M) (by omega : N ≤ 2 * N)
  rw [div_le_div_iff₀ hpos2 hpos]
  calc glErrorConst N * ((M : ℕ) : ℝ) ^ N
      ≤ chebErrorConst N * ((M : ℕ) : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (glErrorConst_le_chebErrorConst N hN) hpos.le
    _ ≤ chebErrorConst N * ((M : ℕ) : ℝ) ^ (2 * N) :=
        mul_le_mul_of_nonneg_left hMpown (chebErrorConst_pos N).le

theorem quadratureCompositeComparisonEntry (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (f : ℝ → ℝ)
    (hfN : ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) f)
    (hf2N : ContDiff ℝ ((2 * N : ℕ) : WithTop ℕ∞) f) :
    (∃ node weight : Fin N → ℝ,
      (∀ q, node q ∈ Set.Ioo (-1) 1) ∧ Function.Injective node ∧ (∀ q, 0 < weight q) ∧
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * N - 1 →
        (∫ x in (-1 : ℝ)..1, p.eval x) = glCompositeQuad N M node weight p.eval) ∧
      |(∫ x in (-1 : ℝ)..1, f x) - glCompositeQuad N M node weight f| ≤
        (glErrorConst N / ((M : ℕ) : ℝ) ^ (2 * N))
          * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * N) f k|)) ∧
    |(∫ x in (-1 : ℝ)..1, f x) - chebCompositeQuad N M f| ≤
      (chebErrorConst N / ((M : ℕ) : ℝ) ^ N)
        * (⨆ k ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv N f k|) ∧
    glErrorConst N / ((M : ℕ) : ℝ) ^ (2 * N) ≤ chebErrorConst N / ((M : ℕ) : ℝ) ^ N ∧
    (∑ _i : Fin M, ∑ _j : Fin N, (1 : ℝ)) = ((M * N : ℕ) : ℝ) := by
  obtain ⟨node, weight, hIoo, hinj, hwpos, hexact, homega⟩ :=
    gauss_legendre_rule_exists N (by omega)
  exact ⟨⟨node, weight, hIoo, hinj, hwpos,
    fun p hp => glCompositeQuadExact N M hM hexact p hp,
    glCompositeQuadErrorBound N M hN hM node weight hexact homega f hf2N⟩,
    chebCompositeQuadErrorBound hN hM f hfN,
    glCompositeErrorConst_le_chebCompositeErrorConst N M (by omega) (by omega),
    compositeQuadNodeCount N M⟩

private theorem query_lower_translate {q d C num : ℝ}
    (hq : max 0 num / d ≤ q) (hd : 0 < d) (hC : 0 < C) (hdc : d ≤ C) :
    num / C ≤ q := by
  rcases le_total 0 num with hnum | hnum
  · have hq' : num / d ≤ q := by rwa [max_eq_right hnum] at hq
    exact ((div_le_div_iff₀ hC hd).mpr (mul_le_mul_of_nonneg_left hdc hnum)).trans hq'
  · have hq0 : 0 ≤ q := le_trans (div_nonneg (le_max_left 0 num) hd.le) hq
    have hnc : num / C ≤ 0 := (div_le_iff₀ hC).mpr (by rw [zero_mul]; exact hnum)
    linarith

theorem uniformErrorQueryLowerBound : ∀ (W I : Type) [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
    (x y a b eps η m : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps → 0 ≤ η →
    |x - y| ≤ η →
    ‖(a : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
    ‖(b : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
    ((adjointQueryCount word : ℝ) ≥ (|a - b| - 2 * eps) / Real.sqrt (2 * η)) ∧
    (0 ≤ m → m < 1 → |x| ≤ m → |y| ≤ m →
      (adjointQueryCount word : ℝ) ≥
        Real.sqrt (1 - m ^ 2) * (|a - b| - 2 * eps) / η) := by
  intro W I _ _ _ _ _ L R word x y a b eps η m
    hL hR hw hx hy hxy heps hη hηle ha hb
  have hxypos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hηpos : 0 < η := lt_of_lt_of_le hxypos hηle
  have hfrozen := scalar_signal_actual_response_query_lower_bound W I L R word x y a b eps
    hL hR hw hx hy hxy heps ha hb
  have hdpos : 0 < scalarSignalDistance x y :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.1 hxy
  refine ⟨query_lower_translate hfrozen.1 hdpos (Real.sqrt_pos.mpr (by linarith))
    (scalarSignalDistance_le_sqrt_two_mul_of_abs_le x y η hx hy hη hηle), ?_⟩
  intro hm hm1 hxm hym
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith
  have hspos : 0 < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  have hdwm : scalarSignalDistance x y ≤ |x - y| / Real.sqrt (1 - m ^ 2) :=
    scalarSignalDistance_le_abs_div_window m x y hm hm1 hxm hym
  have hdle2 : scalarSignalDistance x y ≤ η / Real.sqrt (1 - m ^ 2) :=
    hdwm.trans ((div_le_div_iff₀ hspos hspos).mpr
      (mul_le_mul_of_nonneg_right hηle (Real.sqrt_nonneg _)))
  have hW := query_lower_translate hfrozen.1 hdpos (div_pos hηpos hspos) hdle2
  have hconv : (|a - b| - 2 * eps) / (η / Real.sqrt (1 - m ^ 2))
      = Real.sqrt (1 - m ^ 2) * (|a - b| - 2 * eps) / η := by
    rw [div_div_eq_mul_div]
    ring
  rwa [hconv] at hW

noncomputable def leakageNumerator (a b eps : ℝ) : ℝ :=
  max (max 0 (|a - b| - 2 * eps))
    (Real.sqrt (1 - (b + eps) ^ 2) - Real.sqrt (1 - (a - eps) ^ 2))

theorem leakageNumerator_nonneg (a b eps : ℝ) : 0 ≤ leakageNumerator a b eps :=
  le_trans (le_max_left 0 (|a - b| - 2 * eps)) (le_max_left _ _)

theorem leakageNumerator_ge_response (a b eps : ℝ) :
    max 0 (|a - b| - 2 * eps) ≤ leakageNumerator a b eps :=
  le_max_left _ _

theorem uniformLeakageQueryLowerBound : ∀ (W I : Type) [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (L R : Matrix (Bool × W) I ℂ) (word : List (AdjointStep (Bool × W)))
    (x y a b eps η m : ℝ),
    IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
    x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x ≠ y → 0 ≤ eps → eps ≤ a → a ≤ 1 →
    0 ≤ b → b + eps ≤ 1 → 0 ≤ η → |x - y| ≤ η →
    ‖(a : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W x) word) R‖ ≤ eps →
    ‖(b : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W y) word) R‖ ≤ eps →
    ((adjointQueryCount word : ℝ) ≥ leakageNumerator a b eps / Real.sqrt (2 * η)) ∧
    (0 ≤ m → m < 1 → |x| ≤ m → |y| ≤ m →
      (adjointQueryCount word : ℝ) ≥
        Real.sqrt (1 - m ^ 2) * leakageNumerator a b eps / η) := by
  intro W I _ _ _ _ _ L R word x y a b eps η m
    hL hR hw hx hy hxy heps haeps ha1 hb0 hbeps hη hηle ha hb
  have hxypos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hηpos : 0 < η := lt_of_lt_of_le hxypos hηle
  have hdpos : 0 < scalarSignalDistance x y :=
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.1 hxy
  have hfrozen : leakageNumerator a b eps / scalarSignalDistance x y ≤
      (adjointQueryCount word : ℝ) :=
    scalar_signal_safe_leakage_query_lower_bound_corrected W I L R word x y a b eps
      hL hR hw hx hy hxy heps haeps ha1 hb0 hbeps ha hb
  have hfrozen' : max 0 (leakageNumerator a b eps) / scalarSignalDistance x y ≤
      (adjointQueryCount word : ℝ) := by
    rw [max_eq_right (leakageNumerator_nonneg a b eps)]
    exact hfrozen
  refine ⟨query_lower_translate hfrozen' hdpos (Real.sqrt_pos.mpr (by linarith))
    (scalarSignalDistance_le_sqrt_two_mul_of_abs_le x y η hx hy hη hηle), ?_⟩
  intro hm hm1 hxm hym
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith
  have hspos : 0 < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  have hdwm : scalarSignalDistance x y ≤ |x - y| / Real.sqrt (1 - m ^ 2) :=
    scalarSignalDistance_le_abs_div_window m x y hm hm1 hxm hym
  have hdle2 : scalarSignalDistance x y ≤ η / Real.sqrt (1 - m ^ 2) :=
    hdwm.trans ((div_le_div_iff₀ hspos hspos).mpr
      (mul_le_mul_of_nonneg_right hηle (Real.sqrt_nonneg _)))
  have hW := query_lower_translate hfrozen' hdpos (div_pos hηpos hspos) hdle2
  have hconv : leakageNumerator a b eps / (η / Real.sqrt (1 - m ^ 2))
      = Real.sqrt (1 - m ^ 2) * leakageNumerator a b eps / η := by
    rw [div_div_eq_mul_div]
    ring
  rwa [hconv] at hW

noncomputable def wordResponse (n : ℕ) (q : Polynomial ℝ) (t : ℝ) : ℂ :=
  (evaluate (scalarSignalLift Unit (q.eval t)) (signalChebyshevUnitWord n))
    (false, ()) (false, ())

theorem wordResponse_eq (n : ℕ) (q : Polynomial ℝ) {t : ℝ}
    (ht : q.eval t ∈ Set.Icc (-1) 1) :
    wordResponse n q t =
      Complex.ofReal ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (q.eval t)) := by
  have hc := scalar_signal_chebyshev_actual_word n (q.eval t) ht
  rw [wordResponse, hc.2.2.2.2.2, tensorGate_apply, Matrix.one_apply_eq, mul_one,
    hc.2.2.2.2.1]

theorem chebT_comp_chebTrunc_natDegree_le (n K : ℕ) (c : ℕ → ℝ) :
    ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).natDegree ≤ n * K := by
  rw [Polynomial.natDegree_comp, chebT_natDegree_eq]
  exact Nat.mul_le_mul_left _ (chebTrunc_natDegree_le K c)

theorem wordResponseQuadratureChain (n K N : ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ) (δ : ℝ)
    (hNK : n * K < N) (hδ : 0 ≤ δ)
    (hq1 : ∀ t ∈ Set.Icc (-1) 1, (chebTrunc K c).eval t ∈ Set.Icc (-1) 1)
    (hf1 : ∀ t ∈ Set.Icc (-1) 1, f t ∈ Set.Icc (-1) 1)
    (huni : ∀ t ∈ Set.Icc (-1) 1, |f t - (chebTrunc K c).eval t| ≤ δ)
    (hfc : ContinuousOn f (Set.Icc (-1) 1)) :
    |(∫ t in (-1)..1, (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t)) -
        chebQuadRule N (fun t => (wordResponse n (chebTrunc K c) t).re)| ≤
      2 * (n : ℝ) * Real.sqrt (2 * δ) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le (n * K)) hNK
  have hnodeeq : ∀ j : Fin N,
      (wordResponse n (chebTrunc K c) (chebGaussNode N j)).re =
        ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval
          (chebGaussNode N j) := by
    intro j
    rw [wordResponse_eq n _ (hq1 _ (chebGaussNode_mem_Icc hN j)),
      Complex.ofReal_re, Polynomial.eval_comp]
  have hrule : chebQuadRule N (fun t => (wordResponse n (chebTrunc K c) t).re)
      = ∫ t in (-1)..1,
          ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t := by
    rw [chebQuadExact hN _ ((chebT_comp_chebTrunc_natDegree_le n K c).trans_lt hNK)]
    simp only [chebQuadRule]
    exact Finset.sum_congr rfl fun j _ => by rw [hnodeeq j]
  have hcontT : Continuous (fun t : ℝ =>
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval t) :=
    Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval _
  have hcontP : Continuous (fun t : ℝ =>
      ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t) :=
    Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval _
  have huIcc : Set.uIcc (-1 : ℝ) 1 = Set.Icc (-1) 1 := by simp
  have hcontf : ContinuousOn (fun t =>
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t)) (Set.uIcc (-1 : ℝ) 1) := by
    rw [huIcc]
    exact hcontT.comp_continuousOn hfc
  have hIntT : IntervalIntegrable (fun t =>
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t)) MeasureTheory.volume (-1) 1 :=
    hcontf.intervalIntegrable
  have hIntP : IntervalIntegrable (fun t =>
      ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t)
      MeasureTheory.volume (-1) 1 := hcontP.intervalIntegrable (-1) 1
  have hIntAbs : IntervalIntegrable (fun t =>
      |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t) -
        ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t|)
      MeasureTheory.volume (-1) 1 :=
    (hcontf.sub hcontP.continuousOn).abs.intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (-1) 1,
      |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t) -
        ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t| ≤
        (n : ℝ) * Real.sqrt (2 * δ) := by
    intro t ht
    have h := (chebyshev_word_output_transport n (f t) ((chebTrunc K c).eval t) δ
      (hf1 t ht) (hq1 t ht) hδ (huni t ht)).2.2
    rwa [← Polynomial.eval_comp] at h
  calc
    |(∫ t in (-1)..1, (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t)) -
        chebQuadRule N (fun t => (wordResponse n (chebTrunc K c) t).re)|
        = |∫ t in (-1)..1,
            (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t) -
              ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t| := by
          rw [hrule, ← intervalIntegral.integral_sub hIntT hIntP]
    _ ≤ ∫ t in (-1)..1,
          |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t) -
            ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).comp (chebTrunc K c)).eval t| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (-1)..1, (n : ℝ) * Real.sqrt (2 * δ) :=
        intervalIntegral.integral_mono_on (by norm_num) hIntAbs
          (continuous_const.intervalIntegrable (-1) 1) (fun z hz => hpt z hz)
    _ = 2 * (n : ℝ) * Real.sqrt (2 * δ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add]
        norm_num
        ring

theorem pow_le_of_log_ge {t r : ℝ} (k : ℕ) (ht : 0 < t) (hr0 : 0 < r)
    (h : Real.log (1 / t) ≤ (k : ℝ) * Real.log (1 / r)) : r ^ k ≤ t := by
  have hp : 0 < r ^ k := pow_pos hr0 k
  refine (Real.log_le_log_iff hp ht).mp ?_
  have hlt : Real.log t = -Real.log (1 / t) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hlr : Real.log r = -Real.log (1 / r) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [Real.log_pow, hlr, hlt]
  linarith

theorem recipChebTruncQueryUpperBound (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (δ m ε : ℝ) (n : ℕ)
    (hw : WellFormedAdjointCircuit word) (hδ : (0 : ℝ) < δ) (hδ1 : δ < 1)
    (hm : (1 : ℝ) / 2 ≤ m) (hm1 : m < 1) (hε : (0 : ℝ) < ε)
    (hQ : (0 : ℝ) < (adjointQueryCount word : ℝ))
    (hn : Real.log ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ) /
        (2 * ε * Real.sqrt (1 - m ^ 2))) ≤
      ((n + 1 : ℕ) : ℝ) * Real.log ((1 + Real.sqrt δ) / (1 - Real.sqrt δ))) :
    ∀ t ∈ Set.Icc (-1) 1,
      ‖evaluate (scalarSignalLift W ((δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t)) word -
          evaluate (scalarSignalLift W (δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)))) word‖ ≤ ε := by
  have hrb := recipChebRatio_bounds δ hδ (le_of_lt hδ1)
  have hs1 : Real.sqrt δ < 1 := by
    have hs := Real.sqrt_lt_sqrt hδ.le hδ1
    rwa [Real.sqrt_one] at hs
  have hne : (1 : ℝ) - Real.sqrt δ ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm (ne_of_lt hs1))
  have hm2 : (0 : ℝ) < 1 - m ^ 2 := by nlinarith
  have hsm : (0 : ℝ) < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  have hrinv : (1 : ℝ) / recipChebRatio δ = (1 + Real.sqrt δ) / (1 - Real.sqrt δ) := by
    unfold recipChebRatio
    field_simp
  have hinv : (1 : ℝ) / (2 * ε * Real.sqrt (1 - m ^ 2) /
      ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ))) =
      (adjointQueryCount word : ℝ) * (1 + Real.sqrt δ) /
        (2 * ε * Real.sqrt (1 - m ^ 2)) := by
    field_simp
  have hpow : recipChebRatio δ ^ (n + 1) ≤
      2 * ε * Real.sqrt (1 - m ^ 2) /
        ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ)) := by
    refine pow_le_of_log_ge (n + 1) (by positivity) ?hr0 (by rwa [hinv, hrinv])
    unfold recipChebRatio
    exact div_pos (by linarith) (by positivity)
  intro t ht
  have hbound := (recipChebTruncWordTransport W word δ n m hw hδ (le_of_lt hδ1) hm hm1).1 t ht
  refine hbound.trans ?_
  have hinner : (1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1) ≤
      (1 + Real.sqrt δ) * (2 * ε * Real.sqrt (1 - m ^ 2) /
        ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ))) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hhalf : (1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1) / 2 ≤
      (1 + Real.sqrt δ) * (2 * ε * Real.sqrt (1 - m ^ 2) /
        ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ))) / 2 :=
    (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).mpr
      (mul_le_mul_of_nonneg_right hinner (by norm_num : (0 : ℝ) ≤ 2))
  have hnum : (adjointQueryCount word : ℝ) * ((1 + Real.sqrt δ) *
      recipChebRatio δ ^ (n + 1) / 2) ≤
      (adjointQueryCount word : ℝ) * ((1 + Real.sqrt δ) *
        (2 * ε * Real.sqrt (1 - m ^ 2) /
          ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ))) / 2) :=
    mul_le_mul_of_nonneg_left hhalf hQ.le
  calc (adjointQueryCount word : ℝ) * ((1 + Real.sqrt δ) *
        recipChebRatio δ ^ (n + 1) / 2) / Real.sqrt (1 - m ^ 2)
      ≤ (adjointQueryCount word : ℝ) * ((1 + Real.sqrt δ) *
          (2 * ε * Real.sqrt (1 - m ^ 2) /
            ((adjointQueryCount word : ℝ) * (1 + Real.sqrt δ))) / 2) /
          Real.sqrt (1 - m ^ 2) :=
        (div_le_div_iff₀ hsm hsm).mpr (mul_le_mul_of_nonneg_right hnum hsm.le)
    _ = ε := by
        field_simp

theorem recipChebTruncQueryUpperBoundGlobal (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (δ m ε : ℝ) (n : ℕ)
    (hw : WellFormedAdjointCircuit word) (hδ : (0 : ℝ) < δ) (hδ1 : δ < 1)
    (hm : (1 : ℝ) / 2 ≤ m) (hm1 : m < 1) (hε : (0 : ℝ) < ε)
    (hQ : (0 : ℝ) < (adjointQueryCount word : ℝ))
    (hn : Real.log ((adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ) / ε ^ 2) ≤
      ((n + 1 : ℕ) : ℝ) * Real.log ((1 + Real.sqrt δ) / (1 - Real.sqrt δ))) :
    ∀ t ∈ Set.Icc (-1) 1,
      ‖evaluate (scalarSignalLift W ((δ / 2) * (chebTrunc n (recipChebCoeff δ)).eval t)) word -
          evaluate (scalarSignalLift W (δ / (2 * ((1 + δ) / 2 + (1 - δ) / 2 * t)))) word‖ ≤ ε := by
  have hrb := recipChebRatio_bounds δ hδ (le_of_lt hδ1)
  have hs1 : Real.sqrt δ < 1 := by
    have hs := Real.sqrt_lt_sqrt hδ.le hδ1
    rwa [Real.sqrt_one] at hs
  have hne : (1 : ℝ) - Real.sqrt δ ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm (ne_of_lt hs1))
  have hrinv : (1 : ℝ) / recipChebRatio δ = (1 + Real.sqrt δ) / (1 - Real.sqrt δ) := by
    unfold recipChebRatio
    field_simp
  have hinv : (1 : ℝ) / (ε ^ 2 /
      ((adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ))) =
      (adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ) / ε ^ 2 := by
    field_simp
  have hpow : recipChebRatio δ ^ (n + 1) ≤
      ε ^ 2 / ((adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ)) := by
    refine pow_le_of_log_ge (n + 1) (by positivity) ?hr0 (by rwa [hinv, hrinv])
    unfold recipChebRatio
    exact div_pos (by linarith) (by positivity)
  intro t ht
  have hbound := (recipChebTruncWordTransport W word δ n m hw hδ (le_of_lt hδ1) hm hm1).2 t ht
  have hrew : (adjointQueryCount word : ℝ) * Real.sqrt (2 * ((1 + Real.sqrt δ) *
      recipChebRatio δ ^ (n + 1) / 2)) =
      (adjointQueryCount word : ℝ) * Real.sqrt
        ((1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1)) := by
    congr 1
    rw [show (2 : ℝ) * ((1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1) / 2) =
      (1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1) from by ring]
  refine (hbound.trans_eq hrew).trans ?_
  have hnn : (0 : ℝ) ≤ (1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1) :=
    mul_nonneg (by positivity) (pow_nonneg hrb.1 _)
  have hsq : ((adjointQueryCount word : ℝ) * Real.sqrt
      ((1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1))) ^ 2 ≤ ε ^ 2 := by
    have hsplit : ((adjointQueryCount word : ℝ) * Real.sqrt
        ((1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1))) ^ 2 =
        (adjointQueryCount word : ℝ) ^ 2 *
          ((1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1)) := by
      rw [mul_pow, Real.sq_sqrt hnn]
    rw [hsplit]
    have hmul : (1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1) ≤
        (1 + Real.sqrt δ) * (ε ^ 2 /
          ((adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ))) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hfin : (adjointQueryCount word : ℝ) ^ 2 * ((1 + Real.sqrt δ) *
        (ε ^ 2 / ((adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ)))) = ε ^ 2 := by
      field_simp
    calc (adjointQueryCount word : ℝ) ^ 2 *
          ((1 + Real.sqrt δ) * recipChebRatio δ ^ (n + 1))
        ≤ (adjointQueryCount word : ℝ) ^ 2 * ((1 + Real.sqrt δ) *
            (ε ^ 2 / ((adjointQueryCount word : ℝ) ^ 2 * (1 + Real.sqrt δ)))) :=
          mul_le_mul_of_nonneg_left hmul (sq_nonneg _)
      _ = ε ^ 2 := hfin
  exact (sq_le_sq₀ (mul_nonneg hQ.le (Real.sqrt_nonneg _)) hε.le).mp hsq

theorem signChebTruncQueryUpperBound (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (K : ℕ) (δ m ε : ℝ)
    (hw : WellFormedAdjointCircuit word) (hδ : (0 : ℝ) < δ) (hε : (0 : ℝ) < ε)
    (hQ : (0 : ℝ) < (adjointQueryCount word : ℝ))
    (hm : (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 ≤ m) (hm1 : m < 1)
    (hK : (adjointQueryCount word : ℝ) / (2 * ε) ≤
      (((K + 1 : ℕ) : ℝ) * Real.pi * δ) * Real.sqrt (1 - m ^ 2)) :
    ∀ t ∈ Set.Icc (-1) 1, δ ≤ |t| →
      ‖evaluate (scalarSignalLift W ((1 / 2) *
          (chebTrunc (2 * K + 1) signChebCoeff).eval t)) word -
          evaluate (scalarSignalLift W (t / (2 * |t|))) word‖ ≤ ε := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hKp : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos K)
  have hc : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) * Real.pi * δ :=
    mul_pos (mul_pos hKp hπ) hδ
  have hm0 : (0 : ℝ) < m := by
    have h2 : (1 : ℝ) / 2 < (1 + 1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
      linarith [one_div_pos.2 hc]
    linarith
  have hm2 : (0 : ℝ) < 1 - m ^ 2 := by nlinarith
  have hsm : (0 : ℝ) < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  intro t ht htδ
  have hbound := (signChebTruncWordTransport W word K δ m hw hδ hm hm1).1 t ht htδ
  refine hbound.trans ?_
  have hident : (adjointQueryCount word : ℝ) *
      (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ) / 2) / Real.sqrt (1 - m ^ 2) =
      (adjointQueryCount word : ℝ) /
        (2 * (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2))) := by
    field_simp
  rw [hident, div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hc hsm))]
  have hK2 : (adjointQueryCount word : ℝ) ≤ 2 * ε *
      (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2)) := by
    have h := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hε)).mp hK
    have hring : (((K + 1 : ℕ) : ℝ) * Real.pi * δ) * Real.sqrt (1 - m ^ 2) * (2 * ε) =
        2 * ε * (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2)) := by
      ring
    rwa [hring] at h
  calc (adjointQueryCount word : ℝ) ≤ 2 * ε *
      (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2)) := hK2
    _ = ε * (2 * (((K + 1 : ℕ) : ℝ) * Real.pi * δ *
        Real.sqrt (1 - m ^ 2))) := by ring

theorem windowTruncQueryUpperBound (W : Type) [Fintype W] [DecidableEq W]
    (word : List (AdjointStep (Bool × W))) (K : ℕ) (a b δ m ε : ℝ)
    (ha : -1 ≤ a) (hb1 : b ≤ 1) (hab : a < b)
    (hw : WellFormedAdjointCircuit word) (hδ : (0 : ℝ) < δ) (hε : (0 : ℝ) < ε)
    (hQ : (0 : ℝ) < (adjointQueryCount word : ℝ))
    (hm : (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 ≤ m) (hm1 : m < 1)
    (hK : (adjointQueryCount word : ℝ) / ε ≤
      (((K + 1 : ℕ) : ℝ) * Real.pi * δ) * Real.sqrt (1 - m ^ 2)) :
    ∀ t ∈ Set.Icc (-1) 1, δ ≤ |t - a| → δ ≤ |t - b| →
      ‖evaluate (scalarSignalLift W ((1 / 2) * (windowTrunc a b K).eval t)) word -
          evaluate (scalarSignalLift W
            ((if t ∈ Set.Ioo a b then (1 : ℝ) else 0) / 2)) word‖ ≤ ε := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hKp : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos K)
  have hc : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) * Real.pi * δ :=
    mul_pos (mul_pos hKp hπ) hδ
  have hm0 : (0 : ℝ) < m := by
    have h2 : (1 : ℝ) / 2 < (1 + 2 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / 2 := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
      linarith [div_pos (by norm_num : (0 : ℝ) < 2) hc]
    linarith
  have hm2 : (0 : ℝ) < 1 - m ^ 2 := by nlinarith
  have hsm : (0 : ℝ) < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hm2
  intro t ht hta htb
  have hbound := (windowTruncWordTransport W word K a b δ m ha hb1 hab hw hδ hm hm1).1 t ht hta htb
  refine hbound.trans ?_
  have hident : (adjointQueryCount word : ℝ) *
      (1 / (((K + 1 : ℕ) : ℝ) * Real.pi * δ)) / Real.sqrt (1 - m ^ 2) =
      (adjointQueryCount word : ℝ) /
        (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2)) := by
    field_simp
  rw [hident, div_le_iff₀ (mul_pos hc hsm)]
  have hK2 : (adjointQueryCount word : ℝ) ≤ ε *
      (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2)) := by
    have h := (div_le_iff₀ hε).mp hK
    have hring : (((K + 1 : ℕ) : ℝ) * Real.pi * δ) * Real.sqrt (1 - m ^ 2) * ε =
        ε * (((K + 1 : ℕ) : ℝ) * Real.pi * δ * Real.sqrt (1 - m ^ 2)) := by
      ring
    rwa [hring] at h
  exact hK2

private def pickEntry : Matrix (Bool × Unit) Unit ℂ :=
  Matrix.of fun i _ => if i.1 = false then (1 : ℂ) else 0

private theorem pickEntry_isometry : IsIsometry pickEntry := by
  unfold IsIsometry
  ext a b
  have hstar : ∀ i : Bool × Unit,
      (pickEntryᴴ a i) * pickEntry i b
        = if i = ((false, ()) : Bool × Unit) then (1 : ℂ) else 0 := by
    intro i
    obtain ⟨i1, iu⟩ := i
    cases iu
    cases i1 <;> simp [pickEntry, Matrix.conjTranspose_apply]
  rw [Matrix.mul_apply, Matrix.one_apply_eq,
    Finset.sum_eq_single ((false, ()) : Bool × Unit)]
  · rw [hstar (false, ()), if_pos rfl]
  · intro i _ hne
    rw [hstar i, if_neg hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem compress_pickEntry (V : Matrix (Bool × Unit) (Bool × Unit) ℂ) :
    compress pickEntry V pickEntry =
      Matrix.of fun _ _ => V (false, ()) (false, ()) := by
  ext a b
  have key : ∀ i j : Bool × Unit,
      (pickEntryᴴ a i) * V i j * (pickEntry j b)
        = if (i = ((false, ()) : Bool × Unit) ∧ j = ((false, ()) : Bool × Unit))
      then V i j else 0 := by
    rintro ⟨i1, iu⟩ ⟨j1, ju⟩
    cases iu
    cases ju
    cases i1 <;> cases j1 <;> simp [pickEntry, Matrix.conjTranspose_apply]
  have step : (pickEntryᴴ * V * pickEntry) a b
      = ∑ j : Bool × Unit, ∑ i : Bool × Unit,
          (pickEntryᴴ a i) * V i j * (pickEntry j b) := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [compress, step, Finset.sum_eq_single ((false, ()) : Bool × Unit)]
  · rw [Finset.sum_eq_single ((false, ()) : Bool × Unit)]
    · rw [key (false, ()) (false, ()),
        if_pos (show ((false, ()) : Bool × Unit) = (false, ()) ∧ (false, ()) = (false, ())
          by simp), Matrix.of_apply]
    · intro i _ hne
      rw [key i (false, ()), if_neg (by rintro ⟨hi, _⟩; exact hne hi)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro j _ hne
    rw [Finset.sum_eq_zero]
    intro i _
    rw [key i j, if_neg (by rintro ⟨_, hj⟩; exact hne hj)]
  · intro h
    exact absurd (Finset.mem_univ _) h

noncomputable def wordResponseQuadQueryCost (n N : ℕ) : ℕ :=
  N * adjointQueryCount (signalChebyshevUnitWord n)

theorem wordResponseQuadQueryCost_eq (n N : ℕ) :
    wordResponseQuadQueryCost n N = N * n := by
  rw [wordResponseQuadQueryCost, (signalChebyshevUnitWord_cost n).2.1]

theorem wordResponseQuadBudget_eq (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    2 * (n : ℝ) * Real.sqrt (2 * (ε ^ 2 / (8 * (n : ℝ) ^ 2))) = ε := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have h2n : (2 * (n : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hnne
  have h4npos : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
  have h4n : (4 : ℝ) * (n : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hnne)
  have h8n : (8 : ℝ) * (n : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hnne)
  have hrw : (2 : ℝ) * (ε ^ 2 / (8 * (n : ℝ) ^ 2)) = ε ^ 2 / (4 * (n : ℝ) ^ 2) := by
    field_simp
    norm_num
  have hs4 : Real.sqrt (4 * (n : ℝ) ^ 2) = 2 * (n : ℝ) := by
    have h : (4 : ℝ) * (n : ℝ) ^ 2 = (2 * (n : ℝ)) ^ 2 := by ring
    rw [h]
    exact Real.sqrt_sq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn0.le)
  have hs : Real.sqrt (2 * (ε ^ 2 / (8 * (n : ℝ) ^ 2))) = ε / (2 * (n : ℝ)) := by
    rw [hrw, Real.sqrt_div (sq_nonneg ε) (4 * (n : ℝ) ^ 2), hs4, Real.sqrt_sq hε.le]
  rw [hs, div_eq_mul_inv, mul_comm ε ((2 * (n : ℝ))⁻¹), ← mul_assoc,
    mul_inv_cancel₀ h2n, one_mul]

theorem wordResponseQuadComplexityLedger (n K N : ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ) (δ ε : ℝ)
    (hn : 0 < n) (hNK : n * K < N) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hδle : δ ≤ ε ^ 2 / (8 * (n : ℝ) ^ 2))
    (hq1 : ∀ t ∈ Set.Icc (-1) 1, (chebTrunc K c).eval t ∈ Set.Icc (-1) 1)
    (hf1 : ∀ t ∈ Set.Icc (-1) 1, f t ∈ Set.Icc (-1) 1)
    (huni : ∀ t ∈ Set.Icc (-1) 1, |f t - (chebTrunc K c).eval t| ≤ δ)
    (hfc : ContinuousOn f (Set.Icc (-1) 1)) :
    |(∫ t in (-1)..1, (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t)) -
        chebQuadRule N (fun t => (wordResponse n (chebTrunc K c) t).re)| ≤ ε ∧
      wordResponseQuadQueryCost n N = N * n := by
  refine ⟨?_, wordResponseQuadQueryCost_eq n N⟩
  have hchain := wordResponseQuadratureChain n K N c f δ hNK hδ hq1 hf1 huni hfc
  refine hchain.trans ?_
  have hmono : 2 * δ ≤ 2 * (ε ^ 2 / (8 * (n : ℝ) ^ 2)) := by linarith
  calc 2 * (n : ℝ) * Real.sqrt (2 * δ)
      ≤ 2 * (n : ℝ) * Real.sqrt (2 * (ε ^ 2 / (8 * (n : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono)
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
    _ = ε := wordResponseQuadBudget_eq n hn ε hε

theorem wordResponseQuadSelector (n K : ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ) (δ ε : ℝ)
    (hn : 0 < n) (hε : 0 < ε) (hδ : 0 ≤ δ) (hδle : δ ≤ ε ^ 2 / (8 * (n : ℝ) ^ 2))
    (hq1 : ∀ t ∈ Set.Icc (-1) 1, (chebTrunc K c).eval t ∈ Set.Icc (-1) 1)
    (hf1 : ∀ t ∈ Set.Icc (-1) 1, f t ∈ Set.Icc (-1) 1)
    (huni : ∀ t ∈ Set.Icc (-1) 1, |f t - (chebTrunc K c).eval t| ≤ δ)
    (hfc : ContinuousOn f (Set.Icc (-1) 1)) :
    |(∫ t in (-1)..1, (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (f t)) -
        chebQuadRule (n * K + 1)
          (fun t => (wordResponse n (chebTrunc K c) t).re)| ≤ ε ∧
      wordResponseQuadQueryCost n (n * K + 1) = (n * K + 1) * n :=
  wordResponseQuadComplexityLedger n K (n * K + 1) c f δ ε hn (Nat.lt_succ_self _)
    hε hδ hδle hq1 hf1 huni hfc

theorem chebyshevWordResponseQueryFloor (n : ℕ) (x y η m : ℝ)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) (hxy : x ≠ y)
    (hη : 0 ≤ η) (hηle : |x - y| ≤ η)
    (hm : 0 ≤ m) (hm1 : m < 1) (hxm : |x| ≤ m) (hym : |y| ≤ m) :
    |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x -
        (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval y| / Real.sqrt (2 * η) ≤ (n : ℝ) ∧
      Real.sqrt (1 - m ^ 2) *
        |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x -
          (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval y| / η ≤ (n : ℝ) := by
  have hcost := signalChebyshevUnitWord_cost n
  have hentry : ∀ s : ℝ, s ∈ Set.Icc (-1) 1 →
      (evaluate (scalarSignalLift Unit s) (signalChebyshevUnitWord n)) (false, ()) (false, ())
        = Complex.ofReal ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval s) := by
    intro s hs
    have h := scalar_signal_chebyshev_actual_word n s hs
    rw [h.2.2.2.2.2, tensorGate_apply, Matrix.one_apply_eq, mul_one, h.2.2.2.2.1]
  have hcomp : ∀ s : ℝ, s ∈ Set.Icc (-1) 1 →
      compress pickEntry (evaluate (scalarSignalLift Unit s) (signalChebyshevUnitWord n))
        pickEntry =
        Matrix.of fun _ _ =>
          Complex.ofReal ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval s) := by
    intro s hs
    rw [compress_pickEntry, hentry s hs]
  have hzero : ∀ s : ℝ, s ∈ Set.Icc (-1) 1 →
      ‖(Complex.ofReal ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval s) : ℂ) •
          (1 : Matrix Unit Unit ℂ) -
        compress pickEntry (evaluate (scalarSignalLift Unit s) (signalChebyshevUnitWord n))
          pickEntry‖ ≤ 0 := by
    intro s hs
    rw [hcomp s hs]
    have h : (Complex.ofReal ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval s) : ℂ) •
        (1 : Matrix Unit Unit ℂ) -
      (Matrix.of fun _ _ =>
        Complex.ofReal ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval s) :
          Matrix Unit Unit ℂ) = 0 := by
      ext a b
      simp [Matrix.smul_apply]
    rw [h, norm_zero]
  have hmain := uniformErrorQueryLowerBound Unit Unit pickEntry pickEntry
    (signalChebyshevUnitWord n) x y
    ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x)
    ((Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval y) 0 η m
    pickEntry_isometry pickEntry_isometry hcost.1 hx hy hxy (by norm_num) hη hηle
    (hzero x hx) (hzero y hy)
  rw [hcost.2.1] at hmain
  have h0sub : |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x -
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval y| - 2 * 0 =
    |(Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval x -
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval y| := by ring
  rw [h0sub] at hmain
  exact ⟨hmain.1, hmain.2 hm hm1 hxm hym⟩

structure AdaptiveSignalQuery (W : Type) [Fintype W] [DecidableEq W] where

  read : Matrix (Bool × W) (Bool × W) ℂ → ℂ

  wordChoice : List ℂ → List (AdjointStep (Bool × W))

  wordChoice_legal : ∀ h : List ℂ, WellFormedAdjointCircuit (wordChoice h)

noncomputable def adaptiveReads {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) : ℕ → List ℂ
  | 0 => []
  | j + 1 => adaptiveReads P x j ++
      [P.read (evaluate (scalarSignalLift W x) (P.wordChoice (adaptiveReads P x j)))]

noncomputable def adaptiveWordAt {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (j : ℕ) :
    List (AdjointStep (Bool × W)) :=
  P.wordChoice (adaptiveReads P x j)

noncomputable def adaptiveReadAt {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (j : ℕ) : ℂ :=
  P.read (evaluate (scalarSignalLift W x) (adaptiveWordAt P x j))

theorem adaptiveReads_succ {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (j : ℕ) :
    adaptiveReads P x (j + 1) = adaptiveReads P x j ++ [adaptiveReadAt P x j] := rfl

theorem adaptiveReads_length {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (j : ℕ) :
    (adaptiveReads P x j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [adaptiveReads_succ, List.length_append, ih, List.length_singleton]

noncomputable def adaptiveQueryCost {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (T : ℕ) : ℕ :=
  ∑ j ∈ Finset.range T, adjointQueryCount (adaptiveWordAt P x j)

theorem adaptiveQueryCost_succ {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (T : ℕ) :
    adaptiveQueryCost P x (T + 1) =
      adaptiveQueryCost P x T + adjointQueryCount (adaptiveWordAt P x T) := by
  simp only [adaptiveQueryCost, Finset.sum_range_succ]

theorem adaptiveConstantProtocolWord {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (w : List (AdjointStep (Bool × W)))
    (hconst : ∀ h : List ℂ, P.wordChoice h = w) (j : ℕ) :
    adaptiveWordAt P x j = w := by
  unfold adaptiveWordAt
  exact hconst _

theorem adaptiveConstantProtocolCost {W : Type} [Fintype W] [DecidableEq W]
    (P : AdaptiveSignalQuery W) (x : ℝ) (w : List (AdjointStep (Bool × W)))
    (hconst : ∀ h : List ℂ, P.wordChoice h = w) (T : ℕ) :
    adaptiveQueryCost P x T = T * adjointQueryCount w := by
  rw [adaptiveQueryCost]
  have h : ∀ j ∈ Finset.range T,
      adjointQueryCount (adaptiveWordAt P x j) = adjointQueryCount w :=
    fun j _ => by rw [adaptiveConstantProtocolWord P x w hconst j]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_id]

private theorem adaptiveReads_eq {W : Type} [Fintype W] [DecidableEq W]
    {P : AdaptiveSignalQuery W} {x y : ℝ} {j : ℕ}
    (hagree : ∀ k < j, adaptiveReadAt P x k = adaptiveReadAt P y k) :
    adaptiveReads P x j = adaptiveReads P y j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hpre := ih fun k hk => hagree k (Nat.lt_succ_of_lt hk)
    rw [adaptiveReads_succ, adaptiveReads_succ, hpre, hagree j (Nat.lt_succ_self j)]

theorem adaptiveWord_eq {W : Type} [Fintype W] [DecidableEq W]
    {P : AdaptiveSignalQuery W} {x y : ℝ} {j : ℕ}
    (hagree : ∀ k < j, adaptiveReadAt P x k = adaptiveReadAt P y k) :
    adaptiveWordAt P x j = adaptiveWordAt P y j := by
  have hreads := adaptiveReads_eq hagree
  unfold adaptiveWordAt
  rw [hreads]

theorem adaptiveRoundTransport {W : Type} [Fintype W] [DecidableEq W]
    {P : AdaptiveSignalQuery W} {x y η m : ℝ} {j : ℕ}
    (hagree : ∀ k < j, adaptiveReadAt P x k = adaptiveReadAt P y k)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1)
    (hε : 0 ≤ η) (hηle : |x - y| ≤ η)
    (hm : 0 ≤ m) (hm1 : m < 1) (hxm : |x| ≤ m) (hym : |y| ≤ m) :
    (‖evaluate (scalarSignalLift W x) (adaptiveWordAt P x j) -
        evaluate (scalarSignalLift W y) (adaptiveWordAt P y j)‖ ≤
        (adjointQueryCount (adaptiveWordAt P x j) : ℝ) * η / Real.sqrt (1 - m ^ 2)) ∧
    (‖evaluate (scalarSignalLift W x) (adaptiveWordAt P x j) -
        evaluate (scalarSignalLift W y) (adaptiveWordAt P y j)‖ ≤
        (adjointQueryCount (adaptiveWordAt P x j) : ℝ) * Real.sqrt (2 * η)) := by
  have hw : adaptiveWordAt P x j = adaptiveWordAt P y j := adaptiveWord_eq hagree
  have hmain := frontier1 W (adaptiveWordAt P y j) m η
    (P.wordChoice_legal _) hε hm hm1
  have hxw : x ∈ Set.Icc (-m) m := abs_le.mp hxm
  have hyw : y ∈ Set.Icc (-m) m := abs_le.mp hym
  rw [hw]
  exact ⟨hmain.1 x y hxw hyw hηle, hmain.2 x y hx hy hηle⟩

theorem adaptiveFirstDivergenceFloor {W I : Type} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] [Nonempty I]
    {P : AdaptiveSignalQuery W} {x y a b eps η : ℝ} {j T : ℕ}
    (L R : Matrix (Bool × W) I ℂ) (hL : IsIsometry L) (hR : IsIsometry R)
    (hj : j < T) (hagree : ∀ k < j, adaptiveReadAt P x k = adaptiveReadAt P y k)
    (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) (hxy : x ≠ y)
    (heps : 0 ≤ eps) (hη : 0 ≤ η) (hηle : |x - y| ≤ η)
    (ha : ‖(a : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W x) (adaptiveWordAt P x j)) R‖ ≤ eps)
    (hb : ‖(b : ℂ) • (1 : Matrix I I ℂ) -
        compress L (evaluate (scalarSignalLift W y) (adaptiveWordAt P y j)) R‖ ≤ eps) :
    (|a - b| - 2 * eps) / Real.sqrt (2 * η) ≤
      (adjointQueryCount (adaptiveWordAt P x j) : ℝ) ∧
    (|a - b| - 2 * eps) / Real.sqrt (2 * η) ≤ (adaptiveQueryCost P x T : ℝ) := by
  have hw : adaptiveWordAt P x j = adaptiveWordAt P y j := adaptiveWord_eq hagree
  rw [← hw] at hb
  have hmain := uniformErrorQueryLowerBound W I L R (adaptiveWordAt P x j) x y a b eps η 0
    hL hR (P.wordChoice_legal _) hx hy hxy heps hη hηle ha hb
  refine ⟨hmain.1, ?_⟩
  have hsingle : ((adjointQueryCount (adaptiveWordAt P x j) : ℕ) : ℝ) ≤
      (adaptiveQueryCost P x T : ℝ) := by
    have h := Finset.single_le_sum
      (f := fun k => ((adjointQueryCount (adaptiveWordAt P x k) : ℕ) : ℝ))
      (fun k _ => Nat.cast_nonneg _) (Finset.mem_range.mpr hj)
    simpa only [adaptiveQueryCost, Nat.cast_sum] using h
  exact hmain.1.trans hsingle

structure MultiSignalQuery (ι W : Type) [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] where

  word : ι → List (AdjointStep (Bool × W))

  word_legal : ∀ i, WellFormedAdjointCircuit (word i)

noncomputable def multiSignalOutput {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (M : MultiSignalQuery ι W) (x : ι → ℝ) :
    ι → Matrix (Bool × W) (Bool × W) ℂ :=
  fun i => evaluate (scalarSignalLift W (x i)) (M.word i)

def multiSignalQueryCost {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (M : MultiSignalQuery ι W) : ℕ :=
  ∑ i, adjointQueryCount (M.word i)

theorem multiSignalQueryCost_ge_single {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (M : MultiSignalQuery ι W) (i₀ : ι) :
    adjointQueryCount (M.word i₀) ≤ multiSignalQueryCost M :=
  Finset.single_le_sum (f := fun i => adjointQueryCount (M.word i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)

theorem multiSignalOutput_congr {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (M : MultiSignalQuery ι W) {x y : ι → ℝ} {i : ι}
    (h : x i = y i) : multiSignalOutput M x i = multiSignalOutput M y i := by
  simp only [multiSignalOutput]
  rw [h]

theorem multiSignalAggregateTransport {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (M : MultiSignalQuery ι W)
    (g : (ι → Matrix (Bool × W) (Bool × W) ℂ) → ℝ) (L m ε : ℝ) (x y : ι → ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ι → Matrix (Bool × W) (Bool × W) ℂ,
      |g u - g v| ≤ L * ∑ i, ‖u i - v i‖)
    (hε : 0 ≤ ε) (hm : 0 ≤ m) (hm1 : m < 1)
    (hx : ∀ i, x i ∈ Set.Icc (-1) 1) (hy : ∀ i, y i ∈ Set.Icc (-1) 1)
    (herr : ∀ i, |x i - y i| ≤ ε)
    (hxm : ∀ i, |x i| ≤ m) (hym : ∀ i, |y i| ≤ m) :
    |g (multiSignalOutput M x) - g (multiSignalOutput M y)| ≤
      L * ((multiSignalQueryCost M : ℝ) * ε / Real.sqrt (1 - m ^ 2)) ∧
    |g (multiSignalOutput M x) - g (multiSignalOutput M y)| ≤
      L * ((multiSignalQueryCost M : ℝ) * Real.sqrt (2 * ε)) := by
  have hper : ∀ i : ι,
      ‖multiSignalOutput M x i - multiSignalOutput M y i‖ ≤
        (adjointQueryCount (M.word i) : ℝ) * ε / Real.sqrt (1 - m ^ 2) ∧
      ‖multiSignalOutput M x i - multiSignalOutput M y i‖ ≤
        (adjointQueryCount (M.word i) : ℝ) * Real.sqrt (2 * ε) := by
    intro i
    have h := frontier1 W (M.word i) m ε (M.word_legal i) hε hm hm1
    exact ⟨h.1 (x i) (y i) (abs_le.mp (hxm i)) (abs_le.mp (hym i)) (herr i),
      h.2 (x i) (y i) (hx i) (hy i) (herr i)⟩
  constructor
  · refine (hLip _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    have h1 : ∑ i, ‖multiSignalOutput M x i - multiSignalOutput M y i‖ ≤
        ∑ i, ((adjointQueryCount (M.word i) : ℝ) * ε / Real.sqrt (1 - m ^ 2)) :=
      Finset.sum_le_sum fun i _ => (hper i).1
    rw [← Finset.sum_div, ← Finset.sum_mul] at h1
    simpa only [multiSignalQueryCost, Nat.cast_sum] using h1
  · refine (hLip _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    have h1 : ∑ i, ‖multiSignalOutput M x i - multiSignalOutput M y i‖ ≤
        ∑ i, ((adjointQueryCount (M.word i) : ℝ) * Real.sqrt (2 * ε)) :=
      Finset.sum_le_sum fun i _ => (hper i).2
    rw [← Finset.sum_mul] at h1
    simpa only [multiSignalQueryCost, Nat.cast_sum] using h1

theorem multiSignalSingleCoordinateFloor {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (M : MultiSignalQuery ι W)
    (g : (ι → Matrix (Bool × W) (Bool × W) ℂ) → ℝ) (L ν η : ℝ) (i₀ : ι)
    (x x' : ι → ℝ)
    (hL : 0 < L) (hη : 0 < η)
    (hLip : ∀ u v : ι → Matrix (Bool × W) (Bool × W) ℂ,
      |g u - g v| ≤ L * ∑ i, ‖u i - v i‖)
    (hdiff : ∀ i, i ≠ i₀ → x i = x' i)
    (hx : ∀ i, x i ∈ Set.Icc (-1) 1) (hx' : ∀ i, x' i ∈ Set.Icc (-1) 1)
    (herr : |x i₀ - x' i₀| ≤ η)
    (hgap : ν ≤ |g (multiSignalOutput M x) - g (multiSignalOutput M x')|) :
    ν / (L * Real.sqrt (2 * η)) ≤ (adjointQueryCount (M.word i₀) : ℝ) ∧
    ν / (L * Real.sqrt (2 * η)) ≤ (multiSignalQueryCost M : ℝ) := by
  have hvanish : ∀ i ∈ (Finset.univ : Finset ι), i ≠ i₀ →
      ‖multiSignalOutput M x i - multiSignalOutput M x' i‖ = 0 := by
    intro i _ hne
    rw [multiSignalOutput_congr M (hdiff i hne), sub_self, norm_zero]
  have hsum : ∑ i, ‖multiSignalOutput M x i - multiSignalOutput M x' i‖ =
      ‖multiSignalOutput M x i₀ - multiSignalOutput M x' i₀‖ :=
    Finset.sum_eq_single i₀ hvanish (fun h => absurd (Finset.mem_univ i₀) h)
  have htrans : ‖multiSignalOutput M x i₀ - multiSignalOutput M x' i₀‖ ≤
      (adjointQueryCount (M.word i₀) : ℝ) * Real.sqrt (2 * η) :=
    (frontier1 W (M.word i₀) (1 / 2) η (M.word_legal i₀) hη.le
      (by norm_num) (by norm_num)).2 (x i₀) (x' i₀) (hx i₀) (hx' i₀) herr
  have hkey : ν ≤ L * ((adjointQueryCount (M.word i₀) : ℝ) * Real.sqrt (2 * η)) := by
    have hchain := (hLip (multiSignalOutput M x) (multiSignalOutput M x')).trans_eq
      (by rw [hsum])
    exact hgap.trans (hchain.trans (mul_le_mul_of_nonneg_left htrans hL.le))
  have hpos : 0 < L * Real.sqrt (2 * η) :=
    mul_pos hL (Real.sqrt_pos.mpr (by linarith))
  have hsingle : ((adjointQueryCount (M.word i₀) : ℕ) : ℝ) ≤
      (multiSignalQueryCost M : ℝ) :=
    by exact_mod_cast multiSignalQueryCost_ge_single M i₀
  have hfirst : ν / (L * Real.sqrt (2 * η)) ≤ (adjointQueryCount (M.word i₀) : ℝ) := by
    apply (div_le_iff₀ hpos).mpr
    rw [mul_left_comm]
    exact hkey
  exact ⟨hfirst, hfirst.trans hsingle⟩

private theorem abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  have h2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, h2, pow_two]
  linarith [sq_nonneg z.im]

noncomputable def sumEntryReAgg {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (w₀ : W)
    (u : ι → Matrix (Bool × W) (Bool × W) ℂ) : ℝ :=
  ∑ i, (u i (false, w₀) (false, w₀)).re

theorem abs_sumEntryReAgg_sub_le {ι W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (w₀ : W)
    (u v : ι → Matrix (Bool × W) (Bool × W) ℂ) :
    |sumEntryReAgg w₀ u - sumEntryReAgg w₀ v| ≤ ∑ i, ‖u i - v i‖ := by
  have h1 : sumEntryReAgg w₀ u - sumEntryReAgg w₀ v =
      ∑ i, ((u i (false, w₀) (false, w₀) - v i (false, w₀) (false, w₀) : ℂ)).re := by
    simp only [sumEntryReAgg, Complex.sub_re, Finset.sum_sub_distrib]
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (abs_re_le_norm _).trans (by
    rw [← Matrix.sub_apply]
    exact norm_entry_le_l2_norm (u i - v i) (false, w₀) (false, w₀))

end Qatlib.Concepts.QsvtCore.QueryLowerBound
