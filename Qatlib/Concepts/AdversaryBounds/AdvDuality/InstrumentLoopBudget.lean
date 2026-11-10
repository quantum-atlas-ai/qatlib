/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.UnboundedInstrumentLoop
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MixedInstrument.ClockBridge

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped ComplexOrder ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable def loopExpectedTime {D : ℕ} (I : Instrument Bool D D) (ρ : Operator D) :
    ℝ≥0∞ :=
  ∑' k, loopPending I ρ k

set_option maxHeartbeats 400000 in

theorem instrument_loop_expected_time_online_budget :
    ∀ (D : ℕ) (I : Instrument Bool D D) (ρ : Operator D) (hρ : IsDensityOperator ρ) (n : ℕ),
      loopExpectedTime I ρ = ∑' k : ℕ, loopPending I ρ k ∧
      (n+1:ℝ≥0∞)*loopPending I ρ n ≤ loopExpectedTime I ρ ∧
      (0 < loopNeverMass I ρ → loopExpectedTime I ρ = ⊤) := by
  intro D I ρ hρ n
  refine ⟨rfl, ?_, ?_⟩
  · have h1 : ∑ k ∈ Finset.range (n + 1), loopPending I ρ n
        ≤ ∑ k ∈ Finset.range (n + 1), loopPending I ρ k :=
      Finset.sum_le_sum fun k hk =>
        (loopPending_antitone I hρ.1) (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have h2 : ∑ k ∈ Finset.range (n + 1), loopPending I ρ k ≤ loopExpectedTime I ρ :=
      ENNReal.sum_le_tsum _
    calc (n+1:ℝ≥0∞) * loopPending I ρ n
        = ∑ k ∈ Finset.range (n + 1), loopPending I ρ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
      _ ≤ ∑ k ∈ Finset.range (n + 1), loopPending I ρ k := h1
      _ ≤ loopExpectedTime I ρ := h2
  · intro hpos
    have hge : ∀ k : ℕ, loopNeverMass I ρ ≤ loopPending I ρ k :=
      fun k => iInf_le (f := loopPending I ρ) k
    have h1 : ∀ n : ℕ, (n : ℝ≥0∞) * loopNeverMass I ρ ≤ loopExpectedTime I ρ := by
      intro n
      calc (n : ℝ≥0∞) * loopNeverMass I ρ
          = ∑ k ∈ Finset.range n, loopNeverMass I ρ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Finset.range n, loopPending I ρ k := Finset.sum_le_sum fun k _ => hge k
        _ ≤ loopExpectedTime I ρ := ENNReal.sum_le_tsum _
    by_contra hE
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (a := loopNeverMass I ρ)
      (b := loopExpectedTime I ρ) (ne_of_gt hpos) hE
    exact absurd (h1 n) (not_le.2 hn)

private theorem geometric_q_nonneg {D : ℕ} (I : Instrument Bool D D) {q : ℝ}
    {ρ : Operator D} (hρ : IsDensityOperator ρ)
    (hcontr : ∀ X : Operator D, X.PosSemidef →
      (Matrix.trace (I.branch false X)).re ≤ q * (Matrix.trace X).re) : (0 : ℝ) ≤ q := by
  have hB : (0 : ℝ) ≤ (Matrix.trace (I.branch false ρ)).re :=
    complex_re_nonneg_of_le ((I.cp false).positive hρ.1).trace_nonneg
  have h1 : (Matrix.trace ρ).re = 1 := by rw [hρ.2]; norm_num
  have hq := hcontr ρ hρ.1
  rw [h1] at hq
  linarith

theorem loop_trace_geometric_psd {D : ℕ} (I : Instrument Bool D D) {q : ℝ}
    (hq0 : 0 ≤ q) {P : Operator D} (hP : P.PosSemidef)
    (hcontr : ∀ X : Operator D, X.PosSemidef →
      (Matrix.trace (I.branch false X)).re ≤ q * (Matrix.trace X).re) :
    ∀ n : ℕ, (Matrix.trace (loopContinueMap I n P)).re ≤ q ^ n * (Matrix.trace P).re := by
  intro n
  induction n with
  | zero =>
      rw [show (loopContinueMap I 0 P) = P from rfl, pow_zero, one_mul]
  | succ n ih =>
      rw [loopContinueMap_succ_apply, pow_succ]
      calc (Matrix.trace (I.branch false (loopContinueMap I n P))).re
          ≤ q * (Matrix.trace (loopContinueMap I n P)).re :=
            hcontr _ (loopContinueMap_posSemidef I n hP)
        _ ≤ q * (q ^ n * (Matrix.trace P).re) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ n * q * (Matrix.trace P).re := by ring
        _ = q ^ (n + 1) * (Matrix.trace P).re := by rw [pow_succ]

theorem loop_trace_geometric {D : ℕ} (I : Instrument Bool D D) {q : ℝ}
    {ρ : Operator D} (hρ : IsDensityOperator ρ) (hq0 : 0 ≤ q)
    (hcontr : ∀ X : Operator D, X.PosSemidef →
      (Matrix.trace (I.branch false X)).re ≤ q * (Matrix.trace X).re) :
    ∀ n : ℕ, (Matrix.trace (loopContinueMap I n ρ)).re ≤ q ^ n := by
  have h := loop_trace_geometric_psd I hq0 hρ.1 hcontr
  have h1 : (Matrix.trace ρ).re = 1 := by rw [hρ.2]; norm_num
  intro n
  exact (h n).trans_eq (by rw [h1, mul_one])

theorem terminal_sub_partial_eq_tsum {D : ℕ} (I : Instrument Bool D D) (X : Operator D)
    (n : ℕ) :
    loopTerminalMap I X - loopPartialMap I n X
      = Matrix.of fun i j => ∑' k, loopHaltAt I (n + k) X i j := by
  ext i j
  rw [Matrix.sub_apply, loopTerminalMap_apply, Matrix.of_apply, loopPartialMap_apply,
    Matrix.sum_apply]
  have hsum := Summable.sum_add_tsum_nat_add n
    (loopHaltAt_entry_summable I X (i := i) (j := j))
  rw [← hsum, add_sub_cancel_left]
  exact tsum_congr fun k => by rw [Nat.add_comm]

theorem terminal_sub_partial_posSemidef {D : ℕ} (I : Instrument Bool D D)
    {X : Operator D} (hX : X.PosSemidef) (n : ℕ) :
    (loopTerminalMap I X - loopPartialMap I n X).PosSemidef := by
  rw [terminal_sub_partial_eq_tsum I X n]
  have hshift : (Matrix.of fun i j => ∑' k, loopHaltAt I (n + k) X i j)
      = Matrix.of fun i j => ∑' k, loopHaltAt I (k + n) X i j := by
    congr 1
    funext i j
    exact tsum_congr fun k => by rw [Nat.add_comm]
  rw [hshift]
  exact posSemidef_of_tsum_entries (fun k => loopHaltAt_posSemidef I (k + n) hX)
    (fun i j => (summable_nat_add_iff n).mpr (loopHaltAt_entry_summable I X i j))

theorem schattenOne_eq_re_trace {D : ℕ} {A : Operator D} (hA : A.PosSemidef) :
    SchattenOne A = (Matrix.trace A).re := by
  have h := Matrix.PosSemidef.traceNorm_eq_trace hA
  have hre : Matrix.traceNorm A = (Matrix.trace A).re := by
    simpa using congrArg Complex.re h
  rw [Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm, hre]

theorem instrument_loop_geometric_actual_trace_cutoff :
    ∀ (D : ℕ) (I : Instrument Bool D D) (q : ℝ) (ρ : Operator D),
      0≤q → q<1 → IsDensityOperator ρ →
      (∀ X : Operator D, X.PosSemidef →
        (Matrix.trace (I.branch false X)).re ≤ q*(Matrix.trace X).re) →
      (∀ n, SchattenOne (loopTerminalMap I ρ-loopPartialMap I n ρ) ≤ q^n) ∧
      loopNeverMass I ρ = 0 ∧ loopExpectedTime I ρ ≤ ENNReal.ofReal ((1-q)⁻¹) := by
  intro D I q ρ hq0 hq1 hρ hcontr
  have hgeo : ∀ n : ℕ, (Matrix.trace (loopContinueMap I n ρ)).re ≤ q ^ n :=
    loop_trace_geometric I hρ hq0 hcontr
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hpsd := terminal_sub_partial_posSemidef I hρ.1 n
    rw [schattenOne_eq_re_trace hpsd]
    have hlimM : Filter.Tendsto (fun m : ℕ => loopPartialMap I (n + m) ρ)
        Filter.atTop (nhds (loopTerminalMap I ρ)) := by
      refine (loopTerminalMap_tendsto I ρ).comp ?_
      exact Filter.tendsto_atTop_mono (f := fun m : ℕ => m) (g := fun m => n + m)
        (fun k => by show k ≤ n + k; omega) Filter.tendsto_id
    have hbase : Filter.Tendsto
        (fun m : ℕ => loopPartialMap I (n + m) ρ - loopPartialMap I n ρ) Filter.atTop
        (nhds (loopTerminalMap I ρ - loopPartialMap I n ρ)) :=
      Filter.Tendsto.sub hlimM tendsto_const_nhds
    have hlim : Filter.Tendsto
        (fun m : ℕ => (Matrix.trace (loopPartialMap I (n + m) ρ
          - loopPartialMap I n ρ)).re) Filter.atTop
        (nhds (Matrix.trace (loopTerminalMap I ρ - loopPartialMap I n ρ)).re) :=
      ((Complex.continuous_re.tendsto
        (x := Matrix.trace (loopTerminalMap I ρ - loopPartialMap I n ρ))).comp
        (tendsto_matrix_trace hbase))
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun m => ?_)

    have hdiff : loopPartialMap I (n + m) ρ - loopPartialMap I n ρ
        = ∑ k ∈ Finset.range m, loopHaltAt I (n + k) ρ := by
      rw [loopPartialMap_apply, loopPartialMap_apply,
        Finset.sum_range_add (f := fun k => loopHaltAt I k ρ) n m, add_sub_cancel_left]
    have htr : (Matrix.trace (loopPartialMap I (n + m) ρ
        - loopPartialMap I n ρ)).re
        = ∑ k ∈ Finset.range m, (Matrix.trace (loopHaltAt I (n + k) ρ)).re := by
      rw [hdiff, Matrix.trace_sum, Complex.re_sum]
    have hsplit2 : (Matrix.trace (loopPartialMap I (n + m) ρ)).re
        = (Matrix.trace (loopPartialMap I n ρ)).re
          + ∑ k ∈ Finset.range m, (Matrix.trace (loopHaltAt I (n + k) ρ)).re := by
      rw [loopPartialMap_apply, loopPartialMap_apply, Matrix.trace_sum, Complex.re_sum,
        Finset.sum_range_add (f := fun k => (Matrix.trace (loopHaltAt I k ρ)).re) n m,
        Matrix.trace_sum, Complex.re_sum]
    have e1 : (Matrix.trace (loopPartialMap I (n + m) ρ)).re
        + (Matrix.trace (loopContinueMap I (n + m) ρ)).re = 1 := by
      rw [← Complex.add_re, loop_trace_partition I (n + m) ρ, hρ.2]
      norm_num
    have e0 : (Matrix.trace (loopPartialMap I n ρ)).re
        + (Matrix.trace (loopContinueMap I n ρ)).re = 1 := by
      rw [← Complex.add_re, loop_trace_partition I n ρ, hρ.2]
      norm_num
    rw [hsplit2] at e1
    have htele : ∑ k ∈ Finset.range m, (Matrix.trace (loopHaltAt I (n + k) ρ)).re
        = (Matrix.trace (loopContinueMap I n ρ)).re
          - (Matrix.trace (loopContinueMap I (n + m) ρ)).re := by
      linarith
    have hnonneg : (0:ℝ) ≤ (Matrix.trace (loopContinueMap I (n + m) ρ)).re :=
      complex_re_nonneg_of_le (loopContinueMap_posSemidef I (n + m) hρ.1).trace_nonneg
    rw [htr, htele]
    linarith [hgeo n]
  · have hle : ∀ n, loopPending I ρ n ≤ ENNReal.ofReal (q ^ n) := fun n =>
      ENNReal.ofReal_le_ofReal (hgeo n)
    have hlim0 : Filter.Tendsto (fun n => ENNReal.ofReal (q ^ n)) Filter.atTop (nhds 0) := by
      simpa using! ((ENNReal.continuous_ofReal.continuousAt.tendsto).comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
    have hzero : loopNeverMass I ρ ≤ 0 :=
      ge_of_tendsto hlim0 (Filter.Eventually.of_forall fun n =>
        le_trans (iInf_le (f := loopPending I ρ) n) (hle n))
    exact le_antisymm hzero (by simp)
  · refine le_trans (ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hgeo k)) ?_
    have hsum : ∑' k : ℕ, ENNReal.ofReal (q ^ k) = ENNReal.ofReal ((1 - q)⁻¹) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hq0 k)
        (summable_geometric_of_lt_one hq0 hq1),
        tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq0])]
    rw [hsum]

@[reducible] def refBlock {D r : ℕ} (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (s t : Fin r) :
    Operator D := fun i j => X (i, s) (j, t)

theorem tensorLeft_diag_trace {D r : ℕ} (T : Operator D →ₗ[ℂ] Operator D)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (s t : Fin r) :
    Matrix.trace (T (refBlock X s t)) = ∑ a : Fin D, tensorLeft T X (a, s) (a, t) := by
  simp [refBlock, Matrix.trace, tensorLeft]

theorem partialTraceFirst_tensorLeft {D r : ℕ} (T : Operator D →ₗ[ℂ] Operator D)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (s t : Fin r) :
    partialTraceFirst (tensorLeft T X) s t = Matrix.trace (T (refBlock X s t)) := by
  simp [partialTraceFirst, Matrix.traceLeft, tensorLeft, refBlock, Matrix.trace]

theorem partialTraceFirst_refBlock {D r : ℕ}
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (s t : Fin r) :
    partialTraceFirst X s t = Matrix.trace (refBlock X s t) := by
  simp [partialTraceFirst, Matrix.traceLeft, refBlock, Matrix.trace]

theorem tendsto_tensorLeft_of {D r : ℕ} {F : ℕ → (Operator D →ₗ[ℂ] Operator D)}
    {T : Operator D →ₗ[ℂ] Operator D} (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (h : ∀ Y : Operator D, Filter.Tendsto (fun n => F n Y) Filter.atTop (nhds (T Y))) :
    Filter.Tendsto (fun n => tensorLeft (F n) X) Filter.atTop (nhds (tensorLeft T X)) := by
  rw [tendsto_matrix_iff_entrywise]
  intro x y
  exact (tendsto_matrix_iff_entrywise.mp (h (fun i j => X (i, x.2) (j, y.2)))) x.1 y.1

private theorem abs_sum_le_sqrt_sums {D : ℕ} (u v : Fin D → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a) :
    |∑ a, Real.sqrt (u a * v a)| ≤ Real.sqrt (∑ a, u a) * Real.sqrt (∑ a, v a) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (u a)) (fun a => Real.sqrt (v a))
  have hf : ∀ a : Fin D, Real.sqrt (u a) * Real.sqrt (v a) = Real.sqrt (u a * v a) := fun a =>
    (Real.sqrt_mul (hu a) (v a)).symm
  rw [Finset.sum_congr rfl (fun a _ => hf a)] at hcs
  have h2u : ∑ a, (Real.sqrt (u a)) ^ 2 = ∑ a, u a :=
    Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hu a)
  have h2v : ∑ a, (Real.sqrt (v a)) ^ 2 = ∑ a, v a :=
    Finset.sum_congr rfl fun a _ => Real.sq_sqrt (hv a)
  rw [h2u, h2v] at hcs
  have huu : (0 : ℝ) ≤ ∑ a, u a := Finset.sum_nonneg fun a _ => hu a
  have hvv : (0 : ℝ) ≤ ∑ a, v a := Finset.sum_nonneg fun a _ => hv a
  have habs : |∑ a, Real.sqrt (u a * v a)|
      = Real.sqrt ((∑ a, Real.sqrt (u a * v a)) ^ 2) := by
    rw [← sq_abs (∑ a, Real.sqrt (u a * v a)), Real.sqrt_sq (abs_nonneg _)]
  calc |∑ a, Real.sqrt (u a * v a)|
      = Real.sqrt ((∑ a, Real.sqrt (u a * v a)) ^ 2) := habs
    _ ≤ Real.sqrt ((∑ a, u a) * (∑ a, v a)) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ a, u a) * Real.sqrt (∑ a, v a) :=
        Real.sqrt_mul huu (∑ a, v a)

private theorem abs_trace_continue_refBlock {D r : ℕ} (I : Instrument Bool D D) {q : ℝ}
    (hq0 : 0 ≤ q) {X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ} (hX : X.PosSemidef)
    (htrX : Matrix.trace X = 1)
    (hcontr : ∀ Y : Operator D, Y.PosSemidef →
      (Matrix.trace (I.branch false Y)).re ≤ q * (Matrix.trace Y).re)
    (s t : Fin r) (n : ℕ) :
    ‖Matrix.trace (loopContinueMap I n (refBlock X s t))‖ ≤ q ^ n := by
  classical
  have hY : (tensorLeft (loopContinueMap I n) X).PosSemidef :=
    tensorLeft_posSemidef (loopContinueMap_completelyPositive I n) hX
  have hu : ∀ a : Fin D, (0 : ℝ) ≤ (tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re :=
    fun a => complex_re_nonneg_of_le (hY.diag_nonneg)
  have hv : ∀ a : Fin D, (0 : ℝ) ≤ (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re :=
    fun a => complex_re_nonneg_of_le (hY.diag_nonneg)

  have hdiag : ∀ u : Fin r, ∑ a : Fin D,
      (tensorLeft (loopContinueMap I n) X (a, u) (a, u)).re ≤ q ^ n := by
    intro u
    have hB : (refBlock X u u).PosSemidef := hX.submatrix fun a => (a, u)
    have hgeo := loop_trace_geometric_psd I hq0 hB hcontr n
    have hsum : ∑ a : Fin D, (tensorLeft (loopContinueMap I n) X (a, u) (a, u)).re
        = (Matrix.trace (loopContinueMap I n (refBlock X u u))).re := by
      rw [tensorLeft_diag_trace (loopContinueMap I n) X u u, Complex.re_sum]
    rw [← hsum] at hgeo
    refine hgeo.trans ?_
    have hBle : (Matrix.trace (refBlock X u u)).re ≤ 1 := by
      have hEq2 : (Matrix.trace (refBlock X u u)).re = ∑ a : Fin D, (X (a, u) (a, u)).re := by
        simp [refBlock, Matrix.trace, Complex.re_sum]
      have hfull : (Matrix.trace X).re = ∑ r' : Fin r, ∑ a : Fin D, (X (a, r') (a, r')).re := by
        simp [Matrix.trace, Complex.re_sum, Fintype.sum_prod_type]
        exact (Finset.sum_comm).symm
      have hslice : ∑ a : Fin D, (X (a, u) (a, u)).re
          ≤ ∑ r' : Fin r, ∑ a : Fin D, (X (a, r') (a, r')).re :=
        Finset.single_le_sum (f := fun r' => ∑ a : Fin D, (X (a, r') (a, r')).re)
          (fun r' _ => Finset.sum_nonneg fun a _ =>
            complex_re_nonneg_of_le (hX.diag_nonneg)) (Finset.mem_univ u)
      rw [hEq2]
      calc ∑ a : Fin D, (X (a, u) (a, u)).re
          ≤ ∑ r' : Fin r, ∑ a : Fin D, (X (a, r') (a, r')).re := hslice
        _ = (Matrix.trace X).re := hfull.symm
        _ = 1 := by rw [htrX]; norm_num
    exact (mul_le_mul_of_nonneg_left hBle (pow_nonneg hq0 n)).trans
      (le_of_eq (mul_one (q ^ n)))

  have hentry : ∀ a : Fin D, ‖tensorLeft (loopContinueMap I n) X (a, s) (a, t)‖
      ≤ Real.sqrt ((tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re
          * (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re) := by
    intro a
    have hsq : Complex.normSq (tensorLeft (loopContinueMap I n) X (a, s) (a, t))
        ≤ (tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re
          * (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re :=
      posSemidef_abs_sq_le (N := tensorLeft (loopContinueMap I n) X) hY (a, s) (a, t)
    rw [← Complex.sq_norm] at hsq
    refine le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
    nlinarith [hsq, Real.sq_sqrt (mul_nonneg (hu a) (hv a))]
  calc ‖Matrix.trace (loopContinueMap I n (refBlock X s t))‖
      = ‖∑ a : Fin D, tensorLeft (loopContinueMap I n) X (a, s) (a, t)‖ := by
        rw [← tensorLeft_diag_trace (loopContinueMap I n) X s t]
    _ ≤ ∑ a : Fin D, ‖tensorLeft (loopContinueMap I n) X (a, s) (a, t)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a : Fin D, Real.sqrt ((tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re
          * (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re) :=
        Finset.sum_le_sum fun a _ => hentry a
    _ ≤ Real.sqrt (∑ a : Fin D, (tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re)
          * Real.sqrt (∑ a : Fin D, (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re) := by
        refine le_trans (le_abs_self _) ?_
        exact abs_sum_le_sqrt_sums _ _ hu hv
    _ ≤ q ^ n := by
        have h1 := hdiag s
        have h2 := hdiag t
        have hqnn : (0:ℝ) ≤ q ^ n := pow_nonneg hq0 n
        have hs1 : Real.sqrt (∑ a : Fin D,
            (tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re) ≤ Real.sqrt (q ^ n) :=
          Real.sqrt_le_sqrt h1
        have hs2 : Real.sqrt (∑ a : Fin D,
            (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re) ≤ Real.sqrt (q ^ n) :=
          Real.sqrt_le_sqrt h2
        calc Real.sqrt (∑ a : Fin D,
              (tensorLeft (loopContinueMap I n) X (a, s) (a, s)).re)
              * Real.sqrt (∑ a : Fin D,
              (tensorLeft (loopContinueMap I n) X (a, t) (a, t)).re)
            ≤ Real.sqrt (q ^ n) * Real.sqrt (q ^ n) :=
              mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          _ = q ^ n := Real.mul_self_sqrt hqnn

theorem instrument_loop_reference_cp_limit_and_marginal :
    ∀ (D r : ℕ) (I : Instrument Bool D D) (q : ℝ)
      (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ), 0≤q → q<1 →
      X.PosSemidef → Matrix.trace X=1 →
      (∀ Y : Operator D, Y.PosSemidef →
        (Matrix.trace (I.branch false Y)).re ≤ q*(Matrix.trace Y).re) →
      Filter.Tendsto (fun n => tensorLeft (loopPartialMap I n) X) Filter.atTop
        (nhds (tensorLeft (loopTerminalMap I) X)) ∧
      partialTraceFirst (tensorLeft (loopTerminalMap I) X) = partialTraceFirst X := by
  intro D r I q X hq0 hq1 hX htrX hcontr
  refine ⟨tendsto_tensorLeft_of X (fun Y => loopTerminalMap_tendsto I Y), ?_⟩
  ext s t
  rw [partialTraceFirst_tensorLeft (loopTerminalMap I) X s t, partialTraceFirst_refBlock X s t]

  set B := refBlock X s t with hB
  have hlim1 : Filter.Tendsto (fun n => Matrix.trace (loopPartialMap I n B)) Filter.atTop
      (nhds (Matrix.trace (loopTerminalMap I B))) :=
    tendsto_matrix_trace (loopTerminalMap_tendsto I B)
  have hbound : ∀ n : ℕ, ‖Matrix.trace (loopContinueMap I n B)‖ ≤ q ^ n :=
    abs_trace_continue_refBlock I hq0 hX htrX hcontr s t
  have hlim0 : Filter.Tendsto (fun n => q ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlim2 : Filter.Tendsto (fun n => Matrix.trace (loopContinueMap I n B)) Filter.atTop
      (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hbound hlim0
  have hsplit : (fun n => Matrix.trace (loopPartialMap I n B))
      = fun n => Matrix.trace B - Matrix.trace (loopContinueMap I n B) := by
    funext n
    rw [eq_sub_iff_add_eq]
    exact loop_trace_partition I n B
  rw [hsplit] at hlim1
  refine tendsto_nhds_unique hlim1 ?_
  have h3 := (tendsto_const_nhds (x := Matrix.trace B)).sub hlim2
  simpa using h3

end Qatlib.Concepts.AdversaryBounds.AdvDuality
