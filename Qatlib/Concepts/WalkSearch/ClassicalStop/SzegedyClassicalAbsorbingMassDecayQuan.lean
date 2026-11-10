/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayStat
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
namespace Qatlib.Concepts.WalkSearch.ClassicalStop

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

private theorem sum_unmarked_indicator {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : I → ℝ) :
    (∑ i, if i ∉ S then f i else 0) = ∑ i : Unmarked I S, f i.1 := by
  have h := Finset.sum_subtype (F := inferInstance) (p := fun i : I => i ∉ S)
    (Finset.univ.filter (fun i => i ∉ S)) (by intro i; simp) f
  simpa only [Finset.sum_filter] using h

private theorem restricted_law_step {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (hs : ∀ i j, P i j = P j i)
    (law : ℕ → I → ℝ)
    (hstep : ∀ t j, law (t + 1) j = ∑ i, law t i *
      (if i ∈ S then (if j = i then 1 else 0) else P i j)) (t : ℕ) :
    (fun j : Unmarked I S => (law (t + 1) j.1 : ℂ)) =
      (unmarkedPrincipal P S) *ᵥ (fun j : Unmarked I S => (law t j.1 : ℂ)) := by
  funext j
  have he : law (t + 1) j.1 = ∑ i : Unmarked I S, law t i.1 * P i.1 j.1 := by
    rw [hstep]
    have ht (i : I) : law t i * (if i ∈ S then (if j.1 = i then 1 else 0) else P i j.1) =
        if i ∉ S then law t i * P i j.1 else 0 := by
      by_cases hi : i ∈ S
      · have hji : j.1 ≠ i := by intro h; exact j.2 (h ▸ hi)
        simp [hi, hji]
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => ht i), sum_unmarked_indicator]
  rw [he, Complex.ofReal_sum]
  simp only [Matrix.mulVec, dotProduct, unmarkedPrincipal]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_mul, hs i.1 j.1]
  ring

theorem szegedyClassicalAbsorbingMassDecay : SzegedyClassicalAbsorbingMassDecay := by
  intro I _ _ _ P S δ ε K hδ hδ1 hP hε hεp law hzero hstep
  let U := Unmarked I S
  let A := unmarkedPrincipal P S
  let a := ‖A‖
  let n : ℝ := Fintype.card I
  let m : ℝ := Fintype.card U
  let v := fun t : ℕ => fun j : U => (law t j.1 : ℂ)
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hmn : m ≤ n := by
    dsimp only [m, n, U]
    exact_mod_cast Fintype.card_subtype_le (fun i : I => i ∉ S)
  have ha : 0 ≤ a := norm_nonneg A
  have hnorm : ∀ t : ℕ, ‖toEuclidean_fromVec (v t)‖ ≤ a ^ t * ‖toEuclidean_fromVec (v 0)‖ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hv : v (t + 1) = A *ᵥ v t := restricted_law_step P S hP.2.1 law hstep t
      rw [hv]
      exact (l2_norm_mulVec_fromVec_le A (v t)).trans
        ((mul_le_mul_of_nonneg_left ih ha).trans_eq (by rw [pow_succ]; ring))
  have hvzero : ‖toEuclidean_fromVec (v 0)‖ ^ 2 = m / n ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [v, hzero, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    change m * (1 / n) ^ 2 = _
    ring
  have hvnorm : ‖toEuclidean_fromVec (v K)‖ ^ 2 ≤ (a ^ K) ^ 2 * (m / n ^ 2) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (hnorm K) 2
    simpa only [mul_pow, hvzero] using h
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset U)
    (fun _ => (1 : ℝ)) (fun i => law K i.1)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one] at hcs
  have hsum : ∑ i : U, (law K i.1) ^ 2 = ‖toEuclidean_fromVec (v K)‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hsum] at hcs
  have hscaled := mul_le_mul_of_nonneg_left hvnorm hm
  have hfrac : m / n ≤ 1 := (div_le_one hn).mpr hmn
  have hfrac0 : 0 ≤ m / n := div_nonneg hm hn.le
  have hfrac2 : (m / n) ^ 2 ≤ 1 := by nlinarith
  have hmass : (∑ i : U, law K i.1) ^ 2 ≤ (a ^ K) ^ 2 := by
    have he : m * ((a ^ K) ^ 2 * (m / n ^ 2)) = (a ^ K) ^ 2 * (m / n) ^ 2 := by ring
    rw [he] at hscaled
    exact hcs.trans
        (hscaled.trans ((mul_le_mul_of_nonneg_left hfrac2 (sq_nonneg _)).trans_eq (mul_one _)))
  have hmass' : (∑ i : U, law K i.1) ≤ a ^ K := by nlinarith [pow_nonneg ha K]
  have hgap := (unmarked_principal_gram_and_gap I P S δ hδ hδ1 hP).2.2
  have hab : a ≤ 1 - δ * ε / 2 := by
    have hp := mul_le_mul_of_nonneg_left hεp hδ.le
    have hh := mul_pos hδ hε
    change ‖unmarkedPrincipal P S‖ ≤ _
    nlinarith
  exact hmass'.trans (pow_le_pow_left₀ ha hab K)

end Qatlib.Concepts.WalkSearch.ClassicalStop
