/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrder
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Asymptotics Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology

theorem general_trotter_mass_nonneg {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : 0 ≤ suzukiMass xs := by
  unfold suzukiMass
  exact List.sum_nonneg
      (fun x hx => by obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg Y)

theorem general_trotter_term_norm {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (n : ℕ) :
    ‖t ^ n • suzukiSeries xs n‖ ≤ (|t| * suzukiMass xs) ^ n / (n.factorial : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ |t| ^ n * (suzukiMass xs ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (suzukiSeries_norm_le xs n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem general_trotter_norm_summable {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) :
    Summable (fun n => ‖t ^ n • suzukiSeries xs n‖) := by
  have h : Summable (fun n => (|t| * suzukiMass xs) ^ n / (n.factorial : ℝ)) := by
    simpa only [smul_eq_mul, inv_mul_eq_div] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (|t| * suzukiMass xs)).summable
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (general_trotter_term_norm xs t)

private theorem general_trotter_exp_hasSum (a : ℝ) :
    HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
  simpa only [smul_eq_mul, inv_mul_eq_div, ← Real.exp_eq_exp_ℝ] using!
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a

theorem general_trotter_scalar_tail (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun n : ℕ => a ^ (n + m) / ((n + m).factorial : ℝ)) ∧
    (∑' n : ℕ, a ^ (n + m) / ((n + m).factorial : ℝ)) ≤
      a ^ m / (m.factorial : ℝ) * Real.exp a := by
  have hterm (n : ℕ) : a ^ (n + m) / ((n + m).factorial : ℝ) ≤
      (a ^ m / (m.factorial : ℝ)) * (a ^ n / (n.factorial : ℝ)) := by
    have hfac : (n.factorial : ℝ) * (m.factorial : ℝ) ≤ ((n + m).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n m)
    calc
      _ ≤ a ^ (n + m) / ((n.factorial : ℝ) * (m.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = _ := by rw [pow_add]; ring
  have hg := (general_trotter_exp_hasSum a).mul_left (a ^ m / (m.factorial : ℝ))
  have hs : Summable (fun n : ℕ => a ^ (n + m) / ((n + m).factorial : ℝ)) :=
    hg.summable.of_nonneg_of_le (fun _ => by positivity) hterm
  exact ⟨hs, (hs.tsum_le_tsum hterm hg.summable).trans_eq hg.tsum_eq⟩

theorem general_trotter_taylor_tail {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (m : ℕ) :
    ‖suzukiExponentialWord xs t - ∑ n ∈ Finset.range m, t ^ n • suzukiSeries xs n‖ ≤
      Real.exp (|t| * suzukiMass xs) * (|t| * suzukiMass xs) ^ m / (m.factorial : ℝ) := by
  let f := fun n : ℕ => t ^ n • suzukiSeries xs n
  let a := |t| * suzukiMass xs
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) (general_trotter_mass_nonneg xs)
  have hs := general_trotter_norm_summable xs t
  have hn : Summable (fun n => ‖f (n + m)‖) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have he : suzukiExponentialWord xs t - ∑ n ∈ Finset.range m, f n = ∑' n, f (n + m) := by
    have h : (∑ n ∈ Finset.range m, f n) + (∑' n, f (n + m)) =
        suzukiExponentialWord xs t :=
      (hs.of_norm.sum_add_tsum_nat_add m).trans (suzukiSeries_hasSum xs t).tsum_eq
    calc
      _ = ((∑ n ∈ Finset.range m, f n) + (∑' n, f (n + m))) -
          (∑ n ∈ Finset.range m, f n) := congrArg (fun X => X - ∑ n ∈ Finset.range m, f n) h.symm
      _ = _ := by abel
  rw [he]
  obtain ⟨hscalar, hb⟩ := general_trotter_scalar_tail a ha m
  calc
    _ ≤ ∑' n, ‖f (n + m)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, a ^ (n + m) / ((n + m).factorial : ℝ) :=
      hn.tsum_le_tsum (fun n => general_trotter_term_norm xs t (n + m)) hscalar
    _ ≤ a ^ m / (m.factorial : ℝ) * Real.exp a := hb
    _ = _ := by ring

theorem general_trotter_matched_local_error {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hc : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H^n) :
    ‖suzukiExponentialWord xs t-NormedSpace.exp (t • H)‖ ≤
      2*Real.exp ((suzukiMass xs+‖H‖)*|t|)*
        ((suzukiMass xs+‖H‖)*|t|)^(p+1)/((p+1).factorial : ℝ) := by
  let P := ∑ n ∈ Finset.range (p+1), t^n • suzukiSeries xs n
  have hP : P = ∑ n ∈ Finset.range (p+1), t^n • suzukiSeries [H] n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hc n (by have := Finset.mem_range.mp hn; omega), suzukiSeries_singleton]
  have hx := general_trotter_taylor_tail xs t (p+1)
  have hh := general_trotter_taylor_tail [H] t (p+1)
  have ht :=
      norm_sub_le_norm_sub_add_norm_sub (suzukiExponentialWord xs t) P (NormedSpace.exp (t • H))
  rw [norm_sub_rev P] at ht
  have hmass := general_trotter_mass_nonneg xs
  let a := (suzukiMass xs+‖H‖)*|t|
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hax : |t| *suzukiMass xs ≤ a := by dsimp [a]; nlinarith [abs_nonneg t, norm_nonneg H]
  have hah : |t| *‖H‖ ≤ a := by dsimp [a]; nlinarith [abs_nonneg t]
  have hmono (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
      Real.exp b*b^(p+1)/((p+1).factorial : ℝ) ≤ Real.exp a*a^(p+1)/((p+1).factorial : ℝ) := by
    gcongr
  have hx' := hx.trans (hmono _ (by positivity) hax)
  have hh' : ‖NormedSpace.exp (t • H)-P‖ ≤ Real.exp a*a^(p+1)/((p+1).factorial : ℝ) := by
    rw [hP]
    simpa only [suzukiExponentialWord, suzukiMass, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, List.sum_cons, List.sum_nil, add_zero] using!
      hh.trans (hmono _ (by simp [suzukiMass]; positivity) (by simpa [suzukiMass] using! hah))
  exact (ht.trans (add_le_add hx' hh')).trans_eq (by dsimp [a]; ring)

theorem general_trotter_exp_unitary {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (s : ℝ) (hX : Xᴴ = -X) :
    NormedSpace.exp (s • X) ∈ Matrix.unitaryGroup I ℂ := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (s • X) = -(s • X)
  simp only [star_smul, star_trivial, Matrix.star_eq_conjTranspose, hX, smul_neg]

theorem general_order_actual_word_error_and_cost :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
      (H : Matrix I I ℂ) (p r : ℕ) (t : ℝ),
      (∀ X ∈ xs, Xᴴ = -X) → Hᴴ = -H → 0 < r →
      (∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H^n) →
      let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t/r) • X)))).flatten
      w.prod ∈ Matrix.unitaryGroup I ℂ ∧ w.length = r*xs.length ∧
      ‖w.prod - NormedSpace.exp (t • H)‖ ≤
        2*r*Real.exp ((suzukiMass xs+‖H‖)*|t/r|)*
          ((suzukiMass xs+‖H‖)*|t/r|)^(p+1)/((p+1).factorial : ℝ) := by
  intro I _ _ xs H p r t hxs hH hr hc
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  have hu : suzukiExponentialWord xs (t/r) ∈ Matrix.unitaryGroup I ℂ := by
    apply (Matrix.unitaryGroup I ℂ).list_prod_mem
    intro U hU
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hU
    exact general_trotter_exp_unitary X (t/r) (hxs X hX)
  have he : NormedSpace.exp ((t/r) • H)^r = NormedSpace.exp (t • H) := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    field_simp
  have hw : ((List.replicate r (xs.map (fun X => NormedSpace.exp ((t/r) • X)))).flatten).prod =
      suzukiExponentialWord xs (t/r)^r := by
    simp [List.prod_flatten, suzukiExponentialWord]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]
    exact (Matrix.unitaryGroup I ℂ).pow_mem hu r
  · simp [List.length_flatten]
  · rw [hw, ← he]
    have hh := pf_unitary_power_error _ _ hu (general_trotter_exp_unitary H (t/r) hH) r
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (general_trotter_matched_local_error xs H p (t/r) hc) (Nat.cast_nonneg r)).trans_eq (by ring))

theorem general_trotter_word_contDiff {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : ContDiff ℝ ∞ (suzukiExponentialWord xs) := by
  induction xs with
  | nil => simpa [suzukiExponentialWord] using! (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : Matrix I I ℂ)))
  | cons X xs ih =>
    simpa [suzukiExponentialWord] using! (trotter_exp_contDiff X).mul ih

theorem general_trotter_word_order {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p : ℕ)
    (hc : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H^n) :
    trotterOrder (fun t => suzukiExponentialWord xs t-NormedSpace.exp (t • H)) (p+1) := by
  let L := suzukiMass xs+‖H‖
  have hL : 0 ≤ L := add_nonneg (general_trotter_mass_nonneg xs) (norm_nonneg H)
  let c := 2*Real.exp L*L^(p+1)/((p+1).factorial : ℝ)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c+1, 1, by positivity, by norm_num, ?_⟩
  intro t ht
  have he : Real.exp (L*|t|) ≤ Real.exp L :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right hL ht)
  have hb : 2*Real.exp (L*|t|)*(L*|t|)^(p+1)/((p+1).factorial : ℝ) ≤ c*|t|^(p+1) := by
    dsimp [c]
    rw [mul_pow]
    calc
      _ ≤ 2*Real.exp L*(L^(p+1)*|t|^(p+1))/((p+1).factorial : ℝ) := by gcongr
      _ = _ := by ring
  exact (general_trotter_matched_local_error xs H p t hc).trans
    (hb.trans (by gcongr; linarith))

theorem general_trotter_actual_canonical_consumer {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (p r : ℕ) (t : ℝ)
    (hxs : ∀ X ∈ xs, Xᴴ = -X) (hH : Hᴴ = -H) (hr : 0 < r)
    (hc : ∀ n : ℕ, n ≤ p → suzukiSeries xs n = ((n.factorial : ℝ)⁻¹) • H^n) :
    let S := suzukiExponentialWord xs
    let D := fun s => deriv S s-H*S s
    let w := (List.replicate r (xs.map (fun X => NormedSpace.exp ((t/r) • X)))).flatten
    trotterOrder (fun s => Ring.inverse (S s)*D s) p ∧
    trotterOrder (fun s => D s*Ring.inverse (S s)) p ∧
    trotterOrder (fun s => NormedSpace.exp ((-s) • H)*S s-1) (p+1) ∧
    w.prod ∈ Matrix.unitaryGroup I ℂ ∧ w.length = r*xs.length ∧
    ‖w.prod-NormedSpace.exp (t • H)‖ ≤
      2*r*Real.exp ((suzukiMass xs+‖H‖)*|t/r|)*
        ((suzukiMass xs+‖H‖)*|t/r|)^(p+1)/((p+1).factorial : ℝ) := by
  have h4 := general_trotter_four_order_conditions I H (suzukiExponentialWord xs) p
    (general_trotter_word_contDiff xs) (by simp [suzukiExponentialWord])
  have hT := h4.1.mp (general_trotter_word_order xs H p hc)
  have hE := h4.2.1.mp hT
  have hM := h4.2.2.mp hE
  exact ⟨hT, hE, hM, general_order_actual_word_error_and_cost I xs H p r t hxs hH hr hc⟩

end Qatlib.Concepts.TrotterFormula.GeneralOrder
