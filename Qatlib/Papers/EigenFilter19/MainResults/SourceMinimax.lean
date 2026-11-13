/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EigenFilter19.MainResults.SourceChebyshevBound
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial

set_option backward.isDefEq.respectTransparency false

/-!
# Chebyshev Minimax Optimality and Exponential Decay of the Eigenstate Filter

This module proves Lemma 2 and Lemma 12 of Lin and Tong on the shifted-Chebyshev
eigenstate filter polynomial `R_ℓ(x; Δ) = Q_ℓ(x; Δ) / Q_ℓ(0; Δ)` over the spectral
exclusion set `D_Δ = [-1, -Δ] ∪ [Δ, 1]` (`0 < Δ < 1`), establishing its minimax
sup-norm optimality among degree-`≤ 2ℓ` polynomials normalized by `p(0) = 1`, its
`2 e^{-√2 ℓ Δ}` suppression bound for `0 < Δ ≤ 1 / √12`, its unit-interval bound
`|R_ℓ(x; Δ)| ≤ 1`, and the outside-`D_Δ` extremal dominance of `Q_ℓ`.

## Main statements

* `source_lemma2_minimax`: Lemma 2(i), feasibility and minimax optimality of `Rpoly ℓ Δ`
  on `spectralSet Δ`.
* `source_lemma2_decay`: Lemma 2(ii), `|(Rpoly ℓ Δ).eval x| ≤ 2 * exp(-√2 * ℓ * Δ)` on
  `spectralSet Δ` for `0 < Δ ≤ (√12)⁻¹`.
* `source_lemma2_unit`: Lemma 2(iii), `|(Rpoly ℓ Δ).eval x| ≤ 1` for `|x| ≤ 1`.
* `source_lemma12_extremal`: Lemma 12, `|p.eval x| ≤ |(Qpoly ℓ Δ).eval x|` outside
  `spectralSet Δ` whenever `deg p ≤ 2ℓ` and `|p| ≤ 1` on `spectralSet Δ`.

## References

* [Lin and Tong, 2020][LinTong2020EigenFilter], Lemma 2 (p. 8) and Lemma 12
  (Appendix E, p. 31).
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Classical BigOperators

namespace Qatlib.Papers.EigenFilter19.MainResults

/-- The paper's `D_Δ = [-1,-Δ] ∪ [Δ,1]`. -/
def spectralSet (Δ : ℝ) : Set ℝ := Set.Icc (-1) (-Δ) ∪ Set.Icc Δ 1

/-- The paper's `Q_ℓ(x;Δ) = T_ℓ(-1 + 2(x²-Δ²)/(1-Δ²))`, as a polynomial in `x`. -/
noncomputable def Qpoly (ℓ : ℕ) (Δ : ℝ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (ℓ : ℤ)).comp
    (Polynomial.C (-1) + Polynomial.C 2 *
      (Polynomial.X ^ 2 - Polynomial.C (Δ ^ 2)) *
      Polynomial.C ((1 - Δ ^ 2)⁻¹))

/-- The paper's extremal polynomial `R_ℓ(x;Δ) = Q_ℓ(x;Δ) / Q_ℓ(0;Δ)`. -/
noncomputable def Rpoly (ℓ : ℕ) (Δ : ℝ) : Polynomial ℝ :=
  Polynomial.C ((Qpoly ℓ Δ).eval 0)⁻¹ * Qpoly ℓ Δ

private def shift (Δ x : ℝ) : ℝ := -1 + 2 * (x ^ 2 - Δ ^ 2) / (1 - Δ ^ 2)

private lemma gap_pos {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) : 0 < 1 - Δ ^ 2 := by
  nlinarith

private lemma eval_Q (ℓ : ℕ) (Δ x : ℝ) :
    (Qpoly ℓ Δ).eval x = (Chebyshev.T ℝ (ℓ : ℤ)).eval (shift Δ x) := by
  simp [Qpoly, shift, div_eq_mul_inv]

private lemma degree_Q (ℓ : ℕ) (Δ : ℝ) :
    (Qpoly ℓ Δ).natDegree ≤ 2 * ℓ := by
  have hi : (C (-1 : ℝ) + C 2 * (X ^ 2 - C (Δ ^ 2)) *
      C ((1 - Δ ^ 2)⁻¹)).natDegree ≤ 2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · apply (natDegree_mul_C_le _ _).trans
      apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_sub_le _ _).trans
      simp
  exact natDegree_comp_le.trans (by
    simpa only [Chebyshev.natDegree_T, Int.natAbs_natCast, mul_comm] using
      Nat.mul_le_mul_left ℓ hi)

private lemma T_abs_le (ℓ : ℕ) {v : ℝ} (hv : v ∈ Set.Icc (-1) 1) :
    |(Chebyshev.T ℝ (ℓ : ℤ)).eval v| ≤ 1 := by
  rw [← Real.cos_arccos hv.1 hv.2, Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

private lemma T_ge_one (ℓ : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    1 ≤ (Chebyshev.T ℝ (ℓ : ℤ)).eval v := by
  rw [← Real.cosh_arcosh hv, Chebyshev.T_real_cosh]
  exact Real.one_le_cosh _

private lemma T_mono (ℓ : ℕ) {v w : ℝ} (hv : 1 ≤ v) (hvw : v ≤ w) :
    (Chebyshev.T ℝ (ℓ : ℤ)).eval v ≤ (Chebyshev.T ℝ (ℓ : ℤ)).eval w := by
  have hw : 1 ≤ w := hv.trans hvw
  rw [← Real.cosh_arcosh hv, Chebyshev.T_real_cosh,
    ← Real.cosh_arcosh hw, Chebyshev.T_real_cosh]
  simp only [Int.cast_natCast]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg hv)),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg hw))]
  exact mul_le_mul_of_nonneg_left
    ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hvw) (Nat.cast_nonneg _)

private lemma T_abs_neg (ℓ : ℕ) (v : ℝ) :
    |(Chebyshev.T ℝ (ℓ : ℤ)).eval (-v)| = |(Chebyshev.T ℝ (ℓ : ℤ)).eval v| := by
  rw [Chebyshev.T_eval_neg, abs_mul]
  simp

private lemma spectral_sq {Δ x : ℝ} (h0 : 0 < Δ) (hx : x ∈ spectralSet Δ) :
    Δ ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 := by
  rcases hx with hx | hx <;> rcases hx with ⟨ha, hb⟩ <;> constructor <;> nlinarith

private lemma spectral_of_abs {Δ x : ℝ} (hx : |x| ≤ 1) (hd : Δ ≤ |x|) :
    x ∈ spectralSet Δ := by
  rcases le_total 0 x with hp | hn
  · exact Or.inr ⟨by simpa [abs_of_nonneg hp] using hd,
      by simpa [abs_of_nonneg hp] using hx⟩
  · rw [abs_of_nonpos hn] at hx hd
    exact Or.inl ⟨by linarith, by linarith⟩

private lemma Q_bound (ℓ : ℕ) {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1)
    {x : ℝ} (hx : x ∈ spectralSet Δ) : |(Qpoly ℓ Δ).eval x| ≤ 1 := by
  rw [eval_Q]
  apply T_abs_le
  have hd := gap_pos h0 h1
  obtain ⟨ha, hb⟩ := spectral_sq h0 hx
  constructor <;> dsimp [shift]
  · have := (div_nonneg (by linarith : 0 ≤ 2 * (x ^ 2 - Δ ^ 2)) hd.le)
    linarith
  · have := (div_le_iff₀ hd).mpr (by nlinarith :
      2 * (x ^ 2 - Δ ^ 2) ≤ 2 * (1 - Δ ^ 2))
    linarith

private lemma origin_arg {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) :
    1 ≤ -shift Δ 0 := by
  have hd := gap_pos h0 h1
  dsimp [shift]
  have := div_nonpos_of_nonpos_of_nonneg (by nlinarith : 2 * (0 ^ 2 - Δ ^ 2) ≤ 0) hd.le
  linarith

private lemma Q_origin (ℓ : ℕ) {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) :
    |(Qpoly ℓ Δ).eval 0| = (Chebyshev.T ℝ (ℓ : ℤ)).eval (-shift Δ 0) := by
  rw [eval_Q, ← T_abs_neg ℓ (shift Δ 0)]
  exact abs_of_nonneg (by linarith [T_ge_one ℓ (origin_arg h0 h1)])

private lemma Q_origin_ge (ℓ : ℕ) {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) :
    1 ≤ |(Qpoly ℓ Δ).eval 0| := by
  rw [Q_origin ℓ h0 h1]
  exact T_ge_one ℓ (origin_arg h0 h1)

private lemma eval_R_abs (ℓ : ℕ) (Δ x : ℝ) :
    |(Rpoly ℓ Δ).eval x| = |(Qpoly ℓ Δ).eval x| / |(Qpoly ℓ Δ).eval 0| := by
  simp [Rpoly, abs_mul, div_eq_mul_inv, mul_comm]

private def node (ℓ : ℕ) (Δ : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (Δ ^ 2 + (1 - Δ ^ 2) * (1 + Real.cos ((k : ℝ) * Real.pi / ℓ)) / 2)

private lemma node_properties (ℓ : ℕ) {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ < 1) (k : ℕ) :
    Δ ≤ node ℓ Δ k ∧ node ℓ Δ k ≤ 1 ∧
      (node ℓ Δ k) ^ 2 =
        Δ ^ 2 + (1 - Δ ^ 2) * (1 + Real.cos ((k : ℝ) * Real.pi / ℓ)) / 2 := by
  have hd := gap_pos h0 h1
  have hc := Real.cos_le_one ((k : ℝ) * Real.pi / ℓ)
  have hc' := Real.neg_one_le_cos ((k : ℝ) * Real.pi / ℓ)
  have hr : 0 ≤ Δ ^ 2 + (1 - Δ ^ 2) *
      (1 + Real.cos ((k : ℝ) * Real.pi / ℓ)) / 2 := by
    nlinarith [mul_nonneg hd.le (by linarith :
      0 ≤ 1 + Real.cos ((k : ℝ) * Real.pi / ℓ))]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (Δ ^ 2 + (1 - Δ ^ 2) *
      (1 + Real.cos ((k : ℝ) * Real.pi / ℓ)) / 2)
  dsimp [node]
  exact ⟨by nlinarith, by nlinarith, hs⟩

private lemma node_strictAnti {ℓ : ℕ} (hl : 0 < ℓ) {Δ : ℝ}
    (h0 : 0 < Δ) (h1 : Δ < 1) :
    StrictAnti (fun k : Fin (ℓ + 1) => node ℓ Δ k) := by
  have hlr : (0 : ℝ) < ℓ := by exact_mod_cast hl
  have angle : ∀ k : Fin (ℓ + 1), (k : ℝ) * Real.pi / ℓ ∈ Set.Icc 0 Real.pi := by
    intro k
    have hk : (k : ℝ) ≤ ℓ := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
    constructor
    · positivity
    · apply (div_le_iff₀ hlr).mpr
      nlinarith [Real.pi_pos]
  intro i j hij
  have hijr : (i : ℝ) < j := by exact_mod_cast hij
  have ha : (i : ℝ) * Real.pi / ℓ < (j : ℝ) * Real.pi / ℓ := by
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hijr Real.pi_pos) hlr
  have hc := Real.strictAntiOn_cos (angle i) (angle j) ha
  obtain ⟨hi0, _, hi2⟩ := node_properties ℓ h0 h1 i
  obtain ⟨hj0, _, hj2⟩ := node_properties ℓ h0 h1 j
  have hd := gap_pos h0 h1
  nlinarith

private lemma node_eval {ℓ : ℕ} (hl : 0 < ℓ) {Δ : ℝ}
    (h0 : 0 < Δ) (h1 : Δ < 1) (k : ℕ) :
    (Qpoly ℓ Δ).eval (node ℓ Δ k) = (-1 : ℝ) ^ k ∧
    (Qpoly ℓ Δ).eval (-node ℓ Δ k) = (-1 : ℝ) ^ k := by
  have hd := ne_of_gt (gap_pos h0 h1)
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  have hs : shift Δ (node ℓ Δ k) = Real.cos ((k : ℝ) * Real.pi / ℓ) := by
    dsimp [shift]
    rw [(node_properties ℓ h0 h1 k).2.2]
    field_simp
    nlinarith
  have he : (Qpoly ℓ Δ).eval (node ℓ Δ k) = (-1 : ℝ) ^ k := by
    rw [eval_Q, hs, Chebyshev.T_real_cos]
    simp only [Int.cast_natCast]
    rw [show (ℓ : ℝ) * ((k : ℝ) * Real.pi / ℓ) = (k : ℝ) * Real.pi by
      field_simp]
    exact Real.cos_nat_mul_pi k
  refine ⟨he, ?_⟩
  simpa only [eval_Q, shift, neg_sq] using he

private lemma root_between {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : a < b) (hs : f a * f b < 0) :
    ∃ r ∈ Set.Ioo a b, f r = 0 := by
  have hz : 0 ∈ f '' Set.Icc a b := by
    rcases mul_neg_iff.mp hs with h | h
    · exact intermediate_value_Icc' hab.le hf.continuousOn ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hab.le hf.continuousOn ⟨h.1.le, h.2.le⟩
  obtain ⟨r, hr, he⟩ := hz
  refine ⟨r, ⟨lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_⟩, he⟩
  · intro h
    have : f a = 0 := by simpa [h] using he
    simp [this] at hs
  · intro h
    have : f b = 0 := by simpa [← h] using he
    simp [this] at hs

private lemma alternating_roots {ℓ : ℕ} {nodes : Fin (ℓ + 1) → ℝ}
    (hn : StrictAnti nodes) {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ k : Fin (ℓ + 1), 0 < (-1 : ℝ) ^ (k : ℕ) * f (nodes k)) :
    ∃ r : Fin ℓ → ℝ, StrictAnti r ∧
      ∀ i, r i ∈ Set.Ioo (nodes i.succ) (nodes i.castSucc) ∧ f (r i) = 0 := by
  have hex : ∀ i : Fin ℓ, ∃ r ∈ Set.Ioo (nodes i.succ) (nodes i.castSucc), f r = 0 := by
    intro i
    apply root_between hf (hn (by simp))
    have ha := hs i.castSucc
    have hb := hs i.succ
    simp only [Fin.val_castSucc, Fin.val_succ, pow_succ, mul_neg_one] at ha hb
    have hprod := mul_pos ha hb
    have hsq : ((-1 : ℝ) ^ (i : ℕ)) * ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have he : (((-1 : ℝ) ^ (i : ℕ)) * f (nodes i.castSucc)) *
        (-((-1 : ℝ) ^ (i : ℕ)) * f (nodes i.succ)) =
        -(f (nodes i.succ) * f (nodes i.castSucc)) := by
      calc
        _ = -(((-1 : ℝ) ^ (i : ℕ)) * ((-1 : ℝ) ^ (i : ℕ))) *
            (f (nodes i.succ) * f (nodes i.castSucc)) := by ring
        _ = _ := by rw [hsq]; ring
    linarith
  choose r hr he using hex
  refine ⟨r, ?_, fun i => ⟨hr i, he i⟩⟩
  intro i j hij
  have hnij : nodes j.castSucc ≤ nodes i.succ := hn.antitone (by
    simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
      Nat.succ_le_of_lt hij)
  exact (hr j).2.trans_le hnij |>.trans (hr i).1

/-- **Lemma 12**: for any real polynomial `p` of degree at most `2ℓ` that is bounded
by `1` on `D_Δ`, `Q_ℓ` dominates `p` in absolute value everywhere outside `D_Δ`. -/
theorem source_lemma12_extremal (ℓ : ℕ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (p : Polynomial ℝ) (hpdeg : p.degree ≤ (2 * ℓ : WithBot ℕ))
    (hpb : ∀ x ∈ spectralSet Δ, |p.eval x| ≤ 1) :
    ∀ x : ℝ, x ∉ spectralSet Δ → |p.eval x| ≤ |(Qpoly ℓ Δ).eval x| := by
  intro y hy
  have hone : (1 : ℝ) ∈ spectralSet Δ := Or.inr ⟨hΔ1.le, le_rfl⟩
  by_cases hl : ℓ = 0
  · subst ℓ
    have hp : p = C (p.coeff 0) := eq_C_of_degree_le_zero (by simpa using hpdeg)
    calc
      |p.eval y| = |p.eval 1| := by rw [hp]; simp
      _ ≤ |(Qpoly 0 Δ).eval y| := by simpa [Qpoly] using hpb 1 hone
  have hlpos : 0 < ℓ := Nat.pos_of_ne_zero hl
  by_contra hnot
  have hbig : |(Qpoly ℓ Δ).eval y| < |p.eval y| := lt_of_not_ge hnot
  have hpy : p.eval y ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hbig
    exact (not_lt_of_ge (abs_nonneg _)) hbig
  let lam := (Qpoly ℓ Δ).eval y / p.eval y
  have hlam : |lam| < 1 := by
    dsimp [lam]
    rw [abs_div]
    exact (div_lt_one (abs_pos.mpr hpy)).mpr hbig
  let h := Qpoly ℓ Δ - C lam * p
  have hsign : ∀ k : Fin (ℓ + 1), ∀ z : ℝ,
      z ∈ spectralSet Δ → (Qpoly ℓ Δ).eval z = (-1 : ℝ) ^ (k : ℕ) →
      0 < (-1 : ℝ) ^ (k : ℕ) * h.eval z := by
    intro k z hz he
    have hb : |lam * p.eval z| < 1 := calc
      _ = |lam| * |p.eval z| := abs_mul _ _
      _ ≤ |lam| * 1 := mul_le_mul_of_nonneg_left (hpb z hz) (abs_nonneg _)
      _ < 1 := by simpa using hlam
    have hs : |(-1 : ℝ) ^ (k : ℕ)| = 1 := by simp
    have hs2 : ((-1 : ℝ) ^ (k : ℕ)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hb' : |(-1 : ℝ) ^ (k : ℕ) * (lam * p.eval z)| < 1 := by
      simpa only [abs_mul, hs, one_mul] using hb
    dsimp [h]
    simp only [eval_sub, eval_mul, eval_C, he]
    nlinarith [(abs_lt.mp hb').2]
  let nodes : Fin (ℓ + 1) → ℝ := fun k => node ℓ Δ k
  have hnodes := node_strictAnti hlpos hΔ0 hΔ1
  have hpos : ∀ k : Fin (ℓ + 1), nodes k ∈ spectralSet Δ := by
    intro k
    exact Or.inr ⟨(node_properties ℓ hΔ0 hΔ1 k).1,
      (node_properties ℓ hΔ0 hΔ1 k).2.1⟩
  have hneg : ∀ k : Fin (ℓ + 1), -nodes k ∈ spectralSet Δ := by
    intro k
    have hk := node_properties ℓ hΔ0 hΔ1 k
    exact Or.inl ⟨by linarith [hk.2.1], by linarith [hk.1]⟩
  obtain ⟨rp, hip, hrp⟩ := alternating_roots hnodes h.continuous
    (fun k => hsign k (nodes k) (hpos k) (node_eval hlpos hΔ0 hΔ1 k).1)
  obtain ⟨rn, hin, hrn⟩ := alternating_roots hnodes
    (h.continuous.comp continuous_neg)
    (fun k => hsign k (-nodes k) (hneg k) (node_eval hlpos hΔ0 hΔ1 k).2)
  simp only [Fin.val_succ, Fin.val_castSucc] at hrp hrn
  have hrpD : ∀ i, rp i ∈ spectralSet Δ := by
    intro i
    exact Or.inr ⟨(node_properties ℓ hΔ0 hΔ1 (i + 1)).1.trans (hrp i).1.1.le,
      (hrp i).1.2.le.trans (node_properties ℓ hΔ0 hΔ1 i).2.1⟩
  have hrnD : ∀ i, -rn i ∈ spectralSet Δ := by
    intro i
    have hi0 := (node_properties ℓ hΔ0 hΔ1 (i + 1)).1
    have hi1 := (node_properties ℓ hΔ0 hΔ1 i).2.1
    exact Or.inl ⟨by linarith [(hrn i).1.2], by linarith [(hrn i).1.1]⟩
  have hsep : ∀ i j, rp i ≠ -rn j := by
    intro i j he
    have hi := (node_properties ℓ hΔ0 hΔ1 (i + 1)).1
    have hj := (node_properties ℓ hΔ0 hΔ1 (j + 1)).1
    linarith [(hrp i).1.1, (hrn j).1.1]
  let roots : Option (Fin ℓ ⊕ Fin ℓ) → ℝ
    | none => y
    | some (.inl i) => rp i
    | some (.inr i) => -rn i
  have hroots : Function.Injective roots := by
    rintro (_ | (i | i)) (_ | (j | j)) he
    all_goals dsimp only [roots] at he
    · rfl
    · exact False.elim (hy (he.symm ▸ hrpD j))
    · exact False.elim (hy (he.symm ▸ hrnD j))
    · exact False.elim (hy (he ▸ hrpD i))
    · exact congrArg (fun k => some (Sum.inl k)) (hip.injective he)
    · exact False.elim (hsep i j he)
    · exact False.elim (hy (he ▸ hrnD i))
    · exact False.elim (hsep j i he.symm)
    · exact congrArg (fun k => some (Sum.inr k)) (hin.injective (neg_injective he))
  have hz : ∀ i, h.eval (roots i) = 0 := by
    rintro (_ | (i | i))
    · dsimp [roots, h, lam]
      simp only [eval_sub, eval_mul, eval_C, div_mul_cancel₀ _ hpy, sub_self]
    · exact (hrp i).2
    · exact (hrn i).2
  have hdeg : h.natDegree ≤ 2 * ℓ :=
    (natDegree_sub_le _ _).trans (max_le (degree_Q ℓ Δ)
      ((natDegree_C_mul_le _ _).trans (natDegree_le_of_degree_le hpdeg)))
  have hzero : h = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero h hroots hz (by
    simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] using
      (show h.natDegree < ℓ + ℓ + 1 by omega))
  have hs := hsign ⟨0, by omega⟩ (nodes ⟨0, by omega⟩) (hpos ⟨0, by omega⟩)
    (node_eval hlpos hΔ0 hΔ1 0).1
  simp [hzero] at hs

/-- **Lemma 2(i)**: `R_ℓ(·;Δ)` is feasible (`deg ≤ 2ℓ`, value `1` at the origin) and
minimises the sup-norm over `D_Δ` among all degree-`≤ 2ℓ` polynomials normalised to
one at the origin. -/
theorem source_lemma2_minimax (ℓ : ℕ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    (Rpoly ℓ Δ).eval 0 = 1 ∧
    (Rpoly ℓ Δ).degree ≤ (2 * ℓ : WithBot ℕ) ∧
    ∀ p : Polynomial ℝ, p.degree ≤ (2 * ℓ : WithBot ℕ) → p.eval 0 = 1 →
      ∀ M : ℝ, (∀ y ∈ spectralSet Δ, |p.eval y| ≤ M) →
        ∀ x ∈ spectralSet Δ, |(Rpoly ℓ Δ).eval x| ≤ M := by
  have hA := Q_origin_ge ℓ hΔ0 hΔ1
  have hApos : 0 < |(Qpoly ℓ Δ).eval 0| := by linarith
  have hAne : (Qpoly ℓ Δ).eval 0 ≠ 0 := abs_pos.mp hApos
  refine ⟨?_, degree_le_of_natDegree_le
    ((natDegree_C_mul_le _ _).trans (degree_Q ℓ Δ)), ?_⟩
  · simpa only [Rpoly, eval_mul, eval_C] using inv_mul_cancel₀ hAne
  · intro p hpdeg hp0 M hM x hx
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 (Or.inr ⟨hΔ1.le, le_rfl⟩))
    have hb : 1 / |(Qpoly ℓ Δ).eval 0| ≤ M := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have he : 0 < M + ε := by linarith
      have hsdeg : (C ((M + ε)⁻¹) * p).degree ≤ (2 * ℓ : WithBot ℕ) :=
        degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans
          (natDegree_le_of_degree_le hpdeg))
      have hsb : ∀ z ∈ spectralSet Δ, |(C ((M + ε)⁻¹) * p).eval z| ≤ 1 := by
        intro z hz
        simp only [eval_mul, eval_C, abs_mul, abs_inv, abs_of_pos he]
        calc
          (M + ε)⁻¹ * |p.eval z| ≤ (M + ε)⁻¹ * (M + ε) :=
            mul_le_mul_of_nonneg_left ((hM z hz).trans (by linarith)) (inv_nonneg.mpr he.le)
          _ = 1 := inv_mul_cancel₀ he.ne'
      have hzero : (0 : ℝ) ∉ spectralSet Δ := by
        intro hz
        rcases hz with hz | hz <;> have := hz.2 <;> have := hz.1 <;> linarith
      have hb := source_lemma12_extremal ℓ hΔ0 hΔ1 _ hsdeg hsb 0 hzero
      simp only [eval_mul, eval_C, hp0, mul_one, abs_inv, abs_of_pos he] at hb
      apply (div_le_iff₀ hApos).mpr
      have hb' := (div_le_iff₀ he).mp
        (show 1 / (M + ε) ≤ |(Qpoly ℓ Δ).eval 0| by simpa only [one_div] using hb)
      nlinarith
    rw [eval_R_abs]
    exact (div_le_div_of_nonneg_right (Q_bound ℓ hΔ0 hΔ1 hx) hApos.le).trans hb

/-- **Lemma 2(ii)**: for `0 < Δ ≤ 1/√12` and `x ∈ D_Δ`,
`|R_ℓ(x;Δ)| ≤ 2 e^{-√2 ℓ Δ}`. -/
theorem source_lemma2_decay (ℓ : ℕ) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ1 : Δ ≤ (Real.sqrt 12)⁻¹) :
    ∀ x ∈ spectralSet Δ,
      |(Rpoly ℓ Δ).eval x| ≤ 2 * Real.exp (-(Real.sqrt 2) * (ℓ : ℝ) * Δ) := by
  have hs12 : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  have hs12sq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have hp : Δ * Real.sqrt 12 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hΔ1 hs12.le
    simpa only [inv_mul_cancel₀ hs12.ne'] using this
  have hp2 : (Δ * Real.sqrt 12) ^ 2 ≤ 1 := by
    nlinarith [mul_pos hΔ0 hs12]
  have hd2 : Δ ^ 2 ≤ 1 / 12 := by
    nlinarith [show (Δ * Real.sqrt 12) ^ 2 = Δ ^ 2 * 12 by rw [mul_pow, hs12sq]]
  have hd1 : Δ < 1 := by nlinarith
  have hd := gap_pos hΔ0 hd1
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hδ : 2 * Δ ^ 2 ≤ 3 - 2 * Real.sqrt 2 := by
    have : 2 * Real.sqrt 2 ≤ 17 / 6 := by nlinarith
    nlinarith
  have hlow := source_lemma13_chebyshev_lower ℓ (by positivity : 0 ≤ 2 * Δ ^ 2) hδ
  have harg : 1 + 2 * Δ ^ 2 ≤ -shift Δ 0 := by
    have hdiv : 2 * Δ ^ 2 ≤ 2 * Δ ^ 2 / (1 - Δ ^ 2) :=
      (le_div_iff₀ hd).mpr (by nlinarith [sq_nonneg (Δ ^ 2)])
    rw [show -shift Δ 0 = 1 + 2 * Δ ^ 2 / (1 - Δ ^ 2) by dsimp [shift]; ring]
    linarith
  have hmono := T_mono ℓ (by nlinarith : 1 ≤ 1 + 2 * Δ ^ 2) harg
  have hroot : Real.sqrt (2 * Δ ^ 2) = Real.sqrt 2 * Δ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hΔ0.le]
  have hden : (1 / 2 : ℝ) * Real.exp (Real.sqrt 2 * (ℓ : ℝ) * Δ) ≤
      |(Qpoly ℓ Δ).eval 0| := by
    rw [Q_origin ℓ hΔ0 hd1]
    rw [hroot] at hlow
    rw [show (ℓ : ℝ) * (Real.sqrt 2 * Δ) = Real.sqrt 2 * (ℓ : ℝ) * Δ by ring] at hlow
    exact hlow.trans hmono
  intro x hx
  rw [eval_R_abs]
  have hA : 0 < |(Qpoly ℓ Δ).eval 0| := by linarith [Q_origin_ge ℓ hΔ0 hd1]
  apply (div_le_iff₀ hA).mpr
  have hprod : Real.exp (Real.sqrt 2 * (ℓ : ℝ) * Δ) *
      Real.exp (-(Real.sqrt 2) * (ℓ : ℝ) * Δ) = 1 := by
    rw [show -(Real.sqrt 2) * (ℓ : ℝ) * Δ = -(Real.sqrt 2 * (ℓ : ℝ) * Δ) by ring,
      Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _)]
  have := mul_le_mul_of_nonneg_left hden
    (Real.exp_nonneg (-(Real.sqrt 2) * (ℓ : ℝ) * Δ))
  nlinarith [Q_bound ℓ hΔ0 hd1 hx]

/-- **Lemma 2(iii)**: `|R_ℓ(x;Δ)| ≤ 1` for every `|x| ≤ 1`. -/
theorem source_lemma2_unit (ℓ : ℕ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∀ x : ℝ, |x| ≤ 1 → |(Rpoly ℓ Δ).eval x| ≤ 1 := by
  intro x hx
  have hA := Q_origin_ge ℓ hΔ0 hΔ1
  have hApos : 0 < |(Qpoly ℓ Δ).eval 0| := by linarith
  rw [eval_R_abs, div_le_one hApos]
  by_cases hd : Δ ≤ |x|
  · exact (Q_bound ℓ hΔ0 hΔ1 (spectral_of_abs hx hd)).trans hA
  · have hxd : |x| < Δ := lt_of_not_ge hd
    have hx2 : x ^ 2 ≤ Δ ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hgap := gap_pos hΔ0 hΔ1
    have harg : 1 ≤ -shift Δ x := by
      have := div_nonpos_of_nonpos_of_nonneg
        (by linarith : 2 * (x ^ 2 - Δ ^ 2) ≤ 0) hgap.le
      dsimp [shift]
      linarith
    have harg' : -shift Δ x ≤ -shift Δ 0 := by
      have := div_le_div_of_nonneg_right
        (by nlinarith [sq_nonneg x] : 2 * (0 ^ 2 - Δ ^ 2) ≤ 2 * (x ^ 2 - Δ ^ 2)) hgap.le
      dsimp [shift]
      linarith
    rw [eval_Q, ← T_abs_neg ℓ (shift Δ x),
      abs_of_nonneg (by linarith [T_ge_one ℓ harg]), Q_origin ℓ hΔ0 hΔ1]
    exact T_mono ℓ harg harg'

end Qatlib.Papers.EigenFilter19.MainResults
