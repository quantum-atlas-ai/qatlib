/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.EffectiveNearOptimalSignWindow
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtSignMaterials
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit
open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit

def separationLevel (δ : ℝ) : ℕ := ⌈128/δ⌉₊

def amplificationLevel (ε : ℝ) : ℕ := ⌈8*Real.log (1/ε)⌉₊

def nearOptimalPolynomial (δ ε : ℝ) : Polynomial ℝ :=
  (spoly (amplificationLevel ε)).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator (separationLevel δ))

theorem log_error_lower {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1/2) :
    1/2 ≤ Real.log (1/ε) := by
  have h := Real.log_le_sub_one_of_pos hε
  simp only [one_div,Real.log_inv]
  linarith

theorem amplification_error {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1/2) :
    2*(3/4:ℝ)^(amplificationLevel ε+1) ≤ ε := by
  have hL := log_error_lower hε hε2
  have hceil := Nat.le_ceil (8*Real.log (1/ε))
  have hbase : (3/4:ℝ) ≤ Real.exp (-1/4) := by
    have h := Real.add_one_le_exp (-1/4)
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/4) hbase (amplificationLevel ε+1)
  rw [← Real.exp_nat_mul] at hp
  have he := Real.exp_le_exp.mpr (show ((amplificationLevel ε+1:ℕ):ℝ)*(-1/4) ≤
      -2*Real.log (1/ε) by dsimp [amplificationLevel]; push_cast; linarith)
  have hid : Real.exp (-2*Real.log (1/ε)) = ε^2 := by
    rw [show -2*Real.log (1/ε) = Real.log ε+Real.log ε by simp only [one_div,Real.log_inv]; ring,
      Real.exp_add,Real.exp_log hε]
    ring
  rw [hid] at he
  have hpow := hp.trans he
  nlinarith

theorem separation_level {δ : ℝ} (hδ : 0 < δ) :
    128 ≤ ((separationLevel δ:ℝ)+1)*δ := by
  have h := Nat.le_ceil (128/δ)
  have hh : 128 ≤ (separationLevel δ:ℝ)*δ :=
    (div_le_iff₀ hδ).mp h
  nlinarith

theorem nearOptimalPolynomial_odd (δ ε x : ℝ) :
    (nearOptimalPolynomial δ ε).eval (-x) = -(nearOptimalPolynomial δ ε).eval x := by
  simp only [nearOptimalPolynomial,Polynomial.eval_comp,Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_odd,spoly_odd]

theorem nearOptimalPolynomial_abs_le (δ ε : ℝ) {x : ℝ} (hx : |x| ≤ 2) :
    |(nearOptimalPolynomial δ ε).eval x| ≤ 1 := by
  simp only [nearOptimalPolynomial,Polynomial.eval_comp]
  exact spoly_abs_le _ _ (abs_le.mp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_abs_le _ hx))

theorem amplifiedSeparator_error {δ ε : ℝ} (hδ : 0 < δ) (n k : ℕ)
    (hlevel : 128 ≤ ((n:ℝ)+1)*δ) (herr : 2*(3/4:ℝ)^(k+1) ≤ ε)
    {x : ℝ} (hx : |x| ≤ 2) (hgap : δ ≤ |x|) :
    |((spoly k).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n)).eval x-Real.sign x| ≤ ε := by
  have hpos (y : ℝ) (hy : 0 < y) (hy2 : |y| ≤ 2) (hδy : δ ≤ |y|) :
      |((spoly k).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n)).eval y-1| ≤ ε := by
    have h := Qatlib.Concepts.QsvtCore.ApproxToolkit.constant_error n hδ hlevel hy2 hδy
    rw [Real.sign_of_pos hy] at h
    have hab := Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_abs_le n hy2
    simp only [Polynomial.eval_comp]
    exact (spoly_tail _ (by linarith [(abs_le.mp h).1]) (abs_le.mp hab).2).trans
      herr
  by_cases hp : 0 < x
  · rw [Real.sign_of_pos hp]
    exact hpos x hp hx hgap
  · have hn : x < 0 := by
      by_contra hh
      have hz : x=0 := by linarith
      simp [hz] at hgap
      linarith
    rw [Real.sign_of_neg hn,sub_neg_eq_add]
    have he : ((spoly k).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n)).eval x+1 =
        -(((spoly k).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n)).eval (-x)-1) := by
      simp only [Polynomial.eval_comp,Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_odd,spoly_odd]

      ring
    rw [he,abs_neg]
    exact hpos (-x) (by linarith) (by simpa only [abs_neg] using! hx)
      (by simpa only [abs_neg] using! hgap)

theorem nearOptimalPolynomial_error {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε < 1/2) {x : ℝ} (hx : |x| ≤ 2) (hgap : δ ≤ |x|) :
    |(nearOptimalPolynomial δ ε).eval x-Real.sign x| ≤ ε :=
  amplifiedSeparator_error hδ _ _ (separation_level hδ) (amplification_error hε hε2) hx hgap

theorem amplifiedSeparator_degree {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (n k : ℕ)
    (hnBound : n ≤ separationLevel δ) (hkBound : k ≤ amplificationLevel ε) :
    (((spoly k).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n)).natDegree:ℝ) ≤
      12000*(1+(1/δ)*Real.log (1/ε)) := by
  have hL := log_error_lower hε hε2
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 128/δ by positivity)
  have hk := Nat.ceil_lt_add_one (show 0 ≤ 8*Real.log (1/ε) by linarith)
  have hs : ((Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n).natDegree:ℝ) ≤ 526/δ := by
    have hd : ((Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n).natDegree:ℝ) ≤
        4*(n:ℝ)+3 := by exact_mod_cast Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_degree n
    have hn' : (n:ℝ) < 128/δ+1 :=
        (show (n:ℝ) ≤ (separationLevel δ:ℝ) by exact_mod_cast hnBound).trans_lt hn
    have ht : (4*(n:ℝ)+3)*δ ≤ 526 := by
      have := (lt_div_iff₀ hδ).mp (show (n:ℝ)-1 < 128/δ by linarith)
      nlinarith
    exact hd.trans ((le_div_iff₀ hδ).mpr ht)
  have ha : ((spoly k).natDegree:ℝ) ≤ 22*Real.log (1/ε) := by
    have hd : ((spoly k).natDegree:ℝ) ≤ 2*(k:ℝ)+1 :=
      by exact_mod_cast spoly_natDegree_le k
    have hk' : (k:ℝ) < 8*Real.log (1/ε)+1 :=
        (show (k:ℝ) ≤ (amplificationLevel ε:ℝ) by exact_mod_cast hkBound).trans_lt hk
    linarith
  have hcomp : (((spoly k).comp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n)).natDegree:ℝ) ≤
      ((spoly k).natDegree:ℝ)*((Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n).natDegree:ℝ) :=
    by exact_mod_cast (Polynomial.natDegree_comp_le (p := spoly k)
      (q := Qatlib.Concepts.QsvtCore.ApproxToolkit.separator n))
  have hprod := mul_le_mul ha hs (Nat.cast_nonneg _) (by positivity : (0:ℝ)≤22*Real.log (1/ε))
  calc
    _ ≤ (22*Real.log (1/ε))*(526/δ) := hcomp.trans hprod
    _ = 11572*((1/δ)*Real.log (1/ε)) := by ring
    _ ≤ _ := by
      have hn : 0 ≤ (1/δ)*Real.log (1/ε) := by positivity
      nlinarith

theorem nearOptimalPolynomial_degree {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) :
    ((nearOptimalPolynomial δ ε).natDegree:ℝ) ≤ 12000*(1+(1/δ)*Real.log (1/ε)) :=
  amplifiedSeparator_degree hδ hδ2 hε hε2 _ _ le_rfl le_rfl

theorem nearOptimalPolynomial_spec {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) :
    NearOptimalSignApproximation 12000 δ ε (nearOptimalPolynomial δ ε) := by
  refine ⟨by norm_num,hδ,hε,?_,?_,nearOptimalPolynomial_odd δ ε,
    nearOptimalPolynomial_degree hδ hδ2 hε hε2⟩
  · intro x hx
    exact nearOptimalPolynomial_abs_le δ ε hx
  · intro x hx hgap
    exact nearOptimalPolynomial_error hδ hε hε2 hx hgap

end Qatlib.Concepts.QsvtCore.ApproxToolkit

end

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open scoped BigOperators

def nativePower (xs : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | k+1 => ratMulList (nativePower xs k) xs

def nativeCentralCoefficient (i : ℕ) : ℚ := (2*i).choose i/(4:ℚ)^i

def nativeAmplifierSeries : ℕ → List ℚ
  | 0 => [1]
  | k+1 => ratAddList (nativeAmplifierSeries k)
      ((nativePower [1,0,-1] (k+1)).map (fun a => nativeCentralCoefficient (k+1)*a))

def nativeAmplifier (k : ℕ) : List ℚ := ratMulList [0,1] (nativeAmplifierSeries k)

def nativeSeparationLevel (δ : ℚ) : ℕ := ⌈128/δ⌉₊

theorem rational_half_lt {ε : ℚ} (h : ε < 1/2) : (ε:ℝ) < 1/2 := by
  have hc : (ε:ℝ) < ((1/2:ℚ):ℝ) := Rat.cast_lt.mpr h
  norm_num at hc
  exact hc

theorem geometric_rat_cast (ε : ℚ) (k : ℕ) :
    (2*(3/4:ℝ)^(k+1) ≤ (ε:ℝ)) ↔ (2*(3/4:ℚ)^(k+1) ≤ ε) := by
  rw [← Rat.cast_le (K := ℝ)]
  norm_num

theorem nativeAmplification_witness (ε : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) :
    ∃ k : ℕ, 2*(3/4:ℚ)^(k+1) ≤ ε := by
  refine ⟨amplificationLevel (ε:ℝ),?_⟩
  have h := amplification_error (ε := (ε:ℝ)) (by exact_mod_cast hε) (rational_half_lt hε2)
  exact (geometric_rat_cast ε _).mp h

def nativeAmplificationLevel (ε : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) : ℕ :=
  Nat.find (nativeAmplification_witness ε hε hε2)

def nativeSignCoefficients (δ ε : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) : List ℚ :=
  rationalPolynomialCompose (nativeAmplifier (nativeAmplificationLevel ε hε hε2))
    (Kernel.nativeSeparator (nativeSeparationLevel δ))

theorem nativePower_semantics (xs : List ℚ) (k : ℕ) :
    realTarget (nativePower xs k) = (realTarget xs)^k := by
  induction k with
  | zero => simp [nativePower,realTarget_cons]
  | succ k ih => rw [nativePower,realTarget_mul,ih,pow_succ]

theorem nativeCentralCoefficient_semantics (i : ℕ) :
    ((nativeCentralCoefficient i:ℚ):ℝ) = cReal i := by
  simp [nativeCentralCoefficient,cReal]

theorem nativeAmplifierSeries_semantics (k : ℕ) :
    realTarget (nativeAmplifierSeries k) =
      ∑ i ∈ Finset.range (k+1),C (cReal i)*(1-X^2)^i := by
  have hb : realTarget [1,0,-1] = (1-X^2 : Polynomial ℝ) := by
    simp [realTarget_cons]
    ring
  induction k with
  | zero => simp [nativeAmplifierSeries,realTarget_cons,cReal]
  | succ k ih =>
    rw [nativeAmplifierSeries,realTarget_add,ih,realTarget_scale,nativePower_semantics,
      hb,nativeCentralCoefficient_semantics]
    simp only [Finset.sum_range_succ]

theorem nativeAmplifier_semantics (k : ℕ) : realTarget (nativeAmplifier k) = spoly k := by
  rw [nativeAmplifier,realTarget_mul,nativeAmplifierSeries_semantics]
  simp [realTarget_cons,spoly]

theorem nativeSignCoefficients_semantics (δ ε : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) :
    realTarget (nativeSignCoefficients δ ε hε hε2) =
      (spoly (nativeAmplificationLevel ε hε hε2)).comp
        (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator (nativeSeparationLevel δ)) := by
  rw [nativeSignCoefficients,rationalPolynomialCompose_semantics,
    nativeAmplifier_semantics,Kernel.nativeSeparator_semantics]

theorem nativeSeparation_level {δ : ℚ} (hδ : 0 < δ) :
    128 ≤ ((nativeSeparationLevel δ:ℝ)+1)*(δ:ℝ) := by
  have hq := Nat.le_ceil (128/δ)
  have h : (128:ℚ) ≤ (nativeSeparationLevel δ:ℚ)*δ := (div_le_iff₀ hδ).mp hq
  have hr : (128:ℝ) ≤ (nativeSeparationLevel δ:ℝ)*(δ:ℝ) := by exact_mod_cast h
  have hp : (0:ℝ)<(δ:ℝ) := by exact_mod_cast hδ
  nlinarith

theorem nativeSeparation_le (δ : ℚ) : nativeSeparationLevel δ ≤ separationLevel (δ:ℝ) := by
  apply Nat.ceil_le.mpr
  have h := Nat.le_ceil (128/(δ:ℝ))
  have hc : ((128/δ:ℚ):ℝ) ≤ (separationLevel (δ:ℝ):ℝ) := by
    push_cast
    exact h
  exact Rat.cast_le.mp (by simpa only [Rat.cast_natCast] using! hc)

theorem nativeAmplification_error (ε : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) :
    2*(3/4:ℝ)^(nativeAmplificationLevel ε hε hε2+1) ≤ (ε:ℝ) := by
  have h := Nat.find_spec (nativeAmplification_witness ε hε hε2)
  exact (geometric_rat_cast ε _).mpr h

theorem nativeAmplification_le (ε : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) :
    nativeAmplificationLevel ε hε hε2 ≤ amplificationLevel (ε:ℝ) := by
  apply Nat.find_min'
  have h := amplification_error (ε := (ε:ℝ)) (by exact_mod_cast hε) (rational_half_lt hε2)
  exact (geometric_rat_cast ε _).mp h

theorem nativeSignCoefficients_spec {δ ε : ℚ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) :
    NearOptimalSignApproximation 12000 (δ:ℝ) (ε:ℝ)
      (realTarget (nativeSignCoefficients δ ε hε hε2)) := by
  have hδr : (0:ℝ)<(δ:ℝ) := by exact_mod_cast hδ
  rw [nativeSignCoefficients_semantics]
  refine ⟨by norm_num,hδr,by exact_mod_cast hε,?_,?_,?_,?_⟩
  · intro x hx
    simp only [Polynomial.eval_comp]
    exact spoly_abs_le _ _
        (abs_le.mp (Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_abs_le _ hx))
  · intro x hx hg
    exact amplifiedSeparator_error hδr _ _ (nativeSeparation_level hδ)
      (nativeAmplification_error ε hε hε2) hx hg
  · intro x
    simp only [Polynomial.eval_comp,Qatlib.Concepts.QsvtCore.ApproxToolkit.separator_odd,spoly_odd]
  · exact amplifiedSeparator_degree hδr (by exact_mod_cast hδ2)
      (by exact_mod_cast hε) (rational_half_lt hε2) _ _
      (nativeSeparation_le δ) (nativeAmplification_le ε hε hε2)

end Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow

noncomputable section
namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
open Polynomial
open scoped BigOperators

theorem nearOptimalSign_allThresholdRectangle {C δ ε t : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation C δ (ε/2) S)
    (hε : 0 < ε) (hε2 : ε < 1/2) (ht1 : t ≤ 1) :
    PrintedRectangleBand (sourceRectanglePolynomial S (ε/2) t) ε δ t := by
  have hδ := hS.2.1
  by_cases ht : t < 0
  · exact sourceRectangle_neg_t hε.le hδ ht
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    rw [sourceRectanglePolynomial,if_neg ht]
    exact twoTranslateRectangleBands_allThresholds hδ (by linarith) (by linarith) rfl
      (by nlinarith [sq_nonneg ε]) (by nlinarith [sq_nonneg ε]) ht0 ht1
      (nearOptimalSign_approximation hS)

def nearOptimalRectangle (δ ε t : ℝ) : Polynomial ℝ :=
  sourceRectanglePolynomial (nearOptimalPolynomial δ (ε/2)) (ε/2) t

theorem nearOptimalRectangle_spec {δ ε t : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (ht1 : t ≤ 1) :
    PrintedRectangleBand (nearOptimalRectangle δ ε t) ε δ t :=
  nearOptimalSign_allThresholdRectangle
    (nearOptimalPolynomial_spec hδ hδ2 (by linarith) (by linarith)) hε hε2 ht1

theorem nearOptimalRectangle_even (δ ε t x : ℝ) :
    (nearOptimalRectangle δ ε t).eval (-x) = (nearOptimalRectangle δ ε t).eval x := by
  by_cases ht : t < 0
  · simp [nearOptimalRectangle,sourceRectanglePolynomial,ht]
  · exact sourceRectanglePolynomial_even (le_of_not_gt ht)

theorem nearOptimalRectangle_degree {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (t : ℝ) :
    ((nearOptimalRectangle δ ε t).natDegree:ℝ) ≤
      36000*(1+(1/δ)*Real.log (1/ε)) := by
  have hnat := sourceRectangle_natDegree_le (S := nearOptimalPolynomial δ (ε/2))
    (ε₀ := ε/2) (t := t)
  have hle : ((nearOptimalRectangle δ ε t).natDegree:ℝ) ≤
      ((nearOptimalPolynomial δ (ε/2)).natDegree:ℝ) := by exact_mod_cast hnat
  have hd := nearOptimalPolynomial_degree hδ hδ2
    (show 0<ε/2 by linarith) (show ε/2<1/2 by linarith)
  have hL := log_error_lower hε hε2
  have hlog : Real.log (1/(ε/2)) ≤ 3*Real.log (1/ε) := by
    rw [show 1/(ε/2) = 2*(1/ε) by ring,Real.log_mul (by norm_num) (by positivity)]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1/δ by positivity)
  nlinarith [hle.trans hd]

theorem frontier1 {δ ε t : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (ht1 : t ≤ 1) :
    NearOptimalSignApproximation 12000 δ ε (nearOptimalPolynomial δ ε) ∧
    PrintedRectangleBand (nearOptimalRectangle δ ε t) ε δ t ∧
    (∀ x, (nearOptimalRectangle δ ε t).eval (-x) = (nearOptimalRectangle δ ε t).eval x) ∧
    ((nearOptimalRectangle δ ε t).natDegree:ℝ) ≤ 36000*(1+(1/δ)*Real.log (1/ε)) :=
  ⟨nearOptimalPolynomial_spec hδ hδ2 hε hε2,
    nearOptimalRectangle_spec hδ hδ2 hε hε2 ht1,nearOptimalRectangle_even δ ε t,
    nearOptimalRectangle_degree hδ hδ2 hε hε2 t⟩

end Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
end

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord

def nativeRectangleCoefficients (δ ε t : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) : List ℚ :=
  if t < 0 then [] else
    let xs := nativeSignCoefficients δ (ε/2) (by linarith) (by linarith)
    ratAddList ((ratAddList (rationalPolynomialCompose xs [t,1])
      (rationalPolynomialCompose xs [t,-1])).map (fun a => ((1-ε/2)/2)*a)) [ε/2]

theorem nativeRectangleCoefficients_semantics (δ ε t : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2) :
    realTarget (nativeRectangleCoefficients δ ε t hε hε2) =
      sourceRectanglePolynomial
        (realTarget (nativeSignCoefficients δ (ε/2) (by linarith) (by linarith)))
        ((ε:ℝ)/2) (t:ℝ) := by
  by_cases ht : t < 0
  · have htr : (t:ℝ)<0 := by exact_mod_cast ht
    simp [nativeRectangleCoefficients,ht,sourceRectanglePolynomial,htr]
  · have htr : (0:ℝ)≤(t:ℝ) := by exact_mod_cast le_of_not_gt ht
    rw [nativeRectangleCoefficients,if_neg ht,realTarget_add,realTarget_scale,
      realTarget_add,rationalPolynomialCompose_semantics,rationalPolynomialCompose_semantics]
    apply Polynomial.funext
    intro x
    rw [sourceRectanglePolynomial_eval htr]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp,
      realTarget_cons,realTarget_nil,Polynomial.eval_X,Polynomial.eval_zero]
    push_cast
    ring

theorem nativeRectangleCoefficients_spec {δ ε t : ℚ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (ht1 : t ≤ 1) :
    PrintedRectangleBand (realTarget (nativeRectangleCoefficients δ ε t hε hε2))
      (ε:ℝ) (δ:ℝ) (t:ℝ) := by
  rw [nativeRectangleCoefficients_semantics]
  apply nearOptimalSign_allThresholdRectangle (ε := (ε:ℝ))
  · have h := nativeSignCoefficients_spec hδ hδ2
      (show 0<ε/2 by linarith) (show ε/2<1/2 by linarith)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using! h
  · exact_mod_cast hε
  · exact rational_half_lt hε2
  · exact_mod_cast ht1

end Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord

theorem sign_vacuous {δ ε : ℝ} (hδ : 2 < δ) (hε : 0 < ε) (hε2 : ε < 1/2) :
    NearOptimalSignApproximation 12000 δ ε (0:Polynomial ℝ) := by
  refine ⟨by norm_num,by linarith,hε,?_,?_,?_,?_⟩
  · intro x hx
    simp
  · intro x hx hg
    exfalso
    linarith
  · intro x
    simp
  · have hL := log_error_lower hε hε2
    simp only [Polynomial.natDegree_zero,Nat.cast_zero]
    positivity

theorem normalized_value_bounds {v w s ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hv : |v| ≤ 1) (hvs : |v-s| ≤ ε) (hwv : |w-v| ≤ η) (hs : |s| ≤ 1) :
    |w/(1+η)| ≤ 1 ∧ |w/(1+η)-s| ≤ ε+2*η := by
  have hp : 0 < 1+η := by linarith
  have hw : |w| ≤ 1+η := by
    calc
      _ = |(w-v)+v| := by congr 1; ring
      _ ≤ |w-v|+|v| := abs_add_le _ _
      _ ≤ _ := by linarith
  refine ⟨?_,?_⟩
  · rw [abs_div,abs_of_pos hp]
    exact (div_le_one hp).mpr hw
  · have h1 := abs_le.mp hvs
    have h2 := abs_le.mp hwv
    have h3 := abs_le.mp hs
    have hm := mul_nonneg hη (show 0 ≤ ε+2*η by linarith)
    have hslo := mul_nonneg hη (show 0 ≤ s+1 by linarith)
    have hshi := mul_nonneg hη (show 0 ≤ 1-s by linarith)
    apply abs_le.mpr
    constructor
    · apply (le_sub_iff_add_le).mpr
      apply (le_div_iff₀ hp).mpr
      nlinarith
    · apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hp).mpr
      nlinarith

def nativeRoundedNormalized (xs : List ℚ) (b : ℕ) (η : ℚ) : List ℚ :=
  (Kernel.nativeRounded b xs).map (fun a => a/(1+η))

theorem nativeRoundedNormalized_eval (xs : List ℚ) (b : ℕ) (η : ℚ) (x : ℝ) :
    (realTarget (nativeRoundedNormalized xs b η)).eval x =
      (realTarget (Kernel.nativeRounded b xs)).eval x/(1+(η:ℝ)) := by
  rw [nativeRoundedNormalized,realTarget_div]
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  push_cast
  ring

theorem nativeRoundedSign_bounds {δ ε η : ℚ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (hη : 0 ≤ η) (b : ℕ)
    (hprecision : ((2:ℝ)^(nativeSignCoefficients δ ε hε hε2).length-1)/(2:ℝ)^(b+1) ≤ (η:ℝ)) :
    (∀ x : ℝ, |x| ≤ 2 →
      |(realTarget (nativeRoundedNormalized (nativeSignCoefficients δ ε hε hε2) b η)).eval x| ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ 2 → (δ:ℝ) ≤ |x| →
      |(realTarget (nativeRoundedNormalized (nativeSignCoefficients δ ε hε hε2) b η)).eval x-
        Real.sign x| ≤ (ε:ℝ)+2*(η:ℝ)) := by
  have hS := nativeSignCoefficients_spec hδ hδ2 hε hε2
  have hεr : (0:ℝ) ≤ (ε:ℝ) := by exact_mod_cast hε.le
  have hηr : (0:ℝ) ≤ (η:ℝ) := by exact_mod_cast hη
  have herr (x : ℝ) (hx : |x|≤2) :=
    (Kernel.nativeRounded_eval_error b (nativeSignCoefficients δ ε hε hε2) hx).trans hprecision
  constructor
  · intro x hx
    rw [nativeRoundedNormalized_eval,abs_div,abs_of_pos (show (0:ℝ)<1+(η:ℝ) by linarith)]
    apply (div_le_one (show (0:ℝ)<1+(η:ℝ) by linarith)).mpr
    have ht := abs_add_le
      ((realTarget (Kernel.nativeRounded b (nativeSignCoefficients δ ε hε hε2))).eval x-
        (realTarget (nativeSignCoefficients δ ε hε hε2)).eval x)
      ((realTarget (nativeSignCoefficients δ ε hε hε2)).eval x)
    simp only [sub_add_cancel] at ht
    linarith [herr x hx,hS.2.2.2.1 x hx]
  · intro x hx hg
    rw [nativeRoundedNormalized_eval]
    apply (normalized_value_bounds hεr hηr (hS.2.2.2.1 x hx)
      (hS.2.2.2.2.1 x hx hg) (herr x hx) ?_).2
    rcases lt_trichotomy x 0 with hn | hz | hp
    · rw [Real.sign_of_neg hn]; norm_num
    · simp [hz]
    · rw [Real.sign_of_pos hp]; norm_num

end Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
set_option warningAsError false

theorem sourceRectangle_degree_of_sign {δ ε : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation 12000 δ (ε/2) S)
    (hε : 0 < ε) (hε2 : ε < 1/2) (t : ℝ) :
    ((sourceRectanglePolynomial S (ε/2) t).natDegree:ℝ) ≤
      36000*(1+(1/δ)*Real.log (1/ε)) := by
  have hnat := sourceRectangle_natDegree_le (S := S) (ε₀ := ε/2) (t := t)
  have hle : ((sourceRectanglePolynomial S (ε/2) t).natDegree:ℝ) ≤ (S.natDegree:ℝ) :=
    by exact_mod_cast hnat
  have hd := hS.2.2.2.2.2.2
  have hL := log_error_lower hε hε2
  have hlog : Real.log (1/(ε/2)) ≤ 3*Real.log (1/ε) := by
    rw [show 1/(ε/2) = 2*(1/ε) by ring,Real.log_mul (by norm_num) (by positivity)]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1/δ by have := hS.2.1; positivity)
  nlinarith [hle.trans hd]

theorem nativeRectangleCoefficients_even (δ ε t : ℚ) (hε : 0 < ε) (hε2 : ε < 1/2)
    (x : ℝ) :
    (realTarget (nativeRectangleCoefficients δ ε t hε hε2)).eval (-x) =
      (realTarget (nativeRectangleCoefficients δ ε t hε hε2)).eval x := by
  simp only [nativeRectangleCoefficients_semantics]
  by_cases ht : (t:ℝ)<0
  · simp [sourceRectanglePolynomial,ht]
  · exact sourceRectanglePolynomial_even (le_of_not_gt ht)

theorem nativeRectangleCoefficients_degree {δ ε : ℚ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hε : 0 < ε) (hε2 : ε < 1/2) (t : ℚ) :
    ((realTarget (nativeRectangleCoefficients δ ε t hε hε2)).natDegree:ℝ) ≤
      36000*(1+(1/(δ:ℝ))*Real.log (1/(ε:ℝ))) := by
  rw [nativeRectangleCoefficients_semantics]
  apply sourceRectangle_degree_of_sign
  · have h := nativeSignCoefficients_spec hδ hδ2
      (show 0<ε/2 by linarith) (show ε/2<1/2 by linarith)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using! h
  · exact_mod_cast hε
  · exact rational_half_lt hε2

end Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
