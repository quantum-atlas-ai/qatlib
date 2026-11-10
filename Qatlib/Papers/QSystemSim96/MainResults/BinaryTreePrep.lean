/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QSystemSim96.MainResults

open Qatlib.Foundations.PureStateMath

def dyadicMass (l : ℕ) (w : ℕ → ℝ) (i k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (2 ^ (l - i)), w (k * 2 ^ (l - i) + n)

theorem dyadicMass_nonneg {l : ℕ} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (i k : ℕ) : 0 ≤ dyadicMass l w i k := by
  unfold dyadicMass
  exact Finset.sum_nonneg fun n _ => hw _

theorem dyadicMass_pos {l : ℕ} {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (i k : ℕ) : 0 < dyadicMass l w i k := by
  unfold dyadicMass
  refine Finset.sum_pos (fun n _ => hw _) ?_
  exact ⟨0, Finset.mem_range.mpr (Nat.two_pow_pos (l - i))⟩

theorem dyadicMass_root (l : ℕ) (w : ℕ → ℝ) :
    dyadicMass l w 0 0 = ∑ n ∈ Finset.range (2 ^ l), w n := by
  unfold dyadicMass
  simp

theorem dyadicMass_leaf (l : ℕ) (w : ℕ → ℝ) (n : ℕ) :
    dyadicMass l w l n = w n := by
  unfold dyadicMass
  simp

theorem dyadicMass_split (l : ℕ) (w : ℕ → ℝ) {i : ℕ} (hi : i < l) (k : ℕ) :
    dyadicMass l w i k =
      dyadicMass l w (i + 1) (2 * k) + dyadicMass l w (i + 1) (2 * k + 1) := by
  unfold dyadicMass
  have hexp : l - i = (l - (i + 1)) + 1 := by omega
  have hpow : 2 ^ (l - i) = 2 ^ (l - (i + 1)) + 2 ^ (l - (i + 1)) := by
    rw [hexp, pow_succ]
    ring
  rw [hpow, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring

def pathNode (l i n : ℕ) : ℕ := n / 2 ^ (l - i)

theorem pathNode_root (l n : ℕ) : pathNode l 0 n = n / 2 ^ l := rfl

theorem pathNode_leaf (l n : ℕ) : pathNode l l n = n := by
  unfold pathNode
  simp

theorem pathNode_succ {l i n : ℕ} (hi : i < l) :
    pathNode l (i + 1) n =
      2 * pathNode l i n + pathNode l (i + 1) n % 2 := by
  unfold pathNode
  have hpow : 2 ^ (l - i) = 2 ^ (l - (i + 1)) * 2 := by
    have h : l - i = (l - (i + 1)) + 1 := by omega
    rw [h, pow_succ]
  have hdiv : n / 2 ^ (l - i) = n / 2 ^ (l - (i + 1)) / 2 := by
    rw [hpow]
    exact (Nat.div_div_eq_div_mul n (2 ^ (l - (i + 1))) 2).symm
  rw [hdiv]
  exact (Nat.div_add_mod (n / 2 ^ (l - (i + 1))) 2).symm

def pathMass (l : ℕ) (w : ℕ → ℝ) (n i : ℕ) : ℝ :=
  dyadicMass l w i (pathNode l i n)

noncomputable def pathRatio (l : ℕ) (w : ℕ → ℝ) (n i : ℕ) : ℝ :=
  pathMass l w n (i + 1) / pathMass l w n i

noncomputable def pathAmplitude (l : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range l, Real.sqrt (pathRatio l w n i)

theorem sq_prod_sqrt (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∏ i ∈ s, Real.sqrt (a i)) ^ 2 = ∏ i ∈ s, a i := by
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← pow_two, Real.sq_sqrt (ha i hi)]

theorem prod_range_div_of_ne_zero (f : ℕ → ℝ) (n : ℕ)
    (h : ∀ i ≤ n, f i ≠ 0) :
    (∏ i ∈ Finset.range n, f (i + 1) / f i) = f n / f 0 := by
  induction n with
  | zero => rw [Finset.prod_range_zero, div_self (h 0 le_rfl)]
  | succ n ih =>
    rw [Finset.prod_range_succ,
      ih (fun i hi => h i (Nat.le_trans hi (Nat.le_succ n)))]
    have hn : f n ≠ 0 := h n (Nat.le_succ n)
    have h0 : f 0 ≠ 0 := h 0 (Nat.zero_le (n + 1))
    field_simp
    try ring

theorem pathAmplitude_sq (l : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) {n : ℕ}
    (hn : n < 2 ^ l) :
    pathAmplitude l w n ^ 2 = dyadicMass l w l n / dyadicMass l w 0 0 := by
  have hnode0 : pathNode l 0 n = 0 := by
    unfold pathNode
    simp [Nat.div_eq_of_lt hn]
  have hnodeL : pathNode l l n = n := pathNode_leaf l n
  unfold pathAmplitude pathRatio
  rw [sq_prod_sqrt]
  · rw [prod_range_div_of_ne_zero (fun i => pathMass l w n i) l]
    · simp [pathMass, hnode0, hnodeL]
    · intro i _
      exact ne_of_gt (dyadicMass_pos hw i (pathNode l i n))
  · intro i _
    apply div_nonneg
    · exact le_of_lt (dyadicMass_pos hw _ _)
    · exact le_of_lt (dyadicMass_pos hw _ _)

theorem pathMass_pos {l i n : ℕ} (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m) (hwn : 0 < w n) :
    0 < pathMass l w n i := by
  unfold pathMass dyadicMass
  have hlt : n % 2 ^ (l - i) < 2 ^ (l - i) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmem : n % 2 ^ (l - i) ∈ Finset.range (2 ^ (l - i)) := Finset.mem_range.mpr hlt
  have hdecomp : pathNode l i n * 2 ^ (l - i) + n % 2 ^ (l - i) = n := by
    unfold pathNode
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n (2 ^ (l - i))
  refine Finset.sum_pos' (fun m _ => hw _) ⟨_, hmem, ?_⟩
  rw [hdecomp]
  exact hwn

theorem pathAmplitude_sq_nonneg (l : ℕ) (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m) {n : ℕ}
    (hwn : 0 < w n) (hn : n < 2 ^ l) :
    pathAmplitude l w n ^ 2 = dyadicMass l w l n / dyadicMass l w 0 0 := by
  have hnode0 : pathNode l 0 n = 0 := by
    unfold pathNode
    simp [Nat.div_eq_of_lt hn]
  have hnodeL : pathNode l l n = n := pathNode_leaf l n
  unfold pathAmplitude pathRatio
  rw [sq_prod_sqrt]
  · rw [prod_range_div_of_ne_zero (fun i => pathMass l w n i) l]
    · simp [pathMass, hnode0, hnodeL]
    · intro i hi
      exact ne_of_gt (pathMass_pos (l := l) (i := i) (n := n) w hw hwn)
  · intro i hi
    apply div_nonneg
    · exact le_of_lt (pathMass_pos (l := l) (i := i + 1) (n := n) w hw hwn)
    · exact le_of_lt (pathMass_pos (l := l) (i := i) (n := n) w hw hwn)

def treeNodeCount (l : ℕ) : ℕ := 2 ^ l - 1

theorem sum_two_pow_range (l : ℕ) : (∑ i ∈ Finset.range l, 2 ^ i) = treeNodeCount l := by
  induction l with
  | zero => simp [treeNodeCount]
  | succ l ih =>
    rw [Finset.sum_range_succ, ih]
    unfold treeNodeCount
    have hpos : 0 < 2 ^ l := Nat.two_pow_pos l
    rw [pow_succ]
    omega

theorem pathAmplitude_sq_eq_weight (l : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hsum : ∑ n ∈ Finset.range (2 ^ l), w n = 1) {n : ℕ} (hn : n < 2 ^ l) :
    pathAmplitude l w n ^ 2 = w n := by
  rw [pathAmplitude_sq l w hw hn, dyadicMass_leaf, dyadicMass_root, hsum, div_one]

noncomputable def splitRotationR (L R : ℝ) : Matrix Bool Bool ℝ :=
  Matrix.of fun a b =>
    if a then
      (if b then Real.sqrt (L / (L + R)) else Real.sqrt (R / (L + R)))
    else
      (if b then -Real.sqrt (R / (L + R)) else Real.sqrt (L / (L + R)))

theorem splitRotation_eq_map (L R : ℝ) :
    (splitRotationR L R).map (Complex.ofReal) =
      Matrix.of fun a b =>
        if a then
          (if b then (Real.sqrt (L / (L + R)) : ℂ) else (Real.sqrt (R / (L + R)) : ℂ))
        else
          (if b then -(Real.sqrt (R / (L + R)) : ℂ) else (Real.sqrt (L / (L + R)) : ℂ)) := by
  ext a b
  cases a <;> cases b <;> simp [splitRotationR]

theorem splitRotationR_mul_transpose {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hM : 0 < L + R) :
    splitRotationR L R * (splitRotationR L R)ᵀ = 1 := by
  have hLr : Real.sqrt (L / (L + R)) ^ 2 = L / (L + R) :=
    Real.sq_sqrt (div_nonneg hL (le_of_lt hM))
  have hRr : Real.sqrt (R / (L + R)) ^ 2 = R / (L + R) :=
    Real.sq_sqrt (div_nonneg hR (le_of_lt hM))
  have hsum' : L / (L + R) + R / (L + R) = 1 := by
    rw [← add_div, div_self (ne_of_gt hM)]
  ext a b
  simp only [splitRotationR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply, Fintype.sum_bool]
  cases a <;> cases b <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]
  all_goals nlinarith [hLr, hRr, hsum']

noncomputable def splitRotation (L R : ℝ) : Matrix Bool Bool ℂ :=
  (splitRotationR L R).map (Complex.ofReal)

theorem splitRotation_unitary {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hM : 0 < L + R) : splitRotation L R ∈ Matrix.unitaryGroup Bool ℂ := by
  let f : ℝ →+* ℂ :=
    { toFun := Complex.ofReal, map_zero' := Complex.ofReal_zero,
      map_one' := Complex.ofReal_one, map_add' := Complex.ofReal_add,
      map_mul' := Complex.ofReal_mul }
  have hreal : splitRotationR L R * (splitRotationR L R)ᵀ = 1 :=
    splitRotationR_mul_transpose hL hR hM
  have hstar : star ((splitRotationR L R).map (Complex.ofReal)) =
      ((splitRotationR L R).map (Complex.ofReal)).transpose := by
    ext a b
    simp [Matrix.star_apply, Matrix.transpose_apply]
  have htrans : ((splitRotationR L R).map (Complex.ofReal)).transpose =
      ((splitRotationR L R)ᵀ).map (Complex.ofReal) := by
    ext a b
    simp [Matrix.transpose_apply]
  unfold splitRotation
  rw [Matrix.mem_unitaryGroup_iff, hstar, htrans]
  change (splitRotationR L R).map ⇑f * ((splitRotationR L R)ᵀ).map ⇑f = 1
  rw [← Matrix.map_mul (f := f), hreal]
  ext a b
  cases a <;> cases b <;> simp [Matrix.map_apply]

theorem splitRotation_ket_false (L R : ℝ) :
    ApplyGate (splitRotation L R) (Ket false) =
      (Real.sqrt (L / (L + R)) : ℂ) • Ket false +
        (Real.sqrt (R / (L + R)) : ℂ) • Ket true := by
  funext a
  cases a <;>
    simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, splitRotation, splitRotationR, Matrix.map]

theorem splitRotation_angle {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hM : 0 < L + R) :
    Real.sin (Real.arcsin (Real.sqrt (R / (L + R)))) = Real.sqrt (R / (L + R)) ∧
      Real.cos (Real.arcsin (Real.sqrt (R / (L + R)))) = Real.sqrt (L / (L + R)) := by
  have hMne : L + R ≠ 0 := ne_of_gt hM
  have hle : R / (L + R) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hnonneg : 0 ≤ R / (L + R) := div_nonneg hR (le_of_lt hM)
  have hsqrtle : Real.sqrt (R / (L + R)) ≤ 1 := Real.sqrt_le_one.mpr hle
  have hsqrtge : -1 ≤ Real.sqrt (R / (L + R)) := by
    linarith [Real.sqrt_nonneg (R / (L + R))]
  have hsin : Real.sin (Real.arcsin (Real.sqrt (R / (L + R)))) =
      Real.sqrt (R / (L + R)) :=
    Real.sin_arcsin hsqrtge hsqrtle
  refine ⟨hsin, ?_⟩
  rw [Real.cos_arcsin]
  have hsq : (Real.sqrt (R / (L + R))) ^ 2 = R / (L + R) :=
    Real.sq_sqrt hnonneg
  rw [hsq]
  have h1 : 1 - R / (L + R) = L / (L + R) := by
    have hone : (1 : ℝ) = (L + R) / (L + R) := (div_self (ne_of_gt hM)).symm
    rw [hone, ← sub_div]
    congr 1
    ring
  rw [h1]

noncomputable def preparedState (l : ℕ) (w : ℕ → ℝ) : QState (Fin (2 ^ l)) :=
  fun n => (Real.sqrt (w n.val) : ℂ)

theorem preparedState_norm (l : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (n : Fin (2 ^ l)) : ‖preparedState l w n‖ ^ 2 = w n.val := by
  unfold preparedState
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hw n.val)]

theorem preparedState_normalized (l : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hsum : ∑ n ∈ Finset.range (2 ^ l), w n = 1) :
    Normalized (preparedState l w) := by
  unfold Normalized
  simp only [preparedState]
  rw [Fin.sum_univ_eq_sum_range (fun n => ‖(Real.sqrt (w n) : ℂ)‖ ^ 2)]
  simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hw _)]
  exact hsum

theorem tree_loading_probability_and_normalization (l : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 < w n) (hsum : ∑ n ∈ Finset.range (2 ^ l), w n = 1) :
    (∀ n, n < 2 ^ l → pathAmplitude l w n ^ 2 = w n) ∧
      Normalized (preparedState l w) := by
  refine ⟨fun n hn => pathAmplitude_sq_eq_weight l w hw hsum hn, ?_⟩
  exact preparedState_normalized l w (fun n => le_of_lt (hw n)) hsum

end Qatlib.Papers.QSystemSim96.MainResults
