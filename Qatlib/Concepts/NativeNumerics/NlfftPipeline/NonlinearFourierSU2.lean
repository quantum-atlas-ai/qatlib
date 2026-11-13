/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Basic
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain

/-!
# SU(2) nonlinear Fourier polynomials and layer stripping

This module defines the finite SU(2) nonlinear Fourier transform `nlftSU2`, fixed-degree
conjugate reversal `conjRevN`, and sequential layer stripping `layerStripSU2`. Nonlinear Fourier
transforms also appear in quantum signal processing; see [AlexisEtAl2026].

The polynomial pair satisfies a conjugate-reversal identity and has unit total squared norm on
the unit circle. The transform is injective at fixed list length, and the layer-stripping
reconstruction theorem recovers polynomial pairs satisfying the stated identity and
normalization.

## Main statements

* `nlftSU2_identity`: The transformed polynomial pair satisfies the conjugate-reversal identity.
* `nlftSU2_circle_norm`: The two squared moduli sum to one on the unit circle.
* `nlftSU2_injective`: Equal transforms of lists of equal length have equal parameters.
* `layerStripSU2_correct`: Layer stripping reconstructs a normalized polynomial pair and ends at
  `(1,0)`.

## References

* [Alexis et al., 2026][AlexisEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.NativeNumerics.NlfftPipeline

open Polynomial

set_option autoImplicit false

/-- The conjugate coefficient reflection of `p` about degree `d`, obtained by conjugating its
coefficients and applying `Polynomial.reflect d`. -/
noncomputable def conjRevN (d : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  (p.map (starRingEnd ℂ)).reflect d

/-- The finite SU(2) nonlinear Fourier polynomial pair obtained by recursively applying
normalized transformations for the complex parameters in the list. -/
noncomputable def nlftSU2 : List ℂ → Polynomial ℂ × Polynomial ℂ
  | [] => (1, 0)
  | γ :: rest =>
      let (A, B) := nlftSU2 rest
      let c : ℂ := ((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ)
      (c • (A - (starRingEnd ℂ γ) • (X * B)), c • (X * B + γ • A))

/-- One layer-stripping step, extracting `γ = B.coeff 0 / A.coeff 0` and returning the
normalized residual polynomial pair. -/
noncomputable def layerStripStepSU2 (A B : Polynomial ℂ) :
    ℂ × Polynomial ℂ × Polynomial ℂ :=
  let γ := B.coeff 0 / A.coeff 0
  let c : ℂ := ((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ)
  (γ, c • (A + (starRingEnd ℂ γ) • B), c • (B - γ • A).divX)

/-- The condition that the first polynomial has a nonzero constant coefficient at each of `n`
successive layer-stripping steps. -/
def LayerStripExact (A B : Polynomial ℂ) : ℕ → Prop
  | 0 => True
  | n + 1 =>
      A.coeff 0 ≠ 0 ∧
      LayerStripExact (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 n

/-- The parameters, residual polynomial pair, and operation count returned by sequential SU(2)
layer stripping. -/
structure LayerStripRunSU2 where
  gammas : List ℂ
  finalA : Polynomial ℂ
  finalB : Polynomial ℂ
  operations : ℕ

/-- Performs `n` sequential layer-stripping steps and records the extracted parameters, final
residual pair, and operation count. -/
noncomputable def layerStripSU2 (A B : Polynomial ℂ) : ℕ → LayerStripRunSU2
  | 0 => { gammas := [], finalA := A, finalB := B, operations := 0 }
  | n + 1 =>
      let s := layerStripStepSU2 A B
      let r := layerStripSU2 s.2.1 s.2.2 n
      { gammas := s.1 :: r.gammas, finalA := r.finalA, finalB := r.finalB,
        operations := 6 * (n + 1) + 5 + r.operations }

/-- A coefficient of the conjugate reflection is the conjugate of the coefficient indexed by
`revAt d i`. -/
private theorem conjRevN_coeff_revAt (d : ℕ) (p : Polynomial ℂ) (i : ℕ) :
    (conjRevN d p).coeff i = (starRingEnd ℂ) (p.coeff (revAt d i)) := by
  simp [conjRevN, coeff_reflect, coeff_map]

/-- For `i ≤ d`, the coefficient at `i` of `conjRevN d p` is the conjugate of `p.coeff (d-i)`. -/
theorem conjRevN_coeff (d : ℕ) (p : Polynomial ℂ) (i : ℕ) (hi : i ≤ d) :
    (conjRevN d p).coeff i = (starRingEnd ℂ) (p.coeff (d - i)) := by
  rw [conjRevN_coeff_revAt, revAt_le hi]

/-- Conjugate reflection about `d` preserves the natural-degree bound `d`. -/
theorem conjRevN_natDegree_le (d : ℕ) (p : Polynomial ℂ) (hp : p.natDegree ≤ d) :
    (conjRevN d p).natDegree ≤ d := by
  simp only [conjRevN]
  exact le_trans natDegree_reflect_le (max_le le_rfl (natDegree_map_le.trans hp))

/-- Conjugate reflection distributes over polynomial addition. -/
private theorem conjRevN_add' (d : ℕ) (p q : Polynomial ℂ) :
    conjRevN d (p + q) = conjRevN d p + conjRevN d q := by
  simp [conjRevN]

/-- Conjugate reflection distributes over polynomial subtraction. -/
private theorem conjRevN_sub' (d : ℕ) (p q : Polynomial ℂ) :
    conjRevN d (p - q) = conjRevN d p - conjRevN d q := by
  simp [conjRevN]

/-- Conjugate reflection of a constant multiple conjugates the constant and reflects the
polynomial. -/
private theorem conjRevN_C_mul' (d : ℕ) (c : ℂ) (p : Polynomial ℂ) :
    conjRevN d (C c * p) = C ((starRingEnd ℂ) c) * conjRevN d p := by
  simp [conjRevN]

/-- Conjugate reflection commutes with scalar multiplication after conjugating the scalar. -/
private theorem conjRevN_smul' (d : ℕ) (c : ℂ) (p : Polynomial ℂ) :
    conjRevN d (c • p) = (starRingEnd ℂ) c • conjRevN d p := by
  rw [smul_eq_C_mul, smul_eq_C_mul, conjRevN_C_mul']

/-- The complex conjugation ring endomorphism fixes every real scalar. -/
private theorem starRingEnd_ofReal (x : ℝ) :
    (starRingEnd ℂ) ((x : ℝ) : ℂ) = (x : ℂ) :=
  Complex.conj_ofReal x

/-- Under the respective degree bounds, conjugate reflection of a product about `d+e` is the
product of the reflections about `d` and `e`. -/
theorem conjRevN_mul (d e : ℕ) (p q : Polynomial ℂ) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e) :
    conjRevN (d + e) (p * q) = conjRevN d p * conjRevN e q := by
  simp only [conjRevN]
  rw [← Polynomial.coe_mapRingHom, map_mul, Polynomial.coe_mapRingHom]
  rw [reflect_mul _ _ (natDegree_map_le.trans hp) (natDegree_map_le.trans hq)]

/-- Conjugate reflection about `d` is involutive on polynomials with natural degree at most `d`. -/
theorem conjRevN_conjRevN (d : ℕ) (p : Polynomial ℂ) (_hp : p.natDegree ≤ d) :
    conjRevN d (conjRevN d p) = p := by
  ext i
  rw [conjRevN_coeff_revAt, conjRevN_coeff_revAt, revAt_invol, starRingEnd_apply,
    starRingEnd_apply, star_star]

/-- At nonzero `z`, evaluation of reflection about `d` equals `z^d` times evaluation of the
original polynomial at `z⁻¹`, under the degree bound. -/
private theorem eval_reflect' (q : Polynomial ℂ) (d : ℕ) (hq : q.natDegree ≤ d) {z : ℂ}
    (hz : z ≠ 0) :
    (q.reflect d).eval z = z ^ d * q.eval z⁻¹ := by
  have hr : (q.reflect d).natDegree ≤ max d (q.natDegree) :=
    natDegree_reflect_le
  have hr' : (q.reflect d).natDegree ≤ d := le_trans hr (max_le le_rfl hq)
  rw [eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hr') z,
    eval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le hq) z⁻¹]
  have h₁ : (∑ i ∈ Finset.range (d + 1), (q.reflect d).coeff i * z ^ i)
      = ∑ j ∈ Finset.range (d + 1), q.coeff j * z ^ (d - j) := by
    have h2 := Finset.sum_range_reflect (fun j => q.coeff j * z ^ (d - j)) (d + 1)
    rw [← h2]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_reflect, revAt_le hi']
    congr 1; congr 1; omega
  rw [h₁, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hzj : z ^ j * (z⁻¹) ^ j = 1 := by rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have e : z ^ (d - j) = z ^ d * (z⁻¹) ^ j := by
    calc z ^ (d - j) = z ^ (d - j) * (z ^ j * (z⁻¹) ^ j) := by rw [hzj, mul_one]
      _ = z ^ d * (z⁻¹) ^ j := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjd]
  rw [e]
  ring

/-- On the unit circle, evaluating `conjRevN d p` gives `z^d` times the complex conjugate of
`p.eval z`, under the degree bound. -/
theorem conjRevN_eval_circle (d : ℕ) (p : Polynomial ℂ) (hp : p.natDegree ≤ d) (z : ℂ)
    (hz : ‖z‖ = 1) :
    (conjRevN d p).eval z = z ^ d * (starRingEnd ℂ) (p.eval z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hstar : (starRingEnd ℂ) z = z⁻¹ := by
    rw [starRingEnd_apply, Complex.inv_eq_conj hz, Complex.star_def]
  have hmapeval : (p.map (starRingEnd ℂ)).eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (p.eval z) := by
    rw [eval_map, eval₂_at_apply]
  rw [conjRevN, eval_reflect' (p.map (starRingEnd ℂ)) d (natDegree_map_le.trans hp) hz0, ← hstar,
    hmapeval]

/-- The square of the SU(2) normalization factor multiplied by `1 + normSq γ` equals one. -/
private theorem nlftC_sq (γ : ℂ) :
    (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
      * (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
      * (1 + ((Complex.normSq γ : ℝ) : ℂ)) = 1 := by
  have hpos : (0 : ℝ) < 1 + Complex.normSq γ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have h2 : Real.sqrt (1 + Complex.normSq γ) ^ 2 = 1 + Complex.normSq γ :=
    Real.sq_sqrt hpos.le
  have h3 : (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
      * (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
      * (1 + ((Complex.normSq γ : ℝ) : ℂ))
      = ((Real.sqrt (1 + Complex.normSq γ))⁻¹ * (Real.sqrt (1 + Complex.normSq γ))⁻¹
        * (1 + Complex.normSq γ) : ℝ) := by
    norm_cast
  rw [h3]
  have h4 : (Real.sqrt (1 + Complex.normSq γ))⁻¹ * (Real.sqrt (1 + Complex.normSq γ))⁻¹
      * (1 + Complex.normSq γ) = 1 := by
    have hne : Real.sqrt (1 + Complex.normSq γ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
    rw [h2]
  rw [h4, Complex.ofReal_one]

/-- The SU(2) normalization factor is nonzero for every complex parameter. -/
private theorem nlftC_ne_zero (γ : ℂ) :
    (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < 1 + Complex.normSq γ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have hne : Real.sqrt (1 + Complex.normSq γ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  norm_cast
  exact inv_ne_zero hne

/-- The constant coefficient of the first nonlinear Fourier polynomial is the product of the
real normalization factors. -/
theorem nlftSU2_fst_coeff_zero (γ : List ℂ) :
    (nlftSU2 γ).1.coeff 0
      = (((γ.map fun g => (Real.sqrt (1 + Complex.normSq g))⁻¹).prod : ℝ) : ℂ) := by
  induction γ with
  | nil => simp [nlftSU2]
  | cons γ rest ih =>
    show (((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
        • ((nlftSU2 rest).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 rest).2)))).coeff 0
      = ((((γ :: rest).map fun g => (Real.sqrt (1 + Complex.normSq g))⁻¹).prod : ℝ) : ℂ)
    rw [coeff_smul, coeff_sub, coeff_smul]
    have hX0 : (X * (nlftSU2 rest).2).coeff 0 = 0 := by
      simp [Polynomial.coeff_mul]
    rw [hX0, smul_zero, sub_zero, smul_eq_mul, ih, List.map_cons, List.prod_cons,
      ← Complex.ofReal_mul]

/-- The first nonlinear Fourier polynomial always has a nonzero constant coefficient. -/
private theorem nlftSU2_fst_coeff_zero_ne (γ : List ℂ) :
    (nlftSU2 γ).1.coeff 0 ≠ 0 := by
  rw [nlftSU2_fst_coeff_zero]
  have hpos : (0:ℝ) < (γ.map fun g => (Real.sqrt (1 + Complex.normSq g))⁻¹).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hx
    exact inv_pos.mpr (Real.sqrt_pos.mpr
      (add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)))
  exact_mod_cast ne_of_gt hpos

/-- Both nonlinear Fourier polynomials have natural degree at most the parameter-list length
minus one. -/
private theorem nlftSU2_natDegree_le_pair (γ : List ℂ) :
    (nlftSU2 γ).1.natDegree ≤ γ.length - 1 ∧ (nlftSU2 γ).2.natDegree ≤ γ.length - 1 := by
  induction γ with
  | nil => simp [nlftSU2]
  | cons γ rest ih =>
    obtain ⟨ihA, ihB⟩ := ih
    cases rest with
    | nil =>
      have h1 : (((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          • ((1 : Polynomial ℂ) - (starRingEnd ℂ γ) • (X * 0))))
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) := by
        rw [mul_zero, smul_zero, sub_zero, smul_eq_C_mul, mul_one]
      have h2 : (((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          • (X * 0 + γ • (1 : Polynomial ℂ))))
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ) := by
        rw [mul_zero, zero_add, smul_eq_C_mul, smul_eq_C_mul, mul_one, ← C_mul]
      exact ⟨by
        show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • ((1 : Polynomial ℂ) - (starRingEnd ℂ γ) • (X * 0))).natDegree ≤ [γ].length - 1
        rw [h1]
        have h0 : (C (((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)))).natDegree = 0 :=
            natDegree_C _
        have e0 : ([γ].length : ℕ) = 1 := rfl
        omega, by
        show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • (X * 0 + γ • (1 : Polynomial ℂ))).natDegree ≤ [γ].length - 1
        rw [h2]
        have hle : (C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ)).natDegree ≤ 0 := by
          rw [C_mul]
          exact natDegree_mul_le.trans (by rw [natDegree_C _, natDegree_C _])
        have e0 : ([γ].length : ℕ) = 1 := rfl
        omega⟩
    | cons γ₂ rest' =>
      have ihA' : (nlftSU2 (γ₂ :: rest')).1.natDegree ≤ rest'.length := ihA
      have ihB' : (nlftSU2 (γ₂ :: rest')).2.natDegree ≤ rest'.length := ihB
      have hX : (X * (nlftSU2 (γ₂ :: rest')).2).natDegree ≤ rest'.length + 1 :=
        natDegree_mul_le.trans (by rw [natDegree_X]; omega)
      refine ⟨?_, ?_⟩
      · show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • ((nlftSU2 (γ₂ :: rest')).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 (γ₂ :: rest')).2))).natDegree
          ≤ (γ :: γ₂ :: rest').length - 1
        rw [List.length_cons, List.length_cons, Nat.add_sub_cancel]
        refine (natDegree_smul_le _ _).trans ?_
        refine (natDegree_sub_le _ _).trans ?_
        apply max_le (le_trans ihA' (Nat.le_add_right _ _))
        exact (natDegree_smul_le _ _).trans hX
      · show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • (X * (nlftSU2 (γ₂ :: rest')).2 + γ • (nlftSU2 (γ₂ :: rest')).1)).natDegree
          ≤ (γ :: γ₂ :: rest').length - 1
        rw [List.length_cons, List.length_cons, Nat.add_sub_cancel]
        refine (natDegree_smul_le _ _).trans ?_
        refine (natDegree_add_le _ _).trans ?_
        apply max_le hX
        exact (natDegree_smul_le _ _).trans (le_trans ihA' (Nat.le_add_right _ _))

/-- The first nonlinear Fourier polynomial has natural degree at most the parameter-list length
minus one. -/
theorem nlftSU2_fst_natDegree_le (γ : List ℂ) :
    (nlftSU2 γ).1.natDegree ≤ γ.length - 1 :=
  (nlftSU2_natDegree_le_pair γ).1

/-- The second nonlinear Fourier polynomial has natural degree at most the parameter-list length
minus one. -/
theorem nlftSU2_snd_natDegree_le (γ : List ℂ) :
    (nlftSU2 γ).2.natDegree ≤ γ.length - 1 :=
  (nlftSU2_natDegree_le_pair γ).2

/-- For `q.natDegree ≤ m`, reflecting `X*q` about `m+1` gives the conjugate reflection of `q`
about `m`. -/
theorem conjRevN_succ_X_mul (m : ℕ) (q : Polynomial ℂ) (hq : q.natDegree ≤ m) :
    conjRevN (m + 1) (X * q) = conjRevN m q := by
  have hX0 : (X * q).coeff 0 = 0 := by simp [Polynomial.coeff_mul]
  ext i
  by_cases hi : i = 0
  · subst hi
    rw [conjRevN_coeff_revAt, revAt_zero, conjRevN_coeff_revAt, revAt_zero,
      Polynomial.coeff_X_mul]
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [conjRevN_coeff_revAt, conjRevN_coeff_revAt]
    by_cases hi' : i' + 1 ≤ m
    · rw [revAt_le (by omega : i' + 1 ≤ m + 1), revAt_le hi',
        show m + 1 - (i' + 1) = m - (i' + 1) + 1 from by omega, Polynomial.coeff_X_mul]
    · by_cases him : i' + 1 = m + 1
      · have e : i' = m := by omega
        subst e
        rw [revAt_le (le_refl (i' + 1)), Nat.sub_self, hX0,
          revAt_eq_self_of_lt (Nat.lt_succ_self i'),
          coeff_eq_zero_of_natDegree_lt (show q.natDegree < i' + 1 from by omega), map_zero]
      · have h1 : m + 1 < i' + 1 := by omega
        rw [revAt_eq_self_of_lt h1, revAt_eq_self_of_lt (by omega : m < i' + 1),
          Polynomial.coeff_X_mul,
          coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < i'),
          coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < i' + 1)]

/-- For `p.natDegree ≤ m`, increasing the reflection degree from `m` to `m+1` multiplies the
conjugate reflection by `X`. -/
theorem conjRevN_succ_eq_X_mul_conjRevN (m : ℕ) (p : Polynomial ℂ) (hp : p.natDegree ≤ m) :
    conjRevN (m + 1) p = X * conjRevN m p := by
  have hX0 : (X * conjRevN m p).coeff 0 = 0 := by simp [Polynomial.coeff_mul]
  ext i
  by_cases hi : i = 0
  · subst hi
    rw [conjRevN_coeff_revAt, revAt_zero,
      coeff_eq_zero_of_natDegree_lt (show p.natDegree < m + 1 from Nat.lt_succ_of_le hp),
      map_zero, hX0]
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [Polynomial.coeff_X_mul, conjRevN_coeff_revAt, conjRevN_coeff_revAt]
    by_cases hi' : i' ≤ m
    · rw [revAt_le (by omega : i' + 1 ≤ m + 1), revAt_le hi',
        show m + 1 - (i' + 1) = m - i' from by omega]
    · rw [revAt_eq_self_of_lt (lt_of_not_ge hi'),
        revAt_eq_self_of_lt (by omega : m + 1 < i' + 1),
        coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i' + 1),
        coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i')]

/-- Conjugate reflection of a constant polynomial about zero conjugates its coefficient. -/
private theorem conjRevN_zero_C (c : ℂ) : conjRevN 0 (C c) = C ((starRingEnd ℂ) c) := by
  simp [conjRevN, reflect_C]

/-- Under the degree bounds, the conjugate reflection of the first nonlinear Fourier update is
the stated normalized combination of the reflected residual polynomials. -/
private theorem conjRevN_nlft_cons_fst (γ : ℂ) (m : ℕ) (A₁ B₁ : Polynomial ℂ)
    (hA₁ : A₁.natDegree ≤ m) (hB₁ : B₁.natDegree ≤ m) :
    conjRevN (m + 1) ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) • (A₁ - (starRingEnd ℂ γ) • (X * B₁)))
      = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
        * (X * conjRevN m A₁ - C γ * conjRevN m B₁) := by
  rw [smul_eq_C_mul, conjRevN_C_mul', starRingEnd_ofReal, conjRevN_sub', conjRevN_smul',
    starRingEnd_apply, starRingEnd_apply, star_star,
    conjRevN_succ_eq_X_mul_conjRevN _ _ hA₁, conjRevN_succ_X_mul _ _ hB₁, smul_eq_C_mul]

/-- Under the degree bounds, the conjugate reflection of the second nonlinear Fourier update is
the stated normalized combination of the reflected residual polynomials. -/
private theorem conjRevN_nlft_cons_snd (γ : ℂ) (m : ℕ) (A₁ B₁ : Polynomial ℂ)
    (hA₁ : A₁.natDegree ≤ m) (hB₁ : B₁.natDegree ≤ m) :
    conjRevN (m + 1) ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) • (X * B₁ + γ • A₁))
      = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
        * (conjRevN m B₁ + C (starRingEnd ℂ γ) * (X * conjRevN m A₁)) := by
  rw [smul_eq_C_mul, conjRevN_C_mul', starRingEnd_ofReal, conjRevN_add',
    conjRevN_succ_X_mul _ _ hB₁, conjRevN_smul', conjRevN_succ_eq_X_mul_conjRevN _ _ hA₁,
    smul_eq_C_mul]

/-- The product of the constant polynomials for `γ` and its conjugate is the constant polynomial
for `normSq γ`. -/
private theorem nlftC_mul_conj (γ : ℂ) :
    C γ * C ((starRingEnd ℂ) γ) = C ((Complex.normSq γ : ℝ) : ℂ) := by
  rw [← C_mul, starRingEnd_apply, Complex.star_def, Complex.mul_conj]

/-- Adding one to the constant polynomial for `normSq γ` gives the constant polynomial for `1 +
normSq γ`. -/
private theorem nlftC_one_add (γ : ℂ) :
    (1 : Polynomial ℂ) + C ((Complex.normSq γ : ℝ) : ℂ) = C (1 + ((Complex.normSq γ : ℝ) : ℂ)) := by
  rw [map_add, map_one]

/-- The nonlinear Fourier pair `(A,B)` satisfies `A * conjRevN d A + B * conjRevN d B = X^d`,
where `d` is the list length minus one. -/
theorem nlftSU2_identity (γ : List ℂ) :
    (nlftSU2 γ).1 * conjRevN (γ.length - 1) (nlftSU2 γ).1
      + (nlftSU2 γ).2 * conjRevN (γ.length - 1) (nlftSU2 γ).2 = X ^ (γ.length - 1) := by
  induction γ with
  | nil =>
    show ((1 : Polynomial ℂ) * conjRevN ([].length - 1) (1 : Polynomial ℂ)
        + (0 : Polynomial ℂ) * conjRevN ([].length - 1) (0 : Polynomial ℂ)) = X ^ ([].length - 1)
    simp [conjRevN]
  | cons γ rest ih =>
    cases rest with
    | nil =>
      have hA : (nlftSU2 [γ]).1 = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) := by
        show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • ((1 : Polynomial ℂ) - (starRingEnd ℂ γ) • (X * 0)))
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
        rw [smul_eq_C_mul, mul_zero, smul_zero, sub_zero, mul_one]
      have hB : (nlftSU2 [γ]).2 = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ) := by
        show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • (X * 0 + γ • (1 : Polynomial ℂ)))
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ)
        rw [smul_eq_C_mul, mul_zero, zero_add, smul_eq_C_mul, mul_one, ← C_mul]
      show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          • ((1 : Polynomial ℂ) - (starRingEnd ℂ γ) • (X * 0))) * conjRevN ([γ].length - 1) _
        + ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) • (X * 0 + γ • (1 : Polynomial ℂ)))
          * conjRevN ([γ].length - 1) _ = X ^ ([γ].length - 1)
      rw [hA, hB]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub]
      rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, mul_zero, mul_zero,
        sub_zero, zero_add, mul_one, mul_one, ← C_mul]
      rw [conjRevN_zero_C, starRingEnd_ofReal, conjRevN_zero_C,
        starRingEnd_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
      rw [← C_mul, ← C_mul, ← C_add]
      have h1 : γ * (starRingEnd ℂ) γ = ((Complex.normSq γ : ℝ) : ℂ) := Complex.mul_conj γ
      have key : (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          + (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ
            * (((starRingEnd ℂ) γ) * (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
        = (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          * (1 + ((Complex.normSq γ : ℝ) : ℂ)) := by
        linear_combination
          ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            * (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) * h1
      rw [key, pow_zero, nlftC_sq γ, C_1]
    | cons γ₂ rest' =>
      show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          • ((nlftSU2 (γ₂ :: rest')).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 (γ₂ :: rest')).2)))
          * conjRevN (rest'.length + 1)
            ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
              • ((nlftSU2 (γ₂ :: rest')).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 (γ₂ :: rest')).2)))
        + ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          • (X * (nlftSU2 (γ₂ :: rest')).2 + γ • (nlftSU2 (γ₂ :: rest')).1))
          * conjRevN (rest'.length + 1)
            ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
              • (X * (nlftSU2 (γ₂ :: rest')).2 + γ • (nlftSU2 (γ₂ :: rest')).1))
        = X ^ (rest'.length + 1)
      generalize hs : nlftSU2 (γ₂ :: rest') = s at ih ⊢
      obtain ⟨A₁, B₁⟩ := s
      rw [List.length_cons, Nat.add_sub_cancel] at ih
      dsimp only [] at ih
      have hA₁ : A₁.natDegree ≤ rest'.length := by
        have h := nlftSU2_fst_natDegree_le (γ₂ :: rest')
        rw [hs] at h
        exact h
      have hB₁ : B₁.natDegree ≤ rest'.length := by
        have h := nlftSU2_snd_natDegree_le (γ₂ :: rest')
        rw [hs] at h
        exact h
      rw [conjRevN_nlft_cons_fst γ rest'.length A₁ B₁ hA₁ hB₁,
        conjRevN_nlft_cons_snd γ rest'.length A₁ B₁ hA₁ hB₁,
        smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
      have e := nlftC_mul_conj γ
      have key : C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) * (A₁ - C ((starRingEnd ℂ) γ) * (X * B₁))
          * (C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) * (X * conjRevN rest'.length A₁ - C γ * conjRevN rest'.length B₁))
        + C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) * (X * B₁ + C γ * A₁)
          * (C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) * (conjRevN rest'.length B₁ + C ((starRingEnd ℂ) γ) * (X * conjRevN rest'.length A₁)))
        = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) * C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
          * ((1 + C γ * C ((starRingEnd ℂ) γ)) * (X * (A₁ * conjRevN rest'.length A₁ + B₁ * conjRevN rest'.length B₁))) := by
        ring
      rw [key, e, nlftC_one_add, ← C_mul, ← mul_assoc, ← C_mul, nlftC_sq γ, C_1, one_mul, ih,
        ← pow_succ']

/-- On the unit circle, the squared moduli of the two nonlinear Fourier polynomials sum to one. -/
theorem nlftSU2_circle_norm (γ : List ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    Complex.normSq ((nlftSU2 γ).1.eval z) + Complex.normSq ((nlftSU2 γ).2.eval z) = 1 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hev := congrArg (eval z) (nlftSU2_identity γ)
  rw [eval_add, eval_mul, eval_mul, eval_pow, eval_X,
    conjRevN_eval_circle _ _ (nlftSU2_fst_natDegree_le γ) z hz,
    conjRevN_eval_circle _ _ (nlftSU2_snd_natDegree_le γ) z hz,
    ← mul_assoc, ← mul_assoc,
    mul_comm (eval z (nlftSU2 γ).1) (z ^ (γ.length - 1)),
    mul_comm (eval z (nlftSU2 γ).2) (z ^ (γ.length - 1)),
    mul_assoc, mul_assoc, ← mul_add] at hev
  have hzd : z ^ (γ.length - 1) ≠ 0 := pow_ne_zero _ hz0
  have hmain : (nlftSU2 γ).1.eval z * (starRingEnd ℂ) ((nlftSU2 γ).1.eval z)
      + (nlftSU2 γ).2.eval z * (starRingEnd ℂ) ((nlftSU2 γ).2.eval z) = 1 := by
    apply mul_left_cancel₀ hzd
    rw [mul_one]
    exact hev
  have hmain' : ((Complex.normSq ((nlftSU2 γ).1.eval z) + Complex.normSq ((nlftSU2 γ).2.eval z) : ℝ) : ℂ)
      = 1 := by
    rw [Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply, starRingEnd_apply,
      mul_comm (star ((nlftSU2 γ).1.eval z)) ((nlftSU2 γ).1.eval z),
      mul_comm (star ((nlftSU2 γ).2.eval z)) ((nlftSU2 γ).2.eval z)]
    exact hmain
  have hre := congrArg Complex.re hmain'
  simpa using hre

/-- Dividing `C c * (X*p)` by `X` using `divX` returns `C c * p`. -/
private theorem divX_C_mul_X_mul (c : ℂ) (p : Polynomial ℂ) :
    (C c * (X * p)).divX = C c * p := by
  ext i
  rw [Polynomial.coeff_divX, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

/-- The first parameter of a nonempty nonlinear Fourier transform is the ratio of the constant
coefficients of its second and first polynomials. -/
private theorem nlftSU2_cons_head (γ₀ : ℂ) (rest : List ℂ) :
    γ₀ = (nlftSU2 (γ₀ :: rest)).2.coeff 0 / (nlftSU2 (γ₀ :: rest)).1.coeff 0 := by
  have eA : (nlftSU2 (γ₀ :: rest)).1.coeff 0
      = (((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ) * (nlftSU2 rest).1.coeff 0 := by
    show ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
        • ((nlftSU2 rest).1 - (starRingEnd ℂ γ₀) • (X * (nlftSU2 rest).2))).coeff 0
      = (((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ) * (nlftSU2 rest).1.coeff 0
    rw [coeff_smul, coeff_sub, coeff_smul]
    have hX0 : (X * (nlftSU2 rest).2).coeff 0 = 0 := by simp [Polynomial.coeff_mul]
    rw [hX0, smul_zero, sub_zero, smul_eq_mul]
  have eB : (nlftSU2 (γ₀ :: rest)).2.coeff 0
      = (((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ) * γ₀ * (nlftSU2 rest).1.coeff 0 := by
    show ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
        • (X * (nlftSU2 rest).2 + γ₀ • (nlftSU2 rest).1)).coeff 0
      = (((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ) * γ₀ * (nlftSU2 rest).1.coeff 0
    rw [coeff_smul, coeff_add, coeff_smul]
    have hX0 : (X * (nlftSU2 rest).2).coeff 0 = 0 := by simp [Polynomial.coeff_mul]
    rw [hX0, zero_add, smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [eA, eB]
  have hA₀ : (nlftSU2 rest).1.coeff 0 ≠ 0 := nlftSU2_fst_coeff_zero_ne _
  have hc : (((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ) ≠ 0 := nlftC_ne_zero _
  rw [mul_div_mul_right _ _ hA₀, mul_div_cancel_left₀ _ hc]

/-- One layer-stripping step on the transform of `γ₀ :: rest` recovers the nonlinear Fourier
polynomial pair of `rest`. -/
private theorem nlftSU2_cons_layerStrip (γ₀ : ℂ) (rest : List ℂ) :
    nlftSU2 rest = ((layerStripStepSU2 (nlftSU2 (γ₀ :: rest)).1 (nlftSU2 (γ₀ :: rest)).2).2.1,
                    (layerStripStepSU2 (nlftSU2 (γ₀ :: rest)).1 (nlftSU2 (γ₀ :: rest)).2).2.2) := by
  set A := (nlftSU2 (γ₀ :: rest)).1 with hA
  set B := (nlftSU2 (γ₀ :: rest)).2 with hB
  have hg : B.coeff 0 / A.coeff 0 = γ₀ := by
    rw [hA, hB]
    exact (nlftSU2_cons_head γ₀ rest).symm
  refine Prod.ext ?_ ?_
  · show (nlftSU2 rest).1 = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
        • (A + (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) • B))
    rw [hg]
    show (nlftSU2 rest).1 = ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
        • ((nlftSU2 (γ₀ :: rest)).1 + (starRingEnd ℂ γ₀) • (nlftSU2 (γ₀ :: rest)).2))
    show (nlftSU2 rest).1 = ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
        • ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
            • ((nlftSU2 rest).1 - (starRingEnd ℂ γ₀) • (X * (nlftSU2 rest).2))
          + (starRingEnd ℂ γ₀)
            • ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
              • (X * (nlftSU2 rest).2 + γ₀ • (nlftSU2 rest).1))))
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    have key1 : C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
          * (C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
            * ((nlftSU2 rest).1 - C ((starRingEnd ℂ) γ₀) * (X * (nlftSU2 rest).2))
          + C ((starRingEnd ℂ) γ₀)
            * (C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
              * (X * (nlftSU2 rest).2 + C γ₀ * (nlftSU2 rest).1)))
        = C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)) * C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
          * ((nlftSU2 rest).1 - C ((starRingEnd ℂ) γ₀) * (X * (nlftSU2 rest).2)
            + C ((starRingEnd ℂ) γ₀) * (X * (nlftSU2 rest).2 + C γ₀ * (nlftSU2 rest).1)) := by
      ring
    have key2 : (nlftSU2 rest).1 - C ((starRingEnd ℂ) γ₀) * (X * (nlftSU2 rest).2)
        + C ((starRingEnd ℂ) γ₀) * (X * (nlftSU2 rest).2 + C γ₀ * (nlftSU2 rest).1)
        = (1 + C γ₀ * C ((starRingEnd ℂ) γ₀)) * (nlftSU2 rest).1 := by
      ring
    have key3 : C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)) * C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
        * ((1 + C ((Complex.normSq γ₀ : ℝ) : ℂ)) * (nlftSU2 rest).1) = (nlftSU2 rest).1 := by
      rw [nlftC_one_add, ← mul_assoc, ← C_mul, ← C_mul, nlftC_sq γ₀, C_1, one_mul]
    rw [key1, key2, nlftC_mul_conj γ₀, key3]
  · show (nlftSU2 rest).2 = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
        • (B - (B.coeff 0 / A.coeff 0) • A).divX)
    rw [hg]
    show (nlftSU2 rest).2 = ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
        • ((nlftSU2 (γ₀ :: rest)).2 - γ₀ • (nlftSU2 (γ₀ :: rest)).1).divX)
    show (nlftSU2 rest).2 = ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
        • ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
            • (X * (nlftSU2 rest).2 + γ₀ • (nlftSU2 rest).1)
          - γ₀ • ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)
              • ((nlftSU2 rest).1 - (starRingEnd ℂ γ₀) • (X * (nlftSU2 rest).2)))).divX)
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    have e1 : C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ)) * (X * (nlftSU2 rest).2 + C γ₀ * (nlftSU2 rest).1)
        - C γ₀ * (C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
          * ((nlftSU2 rest).1 - C ((starRingEnd ℂ) γ₀) * (X * (nlftSU2 rest).2)))
        = C ((((Real.sqrt (1 + Complex.normSq γ₀))⁻¹ : ℝ) : ℂ))
          * ((1 + C γ₀ * C ((starRingEnd ℂ) γ₀)) * (X * (nlftSU2 rest).2)) := by
      ring
    rw [e1, nlftC_mul_conj γ₀, ← mul_assoc, nlftC_one_add, ← C_mul, divX_C_mul_X_mul,
      ← mul_assoc, ← C_mul, ← mul_assoc, nlftC_sq γ₀, C_1, one_mul]

/-- The nonlinear Fourier transform of a concatenation with nonempty first list is the stated
bilinear combination of the two transforms and the first pair's conjugate reflections. -/
theorem nlftSU2_append (γ₁ γ₂ : List ℂ) (h₁ : γ₁ ≠ []) :
    nlftSU2 (γ₁ ++ γ₂) = ((nlftSU2 γ₁).1 * (nlftSU2 γ₂).1
        - X * conjRevN (γ₁.length - 1) (nlftSU2 γ₁).2 * (nlftSU2 γ₂).2,
      X * conjRevN (γ₁.length - 1) (nlftSU2 γ₁).1 * (nlftSU2 γ₂).2
        + (nlftSU2 γ₁).2 * (nlftSU2 γ₂).1) := by
  induction γ₁ with
  | nil => exact absurd rfl h₁
  | cons γ γ₁' ih =>
    cases γ₁' with
    | nil =>
      have hA : (nlftSU2 [γ]).1 = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) := by
        show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • ((1 : Polynomial ℂ) - (starRingEnd ℂ γ) • (X * 0)))
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
        rw [smul_eq_C_mul, mul_zero, smul_zero, sub_zero, mul_one]
      have hB : (nlftSU2 [γ]).2 = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ) := by
        show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • (X * 0 + γ • (1 : Polynomial ℂ)))
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ)
        rw [smul_eq_C_mul, mul_zero, zero_add, smul_eq_C_mul, mul_one, ← C_mul]
      have h3 : conjRevN ([γ].length - 1) (nlftSU2 [γ]).1
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) := by
        rw [show ([γ].length - 1 : ℕ) = 0 by simp, hA, conjRevN_zero_C, starRingEnd_ofReal]
      have h4 : conjRevN ([γ].length - 1) (nlftSU2 [γ]).2
          = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ γ)) := by
        rw [show ([γ].length - 1 : ℕ) = 0 by simp, hB, conjRevN_zero_C]
        congr 1
        rw [map_mul (starRingEnd ℂ), starRingEnd_ofReal]
      show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
          • ((nlftSU2 γ₂).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 γ₂).2)),
          ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • (X * (nlftSU2 γ₂).2 + γ • (nlftSU2 γ₂).1)))
        = ((nlftSU2 [γ]).1 * (nlftSU2 γ₂).1 - X * conjRevN ([γ].length - 1) (nlftSU2 [γ]).2 * (nlftSU2 γ₂).2,
          X * conjRevN ([γ].length - 1) (nlftSU2 [γ]).1 * (nlftSU2 γ₂).2
            + (nlftSU2 [γ]).2 * (nlftSU2 γ₂).1)
      rw [h3, h4, hA, hB]
      rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
      rw [C_mul, C_mul]
      refine Prod.ext ?_ ?_ <;> ring
    | cons γ₂' rest' =>
      have ih0 := ih (List.cons_ne_nil γ₂' rest')
      have ih1 := congrArg Prod.fst ih0
      have ih2 := congrArg Prod.snd ih0
      dsimp only [] at ih1 ih2
      rw [List.length_cons, Nat.add_sub_cancel] at ih1 ih2
      refine Prod.ext ?_ ?_
      · show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • ((nlftSU2 ((γ₂' :: rest') ++ γ₂)).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 ((γ₂' :: rest') ++ γ₂)).2)))
          = ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
              • ((nlftSU2 (γ₂' :: rest')).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 (γ₂' :: rest')).2)))
            * (nlftSU2 γ₂).1
          - X * conjRevN (rest'.length + 1)
              ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
                • (X * (nlftSU2 (γ₂' :: rest')).2 + γ • (nlftSU2 (γ₂' :: rest')).1))
            * (nlftSU2 γ₂).2
        rw [ih1, ih2]
        have hA₁ : (nlftSU2 (γ₂' :: rest')).1.natDegree ≤ rest'.length :=
          nlftSU2_fst_natDegree_le _
        have hB₁ : (nlftSU2 (γ₂' :: rest')).2.natDegree ≤ rest'.length :=
          nlftSU2_snd_natDegree_le _
        rw [conjRevN_nlft_cons_snd γ rest'.length _ _ hA₁ hB₁]
        simp only [smul_eq_C_mul]
        ring
      · show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
            • (X * (nlftSU2 ((γ₂' :: rest') ++ γ₂)).2 + γ • (nlftSU2 ((γ₂' :: rest') ++ γ₂)).1))
          = X * conjRevN (rest'.length + 1)
              ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
                • ((nlftSU2 (γ₂' :: rest')).1 - (starRingEnd ℂ γ) • (X * (nlftSU2 (γ₂' :: rest')).2)))
            * (nlftSU2 γ₂).2
          + ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
              • (X * (nlftSU2 (γ₂' :: rest')).2 + γ • (nlftSU2 (γ₂' :: rest')).1))
            * (nlftSU2 γ₂).1
        rw [ih1, ih2]
        have hA₁ : (nlftSU2 (γ₂' :: rest')).1.natDegree ≤ rest'.length :=
          nlftSU2_fst_natDegree_le _
        have hB₁ : (nlftSU2 (γ₂' :: rest')).2.natDegree ≤ rest'.length :=
          nlftSU2_snd_natDegree_le _
        rw [conjRevN_nlft_cons_fst γ rest'.length _ _ hA₁ hB₁]
        simp only [smul_eq_C_mul]
        ring

/-- Two parameter lists of equal length with the same nonlinear Fourier polynomial pair are
equal. -/
theorem nlftSU2_injective {γ γ' : List ℂ} (hlen : γ.length = γ'.length) (h : nlftSU2 γ = nlftSU2 γ') :
    γ = γ' := by
  induction γ generalizing γ' with
  | nil =>
    cases γ' with
    | nil => rfl
    | cons a l => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons γ₀ rest ih =>
    cases γ' with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons γ₀' rest' =>
      have hlen' : rest.length = rest'.length := Nat.succ.inj hlen
      have hγ : γ₀ = γ₀' := by
        have e1 := nlftSU2_cons_head γ₀ rest
        have e2 := nlftSU2_cons_head γ₀' rest'
        have e3 : (nlftSU2 (γ₀ :: rest)).1.coeff 0 = (nlftSU2 (γ₀' :: rest')).1.coeff 0 := by rw [h]
        have e4 : (nlftSU2 (γ₀ :: rest)).2.coeff 0 = (nlftSU2 (γ₀' :: rest')).2.coeff 0 := by rw [h]
        rw [e1, e2, e3, e4]
      subst hγ
      rw [List.cons_eq_cons]
      exact ⟨rfl,
          ih hlen' (by rw [nlftSU2_cons_layerStrip γ₀ rest, nlftSU2_cons_layerStrip γ₀ rest', h])⟩

/-- Sequential layer stripping returns exactly `n` parameters after `n` steps. -/
theorem layerStripSU2_gammas_length (A B : Polynomial ℂ) (n : ℕ) :
    (layerStripSU2 A B n).gammas.length = n := by
  induction n generalizing A B with
  | zero => rfl
  | succ n ih =>
    show ((layerStripStepSU2 A B).1 :: (layerStripSU2 (layerStripStepSU2 A B).2.1
        (layerStripStepSU2 A B).2.2 n).gammas).length = n + 1
    rw [List.length_cons, ih]

/-- The sequential layer-stripping operation count is exactly `3*n^2 + 8*n`. -/
theorem layerStripSU2_operations (A B : Polynomial ℂ) (n : ℕ) :
    (layerStripSU2 A B n).operations = 3 * n ^ 2 + 8 * n := by
  induction n generalizing A B with
  | zero => rfl
  | succ n ih =>
    show 6 * (n + 1) + 5 + (layerStripSU2 (layerStripStepSU2 A B).2.1
        (layerStripStepSU2 A B).2.2 n).operations = 3 * (n + 1) ^ 2 + 8 * (n + 1)
    rw [ih]
    ring

/-- When `A.coeff 0` is nonzero, the updated first polynomial has the stated normalized constant
coefficient after one stripping step. -/
private theorem layerStripStepSU2_fst_coeff (A B : Polynomial ℂ) (_hA0 : A.coeff 0 ≠ 0) :
    (layerStripStepSU2 A B).2.1.coeff 0
      = (((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
        * (A.coeff 0 + (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) * B.coeff 0) := by
  show (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
      • (A + (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) • B))).coeff 0 = _
  rw [coeff_smul, coeff_add, coeff_smul, smul_eq_mul, smul_eq_mul]

/-- A positive real constant coefficient of the first polynomial remains positive and real after
one layer-stripping step. -/
private theorem layerStripStepSU2_fst_coeff_invariant (A B : Polynomial ℂ)
    (hA0 : A.coeff 0 ≠ 0) (h0im : (A.coeff 0).im = 0) (h0re : 0 < (A.coeff 0).re) :
    ((layerStripStepSU2 A B).2.1.coeff 0).im = 0
    ∧ 0 < ((layerStripStepSU2 A B).2.1.coeff 0).re := by
  have hγA : (B.coeff 0 / A.coeff 0) * A.coeff 0 = B.coeff 0 := div_mul_cancel₀ _ hA0
  generalize hγ : B.coeff 0 / A.coeff 0 = γ
  rw [hγ] at hγA
  have hstep : (layerStripStepSU2 A B).2.1.coeff 0
      = (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * (A.coeff 0 * (1 + (Complex.normSq γ : ℝ))) := by
    rw [layerStripStepSU2_fst_coeff A B hA0, hγ]
    rw [← hγA]
    rw [show (starRingEnd ℂ) γ * (γ * A.coeff 0) = ((Complex.normSq γ : ℝ) : ℂ) * A.coeff 0 from by
      rw [← mul_assoc, mul_comm ((starRingEnd ℂ) γ) γ, Complex.mul_conj]]
    ring
  rw [hstep]
  set c : ℂ := (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) with hc
  have hc_im : c.im = 0 := by simp [hc]
  have hc_re : 0 < c.re := by
    simp only [hc, Complex.ofReal_re, inv_pos]
    exact Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _))
  have h1pos : (0:ℝ) < 1 + Complex.normSq γ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have hd1im : (1 + ((Complex.normSq γ : ℝ) : ℂ)).im = 0 := by
    simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero]
  have hd_im : (c * (1 + ((Complex.normSq γ : ℝ) : ℂ))).im = 0 := by
    simp only [Complex.mul_im, hc_im, Complex.add_im, Complex.one_im, Complex.ofReal_im, zero_mul,
      mul_zero, add_zero]
  have hd_re : 0 < (c * (1 + ((Complex.normSq γ : ℝ) : ℂ))).re := by
    rw [Complex.mul_re, hc_im]
    simp only [Complex.add_re, Complex.one_re, zero_mul, sub_zero,
        Complex.ofReal_re]
    exact mul_pos hc_re h1pos
  have hcA0 : (c * A.coeff 0).im = 0 := by
    simp only [Complex.mul_im, hc_im, h0im, zero_mul, mul_zero, add_zero]
  have hcA0re : 0 < (c * A.coeff 0).re := by
    rw [Complex.mul_re, hc_im]
    simp only [zero_mul, sub_zero]
    exact mul_pos hc_re h0re
  have hd1re : 0 < (1 + ((Complex.normSq γ : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    exact h1pos
  rw [← mul_assoc, Complex.mul_im, hd1im, hcA0, mul_zero, zero_mul, add_zero]
  constructor
  · rfl
  · rw [Complex.mul_re, hcA0, zero_mul, sub_zero]
    exact mul_pos hcA0re hd1re

/-- A positive real constant coefficient of `A` ensures `LayerStripExact A B n` for every number
of steps `n`. -/
theorem layerStripExact_of_pos (A B : Polynomial ℂ) (n : ℕ)
    (h0im : (A.coeff 0).im = 0) (h0re : 0 < (A.coeff 0).re) :
    LayerStripExact A B n := by
  induction n generalizing A B with
  | zero => trivial
  | succ n ih =>
    have hA0 : A.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at h0re
      exact lt_irrefl _ h0re
    obtain ⟨him, hre⟩ := layerStripStepSU2_fst_coeff_invariant A B hA0 h0im h0re
    exact ⟨hA0, ih _ _ him hre⟩

/-- Reduction modulo `X^m` preserves every coefficient of index less than `m`. -/
theorem coeff_mod_X_pow (A : Polynomial ℂ) (m i : ℕ) (hi : i < m) :
    (A % X ^ m).coeff i = A.coeff i := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, coeff_sub, coeff_X_pow_mul']
  simp [hi]

/-- The extracted parameter and the two residual polynomials of a layer-stripping step are given
by the stated explicit formulas. -/
theorem layerStripStepSU2_apply (A B : Polynomial ℂ) :
    (layerStripStepSU2 A B).1 = B.coeff 0 / A.coeff 0
    ∧ (layerStripStepSU2 A B).2.1
      = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
        • (A + (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) • B))
    ∧ (layerStripStepSU2 A B).2.2
      = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
        • (B - (B.coeff 0 / A.coeff 0) • A).divX) :=
  ⟨rfl, rfl, rfl⟩

/-- Agreement of the first `j` input coefficients implies agreement of the first `k ≤ j`
extracted layer-stripping parameters. -/
private theorem layerStripSU2_gammas_congr {A B A' B' : Polynomial ℂ} {j k : ℕ}
    (hk : k ≤ j) (h : ∀ i, i < j → A.coeff i = A'.coeff i ∧ B.coeff i = B'.coeff i) :
    (layerStripSU2 A B k).gammas = (layerStripSU2 A' B' k).gammas := by
  induction k generalizing A B A' B' j with
  | zero => rfl
  | succ k ih =>
    have hj : 0 < j := Nat.lt_of_lt_of_le (Nat.succ_pos k) hk
    obtain ⟨hA0, hB0⟩ := h 0 hj
    obtain ⟨hγf, _, _⟩ := layerStripStepSU2_apply A B
    obtain ⟨hγg, _, _⟩ := layerStripStepSU2_apply A' B'
    have hγ : (layerStripStepSU2 A B).1 = (layerStripStepSU2 A' B').1 := by rw [hγf, hγg, hA0, hB0]
    have hj' : k ≤ j - 1 := by omega
    have hstep : ∀ i, i < j - 1 →
        (layerStripStepSU2 A B).2.1.coeff i = (layerStripStepSU2 A' B').2.1.coeff i
        ∧ (layerStripStepSU2 A B).2.2.coeff i = (layerStripStepSU2 A' B').2.2.coeff i := by
      intro i hi
      obtain ⟨hAi, hBi⟩ := h i (by omega)
      have hi1 : i + 1 < j := by omega
      obtain ⟨hAi1, hBi1⟩ := h (i + 1) hi1
      obtain ⟨_, h2f, h3f⟩ := layerStripStepSU2_apply A B
      obtain ⟨_, h2g, h3g⟩ := layerStripStepSU2_apply A' B'
      constructor
      · rw [h2f, h2g, coeff_smul, coeff_add, coeff_smul, coeff_smul, coeff_add, coeff_smul, smul_eq_mul,
          smul_eq_mul, smul_eq_mul, smul_eq_mul, hAi, hBi, hA0, hB0]
      · rw [h3f, h3g, coeff_smul, Polynomial.coeff_divX, coeff_sub, coeff_smul, coeff_smul,
          Polynomial.coeff_divX, coeff_sub, coeff_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
          hBi1, hAi1, hA0, hB0]
    rw [show (layerStripSU2 A B (k + 1)).gammas = (layerStripStepSU2 A B).1
        :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 k).gammas from rfl,
      show (layerStripSU2 A' B' (k + 1)).gammas = (layerStripStepSU2 A' B').1
        :: (layerStripSU2 (layerStripStepSU2 A' B').2.1 (layerStripStepSU2 A' B').2.2 k).gammas from rfl,
      hγ]
    congr 1
    exact ih hj' hstep

/-- Truncating both input polynomials modulo `X^m` preserves the parameters extracted by any `k
≤ m` stripping steps. -/
theorem layerStripSU2_truncate_gammas (m k : ℕ) (A B : Polynomial ℂ) (hk : k ≤ m) :
    (layerStripSU2 (A % X ^ m) (B % X ^ m) k).gammas = (layerStripSU2 A B k).gammas := by
  apply layerStripSU2_gammas_congr (j := m) hk
  intro i hi
  exact ⟨coeff_mod_X_pow A m i hi, coeff_mod_X_pow B m i hi⟩

/-- The transform of a singleton list consists of the constant polynomials for the normalization
factor and that factor times the parameter. -/
theorem nlftSU2_singleton (γ : ℂ) :
    nlftSU2 [γ] = (C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)),
      C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ)) := by
  have hA : (nlftSU2 [γ]).1 = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)) := by
    show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
        • ((1 : Polynomial ℂ) - (starRingEnd ℂ γ) • (X * 0)))
      = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ))
    rw [smul_eq_C_mul, mul_zero, smul_zero, sub_zero, mul_one]
  have hB : (nlftSU2 [γ]).2 = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ) := by
    show ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ)
        • (X * 0 + γ • (1 : Polynomial ℂ)))
      = C ((((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) * γ)
    rw [smul_eq_C_mul, mul_zero, zero_add, smul_eq_C_mul, mul_one, ← C_mul]
  exact Prod.ext hA hB

/-- Conjugate reflection of a constant polynomial about degree one is its conjugate constant
multiplied by `X`. -/
private theorem conjRevN_one_C (c : ℂ) : conjRevN 1 (C c) = C ((starRingEnd ℂ) c) * X := by
  simp [conjRevN, reflect_C, pow_one]

/-- For positive `m` and exact stripping, multiplying the residual pair by `X^m` gives the
stated transfer formulas in terms of the original pair and the transform of the extracted
parameters. -/
theorem layerStripSU2_transfer (m : ℕ) (A B : Polynomial ℂ) (hm : 1 ≤ m)
    (hex : LayerStripExact A B m) :
    X ^ m * (layerStripSU2 A B m).finalA
      = conjRevN m (nlftSU2 (layerStripSU2 A B m).gammas).1 * A
        + conjRevN m (nlftSU2 (layerStripSU2 A B m).gammas).2 * B
    ∧ X ^ m * (layerStripSU2 A B m).finalB
      = (nlftSU2 (layerStripSU2 A B m).gammas).1 * B
        - (nlftSU2 (layerStripSU2 A B m).gammas).2 * A := by
  induction m generalizing A B with
  | zero => exact absurd hm (by decide)
  | succ m ih =>
    cases m with
    | zero =>
      obtain ⟨hA0, _⟩ := hex
      obtain ⟨hγf, h2f, h3f⟩ := layerStripStepSU2_apply A B
      have hs := nlftSU2_singleton ((layerStripStepSU2 A B).1)
      have hs1 := congrArg Prod.fst hs
      have hs2 := congrArg Prod.snd hs
      dsimp only [] at hs1 hs2
      rw [Nat.zero_add, pow_one]
      constructor
      · show X * (layerStripStepSU2 A B).2.1
          = conjRevN 1 (nlftSU2 ((layerStripStepSU2 A B).1 :: [])).1 * A
            + conjRevN 1 (nlftSU2 ((layerStripStepSU2 A B).1 :: [])).2 * B
        rw [hs1, hs2, conjRevN_one_C, conjRevN_one_C, h2f, hγf, starRingEnd_ofReal,
          map_mul (starRingEnd ℂ), starRingEnd_ofReal]
        rw [smul_eq_C_mul, smul_eq_C_mul]
        simp only [C_mul]
        ring
      · show X * (layerStripStepSU2 A B).2.2
          = (nlftSU2 ((layerStripStepSU2 A B).1 :: [])).1 * B
            - (nlftSU2 ((layerStripStepSU2 A B).1 :: [])).2 * A
        rw [hs1, hs2, h3f, hγf]
        have hp0 : (B - (B.coeff 0 / A.coeff 0) • A).coeff 0 = 0 := by
          rw [coeff_sub, coeff_smul, smul_eq_mul]
          have e : B.coeff 0 / A.coeff 0 * A.coeff 0 = B.coeff 0 := div_mul_cancel₀ _ hA0
          rw [e, sub_self]
        have hXdiv : X * (B - (B.coeff 0 / A.coeff 0) • A).divX
            = B - (B.coeff 0 / A.coeff 0) • A := by
          have h := Polynomial.X_mul_divX_add (B - (B.coeff 0 / A.coeff 0) • A)
          rw [hp0, Polynomial.C_0, add_zero] at h
          exact h
        have hpull : X * ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
              • (B - (B.coeff 0 / A.coeff 0) • A).divX)
            = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
              • (X * (B - (B.coeff 0 / A.coeff 0) • A).divX)) := by
          simp only [smul_eq_C_mul]; ring
        rw [hpull, hXdiv]
        simp only [smul_eq_C_mul, C_mul]
        ring
    | succ m =>
      obtain ⟨hA0, hex1⟩ := hex
      obtain ⟨ihA, ihB⟩ := ih (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2
        (Nat.succ_pos m) hex1
      obtain ⟨hγf, h2f, h3f⟩ := layerStripStepSU2_apply A B
      have hp0 : (B - (B.coeff 0 / A.coeff 0) • A).coeff 0 = 0 := by
        rw [coeff_sub, coeff_smul, smul_eq_mul]
        have e : B.coeff 0 / A.coeff 0 * A.coeff 0 = B.coeff 0 := div_mul_cancel₀ _ hA0
        rw [e, sub_self]
      have hXA1 : X * (layerStripStepSU2 A B).2.1
          = C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) * (X * (A + C ((starRingEnd ℂ) (B.coeff 0 / A.coeff 0)) * B)) := by
        rw [h2f, smul_eq_C_mul, smul_eq_C_mul]
        rw [show X * (C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) * (A + C ((starRingEnd ℂ) (B.coeff 0 / A.coeff 0)) * B))
            = C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) * (X * (A + C ((starRingEnd ℂ) (B.coeff 0 / A.coeff 0)) * B)) from by ring]
      have hXB1 : X * (layerStripStepSU2 A B).2.2
          = (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • (B - (B.coeff 0 / A.coeff 0) • A)) := by
        have h := Polynomial.X_mul_divX_add (B - (B.coeff 0 / A.coeff 0) • A)
        rw [hp0, Polynomial.C_0, add_zero] at h
        rw [h3f]
        rw [show X * (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • (B - (B.coeff 0 / A.coeff 0) • A).divX)
            = (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • (X * (B - (B.coeff 0 / A.coeff 0) • A).divX)) from by
          simp only [smul_eq_C_mul]; ring, h]
      have hEdeg : (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1.natDegree ≤ m + 1 := by
        have h1 :=
            nlftSU2_fst_natDegree_le
            (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas
        have h2 := layerStripSU2_gammas_length (layerStripStepSU2 A B).2.1
          (layerStripStepSU2 A B).2.2 (m + 1)
        omega
      have hFdeg : (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2.natDegree ≤ m + 1 := by
        have h1 :=
            nlftSU2_snd_natDegree_le
            (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas
        have h2 := layerStripSU2_gammas_length (layerStripStepSU2 A B).2.1
          (layerStripStepSU2 A B).2.2 (m + 1)
        omega
      have hcr1 : conjRevN (m + 2) (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • ((nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 - (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2)))
          = C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) * (X * conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 - C (B.coeff 0 / A.coeff 0) * conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2) :=
        conjRevN_nlft_cons_fst (B.coeff 0 / A.coeff 0) (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 hEdeg hFdeg
      have hcr2 : conjRevN (m + 2) (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 + (B.coeff 0 / A.coeff 0) • (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1))
          = C ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) * (conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 + C ((starRingEnd ℂ) (B.coeff 0 / A.coeff 0))
            * (X * conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1)) :=
        conjRevN_nlft_cons_snd (B.coeff 0 / A.coeff 0) (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 hEdeg hFdeg
      have hgam : (layerStripSU2 A B (m + 2)).gammas
          = (B.coeff 0 / A.coeff 0) :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas := rfl
      have hfA : (layerStripSU2 A B (m + 2)).finalA
          = (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).finalA := rfl
      have hfB : (layerStripSU2 A B (m + 2)).finalB
          = (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).finalB := rfl
      constructor
      · rw [hfA, show X ^ (m + 2) * (layerStripSU2 (layerStripStepSU2 A B).2.1
                (layerStripStepSU2 A B).2.2 (m + 1)).finalA
            = X * (X ^ (m + 1) * (layerStripSU2 (layerStripStepSU2 A B).2.1
                (layerStripStepSU2 A B).2.2 (m + 1)).finalA) from by
          rw [pow_succ]; ring, ihA, hgam,
          show (nlftSU2 ((B.coeff 0 / A.coeff 0) :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas)).1
            = (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • ((nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 - (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2))) from rfl,
          show (nlftSU2 ((B.coeff 0 / A.coeff 0) :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas)).2
            = (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 + (B.coeff 0 / A.coeff 0) • (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1)) from rfl]
        rw [show X * (conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 * (layerStripStepSU2 A B).2.1
              + conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 * (layerStripStepSU2 A B).2.2)
            = conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 * (X * (layerStripStepSU2 A B).2.1)
              + conjRevN (m + 1) (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 * (X * (layerStripStepSU2 A B).2.2) from by ring]
        rw [hXA1, hXB1, hcr1, hcr2]
        simp only [smul_eq_C_mul]
        ring
      · rw [hfB, show X ^ (m + 2) * (layerStripSU2 (layerStripStepSU2 A B).2.1
                (layerStripStepSU2 A B).2.2 (m + 1)).finalB
            = X * (X ^ (m + 1) * (layerStripSU2 (layerStripStepSU2 A B).2.1
                (layerStripStepSU2 A B).2.2 (m + 1)).finalB) from by
          rw [pow_succ]; ring, ihB, hgam,
          show (nlftSU2 ((B.coeff 0 / A.coeff 0) :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas)).1
            = (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • ((nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 - (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2))) from rfl,
          show (nlftSU2 ((B.coeff 0 / A.coeff 0) :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas)).2
            = (((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 + (B.coeff 0 / A.coeff 0) • (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1)) from rfl]
        rw [show X * ((nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 * (layerStripStepSU2 A B).2.2 - (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 * (layerStripStepSU2 A B).2.1)
            = (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).1 * (X * (layerStripStepSU2 A B).2.2) - (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (m + 1)).gammas).2 * (X * (layerStripStepSU2 A B).2.1) from by
          ring]
        rw [hXA1, hXB1]
        simp only [smul_eq_C_mul]
        ring

/-- For `A.natDegree ≤ d`, the coefficient at `2*d` of `A * conjRevN d A` is `A.coeff d` times
the conjugate of `A.coeff 0`. -/
private theorem coeff_mul_conjRevN_top (A : Polynomial ℂ) (d : ℕ) (hd : A.natDegree ≤ d) :
    (A * conjRevN d A).coeff (2 * d) = A.coeff d * (starRingEnd ℂ) (A.coeff 0) := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (d, d)]
  · show A.coeff d * (conjRevN d A).coeff d = A.coeff d * (starRingEnd ℂ) (A.coeff 0)
    rw [conjRevN_coeff_revAt, revAt_le (le_refl d), Nat.sub_self]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    have hi : i ≤ 2 * d := by omega
    by_cases h1 : d < i
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd h1), zero_mul]
    · have hjd : d < j := by
        by_contra hj
        push Not at hj
        have : i = d ∧ j = d := by omega
        obtain ⟨rfl, rfl⟩ := this
        exact hne rfl
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (conjRevN_natDegree_le d A hd) hjd),
          mul_zero]
  · intro hdd
    exact absurd (Finset.mem_antidiagonal.mpr (show d + d = 2 * d by omega)) hdd

/-- A degree-bounded polynomial pair satisfying the conjugate-reversal identity and a positive
real first constant coefficient is reconstructed by `d+1` stripping steps, whose residual
pair is `(1,0)`. -/
theorem layerStripSU2_correct (d : ℕ) (A B : Polynomial ℂ) (hA : A.natDegree ≤ d)
    (hB : B.natDegree ≤ d)
    (hid : A * conjRevN d A + B * conjRevN d B = X ^ d)
    (h0im : (A.coeff 0).im = 0) (h0re : 0 < (A.coeff 0).re) :
    nlftSU2 (layerStripSU2 A B (d + 1)).gammas = (A, B)
    ∧ (layerStripSU2 A B (d + 1)).finalA = 1 ∧ (layerStripSU2 A B (d + 1)).finalB = 0 := by
  induction d generalizing A B with
  | zero =>
    have hA : A = C (A.coeff 0) := eq_C_of_natDegree_le_zero hA
    have hB : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
    obtain ⟨hγf, h2f, h3f⟩ := layerStripStepSU2_apply A B
    have hA0 : A.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at h0re
      exact lt_irrefl _ h0re
    have hsA : (starRingEnd ℂ) (A.coeff 0) = A.coeff 0 := by
      rw [starRingEnd_apply, Complex.star_def, Complex.ext_iff]
      constructor <;> simp [h0im]
    have hA0re : A.coeff 0 = (((A.coeff 0).re : ℝ) : ℂ) := by
      rw [Complex.ext_iff]
      constructor <;> simp [h0im]
    have hhid0 : ((A.coeff 0).re ^ 2 + Complex.normSq (B.coeff 0) : ℝ) = 1 := by
      have e := congrArg (fun p : Polynomial ℂ => p.eval 0) hid
      rw [hA, hB, conjRevN_zero_C, conjRevN_zero_C, eval_add, eval_mul, eval_mul, eval_C, eval_C,
        eval_C, eval_C, hsA, starRingEnd_apply, Complex.star_def, Complex.mul_conj,
        hA0re, ← Complex.ofReal_mul, ← Complex.ofReal_add, pow_zero, eval_one,
        ← Complex.ofReal_one] at e
      rw [pow_two]
      exact Complex.ofReal_injective e
    have hγB : B.coeff 0 / A.coeff 0 * A.coeff 0 = B.coeff 0 := div_mul_cancel₀ _ hA0
    have hp : B - (B.coeff 0 / A.coeff 0) • A = 0 := by
      have e : C (B.coeff 0 - B.coeff 0 / A.coeff 0 * A.coeff 0)
          = B - (B.coeff 0 / A.coeff 0) • A := by
        rw [map_sub C, C_mul, ← hB, ← hA, ← smul_eq_C_mul]
      rw [← e,
          show B.coeff 0 - B.coeff 0 / A.coeff 0 * A.coeff 0 = 0 from by linear_combination -hγB, C_0]
    have hns : (1 + Complex.normSq (B.coeff 0 / A.coeff 0)) * (A.coeff 0).re ^ 2 = 1 := by
      have e1 : Complex.normSq (B.coeff 0 / A.coeff 0) * Complex.normSq (A.coeff 0)
          = Complex.normSq (B.coeff 0) := by rw [← Complex.normSq_mul, hγB]
      have e2 : Complex.normSq (A.coeff 0) = (A.coeff 0).re ^ 2 := by
        rw [hA0re, Complex.normSq_ofReal, pow_two, Complex.ofReal_re]
      rw [add_mul, one_mul, ← e2, e1, e2]
      exact hhid0
    have hAc : A.coeff 0 = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) := by
      have h1pos : (0:ℝ) < 1 + Complex.normSq (B.coeff 0 / A.coeff 0) :=
        add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
      have hcr : (Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)) * (A.coeff 0).re) ^ 2 = 1 := by
        rw [mul_pow, Real.sq_sqrt h1pos.le, hns]
      have hcr1 : Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)) * (A.coeff 0).re = 1 := by
        rcases sq_eq_one_iff.mp hcr with h | h
        · exact h
        · have hp1 : 0 ≤ Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)) * (A.coeff 0).re :=
            mul_nonneg (Real.sqrt_nonneg _) (le_of_lt h0re)
          nlinarith
      have hcr2 : Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr h1pos)
      have hr2 : (Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ = (A.coeff 0).re := by
        rw [show (Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹
              = (Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹
                * (Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)) * (A.coeff 0).re) from by
          rw [hcr1, mul_one], ← mul_assoc, inv_mul_cancel₀ hcr2, one_mul]
      rw [hr2]
      exact hA0re
    have hfinA : (layerStripSU2 A B 1).finalA = 1 := by
      show (layerStripStepSU2 A B).2.1 = 1
      have e1 : A.coeff 0 + (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) * B.coeff 0
          = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ))
            * (1 + (Complex.normSq (B.coeff 0 / A.coeff 0) : ℝ)) := by
        generalize hgg : B.coeff 0 / A.coeff 0 = γ
        have hγB' : γ * A.coeff 0 = B.coeff 0 := by rw [← hgg]; exact hγB
        have hAc' : A.coeff 0 = (((Real.sqrt (1 + Complex.normSq γ))⁻¹ : ℝ) : ℂ) := by
          rw [← hgg]; exact hAc
        rw [← hγB', hAc'.symm]
        rw [show (starRingEnd ℂ) γ * (γ * A.coeff 0) = ((Complex.normSq γ : ℝ) : ℂ) * A.coeff 0 from by
          rw [← mul_assoc, mul_comm ((starRingEnd ℂ) γ) γ, Complex.mul_conj]]
        ring
      have e3 : A + C ((starRingEnd ℂ) (B.coeff 0 / A.coeff 0)) * B
          = C (A.coeff 0 + (starRingEnd ℂ) (B.coeff 0 / A.coeff 0) * B.coeff 0) := by
        rw [map_add C, C_mul, ← smul_eq_C_mul, ← hB, ← hA, smul_eq_C_mul]
      rw [h2f, smul_eq_C_mul, smul_eq_C_mul, e3, e1, ← C_mul, ← mul_assoc,
        nlftC_sq (B.coeff 0 / A.coeff 0), C_1]
    have hfinB : (layerStripSU2 A B 1).finalB = 0 := by
      show (layerStripStepSU2 A B).2.2 = 0
      rw [h3f, hp, Polynomial.divX_zero, smul_zero]
    have hnlft : nlftSU2 [B.coeff 0 / A.coeff 0] = (A, B) := by
      have e2 : ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ))
          * (B.coeff 0 / A.coeff 0) = B.coeff 0 := by
        rw [hAc.symm]
        field_simp
      rw [nlftSU2_singleton, e2, ← hAc, ← hA, ← hB]
    exact ⟨by rw [show (layerStripSU2 A B 1).gammas = [B.coeff 0 / A.coeff 0] from rfl, hnlft],
      hfinA, hfinB⟩
  | succ d ih =>
    obtain ⟨hγf, h2f, h3f⟩ := layerStripStepSU2_apply A B
    have hA0 : A.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at h0re
      exact lt_irrefl _ h0re

    have hex : LayerStripExact A B (d + 2) := layerStripExact_of_pos A B (d + 2) h0im h0re
    obtain ⟨-, hex1⟩ := hex
    obtain ⟨hA₁0, _⟩ := hex1

    have htop := congrArg (fun p : Polynomial ℂ => p.coeff (2 * (d + 1))) hid
    rw [coeff_add, coeff_mul_conjRevN_top A (d + 1) hA,
      coeff_mul_conjRevN_top B (d + 1) hB] at htop
    rw [show (X ^ (d + 1) : Polynomial ℂ).coeff (2 * (d + 1)) = 0 from by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_X_pow]
      omega] at htop
    have hsA : (starRingEnd ℂ) (A.coeff 0) = A.coeff 0 := by
      rw [starRingEnd_apply, Complex.star_def, Complex.ext_iff]
      constructor <;> simp [h0im]
    rw [hsA] at htop
    have hA₁top : (layerStripStepSU2 A B).2.1.coeff (d + 1) = 0 := by
      rw [h2f, coeff_smul, coeff_add, coeff_smul, smul_eq_mul, smul_eq_mul]
      have hγstar : (starRingEnd ℂ) (B.coeff 0 / A.coeff 0)
          = (starRingEnd ℂ) (B.coeff 0) / A.coeff 0 := by
        rw [div_eq_mul_inv, map_mul (starRingEnd ℂ), map_inv₀, ← div_eq_mul_inv, hsA]
      rw [hγstar]
      have e : A.coeff (d + 1) + (starRingEnd ℂ) (B.coeff 0) / A.coeff 0 * B.coeff (d + 1) = 0 := by
        field_simp
        linear_combination htop
      rw [e, mul_zero]
    have hA₁deg : (layerStripStepSU2 A B).2.1.natDegree ≤ d := by
      have h1 : (layerStripStepSU2 A B).2.1.natDegree ≤ d + 1 := by
        rw [h2f]
        exact (natDegree_smul_le _ _).trans
          ((natDegree_add_le _ _).trans (max_le hA ((natDegree_smul_le _ _).trans hB)))
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      by_cases hkd : k = d + 1
      · rw [hkd]
        exact hA₁top
      · have hdk : d + 1 < k := by omega
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h1 hdk)
    have hB₁deg : (layerStripStepSU2 A B).2.2.natDegree ≤ d := by
      rw [h3f]
      refine (natDegree_smul_le _ _).trans ?_
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have h1 : (B - (B.coeff 0 / A.coeff 0) • A).natDegree ≤ d + 1 :=
        (natDegree_sub_le _ _).trans (max_le hB ((natDegree_smul_le _ _).trans hA))
      omega

    obtain ⟨him, hre⟩ := layerStripStepSU2_fst_coeff_invariant A B hA0 h0im h0re

    have hp0 : (B - (B.coeff 0 / A.coeff 0) • A).coeff 0 = 0 := by
      rw [coeff_sub, coeff_smul, smul_eq_mul]
      have e : B.coeff 0 / A.coeff 0 * A.coeff 0 = B.coeff 0 := div_mul_cancel₀ _ hA0
      rw [e, sub_self]
    have hXB1 : X * (layerStripStepSU2 A B).2.2
        = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
          • (B - (B.coeff 0 / A.coeff 0) • A)) := by
      have h := Polynomial.X_mul_divX_add (B - (B.coeff 0 / A.coeff 0) • A)
      rw [hp0, Polynomial.C_0, add_zero] at h
      rw [h3f]
      rw [show X * ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
            • (B - (B.coeff 0 / A.coeff 0) • A).divX)
          = ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)
            • (X * (B - (B.coeff 0 / A.coeff 0) • A).divX)) from by
        simp only [smul_eq_C_mul]; ring, h]
    set Ac := conjRevN (d + 1) A with hAc
    set Bc := conjRevN (d + 1) B with hBc
    set c : ℂ := ((((Real.sqrt (1 + Complex.normSq (B.coeff 0 / A.coeff 0)))⁻¹ : ℝ) : ℂ)) with hc
    set γ₀ := B.coeff 0 / A.coeff 0 with hγ₀
    have hA₁s : conjRevN (d + 1) (layerStripStepSU2 A B).2.1
        = C c * (Ac + C γ₀ * Bc) := by
      rw [h2f, smul_eq_C_mul, conjRevN_C_mul', starRingEnd_ofReal, conjRevN_add',
        conjRevN_smul', starRingEnd_apply, starRingEnd_apply, star_star, smul_eq_C_mul,
        show conjRevN (d + 1) A = Ac from rfl, show conjRevN (d + 1) B = Bc from rfl, ← hc]
    have hB₁s : conjRevN d (layerStripStepSU2 A B).2.2 = C c * (Bc - C ((starRingEnd ℂ) γ₀) * Ac) := by
      rw [← conjRevN_succ_X_mul d _ hB₁deg, hXB1, smul_eq_C_mul, conjRevN_C_mul',
        starRingEnd_ofReal, conjRevN_sub', conjRevN_smul', smul_eq_C_mul,
        show conjRevN (d + 1) A = Ac from rfl, show conjRevN (d + 1) B = Bc from rfl, ← hc]
    have hS : (layerStripStepSU2 A B).2.1 * conjRevN d (layerStripStepSU2 A B).2.1
        + (layerStripStepSU2 A B).2.2 * conjRevN d (layerStripStepSU2 A B).2.2 = X ^ d := by
      have e1 : X * ((layerStripStepSU2 A B).2.1 * conjRevN d (layerStripStepSU2 A B).2.1
          + (layerStripStepSU2 A B).2.2 * conjRevN d (layerStripStepSU2 A B).2.2) = X ^ (d + 1) := by
        rw [show X * ((layerStripStepSU2 A B).2.1 * conjRevN d (layerStripStepSU2 A B).2.1
              + (layerStripStepSU2 A B).2.2 * conjRevN d (layerStripStepSU2 A B).2.2)
            = (layerStripStepSU2 A B).2.1 * (X * conjRevN d (layerStripStepSU2 A B).2.1)
              + (X * (layerStripStepSU2 A B).2.2) * conjRevN d (layerStripStepSU2 A B).2.2 from by
          ring]
        rw [← conjRevN_succ_eq_X_mul_conjRevN d _ hA₁deg, hA₁s, hXB1, hB₁s]
        rw [h2f]
        simp only [smul_eq_C_mul]
        rw [show (C c * (A + C ((starRingEnd ℂ) γ₀) * B)) * (C c * (Ac + C γ₀ * Bc))
            + (C c * (B - C γ₀ * A)) * (C c * (Bc - C ((starRingEnd ℂ) γ₀) * Ac))
            = C c * C c * ((1 + C ((Complex.normSq γ₀ : ℝ) : ℂ)) * (A * Ac + B * Bc)) from by
          linear_combination (C c * C c * (A * Ac + B * Bc)) * (nlftC_mul_conj γ₀)]
        rw [← C_mul, nlftC_one_add, ← mul_assoc, ← C_mul, nlftC_sq γ₀, C_1, one_mul]
        rw [show Ac = conjRevN (d + 1) A from rfl, show Bc = conjRevN (d + 1) B from rfl, hid]
      rw [pow_succ'] at e1
      exact mul_left_cancel₀ Polynomial.X_ne_zero e1

    obtain ⟨ih1, ih2, ih3⟩ := ih (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2
      hA₁deg hB₁deg hS him hre
    have eG := ih1
    have eGA := congrArg Prod.fst eG
    have eGB := congrArg Prod.snd eG
    dsimp only [] at eGA eGB
    have hcombine : nlftSU2 ((B.coeff 0 / A.coeff 0)
        :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (d + 1)).gammas)
        = (A, B) := by
      show (c • ((nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1
              (layerStripStepSU2 A B).2.2 (d + 1)).gammas).1
            - (starRingEnd ℂ) γ₀
              • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1
                  (layerStripStepSU2 A B).2.2 (d + 1)).gammas).2)),
          c • (X * (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1
                (layerStripStepSU2 A B).2.2 (d + 1)).gammas).2
              + γ₀ • (nlftSU2 (layerStripSU2 (layerStripStepSU2 A B).2.1
                  (layerStripStepSU2 A B).2.2 (d + 1)).gammas).1)) = (A, B)
      rw [eGA, eGB, h2f, hXB1]
      simp only [smul_eq_C_mul]
      refine Prod.ext ?_ ?_
      · rw [show C c * (C c * (A + C ((starRingEnd ℂ) γ₀) * B)
              - C ((starRingEnd ℂ) γ₀) * (C c * (B - C γ₀ * A)))
            = C c * C c * ((1 + C ((Complex.normSq γ₀ : ℝ) : ℂ)) * A) from by
          linear_combination (C c * C c * A) * (nlftC_mul_conj γ₀)]
        rw [← C_mul, nlftC_one_add, ← mul_assoc, ← C_mul, nlftC_sq γ₀, C_1, one_mul]
      · show C c * (C c * (B - C γ₀ * A) + C γ₀ * (C c * (A + C ((starRingEnd ℂ) γ₀) * B))) = B
        rw [show C c * (C c * (B - C γ₀ * A) + C γ₀ * (C c * (A + C ((starRingEnd ℂ) γ₀) * B)))
            = C c * C c * ((1 + C ((Complex.normSq γ₀ : ℝ) : ℂ)) * B) from by
          linear_combination (C c * C c * B) * (nlftC_mul_conj γ₀)]
        rw [← C_mul, nlftC_one_add, ← mul_assoc, ← C_mul, nlftC_sq γ₀, C_1, one_mul]
    exact ⟨by rw [show (layerStripSU2 A B (d + 2)).gammas = (B.coeff 0 / A.coeff 0)
          :: (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (d + 1)).gammas
        from rfl, hcombine], by rw [show (layerStripSU2 A B (d + 2)).finalA
          = (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (d + 1)).finalA
        from rfl, ih2], by rw [show (layerStripSU2 A B (d + 2)).finalB
          = (layerStripSU2 (layerStripStepSU2 A B).2.1 (layerStripStepSU2 A B).2.2 (d + 1)).finalB
        from rfl, ih3]⟩

end Qatlib.Concepts.NativeNumerics.NlfftPipeline
