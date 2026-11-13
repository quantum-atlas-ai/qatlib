/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Qatlib.Papers.NonSparseHam09.MainResults.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral-Norm Tail Bound for Random Symmetric Circulant Matrices

This module formalizes Lemma 3 (Eq. (19)) of Childs and Kothari showing that for
the `(2M + 1) × (2M + 1)` real symmetric circulant matrix built from `M`
independent uniform signs, the probability that its spectral norm reaches
`4 d √(M log M)` is eventually bounded above by `(4 + ε) / M^{2 d^2 - 1}` for
every `d > 0` and `ε > 0`.

## Main statements

* `lemma3_circulant_tail`: Lemma 3, upper-bounding
  `probOf M (fun b => 4 * d * √(M log M) ≤ specNorm (circulantMatrix (signVec b)))`.

## References

* [Childs and Kothari, 2010][ChildsKothari2010], Section 4, Lemma 3, Eq. (19),
  p. 8 and Appendix, pp. 12--13.
-/

set_option autoImplicit false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

private lemma sum_odd_pair (M : ℕ) (f : Fin (2 * M + 1) → ℂ) :
    (∑ r, f r) = f 0 + ∑ j : Fin M,
      (f ⟨j.val + 1, by omega⟩ + f ⟨2 * M - j.val, by omega⟩) := by
  classical
  rw [Fin.sum_univ_succ]
  have hcast : (∑ i : Fin (2 * M), f i.succ) =
      ∑ i : Fin (M + M), f ⟨i.val + 1, by omega⟩ :=
    Fintype.sum_equiv (finCongr (show 2 * M = M + M by omega)) _ _ (fun _ => rfl)
  rw [hcast, Fin.sum_univ_add, Finset.sum_add_distrib]
  congr 1
  congr 1
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  congr 1
  apply Fin.ext
  simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_natAdd]
  omega

private def circulantFourier (M : ℕ) :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun r k => ((Real.sqrt (2 * M + 1 : ℕ) : ℂ))⁻¹ *
    ZMod.stdAddChar (N := 2 * M + 1) (r * k)

private lemma circulantFourier_unitary (M : ℕ) :
    circulantFourier M ∈ Matrix.unitaryGroup (Fin (2 * M + 1)) ℂ := by
  classical
  let c : ℂ := ((Real.sqrt (2 * M + 1 : ℕ) : ℂ))⁻¹
  have hc : c * c * (2 * M + 1 : ℕ) = 1 := by
    have hs : ((Real.sqrt (2 * M + 1 : ℕ) : ℂ)) ^ 2 = (2 * M + 1 : ℕ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (2 * M + 1) :
        (0 : ℝ) ≤ (2 * M + 1 : ℕ))
    dsimp [c]
    rw [← pow_two, inv_pow, hs, inv_mul_cancel₀]
    exact_mod_cast (show 2 * M + 1 ≠ 0 by omega)
  have hsum (a : Fin (2 * M + 1)) :
      (∑ r : Fin (2 * M + 1), ZMod.stdAddChar (N := 2 * M + 1) (r * a)) =
        if a = 0 then ((2 * M + 1 : ℕ) : ℂ) else 0 := by
    have hs := AddChar.sum_mulShift (R := ZMod (2 * M + 1)) (ZMod.finEquiv _ a)
      (ZMod.isPrimitive_stdAddChar (2 * M + 1))
    have hfin : (∑ r : Fin (2 * M + 1), ZMod.stdAddChar (N := 2 * M + 1) (r * a)) =
        ∑ r : ZMod (2 * M + 1), ZMod.stdAddChar (N := 2 * M + 1)
          (r * ZMod.finEquiv _ a) :=
      Fintype.sum_equiv (ZMod.finEquiv _).toEquiv _ _ (fun _ => rfl)
    rw [hfin, hs]
    simp
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (circulantFourier M)ᴴ * circulantFourier M = 1
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hentry (r : Fin (2 * M + 1)) :
      star (circulantFourier M r k) * circulantFourier M r l =
        (c * c) * ZMod.stdAddChar (N := 2 * M + 1) (r * (l - k)) := by
    calc
      _ = (c * c) * (star (ZMod.stdAddChar (N := 2 * M + 1) (r * k)) *
          ZMod.stdAddChar (N := 2 * M + 1) (r * l)) := by
        simp only [circulantFourier, RCLike.star_def, map_mul, map_inv₀,
          Complex.conj_ofReal, c]
        ring
      _ = _ := by
        rw [RCLike.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hentry]
  rw [← Finset.mul_sum, hsum]
  by_cases h : k = l
  · subst l
    simpa only [sub_self, ite_true, Matrix.one_apply_eq] using hc
  · simp [sub_eq_zero, h, Ne.symm h]

private def circulantWeight (M : ℕ) (k : Fin (2 * M + 1)) (j : Fin M) : ℝ :=
  2 * Real.cos (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
    (k.val : ℝ) / (2 * (M : ℝ) + 1))

private def circulantEigenvalue {M : ℕ} (s : Fin M → ℝ) (k : Fin (2 * M + 1)) : ℝ :=
  ∑ j, s j * circulantWeight M k j

private lemma circulant_shift {M : ℕ} (s : Fin M → ℝ) (i j : Fin (2 * M + 1)) :
    circulantMatrix s i j = circulantMatrix s 0 (j - i) := by
  have hmod : (j.val + (2 * M + 1) - i.val) % (2 * M + 1) = (j - i).val := by
    rw [Fin.val_sub]
    congr 1
    omega
  have hzero : ((j - i).val + (2 * M + 1) - 0) % (2 * M + 1) = (j - i).val := by
    simpa only [Nat.sub_zero, Nat.add_mod_right] using Nat.mod_eq_of_lt (j - i).isLt
  simp only [circulantMatrix, hmod, Fin.val_zero, hzero]

private lemma circulant_first_pos {M : ℕ} (s : Fin M → ℝ) (j : Fin M) :
    circulantMatrix s 0 ⟨j.val + 1, by omega⟩ = s j := by
  have hj : j.val + 1 ≤ M := by omega
  have hjN : j.val + 1 < 2 * M + 1 := by omega
  simp [circulantMatrix, Nat.add_mod_right, Nat.mod_eq_of_lt hjN, hj]

private lemma circulant_first_neg {M : ℕ} (s : Fin M → ℝ) (j : Fin M) :
    circulantMatrix s 0 ⟨2 * M - j.val, by omega⟩ = s j := by
  have hj0 : 2 * M - j.val ≠ 0 := by omega
  have hj : ¬2 * M - j.val ≤ M := by omega
  have hjN : 2 * M - j.val < 2 * M + 1 := by omega
  simp only [circulantMatrix, Fin.val_zero, Nat.sub_zero,
    Nat.add_mod_right, Nat.mod_eq_of_lt hjN, hj0, hj, ↓reduceDIte]
  congr 1
  apply Fin.ext
  dsimp
  omega

private lemma circulant_char_pair (M : ℕ) (j : Fin M) (k : Fin (2 * M + 1)) :
    ZMod.stdAddChar (N := 2 * M + 1) ((⟨j.val + 1, by omega⟩ : Fin (2 * M + 1)) * k) +
      ZMod.stdAddChar (N := 2 * M + 1) ((⟨2 * M - j.val, by omega⟩ : Fin (2 * M + 1)) * k) =
        (circulantWeight M k j : ℂ) := by
  let p : Fin (2 * M + 1) := ⟨j.val + 1, by omega⟩
  have hneg : (⟨2 * M - j.val, by omega⟩ : Fin (2 * M + 1)) = -p := by
    apply Fin.ext
    simp only [Fin.val_neg, p]
    split_ifs with h
    · have hz := congrArg Fin.val h
      change j.val + 1 = 0 at hz
      omega
    · omega
  have hcast : (p * k : ZMod (2 * M + 1)) =
      (((j.val + 1) * k.val : ℕ) : ZMod (2 * M + 1)) := by
    rw [Nat.cast_mul]
    congr 1
    · exact (ZMod.natCast_zmod_val (ZMod.finEquiv _ p)).symm
    · exact (ZMod.natCast_zmod_val (ZMod.finEquiv _ k)).symm
  have hexp : ZMod.stdAddChar (N := 2 * M + 1) (p * k) =
      Complex.exp ((2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
        (k.val : ℝ) / (2 * (M : ℝ) + 1) : ℝ) * Complex.I) := by
    rw [hcast]
    have h := ZMod.stdAddChar_coe (N := 2 * M + 1) (((j.val + 1) * k.val : ℕ) : ℤ)
    push_cast at h ⊢
    rw [h]
    congr 1
    ring
  change ZMod.stdAddChar (N := 2 * M + 1) (p * k) + _ = _
  rw [hneg]
  rw [neg_mul]
  rw [AddChar.map_neg_eq_conj, hexp]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show ∀ x : ℂ, x * -Complex.I = -x * Complex.I by intro x; ring,
    ← Complex.two_cos]
  simp [circulantWeight]

private lemma circulant_fourier_diagonal {M : ℕ} (s : Fin M → ℝ) :
    (circulantMatrix s).map Complex.ofReal * circulantFourier M =
      circulantFourier M * Matrix.diagonal (fun k => (circulantEigenvalue s k : ℂ)) := by
  classical
  have heigen (k : Fin (2 * M + 1)) :
      (∑ r : Fin (2 * M + 1), (circulantMatrix s 0 r : ℂ) *
        ZMod.stdAddChar (N := 2 * M + 1) (r * k)) = (circulantEigenvalue s k : ℂ) := by
    rw [sum_odd_pair]
    have hz : circulantMatrix s 0 0 = 0 := by simp [circulantMatrix]
    simp only [hz, Complex.ofReal_zero, zero_mul, zero_add]
    simp_rw [circulant_first_pos, circulant_first_neg, ← mul_add, circulant_char_pair]
    simp [circulantEigenvalue]
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.map_apply]
  calc
    _ = ∑ r : Fin (2 * M + 1), (circulantMatrix s i (i + r) : ℂ) *
        circulantFourier M (i + r) k :=
      (Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun _ => rfl)).symm
    _ = circulantFourier M i k *
        ∑ r : Fin (2 * M + 1), (circulantMatrix s 0 r : ℂ) *
          ZMod.stdAddChar (N := 2 * M + 1) (r * k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [circulant_shift]
      simp only [add_sub_cancel_left, circulantFourier]
      rw [add_mul, AddChar.map_add_eq_mul]
      ring
    _ = _ := by rw [heigen]

private lemma real_matrix_norm_le_complex {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ‖A‖ ≤ ‖A.map Complex.ofReal‖ := by
  have hn (v : n → ℝ) :
      ‖WithLp.toLp 2 (fun i => (v i : ℂ))‖ = ‖WithLp.toLp 2 v‖ := by
    simp only [EuclideanSpace.norm_eq, Complex.norm_real]
  change ‖(⇑(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ))) A‖ ≤ ‖A.map Complex.ofReal‖
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hmul : (A.map Complex.ofReal) *ᵥ (fun i => (x i : ℂ)) =
      fun i => ((A *ᵥ x.ofLp) i : ℂ) := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  have hb := (A.map Complex.ofReal).l2_opNorm_mulVec
    (WithLp.toLp 2 (fun i => (x i : ℂ)))
  change ‖WithLp.toLp 2 ((A.map Complex.ofReal) *ᵥ (fun i => (x i : ℂ)))‖ ≤
    ‖A.map Complex.ofReal‖ * ‖WithLp.toLp 2 (fun i => (x i : ℂ))‖ at hb
  rw [hmul, hn, hn] at hb
  exact hb

private lemma sign_mgf_eq (M : ℕ) (w : Fin M → ℝ) (t : ℝ) :
    (∑ b : Fin M → Bool, Real.exp (t * ∑ j, signVec b j * w j)) =
      (2 : ℝ) ^ M * ∏ j, Real.cosh (t * w j) := by
  classical
  calc
    _ = ∑ b : Fin M → Bool, ∏ j, Real.exp (t * signOf (b j) * w j) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      simp only [signVec, mul_assoc]
    _ = ∏ j : Fin M, ∑ b : Bool, Real.exp (t * signOf b * w j) :=
      (Fintype.prod_sum (fun (j : Fin M) (b : Bool) =>
        Real.exp (t * signOf b * w j))).symm
    _ = ∏ j : Fin M, 2 * Real.cosh (t * w j) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [signOf, Real.cosh_eq]
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

private lemma sign_mgf_le (M : ℕ) (w : Fin M → ℝ) (t : ℝ) :
    (∑ b : Fin M → Bool, Real.exp (t * ∑ j, signVec b j * w j)) ≤
      (2 : ℝ) ^ M * Real.exp (t ^ 2 * (∑ j, (w j) ^ 2) / 2) := by
  rw [sign_mgf_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∏ j : Fin M, Real.cosh (t * w j) ≤ ∏ j : Fin M, Real.exp ((t * w j) ^ 2 / 2) :=
      Finset.prod_le_prod₀ (fun j _ => (Real.cosh_pos _).le)
        (fun j _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp_rw [mul_pow, ← Finset.sum_div, ← Finset.mul_sum]

private lemma sign_tail_le (M : ℕ) (w : Fin M → ℝ)
    (hS : 0 < ∑ j, (w j) ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    probOf M (fun b => τ ≤ |∑ j, signVec b j * w j|) ≤
      2 * Real.exp (-τ ^ 2 / (2 * ∑ j, (w j) ^ 2)) := by
  classical
  let S := ∑ j, (w j) ^ 2
  let t := τ / S
  have ht : 0 < t := div_pos hτ hS
  have hcard :
      ((Finset.univ.filter (fun b : Fin M → Bool =>
        τ ≤ |∑ j, signVec b j * w j|)).card : ℝ) * Real.exp (t * τ) ≤
      ∑ b : Fin M → Bool,
        (Real.exp (t * ∑ j, signVec b j * w j) +
          Real.exp ((-t) * ∑ j, signVec b j * w j)) := by
    rw [Finset.natCast_card_filter, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    split_ifs with h
    · simp only [one_mul]
      rcases le_abs.mp h with h | h
      · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ht.le)).trans
          (le_add_of_nonneg_right (Real.exp_pos _).le)
      · apply (Real.exp_le_exp.mpr (show t * τ ≤ (-t) * ∑ j, signVec b j * w j by
          nlinarith)).trans
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    · simp only [zero_mul]
      positivity
  rw [Finset.sum_add_distrib] at hcard
  have hsum := add_le_add (sign_mgf_le M w t) (sign_mgf_le M w (-t))
  have hbound :
      ((Finset.univ.filter (fun b : Fin M → Bool =>
        τ ≤ |∑ j, signVec b j * w j|)).card : ℝ) * Real.exp (t * τ) ≤
        (2 : ℝ) ^ M * (2 * Real.exp (t ^ 2 * S / 2)) := by
    calc
      _ ≤ _ := hcard.trans hsum
      _ = _ := by simp only [neg_sq]; ring
  have hprob : probOf M (fun b => τ ≤ |∑ j, signVec b j * w j|) ≤
      2 * Real.exp (t ^ 2 * S / 2 - t * τ) := by
    rw [probOf, div_le_iff₀ (by positivity)]
    have he : Real.exp (t ^ 2 * S / 2 - t * τ) * Real.exp (t * τ) =
        Real.exp (t ^ 2 * S / 2) := by rw [← Real.exp_add]; congr 1; ring
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (t * τ))).mp
    calc
      _ ≤ _ := hbound
      _ = 2 * (Real.exp (t ^ 2 * S / 2 - t * τ) * Real.exp (t * τ)) *
          (2 : ℝ) ^ M := by rw [he]; ring
      _ = _ := by ring
  have hexp : t ^ 2 * S / 2 - t * τ = -τ ^ 2 / (2 * S) := by
    dsimp [t]
    field_simp [ne_of_gt hS]
    ring
  simpa only [hexp] using hprob

private lemma circulant_cos_sum (M k : ℕ) (hk : k ≠ 0) (hkN : k < 2 * M + 1) :
    (∑ j : Fin M, Real.cos (4 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (k : ℝ) /
      (2 * (M : ℝ) + 1))) = -(1 / 2 : ℝ) := by
  let N : ℝ := 2 * (M : ℝ) + 1
  let a : ℝ := 4 * Real.pi * (k : ℝ) / N
  have hN : 0 < N := by dsimp [N]; positivity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkNR : (k : ℝ) < N := by dsimp [N]; exact_mod_cast hkN
  have ha : a / 2 = 2 * Real.pi * (k : ℝ) / N := by dsimp [a]; ring
  have hsin : Real.sin (a / 2) ≠ 0 := by
    intro hs
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    rw [ha] at hn
    have hmul := (eq_div_iff (ne_of_gt hN)).mp hn
    have heq : (n : ℝ) * N = 2 * (k : ℝ) := by
      apply mul_right_cancel₀ Real.pi_ne_zero
      nlinarith [hmul]
    have hn0R : 0 < (n : ℝ) :=
      (mul_pos_iff_of_pos_right hN).mp (by rw [heq]; positivity)
    have hn2R : (n : ℝ) < 2 :=
      (mul_lt_mul_iff_left₀ hN).mp (by rw [heq]; linarith)
    have hn0 : 0 < n := by exact_mod_cast hn0R
    have hn2 : n < 2 := by exact_mod_cast hn2R
    have hn1 : n = 1 := by omega
    have hnR : (n : ℝ) = 1 := by exact_mod_cast hn1
    rw [hnR, one_mul] at heq
    dsimp [N] at heq
    have hodd : 2 * k = 2 * M + 1 := by exact_mod_cast heq.symm
    omega
  have hterm :
      (∑ j : Fin M, Real.cos (4 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (k : ℝ) /
        (2 * (M : ℝ) + 1))) =
      ∑ i ∈ Finset.range M, Real.cos (a * (i : ℝ) + a) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      Real.cos (4 * Real.pi * ((i + 1 : ℕ) : ℝ) * (k : ℝ) / (2 * (M : ℝ) + 1)))]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    dsimp [a, N]
    push_cast
    ring
  have hsum := Real.sin_mul_sum_cos M a a
  rw [← hterm] at hsum
  have hx := Real.two_mul_sin_mul_cos ((M : ℝ) * a / 2)
    (((M : ℝ) - 1) * a / 2 + a)
  have hsub : (M : ℝ) * a / 2 - (((M : ℝ) - 1) * a / 2 + a) = -(a / 2) := by
    ring
  have hadd : (M : ℝ) * a / 2 + (((M : ℝ) - 1) * a / 2 + a) = N * a / 2 := by
    dsimp [N]
    ring
  have haN : N * a / 2 = (2 * (k : ℝ)) * Real.pi := by
    dsimp [a]
    field_simp [ne_of_gt hN]
    ring
  have hz : Real.sin ((2 * (k : ℝ)) * Real.pi) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.sin_nat_mul_pi (2 * k)
  rw [hsub, hadd, haN, hz, Real.sin_neg, add_zero] at hx
  have hfactor : Real.sin (a / 2) *
      (2 * (∑ j : Fin M, Real.cos (4 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
        (k : ℝ) / (2 * (M : ℝ) + 1))) + 1) = 0 := by
    nlinarith [hsum, hx]
  have := (mul_eq_zero.mp hfactor).resolve_left hsin
  linarith

private lemma circulant_variance (M k : ℕ) (hk : k ≠ 0) (hkN : k < 2 * M + 1) :
    (∑ j : Fin M, (2 * Real.cos (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
      (k : ℝ) / (2 * (M : ℝ) + 1))) ^ 2) = 2 * (M : ℝ) - 1 := by
  have hpoint (j : Fin M) :
      (2 * Real.cos (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
        (k : ℝ) / (2 * (M : ℝ) + 1))) ^ 2 =
      2 + 2 * Real.cos (4 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
        (k : ℝ) / (2 * (M : ℝ) + 1)) := by
    have h := Real.cos_two_mul (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
      (k : ℝ) / (2 * (M : ℝ) + 1))
    have harg : 2 * (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) *
        (k : ℝ) / (2 * (M : ℝ) + 1)) =
      4 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (k : ℝ) / (2 * (M : ℝ) + 1) := by ring
    rw [harg] at h
    nlinarith [h]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [circulant_cos_sum M k hk hkN]
  ring

private lemma circulant_norm_le {M : ℕ} (s : Fin M → ℝ) :
    specNorm (circulantMatrix s) ≤
      ‖fun k : Fin (2 * M + 1) => (circulantEigenvalue s k : ℂ)‖ := by
  have hu := circulantFourier_unitary M
  have hn := congrArg norm (circulant_fourier_diagonal s)
  rw [CStarRing.norm_mul_mem_unitary _ hu, CStarRing.norm_mem_unitary_mul _ hu,
    Matrix.l2_opNorm_diagonal] at hn
  exact (real_matrix_norm_le_complex (circulantMatrix s)).trans hn.le

private lemma circulant_variance_bounds (M : ℕ) (hM : 2 ≤ M)
    (k : Fin (2 * M + 1)) :
    0 < ∑ j, (circulantWeight M k j) ^ 2 ∧
      (∑ j, (circulantWeight M k j) ^ 2) ≤ 4 * (M : ℝ) := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  by_cases hk : k = 0
  · subst k
    simp only [circulantWeight, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
      Real.cos_zero, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    constructor <;> nlinarith
  · have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    dsimp only [circulantWeight]
    rw [circulant_variance M k.val hk0 k.isLt]
    constructor <;> linarith

private lemma circulant_mode_tail (M : ℕ) (hM : 2 ≤ M) (d : ℝ) (hd : 0 < d)
    (k : Fin (2 * M + 1)) :
    probOf M (fun b => 4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ)) ≤
      |circulantEigenvalue (signVec b) k|) ≤ 2 / (M : ℝ) ^ (2 * d ^ 2) := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt ((M : ℝ) * Real.log (M : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos hMp hlog)
  obtain ⟨hS, hSle⟩ := circulant_variance_bounds M hM k
  have hτ : 0 < 4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ)) := by positivity
  have ht := sign_tail_le M (circulantWeight M k) hS _ hτ
  change probOf M (fun b => _ ≤ |circulantEigenvalue (signVec b) k|) ≤ _ at ht
  calc
    _ ≤ 2 * Real.exp (-(4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ))) ^ 2 /
        (2 * ∑ j, (circulantWeight M k j) ^ 2)) := ht
    _ ≤ 2 * Real.exp (-(2 * d ^ 2) * Real.log (M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ (mul_pos (by norm_num) hS)).mpr
      have hsq := Real.sq_sqrt (mul_pos hMp hlog).le
      nlinarith [mul_nonneg (sq_nonneg d) hlog.le,
        mul_nonneg (show 0 ≤ 2 * d ^ 2 * Real.log (M : ℝ) by positivity)
          (sub_nonneg.mpr hSle)]
    _ = _ := by
      rw [Real.rpow_def_of_pos hMp, div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

/-- Lemma 3: for any `d > 0` and `ε > 0`, the spectral norm of the random
symmetric circulant matrix of size `2M + 1` exceeds `4 d √(M log M)` with
probability at most `(4 + ε) / M^{2 d^2 - 1}` for all sufficiently large `M`. -/
theorem lemma3_circulant_tail (d : ℝ) (hd : 0 < d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in Filter.atTop,
      probOf M (fun b => 4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ))
          ≤ specNorm (circulantMatrix (signVec b)))
        ≤ (4 + ε) / (M : ℝ) ^ (2 * d ^ 2 - 1) := by
  classical
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  filter_upwards [eventually_ge_atTop (max 2 n)] with M hM
  have hM2 : 2 ≤ M := (le_max_left _ _).trans hM
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hMp : (0 : ℝ) < M := by linarith
  have hnM : (n : ℝ) ≤ M := by exact_mod_cast (le_max_right 2 n).trans hM
  have hεM : 2 ≤ ε * (M : ℝ) := by
    have := (div_lt_iff₀ hε).mp (hn.trans_le hnM)
    linarith
  let τ := 4 * d * Real.sqrt ((M : ℝ) * Real.log (M : ℝ))
  have hτ : 0 < τ := by
    dsimp [τ]
    exact mul_pos (by positivity)
      (Real.sqrt_pos.mpr (mul_pos hMp (Real.log_pos (by linarith))))
  let E := fun b : Fin M → Bool => τ ≤ specNorm (circulantMatrix (signVec b))
  let F := fun k : Fin (2 * M + 1) =>
    Finset.univ.filter (fun b : Fin M → Bool =>
      τ ≤ |circulantEigenvalue (signVec b) k|)
  have hcover : Finset.univ.filter E ⊆ Finset.univ.biUnion F := by
    intro b hb
    have hbτ : τ ≤ specNorm (circulantMatrix (signVec b)) := (Finset.mem_filter.mp hb).2
    have hex : ∃ k, τ ≤ |circulantEigenvalue (signVec b) k| := by
      by_contra! h
      have hlt : ‖fun k : Fin (2 * M + 1) =>
          (circulantEigenvalue (signVec b) k : ℂ)‖ < τ := by
        apply (pi_norm_lt_iff hτ).mpr
        intro k
        simpa only [Complex.norm_real, Real.norm_eq_abs] using h k
      exact (not_lt_of_ge hbτ) ((circulant_norm_le (signVec b)).trans_lt hlt)
    obtain ⟨k, hk⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hk⟩⟩
  have hprob : probOf M E ≤ ∑ k : Fin (2 * M + 1),
      probOf M (fun b => τ ≤ |circulantEigenvalue (signVec b) k|) := by
    unfold probOf
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ k : Fin (2 * M + 1),
        probOf M (fun b => τ ≤ |circulantEigenvalue (signVec b) k|) := hprob
    _ ≤ ∑ _k : Fin (2 * M + 1), 2 / (M : ℝ) ^ (2 * d ^ 2) :=
      Finset.sum_le_sum (fun k _ => circulant_mode_tail M hM2 d hd k)
    _ = (2 * (M : ℝ) + 1) * (2 / (M : ℝ) ^ (2 * d ^ 2)) := by simp
    _ ≤ (4 + ε) / (M : ℝ) ^ (2 * d ^ 2 - 1) := by
      rw [Real.rpow_sub hMp, Real.rpow_one, div_div_eq_mul_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by nlinarith)
        (Real.rpow_pos_of_pos hMp _).le

end Qatlib.Papers.NonSparseHam09.MainResults
