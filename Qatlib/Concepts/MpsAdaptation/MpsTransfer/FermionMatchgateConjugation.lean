/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matchgate conjugation of Majorana operators

This module proves that a matchgate on distinct modes with an anti-Hermitian generator acts
linearly on Majorana operators. `ad_exp_conjugation` identifies the conjugation with
`frameRotation` by comparing solutions of the commutator differential equation. This is the
covariance evolution mechanism for fermionic linear optics in [Bravyi2005Fermionic].

The single-gate identity extends to well-formed circuits through `frameRotationRun` and
`covarianceRun`. For inputs of the form `gaussianInput gl x`, the module also proves the
measurement update at a mode avoided by every gate of `gl`.

## Main statements

* `ad_exp_conjugation`: the Majorana conjugation formula for one well-formed matchgate.
* `covarianceMatrix_matchGateCircuit`: complete covariance propagation for a well-formed
  circuit.
* `matchGateCircuit_conj_majorana`: the Majorana frame action of a circuit.
* `covarianceMatrix_measurement_gaussianInput`: the measurement identity for a prepared input at
  an avoided mode.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
* [Terhal and DiVincenzo, 2002][TerhalDiVincenzo2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation

/-- The real-parameter derivative of `exp (s • H)` is `H * exp (t • H)` at `t`, with real
scalars cast to complex scalars. -/
theorem hasDerivAt_exp_smul_const_ofReal {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • H))
      (H * NormedSpace.exp ((t : ℂ) • H)) t := by
  set E := NormedSpace.exp ((t : ℂ) • H) with hE
  have hstep : ∀ u : ℂ,
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) H).smulRight E) u = u • (H * E) := by
    intro u
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul, smul_mul_assoc]
  have h1 := hasFDerivAt_exp_smul_const' ℂ H (t : ℂ)
  have h2 := (h1.restrictScalars ℝ).comp t Complex.ofRealCLM.hasFDerivAt
  have heq : (ContinuousLinearMap.restrictScalars ℝ
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) H).smulRight E) ∘SL Complex.ofRealCLM)
      = (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (H * E)) := by
    ext1
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', hstep, Complex.ofRealCLM_apply,
      Complex.ofReal_one, one_smul, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply]
  have hfin : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (H * E)) 1 = H * E := by
    simp
  have h3 := (h2.congr_fderiv heq).hasDerivAt
  exact hfin ▸ h3

/-- The real-parameter derivative of `exp (s • H)` is `exp (t • H) * H` at `t`, with real
scalars cast to complex scalars. -/
theorem hasDerivAt_exp_smul_const_ofReal' {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • H))
      (NormedSpace.exp ((t : ℂ) • H) * H) t := by
  have h1 := hasDerivAt_exp_smul_const_ofReal H t
  have hcomm : H * NormedSpace.exp ((t : ℂ) • H)
      = NormedSpace.exp ((t : ℂ) • H) * H := by
    have hc : Commute H ((t : ℂ) • H) := by
      show H * ((t : ℂ) • H) = ((t : ℂ) • H) * H
      rw [Algebra.mul_smul_comm, smul_mul_assoc]
    exact hc.exp_right.eq
  rw [hcomm] at h1
  exact h1

/-- The four local Majorana indices give the even and odd Majorana operators of `i`, followed by
those of `j`. -/
theorem majorana_localIndices_eq {n : ℕ} (i j : Fin n) :
    majorana (localIndices i j 0) = majoranaEven i
      ∧ majorana (localIndices i j 1) = majoranaOdd i
      ∧ majorana (localIndices i j 2) = majoranaEven j
      ∧ majorana (localIndices i j 3) = majoranaOdd j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : localIndices i j 0 = ⟨2 * i.val, by omega⟩ := rfl
    rw [h]; exact majorana_even_eq _ i
  · have h : localIndices i j 1 = ⟨2 * i.val + 1, by omega⟩ := rfl
    rw [h]; exact majorana_odd_eq _ i
  · have h : localIndices i j 2 = ⟨2 * j.val, by omega⟩ := rfl
    rw [h]; exact majorana_even_eq _ j
  · have h : localIndices i j 3 = ⟨2 * j.val + 1, by omega⟩ := rfl
    rw [h]; exact majorana_odd_eq _ j

/-- An anti-Hermitian two-by-two matrix has purely imaginary diagonal entries and lower
off-diagonal entry equal to minus the conjugate of the upper one. -/
theorem antiHermitean_facts {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) :
    (A 0 0).re = 0 ∧ (A 1 1).re = 0 ∧ A 1 0 = -star (A 0 1) := by
  have h00 : star (A 0 0) = -(A 0 0) := by
    have h := congrArg (fun M => M 0 0) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h11 : star (A 1 1) = -(A 1 1) := by
    have h := congrArg (fun M => M 1 1) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have h01 : star (A 0 1) = -(A 1 0) := by
    have h := congrArg (fun M => M 1 0) hA
    simpa [Matrix.conjTranspose_apply, Matrix.neg_apply] using! h
  have hre : (A 0 0).re = 0 := by
    have h := congrArg Complex.re h00
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  have hre11 : (A 1 1).re = 0 := by
    have h := congrArg Complex.re h11
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  have hrim : (A 0 1).re = -(A 1 0).re ∧ (A 0 1).im = (A 1 0).im := by
    have h := congrArg Complex.re h01
    rw [RCLike.star_def, Complex.conj_re, Complex.neg_re] at h
    have h2 := congrArg Complex.im h01
    rw [RCLike.star_def, Complex.conj_im, Complex.neg_im] at h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨hre, hre11, ?_⟩
  apply Complex.ext
  · show (A 1 0).re = (-star (A 0 1)).re
    rw [RCLike.star_def, Complex.neg_re, Complex.conj_re, hrim.1]; ring
  · show (A 1 0).im = (-star (A 0 1)).im
    rw [RCLike.star_def, Complex.neg_im, Complex.conj_im, hrim.2]; ring

/-- For real `c`, the complex product `Complex.I * (c * Complex.I)` equals `-c`. -/
private theorem I_mul_c_mul_I {c : ℝ} :
    Complex.I * (((c : ℝ) : ℂ) * Complex.I) = -((c : ℝ) : ℂ) := by
  rw [show Complex.I * (((c : ℝ) : ℂ) * Complex.I)
      = (((c : ℝ) : ℂ) * (Complex.I * Complex.I)) from by ring,
    Complex.I_mul_I]
  ring

/-- Casting a real number divided by 2 to the complex numbers commutes with division by 2. -/
private theorem ofReal_div_two {c : ℝ} :
    (((c / 2 : ℝ) : ℂ)) = (((c : ℝ) : ℂ) / 2) := by
  rw [Complex.ofReal_div]
  norm_num

/-- For an anti-Hermitian two-by-two matrix, the four stated complex coefficient expressions
equal the casts of the corresponding half real or imaginary parts. -/
theorem coef_real_cast {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = -A) :
    (-(Complex.I) * A 0 0 / 2 : ℂ) = (((A 0 0).im / 2 : ℝ) : ℂ)
      ∧ (-(Complex.I) * A 1 1 / 2 : ℂ) = (((A 1 1).im / 2 : ℝ) : ℂ)
      ∧ ((A 0 1 - A 1 0) / 4 : ℂ) = (((A 0 1).re / 2 : ℝ) : ℂ)
      ∧ (-(Complex.I) * (A 0 1 + A 1 0) / 4 : ℂ) = (((A 0 1).im / 2 : ℝ) : ℂ) := by
  obtain ⟨h00re, h11re, h10eq⟩ := antiHermitean_facts hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hx : A 0 0 = (((A 0 0).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [h00re, Complex.mul_im, Complex.I_im,
          Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im]
    show -(Complex.I) * A 0 0 / 2 = (((A 0 0).im / 2 : ℝ) : ℂ)
    conv_lhs => rw [hx]
    rw [neg_mul, I_mul_c_mul_I, neg_neg, ← ofReal_div_two]
  · have hx : A 1 1 = (((A 1 1).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [h11re, Complex.mul_im, Complex.I_im,
          Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im]
    show -(Complex.I) * A 1 1 / 2 = (((A 1 1).im / 2 : ℝ) : ℂ)
    conv_lhs => rw [hx]
    rw [neg_mul, I_mul_c_mul_I, neg_neg, ← ofReal_div_two]
  · have hsub : A 0 1 - A 1 0 = (((2 * (A 0 1).re : ℝ) : ℂ)) := by
      rw [h10eq]
      apply Complex.ext
      all_goals simp [RCLike.star_def, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re,
          Complex.ofReal_im]
      all_goals ring
    show (A 0 1 - A 1 0) / 4 = (((A 0 1).re / 2 : ℝ) : ℂ)
    conv_lhs => rw [hsub]
    have hd : (((2 * (A 0 1).re : ℝ) : ℂ) / 4) = (((A 0 1).re : ℝ) : ℂ) / 2 := by
      apply Complex.ext
      all_goals simp [Complex.ofReal_re, Complex.ofReal_im]
      all_goals ring
    rw [hd, ← ofReal_div_two]
  · have hsum : A 0 1 + A 1 0 = (((2 * (A 0 1).im : ℝ) : ℂ)) * Complex.I := by
      rw [h10eq]
      apply Complex.ext
      all_goals simp [Complex.add_re, Complex.add_im, RCLike.star_def, Complex.conj_re,
          Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im]
      all_goals ring
    show -(Complex.I) * (A 0 1 + A 1 0) / 4 = (((A 0 1).im / 2 : ℝ) : ℂ)
    conv_lhs => rw [hsum]
    rw [neg_mul, I_mul_c_mul_I, neg_neg]
    have hd : (((2 * (A 0 1).im : ℝ) : ℂ) / 4) = (((A 0 1).im : ℝ) : ℂ) / 2 := by
      apply Complex.ext
      all_goals simp [Complex.ofReal_re, Complex.ofReal_im]
      all_goals ring
    rw [hd, ← ofReal_div_two]

/-- For distinct modes and anti-Hermitian `A`, the quadratic generator is the scalar half-trace
term plus the upper-triangular Majorana-pair sum determined by `localFormSym A`. -/
theorem quadraticGenerator_eq_localForm {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) :
    quadraticGenerator i j A
      = ((A 0 0 + A 1 1) / 2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ)
        + ∑ p : Fin 4, ∑ q : Fin 4,
            (if p < q then ((localFormSym A p q : ℝ) : ℂ) else 0)
              • (majorana (localIndices i j p) * majorana (localIndices i j q)) := by
  obtain ⟨h0, h1, hX, hY⟩ := coef_real_cast hA
  obtain ⟨e0, e1, e2, e3⟩ := majorana_localIndices_eq i j
  rw [quadraticGenerator_eq_majoranaForm i j hij A]
  rw [← e0, ← e1, ← e2, ← e3, h0, h1, hX, hY]
  have hexp : ∑ p : Fin 4, ∑ q : Fin 4,
      (if p < q then ((localFormSym A p q : ℝ) : ℂ) else 0)
        • (majorana (localIndices i j p) * majorana (localIndices i j q))
      = (((A 0 0).im / 2 : ℝ) : ℂ)
          • (majorana (localIndices i j 0) * majorana (localIndices i j 1))
        + (((A 1 1).im / 2 : ℝ) : ℂ)
          • (majorana (localIndices i j 2) * majorana (localIndices i j 3))
        + (((A 0 1).re / 2 : ℝ) : ℂ)
          • (majorana (localIndices i j 0) * majorana (localIndices i j 2))
        + (((A 0 1).re / 2 : ℝ) : ℂ)
          • (majorana (localIndices i j 1) * majorana (localIndices i j 3))
        + (((A 0 1).im / 2 : ℝ) : ℂ)
          • (majorana (localIndices i j 0) * majorana (localIndices i j 3))
        + (-(((A 0 1).im / 2 : ℝ) : ℂ))
          • (majorana (localIndices i j 1) * majorana (localIndices i j 2)) := by
    simp only [Fin.sum_univ_four, localFormSym, Matrix.of_apply]
    simp +arith +decide
    module
  rw [hexp, smul_add, smul_sub]
  simp only [neg_smul]
  abel

/-- Every Majorana operator squares to the identity. -/
theorem majorana_sq {n : ℕ} (a : Fin (2 * n)) :
    majorana a * majorana a = 1 := by
  have h0 := majorana_clifford n a a
  rw [if_pos (rfl : a = a), two_smul] at h0
  have h2 : (2 : ℂ) • (majorana a * majorana a)
      = (2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
    rw [two_smul, two_smul]
    exact h0
  exact (smul_right_injective _ two_ne_zero) h2

/-- Majorana operators at distinct indices anticommute. -/
theorem majorana_anticommute {n : ℕ} (a b : Fin (2 * n)) (h : a ≠ b) :
    majorana a * majorana b = -(majorana b * majorana a) := by
  have hc : majorana a * majorana b + majorana b * majorana a
      = (0 : Matrix (Reg n) (Reg n) ℂ) := by
    have h2 := majorana_clifford n a b
    rw [if_neg h, zero_smul] at h2
    exact h2
  exact eq_neg_of_add_eq_zero_left hc

/-- A Majorana operator commutes with a product of two Majorana operators when its index differs
from both factor indices. -/
theorem majorana_mul_two_mul {n : ℕ} (x y z : Fin (2 * n)) (hxy : x ≠ y) (hxz : x ≠ z) :
    majorana x * (majorana y * majorana z)
      = majorana y * majorana z * majorana x := by
  rw [show majorana y * majorana z * majorana x
      = majorana y * (majorana z * majorana x) from Matrix.mul_assoc _ _ _]
  calc majorana x * (majorana y * majorana z)
      = (majorana x * majorana y) * majorana z := (Matrix.mul_assoc _ _ _).symm
    _ = (-(majorana y * majorana x)) * majorana z := by
        rw [majorana_anticommute x y hxy]
    _ = -(majorana y * (majorana x * majorana z)) := by
        rw [neg_mul, Matrix.mul_assoc]
    _ = -(majorana y * (-(majorana z * majorana x))) := by
        rw [majorana_anticommute x z hxz]
    _ = majorana y * (majorana z * majorana x) := by
        rw [Matrix.mul_neg, neg_neg]

/-- For distinct indices, `majorana p * majorana q * majorana p` equals `-majorana q`. -/
theorem majorana_mul_mul_self {n : ℕ} (p q : Fin (2 * n)) (hpq : p ≠ q) :
    majorana p * majorana q * majorana p = -majorana q := by
  calc majorana p * majorana q * majorana p
      = majorana p * (majorana q * majorana p) := Matrix.mul_assoc _ _ _
    _ = majorana p * (-(majorana p * majorana q)) := by
        rw [majorana_anticommute q p (Ne.symm hpq)]
    _ = -((majorana p * majorana p) * majorana q) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
    _ = -(1 * majorana q) := by rw [majorana_sq p]
    _ = -majorana q := by rw [Matrix.one_mul]

/-- The commutator of a Majorana operator with a pair of distinct local Majorana operators is
twice the signed sum selected by matching indices. -/
theorem majorana_pair_commutator {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (p q : Fin 4) (hpq : p ≠ q) (r : Fin (2 * n)) :
    majorana r * (majorana (localIndices i j p) * majorana (localIndices i j q))
      - (majorana (localIndices i j p) * majorana (localIndices i j q)) * majorana r
      = (2 : ℂ) • ((if localIndices i j p = r then majorana (localIndices i j q) else 0)
          - (if localIndices i j q = r then majorana (localIndices i j p) else 0)) := by
  have hne : localIndices i j p ≠ localIndices i j q :=
    fun h => hpq (localIndices_inj i j hij p q h)
  by_cases hr : r = localIndices i j p
  · subst hr
    have key := majorana_mul_mul_self (localIndices i j p) (localIndices i j q) hne
    rw [if_pos rfl, if_neg (fun hc => hne hc.symm), sub_zero]
    calc majorana (localIndices i j p)
          * (majorana (localIndices i j p) * majorana (localIndices i j q))
          - majorana (localIndices i j p) * majorana (localIndices i j q)
            * majorana (localIndices i j p)
        = (majorana (localIndices i j p) * majorana (localIndices i j p))
            * majorana (localIndices i j q)
          - majorana (localIndices i j p) * majorana (localIndices i j q)
            * majorana (localIndices i j p) := by
            rw [← Matrix.mul_assoc]
      _ = majorana (localIndices i j q)
            - (-(majorana (localIndices i j q))) := by
            rw [majorana_sq, Matrix.one_mul, key]
      _ = (2 : ℂ) • majorana (localIndices i j q) := by
            rw [two_smul, sub_neg_eq_add]
  · by_cases hr2 : r = localIndices i j q
    · subst hr2
      have key := majorana_mul_mul_self (localIndices i j q) (localIndices i j p)
        (Ne.symm hne)
      rw [if_neg hne, if_pos rfl]
      calc majorana (localIndices i j q)
            * (majorana (localIndices i j p) * majorana (localIndices i j q))
            - majorana (localIndices i j p) * majorana (localIndices i j q)
              * majorana (localIndices i j q)
          = (majorana (localIndices i j q) * majorana (localIndices i j p))
              * majorana (localIndices i j q)
            - majorana (localIndices i j p)
            * (majorana (localIndices i j q) * majorana (localIndices i j q)) := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = (-(majorana (localIndices i j p) * majorana (localIndices i j q)))
              * majorana (localIndices i j q)
            - majorana (localIndices i j p)
            * (majorana (localIndices i j q) * majorana (localIndices i j q)) := by
              rw [majorana_anticommute (localIndices i j q) (localIndices i j p)
                (Ne.symm hne)]
        _ = (-(majorana (localIndices i j p) * majorana (localIndices i j q)))
              * majorana (localIndices i j q)
            - majorana (localIndices i j p) * 1 := by
              rw [majorana_sq]
        _ = -majorana (localIndices i j p) - majorana (localIndices i j p) := by
              rw [neg_mul, Matrix.mul_assoc, majorana_sq, Matrix.mul_one]
        _ = (2 : ℂ) • (0 - majorana (localIndices i j p)) := by
            rw [two_smul]
            abel
    · have key := majorana_mul_two_mul r (localIndices i j p) (localIndices i j q) hr hr2
      rw [if_neg (Ne.symm hr), if_neg (Ne.symm hr2), sub_zero]
      rw [key, sub_self, smul_zero]

/-- Embeds a four-by-four real matrix into the selected Majorana block, setting every entry
outside that block to zero. -/
def frameZeroExtend {n : ℕ} (i j : Fin n) (K : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  Matrix.of fun a b =>
    if isLocalMajorana i j a ∧ isLocalMajorana i j b then K (localSlot i j a) (localSlot i j b)
    else 0

/-- At local row and column indices, zero extension returns the corresponding entry of the
original matrix. -/
theorem frameZeroExtend_apply_local {n : ℕ} (i j : Fin n) (K : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin (2 * n)) (ha : isLocalMajorana i j a) (hb : isLocalMajorana i j b) :
    frameZeroExtend i j K a b = K (localSlot i j a) (localSlot i j b) := by
  simp [frameZeroExtend, ha, hb]

/-- A row outside the selected modes is zero in `frameZeroExtend`. -/
theorem frameZeroExtend_apply_of_not_local {n : ℕ} (i j : Fin n) (K : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin (2 * n)) (ha : ¬ isLocalMajorana i j a) :
    frameZeroExtend i j K a b = 0 := by
  simp [frameZeroExtend, ha]

/-- A column outside the selected modes is zero in `frameZeroExtend`. -/
theorem frameZeroExtend_apply_of_not_local' {n : ℕ} (i j : Fin n) (K : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin (2 * n)) (hb : ¬ isLocalMajorana i j b) :
    frameZeroExtend i j K a b = 0 := by
  simp [frameZeroExtend, hb]

/-- Zero extension preserves addition of local matrices. -/
theorem frameZeroExtend_add {n : ℕ} (i j : Fin n) (K K' : Matrix (Fin 4) (Fin 4) ℝ) :
    frameZeroExtend i j (K + K') = frameZeroExtend i j K + frameZeroExtend i j K' := by
  ext a b
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · simp [frameZeroExtend_apply_local i j _ a b ha hb, Matrix.add_apply]
    · rw [Matrix.add_apply, frameZeroExtend_apply_of_not_local' i j (K + K') a b hb,
        frameZeroExtend_apply_of_not_local' i j K a b hb,
        frameZeroExtend_apply_of_not_local' i j K' a b hb, add_zero]
  · rw [Matrix.add_apply, frameZeroExtend_apply_of_not_local i j (K + K') a b ha,
      frameZeroExtend_apply_of_not_local i j K a b ha,
      frameZeroExtend_apply_of_not_local i j K' a b ha, add_zero]

/-- Zero extension commutes with multiplication by a real scalar. -/
theorem frameZeroExtend_smul {n : ℕ} (i j : Fin n) (t : ℝ) (K : Matrix (Fin 4) (Fin 4) ℝ) :
    frameZeroExtend i j (t • K) = t • frameZeroExtend i j K := by
  ext a b
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · simp [frameZeroExtend_apply_local i j _ a b ha hb, Matrix.smul_apply]
    · rw [Matrix.smul_apply, frameZeroExtend_apply_of_not_local' i j (t • K) a b hb,
        frameZeroExtend_apply_of_not_local' i j K a b hb, smul_zero]
  · rw [Matrix.smul_apply, frameZeroExtend_apply_of_not_local i j (t • K) a b ha,
      frameZeroExtend_apply_of_not_local i j K a b ha, smul_zero]

/-- For distinct selected modes, the product of two zero-extended matrices is the zero extension
of their product. -/
theorem frameZeroExtend_mul {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (K K' : Matrix (Fin 4) (Fin 4) ℝ) :
    frameZeroExtend i j K * frameZeroExtend i j K' = frameZeroExtend i j (K * K') := by
  ext a b
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · have hzero : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
          frameZeroExtend i j K a c * frameZeroExtend i j K' c b = 0 := by
        intro c hc
        rw [frameZeroExtend_apply_of_not_local' i j K a c hc, zero_mul]
      rw [Matrix.mul_apply, frameZeroExtend_apply_local i j (K * K') a b ha hb,
        sum_localMajorana i j hij
          (fun c => frameZeroExtend i j K a c * frameZeroExtend i j K' c b) hzero,
        Matrix.mul_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [frameZeroExtend_apply_local i j K a (localIndices i j q) ha
          (isLocalMajorana_localIndices i j q),
        frameZeroExtend_apply_local i j K' (localIndices i j q) b
          (isLocalMajorana_localIndices i j q) hb,
        localSlot_localIndices i j hij q]
    · rw [Matrix.mul_apply, frameZeroExtend_apply_of_not_local' i j (K * K') a b hb]
      exact Finset.sum_eq_zero fun c _ => by
        by_cases hc : isLocalMajorana i j c
        · rw [frameZeroExtend_apply_of_not_local' i j K' c b hb, mul_zero]
        · rw [frameZeroExtend_apply_of_not_local' i j K a c hc, zero_mul]
  · rw [Matrix.mul_apply, frameZeroExtend_apply_of_not_local i j (K * K') a b ha]
    exact Finset.sum_eq_zero fun c _ => by
      rw [frameZeroExtend_apply_of_not_local i j K a c ha, zero_mul]

/-- Zero extension sends the zero matrix to the zero matrix. -/
theorem frameZeroExtend_zero {n : ℕ} (i j : Fin n) :
    frameZeroExtend i j 0 = 0 := by
  ext a b
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · rw [frameZeroExtend_apply_local i j 0 a b ha hb]
      simp [Matrix.zero_apply]
    · rw [frameZeroExtend_apply_of_not_local' i j 0 a b hb, Matrix.zero_apply]
  · rw [frameZeroExtend_apply_of_not_local i j 0 a b ha, Matrix.zero_apply]

/-- For distinct selected modes, zero extension commutes with every positive power. -/
theorem frameZeroExtend_pow {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (K : Matrix (Fin 4) (Fin 4) ℝ) {m : ℕ} (hm : m ≠ 0) :
    (frameZeroExtend i j K) ^ m = frameZeroExtend i j (K ^ m) := by
  induction m with
  | zero => exact absurd rfl hm
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst hm0
        rw [Nat.zero_add, pow_one, pow_one]
      · rw [pow_succ, ih, frameZeroExtend_mul i j hij, pow_succ]
        exact hm0

/-- Zero extension preserves negation. -/
theorem frameZeroExtend_neg {n : ℕ} (i j : Fin n) (K : Matrix (Fin 4) (Fin 4) ℝ) :
    frameZeroExtend i j (-K) = -(frameZeroExtend i j K) := by
  have h : frameZeroExtend i j (-K) + frameZeroExtend i j K = 0 := by
    rw [← frameZeroExtend_add, neg_add_cancel, frameZeroExtend_zero]
  exact eq_neg_of_add_eq_zero_left h

/-- Zero extension preserves subtraction. -/
theorem frameZeroExtend_sub {n : ℕ} (i j : Fin n) (K K' : Matrix (Fin 4) (Fin 4) ℝ) :
    frameZeroExtend i j (K - K') = frameZeroExtend i j K - frameZeroExtend i j K' := by
  conv_lhs => rw [sub_eq_add_neg]
  rw [frameZeroExtend_add, frameZeroExtend_neg, sub_eq_add_neg]

/-- The additive homomorphism given by zero extension into the selected Majorana block. -/
def frameZeroExtendHom {n : ℕ} (i j : Fin n) :
    Matrix (Fin 4) (Fin 4) ℝ →+ Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ where
  toFun := frameZeroExtend i j
  map_zero' := frameZeroExtend_zero i j
  map_add' := frameZeroExtend_add i j

/-- Zero extension of local real matrices is continuous. -/
theorem continuous_frameZeroExtend {n : ℕ} (i j : Fin n) :
    Continuous (frameZeroExtend i j) := by
  have hlin : ∃ f : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ,
      ⇑f = frameZeroExtend i j := by
    refine ⟨{ toFun := frameZeroExtend i j,
              map_add' := frameZeroExtend_add i j,
              map_smul' := fun r K => frameZeroExtend_smul i j r K }, rfl⟩
  obtain ⟨f, hf⟩ := hlin
  have hc := LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) f
  rw [hf] at hc
  exact hc

/-- For distinct selected modes, the exponential of a zero-extended matrix is the identity plus
the zero extension of its exponential minus the local identity. -/
theorem frameZeroExtend_exp {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (Y : Matrix (Fin 4) (Fin 4) ℝ) :
    NormedSpace.exp (frameZeroExtend i j Y)
      = 1 + frameZeroExtend i j (NormedSpace.exp Y - 1) := by
  have hg : HasSum (fun k : ℕ => ((Nat.factorial k)⁻¹ : ℝ) • Y ^ k) (NormedSpace.exp Y) :=
    NormedSpace.exp_series_hasSum_exp' Y
  have hmap : HasSum (fun k : ℕ => ((Nat.factorial k)⁻¹ : ℝ) • frameZeroExtend i j (Y ^ k))
      (frameZeroExtend i j (NormedSpace.exp Y)) := by
    have h := HasSum.map hg (frameZeroExtendHom i j) (continuous_frameZeroExtend i j)
    have hfun : (⇑(frameZeroExtendHom i j) ∘ fun k : ℕ => ((Nat.factorial k)⁻¹ : ℝ) • Y ^ k)
        = fun k : ℕ => ((Nat.factorial k)⁻¹ : ℝ) • frameZeroExtend i j (Y ^ k) := by
      funext k
      simp [frameZeroExtendHom, frameZeroExtend_smul]
    rw [hfun] at h
    exact h
  have hd : HasSum
      (fun k : ℕ => if k = 0 then
        (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) - frameZeroExtend i j 1 else 0)
      (1 - frameZeroExtend i j 1) :=
    hasSum_single 0 (fun b hb => if_neg hb)
  have hcomb : HasSum
      (fun k : ℕ => (((Nat.factorial k)⁻¹ : ℝ) • frameZeroExtend i j (Y ^ k)
        + (if k = 0 then
          (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) - frameZeroExtend i j 1 else 0)))
      (frameZeroExtend i j (NormedSpace.exp Y) + (1 - frameZeroExtend i j 1)) :=
    HasSum.add hmap hd
  have hpt : ∀ k : ℕ, ((Nat.factorial k)⁻¹ : ℝ) • (frameZeroExtend i j Y) ^ k
      = ((Nat.factorial k)⁻¹ : ℝ) • frameZeroExtend i j (Y ^ k)
        + (if k = 0 then
          (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) - frameZeroExtend i j 1 else 0) := by
    intro k
    match k with
    | 0 =>
        simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero,
          if_true]
        abel
    | (k + 1) =>
        rw [if_neg (Nat.succ_ne_zero k),
          frameZeroExtend_pow i j hij Y (Nat.succ_ne_zero k), add_zero]
  have hfun : (fun k : ℕ => ((Nat.factorial k)⁻¹ : ℝ) • (frameZeroExtend i j Y) ^ k)
      = fun k : ℕ => (((Nat.factorial k)⁻¹ : ℝ) • frameZeroExtend i j (Y ^ k)
        + (if k = 0 then
          (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) - frameZeroExtend i j 1 else 0)) :=
    funext hpt
  rw [← hfun] at hcomb
  have hexpFz : NormedSpace.exp (frameZeroExtend i j Y)
      = frameZeroExtend i j (NormedSpace.exp Y) + (1 - frameZeroExtend i j 1) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    exact hcomb.tsum_eq
  rw [hexpFz, frameZeroExtend_sub]
  abel

/-- A local Majorana index differs from an index outside the selected modes. -/
theorem local_ne_away {n : ℕ} (i j : Fin n) {a b : Fin (2 * n)}
    (ha : isLocalMajorana i j a) (hb : ¬ isLocalMajorana i j b) : a ≠ b := by
  intro h
  exact hb (by rw [← h]; exact ha)

/-- For distinct modes, extending `X` by the identity equals the full identity plus the zero
extension of `X - 1`. -/
theorem frameExtend_eq_one_add {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (X : Matrix (Fin 4) (Fin 4) ℝ) :
    frameExtend i j X = 1 + frameZeroExtend i j (X - 1) := by
  ext a b
  by_cases ha : isLocalMajorana i j a
  · by_cases hb : isLocalMajorana i j b
    · rw [Matrix.add_apply, Matrix.one_apply,
        frameZeroExtend_apply_local i j (X - 1) a b ha hb,
        Matrix.sub_apply, Matrix.one_apply, frameExtend_apply_local i j X a b ha hb]
      by_cases hslot : localSlot i j a = localSlot i j b
      · have hab : a = b := localSlot_inj_local i j hij a b ha hb hslot
        rw [if_pos hab, if_pos hslot]
        ring
      · have hab : a ≠ b := fun h => hslot (congrArg (localSlot i j) h)
        rw [if_neg hab, if_neg hslot, zero_add, sub_zero]
    · rw [frameExtend_apply_left_local_right_away i j X a b ha hb,
        Matrix.add_apply, Matrix.one_apply, if_neg (local_ne_away i j ha hb),
        frameZeroExtend_apply_of_not_local' i j (X - 1) a b hb, zero_add]
  · rw [Matrix.add_apply, Matrix.one_apply,
      frameZeroExtend_apply_of_not_local i j (X - 1) a b ha, add_zero]
    by_cases hb : isLocalMajorana i j b
    · rw [frameExtend_apply_right_local_left_away i j X a b ha hb,
        if_neg (Ne.symm (local_ne_away i j hb ha))]
    · rw [frameExtend_apply_away i j X a b ha hb]

/-- For distinct modes, `frameRotation` is the exponential of the zero extension of twice the
local skew-symmetric form. -/
theorem frameRotation_eq_exp {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    frameRotation i j A
      = NormedSpace.exp (frameZeroExtend i j ((2 : ℝ) • localFormMatrix A)) := by
  have hR : localRotation A = NormedSpace.exp ((2 : ℝ) • localFormMatrix A) := rfl
  rw [← frameExtend_localRotation i j A, frameExtend_eq_one_add i j hij, hR,
    ← frameZeroExtend_exp i j hij]

/-- The entry `localFormSym A p q` vanishes unless `p < q`. -/
theorem localFormSym_eq_zero_of_not_lt {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 4}
    (h : ¬ p < q) : localFormSym A p q = 0 := by
  unfold localFormSym
  simp only [Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6
  · obtain ⟨e1, e2⟩ := h1; subst e1; subst e2; exact absurd (by decide) h
  · obtain ⟨e1, e2⟩ := h2; subst e1; subst e2; exact absurd (by decide) h
  · obtain ⟨e1, e2⟩ := h3; subst e1; subst e2; exact absurd (by decide) h
  · obtain ⟨e1, e2⟩ := h4; subst e1; subst e2; exact absurd (by decide) h
  · obtain ⟨e1, e2⟩ := h5; subst e1; subst e2; exact absurd (by decide) h
  · obtain ⟨e1, e2⟩ := h6; subst e1; subst e2; exact absurd (by decide) h
  · rfl

/-- The upper-triangular indicators can be removed from the antisymmetrized entries of
`localFormSym`. -/
theorem localFormSym_ite_sub {A : Matrix (Fin 2) (Fin 2) ℂ} (s d : Fin 4) :
    ((if s < d then localFormSym A s d else 0) - (if d < s then localFormSym A d s else 0) : ℝ)
      = localFormSym A s d - localFormSym A d s := by
  by_cases h1 : s < d
  · rw [if_pos h1, if_neg (Fin.lt_asymm h1), localFormSym_eq_zero_of_not_lt (Fin.lt_asymm h1)]
  · by_cases h2 : d < s
    · rw [if_neg h1, if_pos h2, localFormSym_eq_zero_of_not_lt h1]
    · rw [if_neg h1, if_neg h2, localFormSym_eq_zero_of_not_lt h1,
        localFormSym_eq_zero_of_not_lt h2]

/-- A factor of 2 can be factored out of the difference of the two indicated triangular
coefficients. -/
theorem ite_coef_sub {f : Fin 4 → Fin 4 → ℝ} (s d : Fin 4) :
    ((if s < d then 2 * f s d else 0) - (if d < s then 2 * f d s else 0) : ℝ)
      = 2 * ((if s < d then f s d else 0) - (if d < s then f d s else 0)) := by
  by_cases h1 : s < d <;> by_cases h2 : d < s
  all_goals simp [h1, h2]
  all_goals ring

/-- A real coefficient acting on twice a complex matrix equals twice that coefficient acting on
the matrix. -/
private theorem coef_two_smul {n : ℕ} (x : ℝ) (γ : Matrix (Reg n) (Reg n) ℂ) :
    ((x : ℝ) : ℂ) • ((2 : ℂ) • γ) = (((2 * x : ℝ) : ℂ)) • γ := by
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- For distinct modes, the commutator with an upper-triangular Majorana-pair sum is the
Majorana row combination with twice the antisymmetrized coefficients. -/
theorem majorana_pairSum_commutator {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (f : Fin 4 → Fin 4 → ℝ) (s : Fin 4) :
    majorana (localIndices i j s)
      * (∑ p : Fin 4, ∑ q : Fin 4,
          (if p < q then ((f p q : ℝ) : ℂ) else 0)
            • (majorana (localIndices i j p) * majorana (localIndices i j q)))
      - (∑ p : Fin 4, ∑ q : Fin 4,
          (if p < q then ((f p q : ℝ) : ℂ) else 0)
            • (majorana (localIndices i j p) * majorana (localIndices i j q)))
        * majorana (localIndices i j s)
      = ∑ d : Fin 4,
          (((2 * ((if s < d then f s d else 0) - (if d < s then f d s else 0)) : ℝ) : ℂ))
          • (majorana (localIndices i j d) : Matrix (Reg n) (Reg n) ℂ) := by
  have hinj : ∀ p s : Fin 4, localIndices i j p = localIndices i j s ↔ p = s := fun p s =>
    ⟨localIndices_inj i j hij p s, fun h => by rw [h]⟩
  simp only [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Algebra.mul_smul_comm, smul_mul_assoc]
  have hcom : ∀ p q : Fin 4,
      ((if p < q then ((f p q : ℝ) : ℂ) else 0)
        • (majorana (localIndices i j s) * (majorana (localIndices i j p)
            * majorana (localIndices i j q))))
      - ((if p < q then ((f p q : ℝ) : ℂ) else 0)
        • (majorana (localIndices i j p) * majorana (localIndices i j q)
            * majorana (localIndices i j s)))
      = (if p = s then (((2 * (if p < q then f p q else 0) : ℝ) : ℂ)
          • (majorana (localIndices i j q) : Matrix (Reg n) (Reg n) ℂ)) else 0)
      - (if q = s then (((2 * (if p < q then f p q else 0) : ℝ) : ℂ)
          • (majorana (localIndices i j p) : Matrix (Reg n) (Reg n) ℂ)) else 0) := by
    intro p q
    by_cases hpq : p < q
    · rw [← smul_sub, if_pos hpq, majorana_pair_commutator i j hij p q (ne_of_lt hpq)
        (localIndices i j s)]
      simp only [hinj]
      rw [smul_sub, smul_sub]
      by_cases hps : p = s
      · rw [← hps]
        have hqp : q ≠ p := fun h => by rw [h] at hpq; exact absurd hpq (lt_irrefl p)
        rw [if_pos rfl, if_neg hqp, if_pos rfl, if_neg hqp, smul_zero, smul_zero,
          sub_zero, sub_zero, coef_two_smul, if_pos hpq]
      · by_cases hqs : q = s
        · rw [← hqs] at hps ⊢
          rw [if_neg hps, if_pos rfl, if_neg hps, if_pos rfl, smul_zero, smul_zero,
            zero_sub, zero_sub, coef_two_smul, if_pos hpq]
        · rw [if_neg hps, if_neg hqs, if_neg hps, if_neg hqs]
          simp
    · rw [if_neg hpq]
      simp [hpq]
  simp only [hcom]
  simp only [Finset.sum_sub_distrib]
  have hA : ∑ p : Fin 4, ∑ q : Fin 4,
      (if p = s then (((2 * (if p < q then f p q else 0) : ℝ) : ℂ)
        • (majorana (localIndices i j q) : Matrix (Reg n) (Reg n) ℂ)) else 0)
    = ∑ d : Fin 4,
        (((if s < d then 2 * f s d else 0 : ℝ) : ℂ)
          • (majorana (localIndices i j d) : Matrix (Reg n) (Reg n) ℂ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ s)]
    by_cases h : s < q <;> simp [h]
  have hB : ∑ p : Fin 4, ∑ q : Fin 4,
      (if q = s then (((2 * (if p < q then f p q else 0) : ℝ) : ℂ)
        • (majorana (localIndices i j p) : Matrix (Reg n) (Reg n) ℂ)) else 0)
    = ∑ d : Fin 4,
        (((if d < s then 2 * f d s else 0 : ℝ) : ℂ)
          • (majorana (localIndices i j d) : Matrix (Reg n) (Reg n) ℂ)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ s)]
    by_cases h : p < s <;> simp [h]
  rw [hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← ite_coef_sub, Complex.ofReal_sub, sub_smul]

/-- For distinct modes and anti-Hermitian `A`, the commutator with `quadraticGenerator i j A`
has Majorana coefficients given by the zero-extended matrix `2 • localFormMatrix A`. -/
theorem majorana_generator_commutator {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) (r : Fin (2 * n)) :
    majorana r * quadraticGenerator i j A - quadraticGenerator i j A * majorana r
      = ∑ c : Fin (2 * n),
          ((frameZeroExtend i j ((2 : ℝ) • localFormMatrix A) r c : ℝ) : ℂ) • majorana c := by
  rw [quadraticGenerator_eq_localForm i j hij A hA]
  have hT : majorana r * (((A 0 0 + A 1 1) / 2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ))
      - (((A 0 0 + A 1 1) / 2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ)) * majorana r = 0 := by
    rw [Algebra.mul_smul_comm, smul_mul_assoc, Matrix.one_mul, Matrix.mul_one, sub_self]
  rw [Matrix.mul_add, Matrix.add_mul, add_sub_add_comm, hT, zero_add]
  by_cases hr : isLocalMajorana i j r
  · obtain ⟨s, hs⟩ := exists_localIndices i j r hr
    subst hs
    have hzero : ∀ c : Fin (2 * n), ¬ isLocalMajorana i j c →
        ((frameZeroExtend i j ((2 : ℝ) • localFormMatrix A) (localIndices i j s) c : ℝ) : ℂ)
          • majorana c = 0 := by
      intro c hc
      rw [frameZeroExtend_apply_of_not_local' i j _ _ c hc, Complex.ofReal_zero, zero_smul]
    rw [sum_localMajorana i j hij _ hzero]
    rw [majorana_pairSum_commutator i j hij (fun p q => localFormSym A p q) s]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [frameZeroExtend_apply_local i j ((2 : ℝ) • localFormMatrix A)
      (localIndices i j s) (localIndices i j d)
      (isLocalMajorana_localIndices i j s) (isLocalMajorana_localIndices i j d),
      localSlot_localIndices i j hij s, localSlot_localIndices i j hij d]
    rw [localFormSym_ite_sub]
    rfl
  · have hterm : ∀ p q : Fin 4,
        ((if p < q then ((localFormSym A p q : ℝ) : ℂ) else 0)
          • (majorana r * (majorana (localIndices i j p)
              * majorana (localIndices i j q))))
        - ((if p < q then ((localFormSym A p q : ℝ) : ℂ) else 0)
          • (majorana (localIndices i j p)
              * majorana (localIndices i j q) * majorana r)) = 0 := by
      intro p q
      by_cases hpq : p < q
      · rw [if_pos hpq]
        have hnp : r ≠ localIndices i j p := fun h =>
          hr (h ▸ isLocalMajorana_localIndices i j p)
        have hnq : r ≠ localIndices i j q := fun h =>
          hr (h ▸ isLocalMajorana_localIndices i j q)
        rw [majorana_mul_two_mul r (localIndices i j p) (localIndices i j q) hnp hnq,
          sub_self]
      · rw [if_neg hpq, zero_smul, zero_smul, sub_self]
    have hrow : ∑ c : Fin (2 * n),
        ((frameZeroExtend i j ((2 : ℝ) • localFormMatrix A) r c : ℝ) : ℂ) • majorana c
        = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [frameZeroExtend_apply_of_not_local i j _ r c hr, Complex.ofReal_zero, zero_smul]
    simp only [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib,
      Algebra.mul_smul_comm, smul_mul_assoc, hterm, Finset.sum_const_zero, hrow]

/-- The continuous real-linear map taking a real matrix to the Majorana combination specified by
its row `a`. -/
noncomputable def majoranaRowCLM {n : ℕ} (a : Fin (2 * n)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ →L[ℝ] Matrix (Reg n) (Reg n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ c : Fin (2 * n), ((X a c : ℝ) : ℂ) • majorana c
      map_add' := fun X Y => by
        simp only [Matrix.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun c _ => by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
          rfl }

/-- The row continuous linear map evaluates to `majoranaInBasis X a`. -/
theorem majoranaRowCLM_apply {n : ℕ} (a : Fin (2 * n))
    (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    majoranaRowCLM a X = majoranaInBasis X a := rfl

/-- Using the identity frame in `majoranaInBasis` returns the original Majorana operator. -/
theorem majoranaInBasis_one {n : ℕ} (a : Fin (2 * n)) :
    majoranaInBasis (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) a = majorana a := by
  simp only [majoranaInBasis, Matrix.one_apply, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (Ne.symm hb)]
  · intro hb; exact absurd (Finset.mem_univ a) hb

/-- The derivative of the Majorana combination in frame `exp (s • K)` is the combination in
frame `exp (t • K) * K`. -/
theorem hasDerivAt_majoranaInBasis_exp {n : ℕ}
    (K : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (a : Fin (2 * n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => majoranaInBasis (NormedSpace.exp (s • K)) a)
      (majoranaInBasis (NormedSpace.exp (t • K) * K) a) t := by
  have h1 : HasFDerivAt (fun X => majoranaRowCLM a X) (majoranaRowCLM a)
      ((fun s : ℝ => NormedSpace.exp (s • K)) t) :=
    ContinuousLinearMap.hasFDerivAt (majoranaRowCLM a)
  have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • K))
      (NormedSpace.exp (t • K) * K) t := hasDerivAt_exp_smul_const K t
  exact HasFDerivAt.comp_hasDerivAt (l := fun X => majoranaRowCLM a X)
    (l' := majoranaRowCLM a) (f := fun s : ℝ => NormedSpace.exp (s • K))
    (f' := NormedSpace.exp (t • K) * K) (x := t) h1 h2

/-- If commutators with `H` are represented by `K`, the Majorana combination in frame `E * K`
equals the commutator of the combination in frame `E` with `H`. -/
theorem majoranaInBasis_mul_apply {n : ℕ}
    (K : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (H : Matrix (Reg n) (Reg n) ℂ)
    (hcomm : ∀ d : Fin (2 * n), majorana d * H - H * majorana d
      = ∑ c : Fin (2 * n), ((K d c : ℝ) : ℂ) • majorana c)
    (E : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (a : Fin (2 * n)) :
    majoranaInBasis (E * K) a = majoranaInBasis E a * H - H * majoranaInBasis E a := by
  have hL : majoranaInBasis (E * K) a
      = ∑ c : Fin (2 * n), ∑ d : Fin (2 * n),
          (((E a d : ℝ) : ℂ) * ((K d c : ℝ) : ℂ)) • majorana c := by
    simp only [majoranaInBasis, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_smul]
  have hR : majoranaInBasis E a * H - H * majoranaInBasis E a
      = ∑ d : Fin (2 * n), ∑ c : Fin (2 * n),
          (((E a d : ℝ) : ℂ) * ((K d c : ℝ) : ℂ)) • majorana c := by
    simp only [majoranaInBasis, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      Algebra.mul_smul_comm, ← Finset.sum_sub_distrib, ← smul_sub, hcomm, Finset.smul_sum,
      smul_smul]
  rw [hL, hR, Finset.sum_comm]

/-- The derivative of `exp (-s • H) * majorana a * exp (s • H)` is its product with `H` minus
the product in the opposite order. -/
theorem hasDerivAt_conjCurve {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (a : Fin (2 * n))
    (u : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-H)) * majorana a
        * NormedSpace.exp ((s : ℂ) • H))
      (NormedSpace.exp ((u : ℂ) • (-H)) * majorana a * NormedSpace.exp ((u : ℂ) • H) * H
        - H * (NormedSpace.exp ((u : ℂ) • (-H)) * majorana a
          * NormedSpace.exp ((u : ℂ) • H))) u := by
  have h1 := hasDerivAt_exp_smul_const_ofReal (-H) u
  have h2 := hasDerivAt_exp_smul_const_ofReal' H u
  have h3 := h1.mul_const (majorana a)
  have h4 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-H)) * majorana a
      * NormedSpace.exp ((s : ℂ) • H))
      ((-H * NormedSpace.exp ((u : ℂ) • (-H))) * majorana a
        * NormedSpace.exp ((u : ℂ) • H)
        + NormedSpace.exp ((u : ℂ) • (-H)) * majorana a
        * (NormedSpace.exp ((u : ℂ) • H) * H)) u := h3.mul h2
  have heq : ((-H * NormedSpace.exp ((u : ℂ) • (-H))) * majorana a
        * NormedSpace.exp ((u : ℂ) • H)
        + NormedSpace.exp ((u : ℂ) • (-H)) * majorana a
          * (NormedSpace.exp ((u : ℂ) • H) * H))
      = NormedSpace.exp ((u : ℂ) • (-H)) * majorana a
          * NormedSpace.exp ((u : ℂ) • H) * H
        - H * (NormedSpace.exp ((u : ℂ) • (-H)) * majorana a
          * NormedSpace.exp ((u : ℂ) • H)) := by
    rw [neg_mul, neg_mul, neg_mul]
    simp only [Matrix.mul_assoc]
    abel
  rwa [heq] at h4

/-- Two matrix-valued curves satisfying the same constant commutator differential equation and
agreeing at zero agree at every real parameter. -/
theorem eq_of_hasDerivAt_adTransport {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ)
    (P C : ℝ → Matrix (Reg n) (Reg n) ℂ)
    (hP : ∀ s : ℝ, HasDerivAt P (P s * H - H * P s) s)
    (hC : ∀ s : ℝ, HasDerivAt C (C s * H - H * C s) s)
    (h0 : P 0 = C 0) (s : ℝ) : P s = C s := by
  have hd : ∀ u : ℝ, HasDerivAt (fun v => P v - C v)
      ((P u - C u) * H - H * (P u - C u)) u := by
    intro u
    have h := (hP u).sub (hC u)
    have heq : (P u * H - H * P u) - (C u * H - H * C u)
        = (P u - C u) * H - H * (P u - C u) := by
      rw [sub_mul, mul_sub]
      abel
    rw [heq] at h
    exact h
  have hcommH' : ∀ u : ℝ, NormedSpace.exp ((u : ℂ) • (-H)) * H
      = H * NormedSpace.exp ((u : ℂ) • (-H)) := by
    intro u
    have hc : Commute H ((u : ℂ) • (-H)) := by
      show H * ((u : ℂ) • (-H)) = ((u : ℂ) • (-H)) * H
      rw [Algebra.mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg]
    exact hc.exp_right.symm.eq
  have hZ : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => NormedSpace.exp ((v : ℂ) • H) * (P v - C v))
      (NormedSpace.exp ((u : ℂ) • H) * (P u - C u) * H) u := by
    intro u
    have h1 := hasDerivAt_exp_smul_const_ofReal' H u
    have h3 : HasDerivAt (fun v : ℝ => NormedSpace.exp ((v : ℂ) • H) * (P v - C v))
        (NormedSpace.exp ((u : ℂ) • H) * H * (P u - C u)
          + NormedSpace.exp ((u : ℂ) • H) * ((P u - C u) * H - H * (P u - C u))) u :=
      h1.mul (hd u)
    have heq : NormedSpace.exp ((u : ℂ) • H) * H * (P u - C u)
          + NormedSpace.exp ((u : ℂ) • H) * ((P u - C u) * H - H * (P u - C u))
        = NormedSpace.exp ((u : ℂ) • H) * (P u - C u) * H := by
      rw [Matrix.mul_sub (NormedSpace.exp ((u : ℂ) • H)) ((P u - C u) * H)
        (H * (P u - C u)), ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      abel
    rwa [heq] at h3
  have hE : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => NormedSpace.exp ((v : ℂ) • H) * (P v - C v)
        * NormedSpace.exp ((v : ℂ) • (-H))) 0 u := by
    intro u
    have hg := hasDerivAt_exp_smul_const_ofReal' (-H) u
    have h4 : HasDerivAt
        (fun v : ℝ => NormedSpace.exp ((v : ℂ) • H) * (P v - C v)
          * NormedSpace.exp ((v : ℂ) • (-H)))
        (NormedSpace.exp ((u : ℂ) • H) * (P u - C u) * H
          * NormedSpace.exp ((u : ℂ) • (-H))
          + NormedSpace.exp ((u : ℂ) • H) * (P u - C u)
            * (NormedSpace.exp ((u : ℂ) • (-H)) * (-H))) u := (hZ u).mul hg
    have heq : NormedSpace.exp ((u : ℂ) • H) * (P u - C u) * H
          * NormedSpace.exp ((u : ℂ) • (-H))
          + NormedSpace.exp ((u : ℂ) • H) * (P u - C u)
            * (NormedSpace.exp ((u : ℂ) • (-H)) * (-H)) = 0 := by
      rw [mul_neg, mul_neg, hcommH' u, ← Matrix.mul_assoc, add_neg_cancel]
    rwa [heq] at h4
  have hf' : ∀ x : ℝ, fderiv ℝ
      (fun v : ℝ => NormedSpace.exp ((v : ℂ) • H) * (P v - C v)
        * NormedSpace.exp ((v : ℂ) • (-H))) x = 0 := by
    intro x
    rw [(hE x).hasFDerivAt.fderiv]
    ext i
    simp
  have h0u := is_const_of_fderiv_eq_zero
    (fun x => (hE x).differentiableAt) hf' 0 s
  rw [Complex.ofReal_zero, zero_smul, zero_smul, NormedSpace.exp_zero, h0, sub_self,
    one_mul, mul_one] at h0u

  have h1 : NormedSpace.exp ((s : ℂ) • H) * (P s - C s)
      * NormedSpace.exp ((s : ℂ) • (-H)) = 0 := h0u.symm
  have hcommHH : Commute ((s : ℂ) • (-H)) ((s : ℂ) • H) := by
    show (s : ℂ) • (-H) * (s : ℂ) • H = (s : ℂ) • H * (s : ℂ) • (-H)
    simp only [smul_neg, neg_mul, mul_neg]
  have hmem : ∀ Y : Matrix (Reg n) (Reg n) ℂ,
      Y ∈ Metric.eball 0 (NormedSpace.expSeries ℂ (Matrix (Reg n) (Reg n) ℂ)).radius :=
    fun Y => (NormedSpace.expSeries_radius_eq_top ℂ (Matrix (Reg n) (Reg n) ℂ)).symm ▸
      (edist_lt_top Y 0)
  have hYX : NormedSpace.exp ((s : ℂ) • (-H)) * NormedSpace.exp ((s : ℂ) • H) = 1 := by
    have h := NormedSpace.exp_add_of_commute_of_mem_ball
      (𝕂 := ℂ) (𝔸 := Matrix (Reg n) (Reg n) ℂ) hcommHH (hmem _) (hmem _)
    have hsum : (s : ℂ) • (-H) + (s : ℂ) • H = 0 := by
      rw [← smul_add, neg_add_cancel, smul_zero]
    calc NormedSpace.exp ((s : ℂ) • (-H)) * NormedSpace.exp ((s : ℂ) • H)
        = NormedSpace.exp ((s : ℂ) • (-H) + (s : ℂ) • H) := h.symm
      _ = NormedSpace.exp 0 := by rw [hsum]
      _ = 1 := NormedSpace.exp_zero
  have hD : P s - C s = NormedSpace.exp ((s : ℂ) • (-H))
      * (NormedSpace.exp ((s : ℂ) • H) * (P s - C s)
        * NormedSpace.exp ((s : ℂ) • (-H)))
      * NormedSpace.exp ((s : ℂ) • H) := by
    calc P s - C s = (NormedSpace.exp ((s : ℂ) • (-H))
          * NormedSpace.exp ((s : ℂ) • H)) * ((P s - C s)
            * (NormedSpace.exp ((s : ℂ) • (-H)) * NormedSpace.exp ((s : ℂ) • H))) := by
            rw [hYX, one_mul, mul_one]
      _ = NormedSpace.exp ((s : ℂ) • (-H)) * (NormedSpace.exp ((s : ℂ) • H)
            * (P s - C s) * NormedSpace.exp ((s : ℂ) • (-H)))
          * NormedSpace.exp ((s : ℂ) • H) := by
            simp only [Matrix.mul_assoc]
  have hfinal : P s - C s = 0 := by
    rw [hD, h1, mul_zero, zero_mul]
  exact sub_eq_zero.mp hfinal

/-- For distinct modes and anti-Hermitian `A`, conjugating a Majorana operator by `matchGate i j
A` gives its combination in the frame `frameRotation i j A`. -/
theorem ad_exp_conjugation {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) (a : Fin (2 * n)) :
    (matchGate i j A)ᴴ * majorana a * matchGate i j A
      = majoranaInBasis (frameRotation i j A) a := by
  have hcommrow : ∀ d : Fin (2 * n),
      majorana d * quadraticGenerator i j A - quadraticGenerator i j A * majorana d
      = ∑ c : Fin (2 * n),
          ((frameZeroExtend i j ((2 : ℝ) • localFormMatrix A) d c : ℝ) : ℂ) • majorana c :=
    fun d => majorana_generator_commutator i j hij A hA d
  have hP : ∀ s : ℝ, HasDerivAt
      (fun v : ℝ => NormedSpace.exp ((v : ℂ) • (-(quadraticGenerator i j A))) * majorana a
        * NormedSpace.exp ((v : ℂ) • (quadraticGenerator i j A)))
      (NormedSpace.exp ((s : ℂ) • (-(quadraticGenerator i j A))) * majorana a
        * NormedSpace.exp ((s : ℂ) • (quadraticGenerator i j A)) * quadraticGenerator i j A
        - quadraticGenerator i j A
          * (NormedSpace.exp ((s : ℂ) • (-(quadraticGenerator i j A))) * majorana a
            * NormedSpace.exp ((s : ℂ) • (quadraticGenerator i j A)))) s :=
    fun s => hasDerivAt_conjCurve (quadraticGenerator i j A) a s
  have hC : ∀ s : ℝ, HasDerivAt
      (fun v => majoranaInBasis
        (NormedSpace.exp (v • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))) a)
      (majoranaInBasis
        (NormedSpace.exp (s • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))
          * frameZeroExtend i j ((2 : ℝ) • localFormMatrix A)) a) s :=
    fun s => hasDerivAt_majoranaInBasis_exp
      (frameZeroExtend i j ((2 : ℝ) • localFormMatrix A)) a s
  have hC' : ∀ s : ℝ, HasDerivAt
      (fun v => majoranaInBasis
        (NormedSpace.exp (v • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))) a)
      (majoranaInBasis
        (NormedSpace.exp (s • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))) a
        * quadraticGenerator i j A
        - quadraticGenerator i j A
          * majoranaInBasis
            (NormedSpace.exp (s • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))) a) s := by
    intro s
    have h := hC s
    rw [majoranaInBasis_mul_apply _ _ hcommrow _ a] at h
    exact h
  have h0 : (fun v : ℝ => NormedSpace.exp ((v : ℂ) • (-(quadraticGenerator i j A)))
        * majorana a
        * NormedSpace.exp ((v : ℂ) • (quadraticGenerator i j A))) 0
      = (fun v : ℝ => majoranaInBasis
        (NormedSpace.exp (v • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))) a) 0 := by
    show (NormedSpace.exp ((0 : ℂ) • (-(quadraticGenerator i j A))) * majorana a)
        * NormedSpace.exp ((0 : ℂ) • (quadraticGenerator i j A))
      = majoranaInBasis
        (NormedSpace.exp (0 • frameZeroExtend i j ((2 : ℝ) • localFormMatrix A))) a
    rw [zero_smul, NormedSpace.exp_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one,
      zero_smul, NormedSpace.exp_zero, majoranaInBasis_one]
  have hfin := eq_of_hasDerivAt_adTransport (quadraticGenerator i j A) _ _ hP hC' h0 1
  rw [Complex.ofReal_one, one_smul, one_smul, one_smul] at hfin
  have hL : (matchGate i j A)ᴴ * majorana a * matchGate i j A
      = NormedSpace.exp (-(quadraticGenerator i j A)) * majorana a
        * NormedSpace.exp (quadraticGenerator i j A) := by
    rw [matchGate, ← Matrix.exp_conjTranspose,
      quadraticGenerator_skewHermitian i j A hA]
  rw [hL, hfin, frameRotation_eq_exp i j hij A]

/-- The condition that a gate uses distinct modes and an anti-Hermitian two-by-two generator. -/
def matchGateWellFormed {n : ℕ} (g : Fin n × Fin n × Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  g.1 ≠ g.2.1 ∧ g.2.2ᴴ = -(g.2.2)

/-- A well-formed matchgate satisfies the Majorana conjugation condition `matchGateBridged`. -/
theorem matchGateBridged_of_wellFormed {n : ℕ}
    {g : Fin n × Fin n × Matrix (Fin 2) (Fin 2) ℂ} (h : matchGateWellFormed g) :
    matchGateBridged g :=
  ⟨h.2, fun a => ad_exp_conjugation g.1 g.2.1 h.1 g.2.2 h.2 a⟩

/-- A circuit of well-formed matchgates transforms the covariance matrix according to the
complete updates of `covarianceRun`, as in the fermionic linear-optics evolution of
[Bravyi2005Fermionic]. -/
theorem covarianceMatrix_matchGateCircuit {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g) (M : Matrix (Reg n) (Reg n) ℂ) :
    covarianceMatrix (matchGateCircuitOp gl * M) = covarianceRun gl (covarianceMatrix M) :=
  covarianceMatrix_matchGateCircuit_of_bridged gl
    (fun g hg => matchGateBridged_of_wellFormed (h g hg)) M

/-- A matchgate circuit with anti-Hermitian generator matrices has a unitary circuit operator. -/
theorem matchGateCircuitOp_mem_unitaryGroup {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, g.2.2ᴴ = -(g.2.2)) :
    matchGateCircuitOp gl ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction gl with
  | nil => simp [matchGateCircuitOp]
  | cons g rest ih =>
      obtain ⟨i, j, A⟩ := g
      have hg := matchGate_unitary i j A (h (i, j, A) List.mem_cons_self)
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      exact Submonoid.mul_mem _ hg hr

/-- The Majorana combination in frame `S * T` is the row combination, with coefficients from
`S`, of the Majorana combinations in frame `T`. -/
theorem majoranaInBasis_mul {n : ℕ} (S T : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) :
    majoranaInBasis (S * T) a
      = ∑ c : Fin (2 * n), ((S a c : ℝ) : ℂ) • majoranaInBasis T c := by
  simp only [majoranaInBasis, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

/-- The product of the full Majorana frame rotations of a circuit in list order, with the empty
product equal to the identity. -/
def frameRotationRun {n : ℕ} : MatchGateCircuit n
    → Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ
  | [] => 1
  | (i, j, A) :: rest => frameRotation i j A * frameRotationRun rest

/-- Conjugation by a well-formed matchgate circuit sends the Majorana combination in frame `S`
to that in frame `S * frameRotationRun gl`. -/
theorem matchGateCircuitOp_conj_majoranaInBasis {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g) (S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (a : Fin (2 * n)) :
    (matchGateCircuitOp gl)ᴴ * majoranaInBasis S a * matchGateCircuitOp gl
      = majoranaInBasis (S * frameRotationRun gl) a := by
  induction gl generalizing S with
  | nil =>
      show (1 : Matrix (Reg n) (Reg n) ℂ)ᴴ * majoranaInBasis S a * 1
        = majoranaInBasis (S * (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)) a
      rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  | cons g rest ih =>
      obtain ⟨i, j, A⟩ := g
      obtain ⟨hij, hA⟩ := h (i, j, A) List.mem_cons_self
      have hrest : ∀ q ∈ rest, matchGateWellFormed q := fun q hq =>
        h q (List.mem_cons_of_mem _ hq)
      have hstep : (matchGate i j A)ᴴ * majoranaInBasis S a * matchGate i j A
          = majoranaInBasis (S * frameRotation i j A) a := by
        have hlin : (matchGate i j A)ᴴ * majoranaInBasis S a * matchGate i j A
            = ∑ c : Fin (2 * n), ((S a c : ℝ) : ℂ)
              • ((matchGate i j A)ᴴ * majorana c * matchGate i j A) := by
          simp only [majoranaInBasis, Matrix.mul_sum, Matrix.sum_mul,
            Algebra.mul_smul_comm, smul_mul_assoc]
        rw [hlin, Finset.sum_congr rfl fun c _ => by
          rw [ad_exp_conjugation i j hij A hA c]]
        rw [majoranaInBasis_mul]
      show (matchGate i j A * matchGateCircuitOp rest)ᴴ * majoranaInBasis S a
          * (matchGate i j A * matchGateCircuitOp rest)
        = majoranaInBasis (S * (frameRotation i j A * frameRotationRun rest)) a
      have hregroup : (matchGate i j A * matchGateCircuitOp rest)ᴴ * majoranaInBasis S a
            * (matchGate i j A * matchGateCircuitOp rest)
          = (matchGateCircuitOp rest)ᴴ
            * ((matchGate i j A)ᴴ * majoranaInBasis S a * matchGate i j A)
            * matchGateCircuitOp rest := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      rw [hregroup, hstep, ih hrest (S * frameRotation i j A), ← Matrix.mul_assoc]

/-- Conjugating a Majorana operator by a well-formed matchgate circuit gives the corresponding
row combination in `frameRotationRun gl`. -/
theorem matchGateCircuit_conj_majorana {n : ℕ} (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g) (a : Fin (2 * n)) :
    (matchGateCircuitOp gl)ᴴ * majorana a * matchGateCircuitOp gl
      = majoranaInBasis (frameRotationRun gl) a := by
  have h := matchGateCircuitOp_conj_majoranaInBasis gl h 1 a
  rw [Matrix.one_mul, majoranaInBasis_one] at h
  exact h

/-- The frame rotation of a matchgate leaves every Majorana operator outside its two modes
unchanged. -/
theorem majoranaInBasis_frameRotation_of_not_local {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) {a : Fin (2 * n)} (ha : ¬ isLocalMajorana i j a) :
    majoranaInBasis (frameRotation i j A) a = majorana a := by
  simp only [majoranaInBasis]
  rw [Finset.sum_eq_single a]
  · rw [frameRotation_apply_away_eq i j A a ha]
    simp
  · intro c _ hc
    by_cases hcl : isLocalMajorana i j c
    · rw [frameRotation_apply_right_local_left_away i j A a c ha hcl]
      simp
    · rw [frameRotation_apply_away_neq i j A a c ha hcl (Ne.symm hc)]
      simp
  · intro hna
    exact absurd (Finset.mem_univ a) hna

/-- The number operator is half the identity minus `Complex.I / 4` times the commutator of the
mode's two Majorana operators. -/
theorem numberOp_eq_half_sub_commutator {n : ℕ} (k : Fin n) :
    numberOp k = (1 / 2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ)
      - (Complex.I / 4) • (majorana (majoranaIndices k 0) * majorana (majoranaIndices k 1)
          - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0)) := by
  have hcomm := majorana_commutator_mode k
  have hsm : (Complex.I / 4) • (majorana (majoranaIndices k 0) * majorana (majoranaIndices k 1)
        - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0))
      = (-(1 / 2 : ℂ)) • (numberOp k + numberOp k - 1) := by
    rw [hcomm, smul_smul, smul_smul]
    have hII : Complex.I / 4 * 2 * Complex.I = -(1 / 2 : ℂ) := by
      have h2 : Complex.I / 4 * 2 * Complex.I = (Complex.I * Complex.I) / 2 := by
        ring
      rw [h2, Complex.I_mul_I]
      norm_num
    rw [hII]
  rw [hsm, neg_smul, sub_neg_eq_add, ← smul_add]
  have h1 : (1 : Matrix (Reg n) (Reg n) ℂ) + (numberOp k + numberOp k - 1)
      = numberOp k + numberOp k := by
    abel
  rw [h1, ← two_smul ℂ (numberOp k), smul_smul]
  norm_num

/-- A well-formed matchgate leaves the number operator of a distinct third mode invariant under
conjugation. -/
theorem matchGate_conj_numberOp {n : ℕ} (i j k : Fin n) (hij : i ≠ j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A) (hik : i ≠ k) (hjk : j ≠ k) :
    (matchGate i j A)ᴴ * numberOp k * matchGate i j A = numberOp k := by
  have hU := matchGate_unitary i j A hA
  have hU1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.star_eq_conjTranspose] at hU1 hU2
  have haway : ∀ b : Fin 2, ¬ isLocalMajorana i j (majoranaIndices k b) := by
    intro b hloc
    rcases hloc with h | h | h | h
    · exact hik (((majoranaIndices_eq k i b 0).mp h).1).symm
    · exact hik (((majoranaIndices_eq k i b 1).mp h).1).symm
    · exact hjk (((majoranaIndices_eq k j b 0).mp h).1).symm
    · exact hjk (((majoranaIndices_eq k j b 1).mp h).1).symm
  have hconjγ : ∀ b : Fin 2,
      (matchGate i j A)ᴴ * majorana (majoranaIndices k b) * matchGate i j A
        = majorana (majoranaIndices k b) := by
    intro b
    rw [ad_exp_conjugation i j hij A hA (majoranaIndices k b),
      majoranaInBasis_frameRotation_of_not_local i j A (haway b)]
  have hkey : ∀ X Y : Matrix (Reg n) (Reg n) ℂ,
      (matchGate i j A)ᴴ * (X * Y) * matchGate i j A
        = ((matchGate i j A)ᴴ * X * matchGate i j A)
          * ((matchGate i j A)ᴴ * Y * matchGate i j A) := by
    intro X Y
    simp only [Matrix.mul_assoc]
    have h1 : matchGate i j A * ((matchGate i j A)ᴴ * (Y * matchGate i j A))
        = Y * matchGate i j A := by
      rw [← Matrix.mul_assoc, hU2, one_mul]
    rw [h1]
  have hC : (matchGate i j A)ᴴ * (majorana (majoranaIndices k 0)
        * majorana (majoranaIndices k 1)
        - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0))
      * matchGate i j A
      = majorana (majoranaIndices k 0) * majorana (majoranaIndices k 1)
          - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hkey _ _, hkey _ _,
      hconjγ 0, hconjγ 1]
  rw [numberOp_eq_half_sub_commutator k, Matrix.mul_sub, Matrix.sub_mul]
  have hs1 : (matchGate i j A)ᴴ * ((1 / 2 : ℂ)
        • (1 : Matrix (Reg n) (Reg n) ℂ)) * matchGate i j A
      = (1 / 2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
    rw [Matrix.mul_assoc, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      Matrix.one_mul, hU1]
  have hs2 : (matchGate i j A)ᴴ * ((Complex.I / 4) • (majorana (majoranaIndices k 0)
        * majorana (majoranaIndices k 1)
        - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0)))
      * matchGate i j A
      = (Complex.I / 4) • (majorana (majoranaIndices k 0) * majorana (majoranaIndices k 1)
          - majorana (majoranaIndices k 1) * majorana (majoranaIndices k 0)) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hC]
  rw [hs1, hs2]

/-- The condition that neither of a gate's two mode indices equals `k`. -/
def avoidsMode {n : ℕ} (k : Fin n) (g : Fin n × Fin n × Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  g.1 ≠ k ∧ g.2.1 ≠ k

/-- A measurement projector commutes with a well-formed matchgate whose two modes differ from
the measured mode. -/
theorem measurementProjector_mul_matchGate {n : ℕ} (k : Fin n) (b : Bool)
    {i j : Fin n} (hij : i ≠ j) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = -A)
    (hik : i ≠ k) (hjk : j ≠ k) :
    measurementProjector k b * matchGate i j A
      = matchGate i j A * measurementProjector k b := by
  have hU := matchGate_unitary i j A hA
  have hU2 := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.star_eq_conjTranspose] at hU2
  have hconj := matchGate_conj_numberOp i j k hij A hA hik hjk
  have hnu : numberOp k * matchGate i j A = matchGate i j A * numberOp k := by
    calc numberOp k * matchGate i j A
        = (matchGate i j A * (matchGate i j A)ᴴ) * numberOp k * matchGate i j A := by
          rw [hU2, one_mul]
      _ = matchGate i j A * ((matchGate i j A)ᴴ * numberOp k * matchGate i j A) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = matchGate i j A * numberOp k := by rw [hconj]
  cases b with
  | true => exact hnu
  | false =>
      show (1 - numberOp k) * matchGate i j A
        = matchGate i j A * (1 - numberOp k)
      rw [one_sub_mul, mul_one_sub, hnu]

/-- A measurement projector commutes with a circuit when every gate is well formed and avoids
the measured mode. -/
theorem measurementProjector_mul_matchGateCircuitOp {n : ℕ} (k : Fin n) (b : Bool)
    (gl : MatchGateCircuit n)
    (h : ∀ g ∈ gl, matchGateWellFormed g ∧ avoidsMode k g) :
    measurementProjector k b * matchGateCircuitOp gl
      = matchGateCircuitOp gl * measurementProjector k b := by
  induction gl with
  | nil => simp [matchGateCircuitOp]
  | cons g rest ih =>
      obtain ⟨i, j, A⟩ := g
      obtain ⟨hwf, hav⟩ := h (i, j, A) List.mem_cons_self
      have hrest := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      show measurementProjector k b * (matchGate i j A * matchGateCircuitOp rest)
          = (matchGate i j A * matchGateCircuitOp rest) * measurementProjector k b
      rw [← Matrix.mul_assoc,
        measurementProjector_mul_matchGate k b hwf.1 A hwf.2 hav.1 hav.2,
        Matrix.mul_assoc, hrest, ← Matrix.mul_assoc]

/-- The diagonal rank-one matrix selecting the register configuration `x`. -/
def fockProjector {n : ℕ} (x : Reg n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y z => if y = x ∧ z = x then 1 else 0

/-- An entry of `fockProjector x` is 1 when both indices equal `x`, and is 0 otherwise. -/
theorem fockProjector_apply {n : ℕ} (x y z : Reg n) :
    fockProjector x y z = if y = x ∧ z = x then 1 else 0 := rfl

/-- The Fock basis projector is Hermitian. -/
theorem fockProjector_hermitian {n : ℕ} (x : Reg n) :
    (fockProjector x)ᴴ = fockProjector x := by
  ext y z
  rw [Matrix.conjTranspose_apply]
  simp only [fockProjector_apply]
  by_cases h : z = x ∧ y = x
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, star_one]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩), star_zero]

/-- The Fock basis projector is idempotent. -/
theorem fockProjector_idem {n : ℕ} (x : Reg n) :
    fockProjector x * fockProjector x = fockProjector x := by
  ext y z
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · by_cases hyx : y = x <;> by_cases hzx : z = x <;>
      simp [fockProjector_apply, hyx, hzx]
  · intro w _ hw
    rw [fockProjector_apply x y w, if_neg (fun hh => hw hh.2), zero_mul]
  · intro hna
    exact absurd (Finset.mem_univ x) hna

/-- The Fock basis projector has trace 1. -/
theorem fockProjector_trace {n : ℕ} (x : Reg n) : Matrix.trace (fockProjector x) = 1 := by
  simp [Matrix.trace, fockProjector]

/-- A mode measurement projector preserves `fockProjector x` if `x k = b` and annihilates it
otherwise. -/
theorem measurementProjector_mul_fockProjector {n : ℕ} (k : Fin n) (b : Bool) (x : Reg n) :
    measurementProjector k b * fockProjector x
      = (if x k = b then (1 : ℂ) else 0) • fockProjector x := by
  ext y z
  rw [Matrix.mul_apply, Finset.sum_eq_single x, measurementProjector_apply k b y x]
  · by_cases hxy : x = y
    · subst hxy
      by_cases hxb : x k = b <;> simp [fockProjector_apply, hxb]
    · have h1 : ¬ (x = y ∧ x k = b) := fun hh => hxy hh.1
      have h2 : ¬ (y = x ∧ z = x) := fun hh => hxy hh.1.symm
      rw [fockProjector_apply x x z, if_neg h1, zero_mul]
      simp [fockProjector_apply, h2]
  · intro w _ hw
    rw [fockProjector_apply x w z, if_neg (fun hh => hw hh.1), mul_zero]
  · intro hna
    exact absurd (Finset.mem_univ x) hna

/-- The matrix obtained by multiplying the circuit operator by the Fock basis projector for `x`. -/
def gaussianInput {n : ℕ} (gl : MatchGateCircuit n) (x : Reg n) :
    Matrix (Reg n) (Reg n) ℂ :=
  matchGateCircuitOp gl * fockProjector x

/-- If every gate is well formed and avoids `k`, projection of `gaussianInput gl x` at `k`
preserves it when `x k = b` and gives zero otherwise. -/
theorem measurementProjector_mul_gaussianInput {n : ℕ} (k : Fin n) (b : Bool)
    (gl : MatchGateCircuit n) (x : Reg n)
    (h : ∀ g ∈ gl, matchGateWellFormed g ∧ avoidsMode k g) :
    measurementProjector k b * gaussianInput gl x
      = (if x k = b then (1 : ℂ) else 0) • gaussianInput gl x := by
  show measurementProjector k b * (matchGateCircuitOp gl * fockProjector x)
      = (if x k = b then (1 : ℂ) else 0) • (matchGateCircuitOp gl * fockProjector x)
  rw [← Matrix.mul_assoc,
    measurementProjector_mul_matchGateCircuitOp k b gl h,
    Matrix.mul_assoc, measurementProjector_mul_fockProjector k b x,
    Algebra.mul_smul_comm]

/-- For a well-formed preparation circuit avoiding `k`, the outcome weight of `gaussianInput gl
x` is 1 when `x k = b` and 0 otherwise. -/
theorem bornWeight_gaussianInput {n : ℕ} (k : Fin n) (b : Bool) (gl : MatchGateCircuit n)
    (x : Reg n) (hwf : ∀ g ∈ gl, matchGateWellFormed g) (hav : ∀ g ∈ gl, avoidsMode k g) :
    bornWeight (gaussianInput gl x) k b = if x k = b then (1 : ℝ) else 0 := by
  have hcomb := measurementProjector_mul_gaussianInput k b gl x
    (fun g hg => ⟨hwf g hg, hav g hg⟩)
  unfold bornWeight
  rw [hcomb]
  by_cases hxk : x k = b
  · rw [if_pos hxk, one_smul]
    have hU := matchGateCircuitOp_mem_unitaryGroup gl (fun g hg => (hwf g hg).2)
    have hU1 := Matrix.mem_unitaryGroup_iff'.mp hU
    rw [Matrix.star_eq_conjTranspose] at hU1
    have hM : (gaussianInput gl x)ᴴ * gaussianInput gl x = fockProjector x := by
      show (matchGateCircuitOp gl * fockProjector x)ᴴ
          * (matchGateCircuitOp gl * fockProjector x) = fockProjector x
      rw [Matrix.conjTranspose_mul, fockProjector_hermitian, Matrix.mul_assoc,
        ← Matrix.mul_assoc (matchGateCircuitOp gl)ᴴ (matchGateCircuitOp gl)
          (fockProjector x), hU1, one_mul, fockProjector_idem]
    rw [hM, fockProjector_trace, Complex.one_re, if_pos hxk]
  · simp [hxk]

/-- For a well-formed preparation circuit avoiding `k`, projection scales each external
covariance entry by its outcome weight. -/
theorem measurement_hAway_gaussianInput {n : ℕ} (k : Fin n) (b : Bool)
    (gl : MatchGateCircuit n) (x : Reg n)
    (hwf : ∀ g ∈ gl, matchGateWellFormed g) (hav : ∀ g ∈ gl, avoidsMode k g)
    (a c : Fin (2 * n)) (ha : ¬ isModeMajorana k a) (hc : ¬ isModeMajorana k c) :
    covarianceMatrix (measurementProjector k b * gaussianInput gl x) a c
      = bornWeight (gaussianInput gl x) k b * covarianceMatrix (gaussianInput gl x) a c := by
  have hcomb := measurementProjector_mul_gaussianInput k b gl x
    (fun g hg => ⟨hwf g hg, hav g hg⟩)
  have hPγa : measurementProjector k b * majorana a
      = majorana a * measurementProjector k b :=
    measurementProjector_mul_majorana_of_not_mode k b ha
  have hPγc : measurementProjector k b * majorana c
      = majorana c * measurementProjector k b :=
    measurementProjector_mul_majorana_of_not_mode k b hc
  have hcomm2 : ∀ X Y : Matrix (Reg n) (Reg n) ℂ,
      measurementProjector k b * X = X * measurementProjector k b →
      measurementProjector k b * Y = Y * measurementProjector k b →
      measurementProjector k b * (X * Y) = (X * Y) * measurementProjector k b := by
    intro X Y hX hY
    rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hY, Matrix.mul_assoc]
  have hPC : measurementProjector k b * (majorana a * majorana c
        - majorana c * majorana a)
      = (majorana a * majorana c - majorana c * majorana a) * measurementProjector k b := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hcomm2 _ _ hPγa hPγc, hcomm2 _ _ hPγc hPγa]
  have hPCP : measurementProjector k b * (majorana a * majorana c
        - majorana c * majorana a) * measurementProjector k b
      = (majorana a * majorana c - majorana c * majorana a) * measurementProjector k b := by
    rw [hPC, Matrix.mul_assoc, measurementProjector_idem k b]
  rw [covarianceMatrix_projector_apply _ _ (measurementProjector_hermitian k b) a c,
    hPCP, Matrix.mul_assoc, Matrix.mul_assoc, hcomb]
  by_cases hxk : x k = b
  · rw [if_pos hxk, one_smul, ← Matrix.mul_assoc,
      bornWeight_gaussianInput k b gl x hwf hav, if_pos hxk, one_mul]
    rfl
  · rw [if_neg hxk, zero_smul, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero,
      mul_zero, Complex.zero_re, bornWeight_gaussianInput k b gl x hwf hav, if_neg hxk,
      zero_mul]

/-- For a well-formed preparation circuit avoiding `k`, the covariance after projection at `k`
equals its outcome weight times `measurementUpdate`. -/
theorem covarianceMatrix_measurement_gaussianInput {n : ℕ} (k : Fin n) (b : Bool)
    (gl : MatchGateCircuit n) (x : Reg n)
    (hwf : ∀ g ∈ gl, matchGateWellFormed g) (hav : ∀ g ∈ gl, avoidsMode k g) :
    covarianceMatrix (measurementProjector k b * gaussianInput gl x)
      = bornWeight (gaussianInput gl x) k b
          • measurementUpdate (covarianceMatrix (gaussianInput gl x)) k b :=
  covarianceMatrix_measurement_eq_update _ k b
    (measurement_hAway_gaussianInput k b gl x hwf hav)

/-- Collects covariance propagation and Majorana conjugation for well-formed circuits, together
with the measurement update for prepared inputs at a mode avoided by every gate. -/
theorem frontier1 :
    (∀ (n : ℕ) (gl : MatchGateCircuit n) (_h : ∀ g ∈ gl, matchGateWellFormed g)
        (M : Matrix (Reg n) (Reg n) ℂ),
        covarianceMatrix (matchGateCircuitOp gl * M) = covarianceRun gl (covarianceMatrix M))
    ∧ (∀ (n : ℕ) (gl : MatchGateCircuit n) (_h : ∀ g ∈ gl, matchGateWellFormed g)
        (a : Fin (2 * n)),
        (matchGateCircuitOp gl)ᴴ * majorana a * matchGateCircuitOp gl
          = majoranaInBasis (frameRotationRun gl) a)
    ∧ (∀ (n : ℕ) (k : Fin n) (b : Bool) (gl : MatchGateCircuit n) (x : Reg n)
        (_hwf : ∀ g ∈ gl, matchGateWellFormed g) (_hav : ∀ g ∈ gl, avoidsMode k g),
        covarianceMatrix (measurementProjector k b * gaussianInput gl x)
          = bornWeight (gaussianInput gl x) k b
              • measurementUpdate (covarianceMatrix (gaussianInput gl x)) k b) :=
  ⟨fun _ gl h M => covarianceMatrix_matchGateCircuit gl h M,
    fun _ gl h a => matchGateCircuit_conj_majorana gl h a,
    fun _ k b gl x hwf hav => covarianceMatrix_measurement_gaussianInput k b gl x hwf hav⟩

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
