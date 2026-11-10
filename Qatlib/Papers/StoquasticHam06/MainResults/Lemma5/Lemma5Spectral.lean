/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Chebyshev
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma5

open Matrix

theorem sum_sq_le_sq_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hle : ∀ i ∈ s, f i ≤ ∑ j ∈ s, f j := fun i hi =>
    Finset.single_le_sum (fun j hj => hf j hj) hi
  calc ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, f i * f i := by simp [pow_two]
    _ ≤ ∑ i ∈ s, f i * (∑ j ∈ s, f j) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h1 := hle i hi
        have h2 := hf i hi
        nlinarith
    _ = (∑ i ∈ s, f i) * (∑ j ∈ s, f j) := by rw [Finset.sum_mul]
    _ = (∑ i ∈ s, f i) ^ 2 := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_repr_dot (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (w : ι → ℝ) :
    ∑ i, (dotProduct w (⇑(hG.eigenvectorBasis i) : ι → ℝ)) •
      (⇑(hG.eigenvectorBasis i) : ι → ℝ) = w := by
  have h := hG.eigenvectorBasis.sum_repr' (WithLp.toLp 2 w)
  have h2 := congrArg (WithLp.ofLp) h
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial] at h2
  exact h2

theorem sum_sq_sums (G : Matrix ι ι ℝ) (hG : G.IsHermitian) :
    ∑ i, (∑ x, (⇑(hG.eigenvectorBasis i) : ι → ℝ) x) ^ 2 = (Fintype.card ι : ℝ) := by
  have h := hG.eigenvectorBasis.sum_inner_mul_inner
    (WithLp.toLp 2 (fun _ : ι => (1:ℝ))) (WithLp.toLp 2 (fun _ : ι => (1:ℝ)))
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  simpa only [pow_two] using h

theorem mulVec_pow_of_eigen (G : Matrix ι ι ℝ) (v : ι → ℝ) (mu : ℝ)
    (hv : G.mulVec v = mu • v) (L : ℕ) : (G ^ L).mulVec v = (mu ^ L) • v := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ']

theorem mulVec_evec_pow (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (i : ι) (L : ℕ) :
    (G ^ L).mulVec (⇑(hG.eigenvectorBasis i) : ι → ℝ) =
      (hG.eigenvalues i ^ L) • (⇑(hG.eigenvectorBasis i) : ι → ℝ) :=
  mulVec_pow_of_eigen G _ _ (hG.mulVec_eigenvectorBasis i) L

theorem mulVec_pow_eq_sum (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (L : ℕ) (w : ι → ℝ) :
    (G ^ L).mulVec w =
      ∑ i, ((hG.eigenvalues i ^ L) * dotProduct w (⇑(hG.eigenvectorBasis i) : ι → ℝ)) •
        (⇑(hG.eigenvectorBasis i) : ι → ℝ) := by
  conv_lhs => rw [← sum_repr_dot G hG w]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mulVec_smul, mulVec_evec_pow, smul_smul]
  ring_nf

theorem sum_entries_pow_eq (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (L : ℕ) :
    ∑ x, ∑ y, (G ^ L) x y =
      ∑ i, (hG.eigenvalues i) ^ L * (∑ x, (⇑(hG.eigenvectorBasis i) : ι → ℝ) x) ^ 2 := by
  have h1 : (∑ x, ∑ y, (G ^ L) x y) =
      dotProduct (fun _ => (1:ℝ)) ((G ^ L).mulVec (fun _ => (1:ℝ))) := by
    simp [Matrix.mulVec, dotProduct]
  rw [h1, mulVec_pow_eq_sum G hG L (fun _ => (1:ℝ)), dotProduct_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dotProduct_smul, smul_eq_mul]
  have hdc : dotProduct (fun _ => (1:ℝ)) (⇑(hG.eigenvectorBasis i) : ι → ℝ) =
      ∑ x, (⇑(hG.eigenvectorBasis i) : ι → ℝ) x := by
    simp [dotProduct]
  rw [hdc]
  ring

theorem lemma5_power_method_error
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian)
    (hpsd : ∀ i, 0 ≤ hG.eigenvalues i)
    (i0 : ι) (hmax : ∀ i, hG.eigenvalues i ≤ hG.eigenvalues i0)
    (hv0 : ∀ x, 0 ≤ (⇑(hG.eigenvectorBasis i0) : ι → ℝ) x)
    (mu1 : ℝ) (hmu1pos : 0 < mu1) (hsecond : ∀ i, i ≠ i0 → hG.eigenvalues i ≤ mu1)
    (L r n : ℕ) (hr : 0 < r) (hL : 5 * n * r ≤ 2 * L)
    (hcard : Fintype.card ι = 2 ^ n)
    (hgap : Real.log (hG.eigenvalues i0) - Real.log mu1 ≥ 1 / (r : ℝ))
    (hmu0pos : 0 < hG.eigenvalues i0) (hmu0le : hG.eigenvalues i0 ≤ 1) :
    |hG.eigenvalues i0 - ExpectedMu G L| ≤ (1 / 2 : ℝ) ^ n := by
  set mu0 : ℝ := hG.eigenvalues i0 with hmu0
  set c : ι → ℝ := fun i => ∑ x, (⇑(hG.eigenvectorBasis i) : ι → ℝ) x with hc
  have hS : ∀ k : ℕ, (∑ x, ∑ y, (G ^ k) x y) = ∑ i, hG.eigenvalues i ^ k * (c i) ^ 2 := by
    intro k
    rw [sum_entries_pow_eq G hG k]

  have hunit : ∑ x, (⇑(hG.eigenvectorBasis i0) : ι → ℝ) x ^ 2 = 1 := by
    have hinner := hG.eigenvectorBasis.orthonormal.1 i0
    have hsq : ‖(hG.eigenvectorBasis i0 : EuclideanSpace ℝ ι)‖ ^ 2 = 1 := by
      rw [hinner]; norm_num
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact hsq
  have hc0_sq : 1 ≤ (c i0) ^ 2 := by
    have hcs := sum_sq_le_sq_sum (s := (Finset.univ : Finset ι))
      (f := fun x => (⇑(hG.eigenvectorBasis i0) : ι → ℝ) x) (fun x _ => hv0 x)
    simpa [hc, hunit] using hcs
  have hc0_nonneg : 0 ≤ c i0 := Finset.sum_nonneg (fun x _ => hv0 x)
  have hc0_ge : 1 ≤ c i0 := by nlinarith [hc0_sq, hc0_nonneg]
  have hm0 : 0 ≤ mu0 := hmu0pos.le
  have h5 : 0 ≤ mu1 ^ L := pow_nonneg hmu1pos.le L

  have hS_ge : ∀ k : ℕ, mu0 ^ k ≤ ∑ x, ∑ y, (G ^ k) x y := by
    intro k
    rw [hS k]
    have hterm : mu0 ^ k * (c i0) ^ 2 ≤
        ∑ i, hG.eigenvalues i ^ k * (c i) ^ 2 :=
      Finset.single_le_sum
        (f := fun i => hG.eigenvalues i ^ k * (c i) ^ 2)
        (fun i _ => mul_nonneg (pow_nonneg (hpsd i) k) (sq_nonneg (c i)))
        (Finset.mem_univ i0)
    have hmul : mu0 ^ k ≤ mu0 ^ k * (c i0) ^ 2 := by
      have h0 : (0:ℝ) ≤ mu0 ^ k := pow_nonneg hmu0pos.le k
      nlinarith [hc0_sq, h0]
    exact le_trans hmul hterm

  have hS_le : (∑ x, ∑ y, (G ^ (L + 1)) x y) ≤ mu0 * (∑ x, ∑ y, (G ^ L) x y) := by
    rw [hS (L + 1), hS L, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [show hG.eigenvalues i ^ (L + 1) * (c i) ^ 2
        = hG.eigenvalues i * (hG.eigenvalues i ^ L * (c i) ^ 2) by ring]
    exact mul_le_mul_of_nonneg_right (hmax i)
      (mul_nonneg (pow_nonneg (hpsd i) L) (sq_nonneg (c i)))

  have hdiff : mu0 * (∑ x, ∑ y, (G ^ L) x y) - (∑ x, ∑ y, (G ^ (L + 1)) x y) ≤
      mu0 * mu1 ^ L * (Fintype.card ι : ℝ) := by
    have hsplit : mu0 * (∑ x, ∑ y, (G ^ L) x y) - (∑ x, ∑ y, (G ^ (L + 1)) x y) =
        ∑ i, (mu0 - hG.eigenvalues i) * (hG.eigenvalues i ^ L * (c i) ^ 2) := by
      rw [hS (L + 1), hS L, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsplit]
    have hterm : ∀ i, i ≠ i0 → (mu0 - hG.eigenvalues i) * (hG.eigenvalues i ^ L * (c i) ^ 2)
        ≤ mu0 * mu1 ^ L * (c i) ^ 2 := by
      intro i hi
      have h1 : 0 ≤ mu0 - hG.eigenvalues i := by linarith [hmax i]
      have h2 : hG.eigenvalues i ^ L ≤ mu1 ^ L :=
        pow_le_pow_left₀ (hpsd i) (hsecond i hi) L
      have h3 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ hG.eigenvalues i ^ L := pow_nonneg (hpsd i) L
      have hstep1 : (mu0 - hG.eigenvalues i) * (hG.eigenvalues i ^ L * (c i) ^ 2)
          ≤ (mu0 - hG.eigenvalues i) * (mu1 ^ L * (c i) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 h3) h1
      have hstep2 : (mu0 - hG.eigenvalues i) * (mu1 ^ L * (c i) ^ 2)
          ≤ mu0 * (mu1 ^ L * (c i) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hpsd i]) (mul_nonneg h5 h3)
      calc (mu0 - hG.eigenvalues i) * (hG.eigenvalues i ^ L * (c i) ^ 2)
          ≤ (mu0 - hG.eigenvalues i) * (mu1 ^ L * (c i) ^ 2) := hstep1
        _ ≤ mu0 * (mu1 ^ L * (c i) ^ 2) := hstep2
        _ = mu0 * mu1 ^ L * (c i) ^ 2 := by ring
    have hterm0 : (mu0 - hG.eigenvalues i0) * (hG.eigenvalues i0 ^ L * (c i0) ^ 2) = 0 := by
      simp [mu0]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0), hterm0, add_zero]
    calc ∑ i ∈ Finset.univ.erase i0, (mu0 - hG.eigenvalues i) *
          (hG.eigenvalues i ^ L * (c i) ^ 2)
        ≤ ∑ i ∈ Finset.univ.erase i0, mu0 * mu1 ^ L * (c i) ^ 2 :=
          Finset.sum_le_sum (fun i hi => hterm i (Finset.ne_of_mem_erase hi))
      _ = mu0 * mu1 ^ L * ∑ i ∈ Finset.univ.erase i0, (c i) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ mu0 * mu1 ^ L * (Fintype.card ι : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hm0 h5)
          calc ∑ i ∈ Finset.univ.erase i0, (c i) ^ 2 ≤ ∑ i, (c i) ^ 2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                    (fun i _ _ => sq_nonneg _)
              _ = (Fintype.card ι : ℝ) := sum_sq_sums G hG

  have hSL_pos : 0 < ∑ x, ∑ y, (G ^ L) x y :=
    lt_of_lt_of_le (pow_pos hmu0pos L) (hS_ge L)

  have hE_le : ExpectedMu G L ≤ mu0 := by
    rw [ExpectedMu]
    rw [div_le_iff₀ hSL_pos]
    linarith [hS_le]
  have habs : |mu0 - ExpectedMu G L| = mu0 - ExpectedMu G L :=
    abs_of_nonneg (by linarith [hE_le])
  rw [habs]

  have hbound1 : mu0 - ExpectedMu G L ≤
      (Fintype.card ι : ℝ) * mu0 * (mu1 / mu0) ^ L := by
    rw [ExpectedMu]
    have hden : (∑ x, ∑ y, (G ^ L) x y) ≠ 0 := ne_of_gt hSL_pos
    have hcalc : mu0 - (∑ x, ∑ y, (G ^ (L + 1)) x y) / (∑ x, ∑ y, (G ^ L) x y)
        = (mu0 * (∑ x, ∑ y, (G ^ L) x y) - (∑ x, ∑ y, (G ^ (L + 1)) x y))
          / (∑ x, ∑ y, (G ^ L) x y) := by
      field_simp
    rw [hcalc]
    have hdiv : (mu0 * (∑ x, ∑ y, (G ^ L) x y) - (∑ x, ∑ y, (G ^ (L + 1)) x y))
          / (∑ x, ∑ y, (G ^ L) x y)
        ≤ (mu0 * mu1 ^ L * (Fintype.card ι : ℝ)) / (∑ x, ∑ y, (G ^ L) x y) :=
      div_le_div_of_nonneg_right hdiff hSL_pos.le
    have hden2 : mu0 ^ L ≤ (∑ x, ∑ y, (G ^ L) x y) := hS_ge L
    have hdenpos : (0:ℝ) < mu0 ^ L := pow_pos hmu0pos L
    have hkey : (mu0 * mu1 ^ L * (Fintype.card ι : ℝ)) / (∑ x, ∑ y, (G ^ L) x y)
        ≤ (mu0 * mu1 ^ L * (Fintype.card ι : ℝ)) / mu0 ^ L :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hmu0pos.le (pow_nonneg hmu1pos.le L)) (Nat.cast_nonneg _))
        hdenpos hden2
    have hsimp : (mu0 * mu1 ^ L * (Fintype.card ι : ℝ)) / mu0 ^ L
        = (Fintype.card ι : ℝ) * mu0 * (mu1 / mu0) ^ L := by
      rw [div_pow]
      field_simp
    linarith [hdiv, hkey, hsimp.le, hsimp.ge]

  have hmu0ne : mu0 ≠ 0 := ne_of_gt hmu0pos
  have hlog : Real.log (mu1 / mu0) ≤ -(1 / (r : ℝ)) := by
    rw [Real.log_div hmu1pos.ne' hmu0ne]
    linarith [hgap]
  have hratio_le : mu1 / mu0 ≤ Real.exp (-(1 / (r : ℝ))) := by
    calc mu1 / mu0 = Real.exp (Real.log (mu1 / mu0)) :=
          (Real.exp_log (div_pos hmu1pos hmu0pos)).symm
      _ ≤ Real.exp (-(1 / (r : ℝ))) := Real.exp_le_exp.mpr hlog
  have hpow_le : (mu1 / mu0) ^ L ≤ Real.exp (-(1 / (r : ℝ))) ^ L :=
    pow_le_pow_left₀ (div_nonneg hmu1pos.le hmu0pos.le) hratio_le L
  have hexp_eq : Real.exp (-(1 / (r : ℝ))) ^ L = Real.exp (-(L : ℝ) / (r : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hrR : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hLr : (5:ℝ) * (n:ℝ) / 2 ≤ (L:ℝ) / (r:ℝ) := by
    rw [le_div_iff₀ hrR]
    have hL' : (5:ℝ) * (n:ℝ) * (r:ℝ) ≤ 2 * (L:ℝ) := by exact_mod_cast hL
    nlinarith
  have hexp_le1 : Real.exp (-(L : ℝ) / (r : ℝ)) ≤ Real.exp (-((5:ℝ) * (n:ℝ) / 2)) :=
    Real.exp_le_exp.mpr (by rw [neg_div]; exact neg_le_neg hLr)
  have hexp2 : Real.exp (-((5:ℝ) * (n:ℝ) / 2)) = Real.exp (-(5:ℝ)/2) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexp_quarter : Real.exp (-(5:ℝ)/2) ≤ (1/4 : ℝ) := by
    have h4 : (4:ℝ) ≤ Real.exp ((5:ℝ)/2) := by
      have hmono : Real.exp 2 ≤ Real.exp ((5:ℝ)/2) := Real.exp_le_exp.mpr (by norm_num)
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have he1 := Real.exp_one_gt_two
      have he1pos : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith [hmono, he2, he1, he1pos]
    have hinv : (Real.exp ((5:ℝ)/2))⁻¹ ≤ (4:ℝ)⁻¹ :=
      inv_anti₀ (by norm_num : (0:ℝ) < 4) h4
    calc Real.exp (-(5:ℝ)/2) = Real.exp (-((5:ℝ)/2)) := by ring_nf
      _ = (Real.exp ((5:ℝ)/2))⁻¹ := Real.exp_neg _
      _ ≤ (4:ℝ)⁻¹ := hinv
      _ = (1/4 : ℝ) := by norm_num
  have hfinal : (Fintype.card ι : ℝ) * mu0 * (mu1 / mu0) ^ L ≤ (1/2 : ℝ) ^ n := by
    have hcardR : (Fintype.card ι : ℝ) = (2:ℝ) ^ n := by
      rw [hcard]; push_cast; ring
    have hr1 : (mu1 / mu0) ^ L ≤ (1/4 : ℝ) ^ n := by
      calc (mu1 / mu0) ^ L ≤ Real.exp (-(1 / (r : ℝ))) ^ L := hpow_le
        _ = Real.exp (-(L : ℝ) / (r : ℝ)) := hexp_eq
        _ ≤ Real.exp (-((5:ℝ) * (n:ℝ) / 2)) := hexp_le1
        _ = Real.exp (-(5:ℝ)/2) ^ n := hexp2
        _ ≤ (1/4 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hexp_quarter n
    have hk : (0:ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    have hrp : (0:ℝ) ≤ (mu1 / mu0) ^ L :=
      pow_nonneg (div_nonneg hmu1pos.le hmu0pos.le) L
    have hq : (0:ℝ) ≤ (1/4 : ℝ) ^ n := pow_nonneg (by norm_num) n
    calc (Fintype.card ι : ℝ) * mu0 * (mu1 / mu0) ^ L
        ≤ (Fintype.card ι : ℝ) * 1 * (1/4 : ℝ) ^ n := by
          have hstep : mu0 * (mu1 / mu0) ^ L ≤ 1 * (1/4 : ℝ) ^ n := by
            nlinarith [hmu0le, hmu0pos.le, hr1, hrp, hq]
          calc (Fintype.card ι : ℝ) * mu0 * (mu1 / mu0) ^ L
              = (Fintype.card ι : ℝ) * (mu0 * (mu1 / mu0) ^ L) := by ring
            _ ≤ (Fintype.card ι : ℝ) * (1 * (1/4 : ℝ) ^ n) :=
                mul_le_mul_of_nonneg_left hstep hk
            _ = (Fintype.card ι : ℝ) * 1 * (1/4 : ℝ) ^ n := by ring
      _ = (1/2 : ℝ) ^ n := by
          rw [hcardR, mul_one, ← mul_pow]
          norm_num
  exact le_trans hbound1 hfinal

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma5
