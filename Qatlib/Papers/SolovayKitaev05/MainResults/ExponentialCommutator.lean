/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecificLimits.Basic

namespace Qatlib.Papers.SolovayKitaev05.MainResults.ExponentialCommutator

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxRecDepth 10000

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def q4 (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ := 4 + 4 * Z + 2 * (Z * Z)

noncomputable def Bq (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ := 4 * Z + 2 * (Z * Z)

noncomputable def Err4 (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  -(128 * (X * X * Y)) + 128 * (X * Y * Y) + 128 * (Y * X * X)
    + -(128 * (Y * Y * X)) + 64 * (X * X * X * X) + 192 * (X * X * Y * Y)
    + 64 * (Y * Y * X * X) + 64 * (Y * Y * Y * Y)

noncomputable def Trip4 (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Bq X * Bq Y * Bq (-X) + Bq X * Bq Y * Bq (-Y) + Bq X * Bq (-X) * Bq (-Y)
    + Bq Y * Bq (-X) * Bq (-Y)

noncomputable def Quad4 (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := Bq X * Bq Y * Bq (-X) * Bq (-Y)

noncomputable def Aexp (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ := (4:ℂ) • NormedSpace.exp Z

noncomputable def QuadProd (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Aexp X * Aexp Y * Aexp (-X) * Aexp (-Y)

noncomputable def q4Prod (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := q4 X * q4 Y * q4 (-X) * q4 (-Y)

noncomputable def Rem (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Err4 X Y + 4 * Trip4 X Y + Quad4 X Y

noncomputable def Lin (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (256:ℂ) • (1 + (X * Y - Y * X))

noncomputable def ExpC (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp (X * Y - Y * X)

lemma six_mul_pow_two_le_factorial (k : ℕ) : 6 * 2 ^ k ≤ (k + 3).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : (k + 4).factorial = (k + 4) * (k + 3).factorial := by
        rw [show k + 4 = (k + 3) + 1 by ring, Nat.factorial_succ]
      rw [h1, pow_succ]
      nlinarith [ih, Nat.zero_le k]

lemma two_pow_succ_le_factorial (k : ℕ) : 2 ^ (k+1) ≤ (k+2).factorial := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : (k+3).factorial = (k+3) * (k+2).factorial := by
        rw [show k+3 = (k+2)+1 by ring, Nat.factorial_succ]
      rw [h1, pow_succ]
      nlinarith [ih, Nat.zero_le k]

lemma exp_sub_quad_le (X : Matrix ι ι ℂ) (hX : ‖X‖ ≤ 1) :
    ‖NormedSpace.exp X - (1 + X + (2:ℂ)⁻¹ • X ^ 2)‖ ≤ ‖X‖ ^ 3 := by
  have hsum : HasSum (fun n : ℕ => (↑(n.factorial) : ℂ)⁻¹ • X ^ n) (NormedSpace.exp X) :=
    NormedSpace.exp_series_hasSum_exp' X
  have h3 : (∑ i ∈ Finset.range 3, (↑(i.factorial) : ℂ)⁻¹ • X ^ i)
      = 1 + X + (2:ℂ)⁻¹ • X ^ 2 := by
    simp [Finset.sum_range_succ]
  have htail : (∑' k : ℕ, (↑((k+3).factorial) : ℂ)⁻¹ • X ^ (k+3))
      = NormedSpace.exp X - (1 + X + (2:ℂ)⁻¹ • X ^ 2) := by
    have h := hsum.summable.sum_add_tsum_nat_add 3
    rw [hsum.tsum_eq] at h
    rw [← h3, ← h]
    abel
  rw [← htail]
  have hS : Summable (fun k : ℕ => ‖(↑((k+3).factorial) : ℂ)⁻¹ • X ^ (k+3)‖) :=
    ((summable_nat_add_iff 3).2 hsum.summable).norm
  have hg : Summable (fun k : ℕ => (6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k) :=
    Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hterm : ∀ k : ℕ,
      ‖(↑((k+3).factorial) : ℂ)⁻¹ • X ^ (k+3)‖ ≤ ‖X‖ ^ 3 * ((6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k) := by
    intro k
    have hnorm : ‖(↑((k+3).factorial) : ℂ)⁻¹ • X ^ (k+3)‖
        = ((k+3).factorial : ℝ)⁻¹ * ‖X ^ (k+3)‖ := by
      rw [norm_smul, norm_inv, Complex.norm_natCast]
    rw [hnorm]
    have hfac : (0:ℝ) < ((k+3).factorial : ℝ) := by positivity
    have h6 : (6:ℝ) * 2 ^ k ≤ ((k+3).factorial : ℝ) := by
      exact_mod_cast six_mul_pow_two_le_factorial k
    have hinv : ((k+3).factorial : ℝ)⁻¹ ≤ (6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k := by
      have h := (inv_le_inv₀ hfac (by positivity : (0:ℝ) < 6 * 2 ^ k)).mpr h6
      rwa [_root_.mul_inv_rev, mul_comm, ← inv_pow] at h
    have h2 : ‖X ^ (k+3)‖ ≤ ‖X‖ ^ (k+3) := norm_pow_le X (k+3)
    have hfacinv : (0:ℝ) ≤ ((k+3).factorial : ℝ)⁻¹ := by positivity
    have h6inv : (0:ℝ) ≤ (6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k := by positivity
    have hXk : ‖X‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hX
    have hX3 : (0:ℝ) ≤ ‖X‖ ^ 3 := by positivity
    calc ((k+3).factorial : ℝ)⁻¹ * ‖X ^ (k+3)‖
        ≤ ((k+3).factorial : ℝ)⁻¹ * ‖X‖ ^ (k+3) :=
          mul_le_mul_of_nonneg_left h2 hfacinv
      _ = ‖X‖ ^ 3 * (((k+3).factorial : ℝ)⁻¹ * ‖X‖ ^ k) := by rw [pow_add]; ring
      _ ≤ ‖X‖ ^ 3 * (((6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hX3
          exact mul_le_mul hinv hXk (by positivity : (0:ℝ) ≤ ‖X‖ ^ k) h6inv
      _ = ‖X‖ ^ 3 * ((6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k) := by ring
  calc ‖∑' k : ℕ, (↑((k+3).factorial) : ℂ)⁻¹ • X ^ (k+3)‖
      ≤ ∑' k : ℕ, ‖(↑((k+3).factorial) : ℂ)⁻¹ • X ^ (k+3)‖ := norm_tsum_le_tsum_norm hS
    _ ≤ ∑' k : ℕ, ‖X‖ ^ 3 * ((6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k) :=
        Summable.tsum_le_tsum hterm hS (hg.mul_left _)
    _ = ‖X‖ ^ 3 * ∑' k : ℕ, ((6:ℝ)⁻¹ * (2:ℝ)⁻¹ ^ k) := tsum_mul_left
    _ = ‖X‖ ^ 3 * ((6:ℝ)⁻¹ * ∑' k : ℕ, ((2:ℝ)⁻¹ ^ k)) := by
        rw [tsum_mul_left]
    _ = ‖X‖ ^ 3 * ((6:ℝ)⁻¹ * 2) := by
        rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)]
        norm_num
    _ ≤ ‖X‖ ^ 3 := by
        have h0 : (0:ℝ) ≤ ‖X‖ ^ 3 := by positivity
        nlinarith

lemma exp_sub_lin_le (X : Matrix ι ι ℂ) (hX : ‖X‖ ≤ 1/2) :
    ‖NormedSpace.exp X - (1 + X)‖ ≤ ‖X‖ ^ 2 := by
  have hsum : HasSum (fun n : ℕ => (↑(n.factorial) : ℂ)⁻¹ • X ^ n) (NormedSpace.exp X) :=
    NormedSpace.exp_series_hasSum_exp' X
  have h2 : (∑ i ∈ Finset.range 2, (↑(i.factorial) : ℂ)⁻¹ • X ^ i) = 1 + X := by
    simp [Finset.sum_range_succ]
  have htail : (∑' k : ℕ, (↑((k+2).factorial) : ℂ)⁻¹ • X ^ (k+2))
      = NormedSpace.exp X - (1 + X) := by
    have h := hsum.summable.sum_add_tsum_nat_add 2
    rw [hsum.tsum_eq] at h
    rw [← h2, ← h]
    abel
  rw [← htail]
  have hS : Summable (fun k : ℕ => ‖(↑((k+2).factorial) : ℂ)⁻¹ • X ^ (k+2)‖) :=
    ((summable_nat_add_iff 2).2 hsum.summable).norm
  have hg : Summable (fun k : ℕ => ((2:ℝ)⁻¹)^(k+1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hterm : ∀ k : ℕ,
      ‖(↑((k+2).factorial) : ℂ)⁻¹ • X ^ (k+2)‖ ≤ ‖X‖ ^ 2 * ((2:ℝ)⁻¹)^(k+1) := by
    intro k
    have hnorm : ‖(↑((k+2).factorial) : ℂ)⁻¹ • X ^ (k+2)‖
        = ((k+2).factorial : ℝ)⁻¹ * ‖X ^ (k+2)‖ := by
      rw [norm_smul, norm_inv, Complex.norm_natCast]
    rw [hnorm]
    have hfac : (0:ℝ) < ((k+2).factorial : ℝ) := by positivity
    have h2k : (2:ℝ) ^ (k+1) ≤ ((k+2).factorial : ℝ) := by
      exact_mod_cast two_pow_succ_le_factorial k
    have hinv : ((k+2).factorial : ℝ)⁻¹ ≤ ((2:ℝ)⁻¹)^(k+1) := by
      have h := (inv_le_inv₀ hfac (by positivity : (0:ℝ) < 2^(k+1))).mpr h2k
      calc ((k+2).factorial : ℝ)⁻¹ ≤ ((2:ℝ)^(k+1))⁻¹ := h
        _ = ((2:ℝ)⁻¹)^(k+1) := by rw [inv_pow]
    have hpow : ‖X ^ (k+2)‖ ≤ ‖X‖ ^ 2 := by
      calc ‖X ^ (k+2)‖ ≤ ‖X‖ ^ (k+2) := norm_pow_le X (k+2)
        _ = ‖X‖ ^ 2 * ‖X‖ ^ k := by rw [pow_add]; ring
        _ ≤ ‖X‖ ^ 2 * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_one₀ (norm_nonneg X) (le_trans hX (by norm_num))
        _ = ‖X‖ ^ 2 := by ring
    calc ((k+2).factorial : ℝ)⁻¹ * ‖X ^ (k+2)‖
        ≤ ((2:ℝ)⁻¹)^(k+1) * ‖X‖^2 := mul_le_mul hinv hpow (by positivity) (by positivity)
      _ = ‖X‖^2 * ((2:ℝ)⁻¹)^(k+1) := by ring
  have hsum1 : (∑' k : ℕ, ((2:ℝ)⁻¹)^(k+1)) = 1 := by
    rw [show (fun k : ℕ => ((2:ℝ)⁻¹)^(k+1)) = (fun k : ℕ => ((2:ℝ)⁻¹)^k * (2:ℝ)⁻¹) by
          ext k; rw [pow_succ]]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)]
    norm_num
  calc ‖∑' k : ℕ, (↑((k+2).factorial) : ℂ)⁻¹ • X ^ (k+2)‖
      ≤ ∑' k : ℕ, ‖(↑((k+2).factorial) : ℂ)⁻¹ • X ^ (k+2)‖ := norm_tsum_le_tsum_norm hS
    _ ≤ ∑' k : ℕ, ‖X‖ ^ 2 * ((2:ℝ)⁻¹)^(k+1) := Summable.tsum_le_tsum hterm hS (hg.mul_left _)
    _ = ‖X‖ ^ 2 * ∑' k : ℕ, ((2:ℝ)⁻¹)^(k+1) := tsum_mul_left
    _ = ‖X‖ ^ 2 := by rw [hsum1, mul_one]

lemma norm_natCast_matrix (n : ℕ) : ‖(n : Matrix ι ι ℂ)‖ = (n:ℝ) := by
  have h : (n : Matrix ι ι ℂ) = (n:ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [Algebra.smul_def, map_natCast, mul_one]
  rw [h, norm_smul, norm_one, mul_one, Complex.norm_natCast]

lemma norm_four : ‖(4 : Matrix ι ι ℂ)‖ = (4:ℝ) := norm_natCast_matrix 4

lemma norm_two : ‖(2 : Matrix ι ι ℂ)‖ = (2:ℝ) := norm_natCast_matrix 2

lemma norm_nat_mul_le (n : ℕ) (Z : Matrix ι ι ℂ) :
    ‖(n : Matrix ι ι ℂ) * Z‖ ≤ n * ‖Z‖ := by
  calc ‖(n : Matrix ι ι ℂ) * Z‖ ≤ ‖(n : Matrix ι ι ℂ)‖ * ‖Z‖ := norm_mul_le _ _
    _ = n * ‖Z‖ := by rw [norm_natCast_matrix]

lemma norm_four_mul_le (Z : Matrix ι ι ℂ) : ‖(4 : Matrix ι ι ℂ) * Z‖ ≤ 4 * ‖Z‖ := by
  calc ‖(4 : Matrix ι ι ℂ) * Z‖ ≤ ‖(4 : Matrix ι ι ℂ)‖ * ‖Z‖ := norm_mul_le _ _
    _ = 4 * ‖Z‖ := by rw [norm_four]

lemma norm_two_mul_le (Z : Matrix ι ι ℂ) : ‖(2 : Matrix ι ι ℂ) * Z‖ ≤ 2 * ‖Z‖ := by
  calc ‖(2 : Matrix ι ι ℂ) * Z‖ ≤ ‖(2 : Matrix ι ι ℂ)‖ * ‖Z‖ := norm_mul_le _ _
    _ = 2 * ‖Z‖ := by rw [norm_two]

lemma q4_eq_smul (Z : Matrix ι ι ℂ) :
    q4 Z = (4:ℂ) • (1 + Z + (2:ℂ)⁻¹ • Z ^ 2) := by
  rw [smul_add, smul_add, smul_smul, pow_two]
  simp only [q4]
  have h1 : (4:ℂ) • (1 : Matrix ι ι ℂ) = 4 := by rw [Algebra.smul_def, map_ofNat, mul_one]
  have h2 : (4:ℂ) • Z = 4 * Z := by rw [Algebra.smul_def, map_ofNat]
  have h3 : (4:ℂ) * (2:ℂ)⁻¹ = 2 := by norm_num
  rw [h3]
  have h4 : (2:ℂ) • (Z * Z) = 2 * (Z * Z) := by rw [Algebra.smul_def, map_ofNat]
  rw [h1, h2, h4]

lemma norm_four_smul_exp_sub_q4_le (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) :
    ‖(4:ℂ) • NormedSpace.exp Z - q4 Z‖ ≤ 4 * ‖Z‖ ^ 3 := by
  rw [q4_eq_smul]
  have h : (4:ℂ) • NormedSpace.exp Z - (4:ℂ) • (1 + Z + (2:ℂ)⁻¹ • Z ^ 2)
      = (4:ℂ) • (NormedSpace.exp Z - (1 + Z + (2:ℂ)⁻¹ • Z ^ 2)) := by rw [smul_sub]
  rw [h]
  calc ‖(4:ℂ) • (NormedSpace.exp Z - (1 + Z + (2:ℂ)⁻¹ • Z ^ 2))‖
      = ‖(4:ℂ)‖ * ‖NormedSpace.exp Z - (1 + Z + (2:ℂ)⁻¹ • Z ^ 2)‖ := norm_smul _ _
    _ ≤ 4 * ‖Z‖ ^ 3 := by
        rw [show ‖(4:ℂ)‖ = (4:ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left (exp_sub_quad_le Z hZ) (by norm_num)

lemma norm_exp_le_two (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1/2) : ‖NormedSpace.exp Z‖ ≤ 2 := by
  have hsum : HasSum (fun n : ℕ => (↑(n.factorial) : ℂ)⁻¹ • Z ^ n) (NormedSpace.exp Z) :=
    NormedSpace.exp_series_hasSum_exp' Z
  have hS : Summable (fun n : ℕ => ‖(↑(n.factorial) : ℂ)⁻¹ • Z ^ n‖) := hsum.summable.norm
  have hg : Summable (fun n : ℕ => ((2:ℝ)⁻¹)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hterm : ∀ n : ℕ, ‖(↑(n.factorial) : ℂ)⁻¹ • Z ^ n‖ ≤ ((2:ℝ)⁻¹)^n := by
    intro n
    have hnorm : ‖(↑(n.factorial) : ℂ)⁻¹ • Z ^ n‖ = ((n.factorial : ℝ))⁻¹ * ‖Z ^ n‖ := by
      rw [norm_smul, norm_inv, Complex.norm_natCast]
    rw [hnorm]
    have hfac1 : (0:ℝ) < (n.factorial : ℝ) := by positivity
    have hinv : ((n.factorial : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hfac1]; exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have hpow : ‖Z ^ n‖ ≤ ((2:ℝ)⁻¹)^n := by
      calc ‖Z ^ n‖ ≤ ‖Z‖ ^ n := norm_pow_le Z n
        _ ≤ ((2:ℝ)⁻¹)^n := by simpa [one_div] using pow_le_pow_left₀ (norm_nonneg Z) hZ n
    calc ((n.factorial : ℝ))⁻¹ * ‖Z ^ n‖ ≤ 1 * ((2:ℝ)⁻¹)^n :=
          mul_le_mul hinv hpow (by positivity) (by norm_num)
      _ = ((2:ℝ)⁻¹)^n := one_mul _
  calc ‖NormedSpace.exp Z‖ = ‖∑' n : ℕ, (↑(n.factorial) : ℂ)⁻¹ • Z ^ n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(↑(n.factorial) : ℂ)⁻¹ • Z ^ n‖ := norm_tsum_le_tsum_norm hS
    _ ≤ ∑' n : ℕ, ((2:ℝ)⁻¹)^n := Summable.tsum_le_tsum hterm hS hg
    _ = 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)]
        norm_num

lemma norm_Bq_le (Z : Matrix ι ι ℂ) (δ : ℝ) (hZ : ‖Z‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖Bq Z‖ ≤ 6 * δ := by
  have hB : Bq Z = (4 : Matrix ι ι ℂ) * Z + (2 : Matrix ι ι ℂ) * (Z * Z) := rfl
  rw [hB]
  calc ‖(4:Matrix ι ι ℂ) * Z + (2:Matrix ι ι ℂ) * (Z*Z)‖
      ≤ ‖(4:Matrix ι ι ℂ) * Z‖ + ‖(2:Matrix ι ι ℂ) * (Z*Z)‖ := norm_add_le _ _
    _ ≤ 4 * ‖Z‖ + 2 * ‖Z * Z‖ := add_le_add (norm_four_mul_le Z) (norm_two_mul_le (Z*Z))
    _ ≤ 4 * δ + 2 * (δ * δ) := by
        have h2 : ‖Z * Z‖ ≤ ‖Z‖ * ‖Z‖ := norm_mul_le _ _
        have h3 : ‖Z‖ * ‖Z‖ ≤ δ * δ := by nlinarith [hZ, norm_nonneg Z, hδ0]
        nlinarith [hZ, h2, h3, norm_nonneg Z]
    _ ≤ 6 * δ := by nlinarith [hδ0, hδ1]

lemma norm_q4_le (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1/2) : ‖q4 Z‖ ≤ 8 := by
  have hq : q4 Z = ((4 : Matrix ι ι ℂ) + (4 : Matrix ι ι ℂ) * Z) + (2 : Matrix ι ι ℂ) * (Z * Z) :=
      rfl
  rw [hq]
  have h1 : ‖(4:Matrix ι ι ℂ) + (4:Matrix ι ι ℂ) * Z‖ ≤ 4 + 4 * ‖Z‖ := by
    calc ‖(4:Matrix ι ι ℂ) + (4:Matrix ι ι ℂ) * Z‖
        ≤ ‖(4:Matrix ι ι ℂ)‖ + ‖(4:Matrix ι ι ℂ) * Z‖ := norm_add_le _ _
      _ ≤ 4 + 4 * ‖Z‖ := add_le_add (le_of_eq norm_four) (norm_four_mul_le Z)
  calc ‖((4:Matrix ι ι ℂ) + (4:Matrix ι ι ℂ) * Z) + (2:Matrix ι ι ℂ) * (Z*Z)‖
      ≤ ‖(4:Matrix ι ι ℂ) + (4:Matrix ι ι ℂ) * Z‖ + ‖(2:Matrix ι ι ℂ) * (Z*Z)‖ := norm_add_le _ _
    _ ≤ (4 + 4 * ‖Z‖) + 2 * ‖Z * Z‖ := add_le_add h1 (norm_two_mul_le (Z*Z))
    _ ≤ 8 := by
        have h2 : ‖Z * Z‖ ≤ ‖Z‖ * ‖Z‖ := norm_mul_le _ _
        have h3 : ‖Z‖ * ‖Z‖ ≤ (1/2:ℝ) * (1/2) := by nlinarith [hZ, norm_nonneg Z]
        have h4 : (0:ℝ) ≤ ‖Z‖ := norm_nonneg Z
        nlinarith [h2, h3, h4, hZ]

lemma norm_exp_four_smul_le (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1/2) :
    ‖(4:ℂ) • NormedSpace.exp Z‖ ≤ 8 := by
  rw [norm_smul, show ‖(4:ℂ)‖ = (4:ℝ) by norm_num]
  nlinarith [norm_exp_le_two Z hZ]

lemma q4_eq (Z : Matrix ι ι ℂ) : q4 Z = 4 + Bq Z := by
  simp only [q4, Bq]; abel

lemma expand_four (a b c d : Matrix ι ι ℂ) :
    (4 + a) * (4 + b) * (4 + c) * (4 + d)
      = 4 * 4 * 4 * 4 + 4 * 4 * 4 * (a + b + c + d)
        + 4 * 4 * (a * b + a * c + a * d + b * c + b * d + c * d)
        + 4 * (a * b * c + a * b * d + a * c * d + b * c * d) + a * b * c * d := by
  noncomm_ring

lemma S1 (X Y : Matrix ι ι ℂ) : Bq X + Bq Y + Bq (-X) + Bq (-Y) = 4 * (X * X) + 4 * (Y * Y) := by
  simp only [Bq]; noncomm_ring

set_option maxHeartbeats 2000000 in

lemma S2 (X Y : Matrix ι ι ℂ) :
    4 * 4 * (Bq X * Bq Y + Bq X * Bq (-X) + Bq X * Bq (-Y) + Bq Y * Bq (-X)
          + Bq Y * Bq (-Y) + Bq (-X) * Bq (-Y))
      + 4 * 4 * 4 * (4 * (X * X) + 4 * (Y * Y))
        = 4 * 4 * 4 * 4 * (X * Y - Y * X) + Err4 X Y := by
  simp only [Bq, Err4]; noncomm_ring

set_option maxHeartbeats 2000000 in

lemma master_identity (X Y : Matrix ι ι ℂ) :
    q4 X * q4 Y * q4 (-X) * q4 (-Y)
      = 256 + 256 * (X * Y - Y * X) + Err4 X Y + 4 * Trip4 X Y + Quad4 X Y := by
  rw [q4_eq, q4_eq, q4_eq, q4_eq]
  rw [expand_four (Bq X) (Bq Y) (Bq (-X)) (Bq (-Y))]
  rw [S1 X Y]
  calc 4 * 4 * 4 * 4 + 4 * 4 * 4 * (4 * (X * X) + 4 * (Y * Y))
        + 4 * 4 * (Bq X * Bq Y + Bq X * Bq (-X) + Bq X * Bq (-Y) + Bq Y * Bq (-X)
            + Bq Y * Bq (-Y) + Bq (-X) * Bq (-Y))
        + 4 * (Bq X * Bq Y * Bq (-X) + Bq X * Bq Y * Bq (-Y) + Bq X * Bq (-X) * Bq (-Y)
            + Bq Y * Bq (-X) * Bq (-Y))
        + Bq X * Bq Y * Bq (-X) * Bq (-Y)
      = 4 * 4 * 4 * 4
        + (4 * 4 * (Bq X * Bq Y + Bq X * Bq (-X) + Bq X * Bq (-Y) + Bq Y * Bq (-X)
            + Bq Y * Bq (-Y) + Bq (-X) * Bq (-Y))
          + 4 * 4 * 4 * (4 * (X * X) + 4 * (Y * Y)))
        + (4 * (Bq X * Bq Y * Bq (-X) + Bq X * Bq Y * Bq (-Y) + Bq X * Bq (-X) * Bq (-Y)
            + Bq Y * Bq (-X) * Bq (-Y)) + Bq X * Bq Y * Bq (-X) * Bq (-Y)) := by abel
    _ = 4 * 4 * 4 * 4
        + (4 * 4 * 4 * 4 * (X * Y - Y * X) + Err4 X Y)
        + (4 * (Bq X * Bq Y * Bq (-X) + Bq X * Bq Y * Bq (-Y) + Bq X * Bq (-X) * Bq (-Y)
            + Bq Y * Bq (-X) * Bq (-Y)) + Bq X * Bq Y * Bq (-X) * Bq (-Y)) := by
        rw [S2]
    _ = 4 * 4 * 4 * 4
        + (4 * 4 * 4 * 4 * (X * Y - Y * X) + Err4 X Y)
        + (4 * Trip4 X Y + Quad4 X Y) := by
        rw [show (4 * (Bq X * Bq Y * Bq (-X) + Bq X * Bq Y * Bq (-Y) + Bq X * Bq (-X) * Bq (-Y)
            + Bq Y * Bq (-X) * Bq (-Y)) + Bq X * Bq Y * Bq (-X) * Bq (-Y))
            = 4 * Trip4 X Y + Quad4 X Y from by
          simp only [Trip4, Quad4]]
    _ = 256 + 256 * (X * Y - Y * X) + Err4 X Y + 4 * Trip4 X Y + Quad4 X Y := by
        have h256 : (4 : Matrix ι ι ℂ) * 4 * 4 * 4 = 256 := by norm_num
        rw [h256]
        try abel

lemma smul_mul_smul' (a b : ℂ) (x y : Matrix ι ι ℂ) : (a • x) * (b • y) = (a*b) • (x*y) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

lemma smul_four_prod (a : ℂ) (x1 x2 x3 x4 : Matrix ι ι ℂ) :
    (a • x1) * (a • x2) * (a • x3) * (a • x4) = (a*a*a*a) • (x1*x2*x3*x4) := by
  rw [smul_mul_smul', smul_mul_smul', smul_mul_smul']

lemma norm_mul3_le (a b c : Matrix ι ι ℂ) : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  calc ‖a * b * c‖ ≤ ‖a * b‖ * ‖c‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖b‖) * ‖c‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg c)

lemma norm_mul4_le (a b c d : Matrix ι ι ℂ) :
    ‖a * b * c * d‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
  calc ‖a * b * c * d‖ ≤ ‖a * b * c‖ * ‖d‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖b‖ * ‖c‖) * ‖d‖ := mul_le_mul_of_nonneg_right (norm_mul3_le a b c) (norm_nonneg d)

lemma norm_add4_le (a b c d : Matrix ι ι ℂ) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h2 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h3 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  linarith

lemma norm_add8_le (a1 a2 a3 a4 a5 a6 a7 a8 : Matrix ι ι ℂ) :
    ‖a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8‖
      ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖a4‖ + ‖a5‖ + ‖a6‖ + ‖a7‖ + ‖a8‖ := by
  have h1 : ‖a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8‖
      ≤ ‖a1 + a2 + a3 + a4 + a5 + a6 + a7‖ + ‖a8‖ := norm_add_le _ _
  have h2 : ‖a1 + a2 + a3 + a4 + a5 + a6 + a7‖
      ≤ ‖a1 + a2 + a3 + a4 + a5 + a6‖ + ‖a7‖ := norm_add_le _ _
  have h3 : ‖a1 + a2 + a3 + a4 + a5 + a6‖
      ≤ ‖a1 + a2 + a3 + a4 + a5‖ + ‖a6‖ := norm_add_le _ _
  have h4 : ‖a1 + a2 + a3 + a4 + a5‖ ≤ ‖a1 + a2 + a3 + a4‖ + ‖a5‖ := norm_add_le _ _
  have h5 : ‖a1 + a2 + a3 + a4‖ ≤ ‖a1 + a2 + a3‖ + ‖a4‖ := norm_add_le _ _
  have h6 : ‖a1 + a2 + a3‖ ≤ ‖a1 + a2‖ + ‖a3‖ := norm_add_le _ _
  have h7 : ‖a1 + a2‖ ≤ ‖a1‖ + ‖a2‖ := norm_add_le a1 a2
  linarith

lemma norm_sub_le_add (a b c : Matrix ι ι ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  have h : a - c = (a - b) + (b - c) := by abel
  rw [h]; exact norm_add_le _ _

lemma norm_Err4_le (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖Err4 X Y‖ ≤ 512 * δ ^ 3 + 384 * δ ^ 4 := by
  have hx : (0:ℝ) ≤ ‖X‖ := norm_nonneg X
  have hy : (0:ℝ) ≤ ‖Y‖ := norm_nonneg Y
  have h3a : ‖X * X * Y‖ ≤ δ ^ 3 := by
    have h := norm_mul3_le X X Y
    have h12 : ‖X‖ * ‖X‖ ≤ δ * δ := mul_le_mul hX hX hx hδ0
    have h123 : ‖X‖ * ‖X‖ * ‖Y‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hY hy (mul_nonneg hδ0 hδ0)
    calc ‖X * X * Y‖ ≤ ‖X‖ * ‖X‖ * ‖Y‖ := h
      _ ≤ δ * δ * δ := h123
      _ = δ ^ 3 := by ring
  have h3b : ‖X * Y * Y‖ ≤ δ ^ 3 := by
    have h := norm_mul3_le X Y Y
    have h12 : ‖X‖ * ‖Y‖ ≤ δ * δ := mul_le_mul hX hY hy hδ0
    have h123 : ‖X‖ * ‖Y‖ * ‖Y‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hY hy (mul_nonneg hδ0 hδ0)
    calc ‖X * Y * Y‖ ≤ ‖X‖ * ‖Y‖ * ‖Y‖ := h
      _ ≤ δ * δ * δ := h123
      _ = δ ^ 3 := by ring
  have h3c : ‖Y * X * X‖ ≤ δ ^ 3 := by
    have h := norm_mul3_le Y X X
    have h12 : ‖Y‖ * ‖X‖ ≤ δ * δ := mul_le_mul hY hX hx hδ0
    have h123 : ‖Y‖ * ‖X‖ * ‖X‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hX hx (mul_nonneg hδ0 hδ0)
    calc ‖Y * X * X‖ ≤ ‖Y‖ * ‖X‖ * ‖X‖ := h
      _ ≤ δ * δ * δ := h123
      _ = δ ^ 3 := by ring
  have h3d : ‖Y * Y * X‖ ≤ δ ^ 3 := by
    have h := norm_mul3_le Y Y X
    have h12 : ‖Y‖ * ‖Y‖ ≤ δ * δ := mul_le_mul hY hY hy hδ0
    have h123 : ‖Y‖ * ‖Y‖ * ‖X‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hX hx (mul_nonneg hδ0 hδ0)
    calc ‖Y * Y * X‖ ≤ ‖Y‖ * ‖Y‖ * ‖X‖ := h
      _ ≤ δ * δ * δ := h123
      _ = δ ^ 3 := by ring
  have h4a : ‖X * X * X * X‖ ≤ δ ^ 4 := by
    have h := norm_mul4_le X X X X
    have h12 : ‖X‖ * ‖X‖ ≤ δ * δ := mul_le_mul hX hX hx hδ0
    have h123 : ‖X‖ * ‖X‖ * ‖X‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hX hx (mul_nonneg hδ0 hδ0)
    have h1234 : ‖X‖ * ‖X‖ * ‖X‖ * ‖X‖ ≤ δ * δ * δ * δ :=
      mul_le_mul h123 hX hx (mul_nonneg (mul_nonneg hδ0 hδ0) hδ0)
    calc ‖X * X * X * X‖ ≤ ‖X‖ * ‖X‖ * ‖X‖ * ‖X‖ := h
      _ ≤ δ * δ * δ * δ := h1234
      _ = δ ^ 4 := by ring
  have h4b : ‖X * X * Y * Y‖ ≤ δ ^ 4 := by
    have h := norm_mul4_le X X Y Y
    have h12 : ‖X‖ * ‖X‖ ≤ δ * δ := mul_le_mul hX hX hx hδ0
    have h123 : ‖X‖ * ‖X‖ * ‖Y‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hY hy (mul_nonneg hδ0 hδ0)
    have h1234 : ‖X‖ * ‖X‖ * ‖Y‖ * ‖Y‖ ≤ δ * δ * δ * δ :=
      mul_le_mul h123 hY hy (mul_nonneg (mul_nonneg hδ0 hδ0) hδ0)
    calc ‖X * X * Y * Y‖ ≤ ‖X‖ * ‖X‖ * ‖Y‖ * ‖Y‖ := h
      _ ≤ δ * δ * δ * δ := h1234
      _ = δ ^ 4 := by ring
  have h4c : ‖Y * Y * X * X‖ ≤ δ ^ 4 := by
    have h := norm_mul4_le Y Y X X
    have h12 : ‖Y‖ * ‖Y‖ ≤ δ * δ := mul_le_mul hY hY hy hδ0
    have h123 : ‖Y‖ * ‖Y‖ * ‖X‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hX hx (mul_nonneg hδ0 hδ0)
    have h1234 : ‖Y‖ * ‖Y‖ * ‖X‖ * ‖X‖ ≤ δ * δ * δ * δ :=
      mul_le_mul h123 hX hx (mul_nonneg (mul_nonneg hδ0 hδ0) hδ0)
    calc ‖Y * Y * X * X‖ ≤ ‖Y‖ * ‖Y‖ * ‖X‖ * ‖X‖ := h
      _ ≤ δ * δ * δ * δ := h1234
      _ = δ ^ 4 := by ring
  have h4d : ‖Y * Y * Y * Y‖ ≤ δ ^ 4 := by
    have h := norm_mul4_le Y Y Y Y
    have h12 : ‖Y‖ * ‖Y‖ ≤ δ * δ := mul_le_mul hY hY hy hδ0
    have h123 : ‖Y‖ * ‖Y‖ * ‖Y‖ ≤ δ * δ * δ :=
      mul_le_mul h12 hY hy (mul_nonneg hδ0 hδ0)
    have h1234 : ‖Y‖ * ‖Y‖ * ‖Y‖ * ‖Y‖ ≤ δ * δ * δ * δ :=
      mul_le_mul h123 hY hy (mul_nonneg (mul_nonneg hδ0 hδ0) hδ0)
    calc ‖Y * Y * Y * Y‖ ≤ ‖Y‖ * ‖Y‖ * ‖Y‖ * ‖Y‖ := h
      _ ≤ δ * δ * δ * δ := h1234
      _ = δ ^ 4 := by ring
  have n1 : ‖-(128 * (X * X * Y))‖ ≤ 128 * δ ^ 3 := by
    rw [norm_neg]
    calc ‖(128 : Matrix ι ι ℂ) * (X * X * Y)‖ ≤ 128 * ‖X * X * Y‖ := norm_nat_mul_le 128 _
      _ ≤ 128 * δ ^ 3 := mul_le_mul_of_nonneg_left h3a (by norm_num)
  have n2 : ‖128 * (X * Y * Y)‖ ≤ 128 * δ ^ 3 := by
    calc ‖(128 : Matrix ι ι ℂ) * (X * Y * Y)‖ ≤ 128 * ‖X * Y * Y‖ := norm_nat_mul_le 128 _
      _ ≤ 128 * δ ^ 3 := mul_le_mul_of_nonneg_left h3b (by norm_num)
  have n3 : ‖128 * (Y * X * X)‖ ≤ 128 * δ ^ 3 := by
    calc ‖(128 : Matrix ι ι ℂ) * (Y * X * X)‖ ≤ 128 * ‖Y * X * X‖ := norm_nat_mul_le 128 _
      _ ≤ 128 * δ ^ 3 := mul_le_mul_of_nonneg_left h3c (by norm_num)
  have n4 : ‖-(128 * (Y * Y * X))‖ ≤ 128 * δ ^ 3 := by
    rw [norm_neg]
    calc ‖(128 : Matrix ι ι ℂ) * (Y * Y * X)‖ ≤ 128 * ‖Y * Y * X‖ := norm_nat_mul_le 128 _
      _ ≤ 128 * δ ^ 3 := mul_le_mul_of_nonneg_left h3d (by norm_num)
  have n5 : ‖64 * (X * X * X * X)‖ ≤ 64 * δ ^ 4 := by
    calc ‖(64 : Matrix ι ι ℂ) * (X * X * X * X)‖ ≤ 64 * ‖X * X * X * X‖ := norm_nat_mul_le 64 _
      _ ≤ 64 * δ ^ 4 := mul_le_mul_of_nonneg_left h4a (by norm_num)
  have n6 : ‖192 * (X * X * Y * Y)‖ ≤ 192 * δ ^ 4 := by
    calc ‖(192 : Matrix ι ι ℂ) * (X * X * Y * Y)‖ ≤ 192 * ‖X * X * Y * Y‖ := norm_nat_mul_le 192 _
      _ ≤ 192 * δ ^ 4 := mul_le_mul_of_nonneg_left h4b (by norm_num)
  have n7 : ‖64 * (Y * Y * X * X)‖ ≤ 64 * δ ^ 4 := by
    calc ‖(64 : Matrix ι ι ℂ) * (Y * Y * X * X)‖ ≤ 64 * ‖Y * Y * X * X‖ := norm_nat_mul_le 64 _
      _ ≤ 64 * δ ^ 4 := mul_le_mul_of_nonneg_left h4c (by norm_num)
  have n8 : ‖64 * (Y * Y * Y * Y)‖ ≤ 64 * δ ^ 4 := by
    calc ‖(64 : Matrix ι ι ℂ) * (Y * Y * Y * Y)‖ ≤ 64 * ‖Y * Y * Y * Y‖ := norm_nat_mul_le 64 _
      _ ≤ 64 * δ ^ 4 := mul_le_mul_of_nonneg_left h4d (by norm_num)
  simp only [Err4]
  refine le_trans (norm_add8_le (-(128 * (X * X * Y))) (128 * (X * Y * Y)) (128 * (Y * X * X))
    (-(128 * (Y * Y * X))) (64 * (X * X * X * X)) (192 * (X * X * Y * Y))
    (64 * (Y * Y * X * X)) (64 * (Y * Y * Y * Y))) ?_
  linarith [n1, n2, n3, n4, n5, n6, n7, n8]

lemma norm_Trip4_le (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖Trip4 X Y‖ ≤ 864 * δ ^ 3 := by
  have hX' : ‖X‖ ≤ 1/2 := le_trans hX hδ1
  have hY' : ‖Y‖ ≤ 1/2 := le_trans hY hδ1
  have hBX := norm_Bq_le X δ hX hδ0 hδ1
  have hBY := norm_Bq_le Y δ hY hδ0 hδ1
  have hBnX := norm_Bq_le (-X) δ (by rwa [norm_neg]) hδ0 hδ1
  have hBnY := norm_Bq_le (-Y) δ (by rwa [norm_neg]) hδ0 hδ1
  have hd : (0:ℝ) ≤ 6 * δ := by linarith [hδ0]
  have t1 : ‖Bq X * Bq Y * Bq (-X)‖ ≤ (6*δ)^3 := by
    have h := norm_mul3_le (Bq X) (Bq Y) (Bq (-X))
    have h12 : ‖Bq X‖ * ‖Bq Y‖ ≤ (6*δ) * (6*δ) := mul_le_mul hBX hBY (norm_nonneg _) hd
    have h123 : ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ ≤ (6*δ) * (6*δ) * (6*δ) :=
      mul_le_mul h12 hBnX (norm_nonneg _) (mul_nonneg hd hd)
    calc ‖Bq X * Bq Y * Bq (-X)‖ ≤ ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ := h
      _ ≤ (6*δ) * (6*δ) * (6*δ) := h123
      _ = (6*δ)^3 := by ring
  have t2 : ‖Bq X * Bq Y * Bq (-Y)‖ ≤ (6*δ)^3 := by
    have h := norm_mul3_le (Bq X) (Bq Y) (Bq (-Y))
    have h12 : ‖Bq X‖ * ‖Bq Y‖ ≤ (6*δ) * (6*δ) := mul_le_mul hBX hBY (norm_nonneg _) hd
    have h123 : ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-Y)‖ ≤ (6*δ) * (6*δ) * (6*δ) :=
      mul_le_mul h12 hBnY (norm_nonneg _) (mul_nonneg hd hd)
    calc ‖Bq X * Bq Y * Bq (-Y)‖ ≤ ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-Y)‖ := h
      _ ≤ (6*δ) * (6*δ) * (6*δ) := h123
      _ = (6*δ)^3 := by ring
  have t3 : ‖Bq X * Bq (-X) * Bq (-Y)‖ ≤ (6*δ)^3 := by
    have h := norm_mul3_le (Bq X) (Bq (-X)) (Bq (-Y))
    have h12 : ‖Bq X‖ * ‖Bq (-X)‖ ≤ (6*δ) * (6*δ) := mul_le_mul hBX hBnX (norm_nonneg _) hd
    have h123 : ‖Bq X‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖ ≤ (6*δ) * (6*δ) * (6*δ) :=
      mul_le_mul h12 hBnY (norm_nonneg _) (mul_nonneg hd hd)
    calc ‖Bq X * Bq (-X) * Bq (-Y)‖ ≤ ‖Bq X‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖ := h
      _ ≤ (6*δ) * (6*δ) * (6*δ) := h123
      _ = (6*δ)^3 := by ring
  have t4 : ‖Bq Y * Bq (-X) * Bq (-Y)‖ ≤ (6*δ)^3 := by
    have h := norm_mul3_le (Bq Y) (Bq (-X)) (Bq (-Y))
    have h12 : ‖Bq Y‖ * ‖Bq (-X)‖ ≤ (6*δ) * (6*δ) := mul_le_mul hBY hBnX (norm_nonneg _) hd
    have h123 : ‖Bq Y‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖ ≤ (6*δ) * (6*δ) * (6*δ) :=
      mul_le_mul h12 hBnY (norm_nonneg _) (mul_nonneg hd hd)
    calc ‖Bq Y * Bq (-X) * Bq (-Y)‖ ≤ ‖Bq Y‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖ := h
      _ ≤ (6*δ) * (6*δ) * (6*δ) := h123
      _ = (6*δ)^3 := by ring
  simp only [Trip4]
  refine le_trans (norm_add4_le _ _ _ _) ?_
  have h864 : 4 * (6*δ)^3 = 864 * δ^3 := by ring
  linarith [t1, t2, t3, t4, h864]

lemma norm_Quad4_le (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖Quad4 X Y‖ ≤ 1296 * δ ^ 4 := by
  have hBX := norm_Bq_le X δ hX hδ0 hδ1
  have hBY := norm_Bq_le Y δ hY hδ0 hδ1
  have hBnX := norm_Bq_le (-X) δ (by rwa [norm_neg]) hδ0 hδ1
  have hBnY := norm_Bq_le (-Y) δ (by rwa [norm_neg]) hδ0 hδ1
  simp only [Quad4]
  have h := norm_mul4_le (Bq X) (Bq Y) (Bq (-X)) (Bq (-Y))
  have hd : (0:ℝ) ≤ 6 * δ := by linarith [hδ0]
  have h1 : ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖ ≤ (6*δ)^4 := by
    have h12 : ‖Bq X‖ * ‖Bq Y‖ ≤ (6*δ) * (6*δ) := mul_le_mul hBX hBY (norm_nonneg _) hd
    have h123 : ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ ≤ (6*δ) * (6*δ) * (6*δ) :=
      mul_le_mul h12 hBnX (norm_nonneg _) (mul_nonneg hd hd)
    have h1234 : ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖
        ≤ (6*δ) * (6*δ) * (6*δ) * (6*δ) :=
      mul_le_mul h123 hBnY (norm_nonneg _) (mul_nonneg (mul_nonneg hd hd) hd)
    calc ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖
        ≤ (6*δ) * (6*δ) * (6*δ) * (6*δ) := h1234
      _ = (6*δ)^4 := by ring
  calc ‖Bq X * Bq Y * Bq (-X) * Bq (-Y)‖
      ≤ ‖Bq X‖ * ‖Bq Y‖ * ‖Bq (-X)‖ * ‖Bq (-Y)‖ := h
    _ ≤ (6*δ)^4 := h1
    _ = 1296 * δ^4 := by ring

lemma norm_prod4_sub_le (a1 a2 a3 a4 b1 b2 b3 b4 : Matrix ι ι ℂ) (M ε : ℝ)
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (Ha1 : ‖a1‖ ≤ M) (Ha2 : ‖a2‖ ≤ M) (Ha3 : ‖a3‖ ≤ M) (Ha4 : ‖a4‖ ≤ M)
    (Hb1 : ‖b1‖ ≤ M) (Hb2 : ‖b2‖ ≤ M) (Hb3 : ‖b3‖ ≤ M) (Hb4 : ‖b4‖ ≤ M)
    (h1 : ‖a1 - b1‖ ≤ ε) (h2 : ‖a2 - b2‖ ≤ ε) (h3 : ‖a3 - b3‖ ≤ ε) (h4 : ‖a4 - b4‖ ≤ ε) :
    ‖a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4‖ ≤ 4 * (ε * M ^ 3) := by
  have e : a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4
      = (a1 - b1) * a2 * a3 * a4 + b1 * (a2 - b2) * a3 * a4
        + b1 * b2 * (a3 - b3) * a4 + b1 * b2 * b3 * (a4 - b4) := by noncomm_ring
  rw [e]
  have t1 : ‖(a1 - b1) * a2 * a3 * a4‖ ≤ ε * M ^ 3 := by
    have h := norm_mul4_le (a1 - b1) a2 a3 a4
    have h12 : ‖a1 - b1‖ * ‖a2‖ ≤ ε * M := mul_le_mul h1 Ha2 (norm_nonneg a2) hε
    have h123 : ‖a1 - b1‖ * ‖a2‖ * ‖a3‖ ≤ ε * M * M :=
      mul_le_mul h12 Ha3 (norm_nonneg a3) (by positivity)
    have hprod : ‖a1 - b1‖ * ‖a2‖ * ‖a3‖ * ‖a4‖ ≤ ε * M * M * M :=
      mul_le_mul h123 Ha4 (norm_nonneg a4) (by positivity)
    linarith [h, hprod]
  have t2 : ‖b1 * (a2 - b2) * a3 * a4‖ ≤ ε * M ^ 3 := by
    have h := norm_mul4_le b1 (a2 - b2) a3 a4
    have h12 : ‖b1‖ * ‖a2 - b2‖ ≤ M * ε := mul_le_mul Hb1 h2 (norm_nonneg (a2 - b2)) hM
    have h123 : ‖b1‖ * ‖a2 - b2‖ * ‖a3‖ ≤ M * ε * M :=
      mul_le_mul h12 Ha3 (norm_nonneg a3) (by positivity)
    have hprod : ‖b1‖ * ‖a2 - b2‖ * ‖a3‖ * ‖a4‖ ≤ M * ε * M * M :=
      mul_le_mul h123 Ha4 (norm_nonneg a4) (by positivity)
    linarith [h, hprod]
  have t3 : ‖b1 * b2 * (a3 - b3) * a4‖ ≤ ε * M ^ 3 := by
    have h := norm_mul4_le b1 b2 (a3 - b3) a4
    have h12 : ‖b1‖ * ‖b2‖ ≤ M * M := mul_le_mul Hb1 Hb2 (norm_nonneg b2) hM
    have h123 : ‖b1‖ * ‖b2‖ * ‖a3 - b3‖ ≤ M * M * ε :=
      mul_le_mul h12 h3 (norm_nonneg (a3 - b3)) (by positivity)
    have hprod : ‖b1‖ * ‖b2‖ * ‖a3 - b3‖ * ‖a4‖ ≤ M * M * ε * M :=
      mul_le_mul h123 Ha4 (norm_nonneg a4) (by positivity)
    linarith [h, hprod]
  have t4 : ‖b1 * b2 * b3 * (a4 - b4)‖ ≤ ε * M ^ 3 := by
    have h := norm_mul4_le b1 b2 b3 (a4 - b4)
    have h12 : ‖b1‖ * ‖b2‖ ≤ M * M := mul_le_mul Hb1 Hb2 (norm_nonneg b2) hM
    have h123 : ‖b1‖ * ‖b2‖ * ‖b3‖ ≤ M * M * M :=
      mul_le_mul h12 Hb3 (norm_nonneg b3) (by positivity)
    have hprod : ‖b1‖ * ‖b2‖ * ‖b3‖ * ‖a4 - b4‖ ≤ M * M * M * ε :=
      mul_le_mul h123 h4 (norm_nonneg (a4 - b4)) (by positivity)
    linarith [h, hprod]
  refine le_trans (norm_add4_le _ _ _ _) ?_
  nlinarith [t1, t2, t3, t4]

lemma q4Prod_master (X Y : Matrix ι ι ℂ) :
    q4Prod X Y = 256 + 256 * (X * Y - Y * X) + Err4 X Y + 4 * Trip4 X Y + Quad4 X Y := by
  rw [q4Prod]; exact master_identity X Y

lemma norm_Aexp_sub_q4_le (Z : Matrix ι ι ℂ) (hZ : ‖Z‖ ≤ 1) :
    ‖Aexp Z - q4 Z‖ ≤ 4 * ‖Z‖ ^ 3 := norm_four_smul_exp_sub_q4_le Z hZ

lemma pow_four_le_half (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    δ ^ 4 ≤ δ ^ 3 * (1/2) := by
  have h : δ ^ 4 = δ ^ 3 * δ := by ring
  rw [h]
  exact mul_le_mul_of_nonneg_left hδ1 (pow_nonneg hδ0 3)

lemma norm_Rem_le (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖Rem X Y‖ ≤ 4808 * δ ^ 3 := by
  have hEn := norm_Err4_le X Y δ hX hY hδ0 (le_trans hδ1 (by norm_num))
  have hTr := norm_Trip4_le X Y δ hX hY hδ0 hδ1
  have hQu := norm_Quad4_le X Y δ hX hY hδ0 hδ1
  have hm4 := pow_four_le_half δ hδ0 hδ1
  have h4T : ‖(4 : Matrix ι ι ℂ) * Trip4 X Y‖ ≤ 3456 * δ ^ 3 := by
    calc ‖(4 : Matrix ι ι ℂ) * Trip4 X Y‖ ≤ ‖(4 : Matrix ι ι ℂ)‖ * ‖Trip4 X Y‖ :=
          norm_mul_le _ _
      _ = 4 * ‖Trip4 X Y‖ := by rw [norm_four]
      _ ≤ 4 * (864 * δ ^ 3) := mul_le_mul_of_nonneg_left hTr (by norm_num)
      _ = 3456 * δ ^ 3 := by ring
  have htri : ‖Rem X Y‖ ≤ ‖Err4 X Y‖ + ‖(4 : Matrix ι ι ℂ) * Trip4 X Y‖ + ‖Quad4 X Y‖ := by
    rw [Rem]
    simpa using norm_add4_le (Err4 X Y) ((4 : Matrix ι ι ℂ) * Trip4 X Y) (Quad4 X Y) 0
  linarith [htri, hEn, h4T, hQu, hm4]

lemma norm_Lin_sub_le (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖Lin X Y - (256:ℂ) • ExpC X Y‖ ≤ 512 * δ ^ 3 := by
  have hC2 : ‖X * Y - Y * X‖ ≤ 2 * δ ^ 2 := by
    have h1 : ‖X * Y‖ ≤ δ * δ := by
      nlinarith [norm_mul_le X Y, hX, hY, hδ0, norm_nonneg X, norm_nonneg Y]
    have h2 : ‖Y * X‖ ≤ δ * δ := by
      nlinarith [norm_mul_le Y X, hX, hY, hδ0, norm_nonneg X, norm_nonneg Y]
    have h3 : ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    nlinarith [h1, h2, h3]
  have hsmall : ‖X * Y - Y * X‖ ≤ 1/2 := by nlinarith [hC2, hδ1, hδ0, sq_nonneg δ]
  have hlin := exp_sub_lin_le (X * Y - Y * X) hsmall
  have hnC : ‖X * Y - Y * X‖ ^ 2 ≤ 4 * δ ^ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg (X * Y - Y * X)) hC2 2
    have h4 : (2 * δ ^ 2) ^ 2 = 4 * δ ^ 4 := by ring
    linarith [h, h4]
  have hm4 := pow_four_le_half δ hδ0 hδ1
  rw [Lin, ExpC]
  have e : (256:ℂ) • (1 + (X * Y - Y * X)) - (256:ℂ) • NormedSpace.exp (X * Y - Y * X)
      = (256:ℂ) • ((1 + (X * Y - Y * X)) - NormedSpace.exp (X * Y - Y * X)) := by
    rw [smul_sub]
  rw [e, norm_smul, show ‖(256:ℂ)‖ = (256:ℝ) by norm_num]
  have e2 : (1 + (X * Y - Y * X)) - NormedSpace.exp (X * Y - Y * X)
      = -(NormedSpace.exp (X * Y - Y * X) - (1 + (X * Y - Y * X))) := by abel
  rw [e2, norm_neg]
  have h1 : 256 * ‖NormedSpace.exp (X * Y - Y * X) - (1 + (X * Y - Y * X))‖
      ≤ 256 * ‖X * Y - Y * X‖ ^ 2 := mul_le_mul_of_nonneg_left hlin (by norm_num)
  have h2 : 256 * ‖X * Y - Y * X‖ ^ 2 ≤ 256 * (4 * δ ^ 4) :=
    mul_le_mul_of_nonneg_left hnC (by norm_num)
  linarith [h1, h2, hm4]

set_option maxHeartbeats 800000 in

lemma norm_P_sub_le (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖q4Prod X Y - (256:ℂ) • ExpC X Y‖ ≤ 5320 * δ ^ 3 := by
  have hRem := norm_Rem_le X Y δ hX hY hδ0 hδ1
  have hL := norm_Lin_sub_le X Y δ hX hY hδ0 hδ1
  have hnum : Lin X Y = 256 + 256 * (X * Y - Y * X) := by
    rw [Lin, smul_add, smul_sub]
    have h1 : (256:ℂ) • (1 : Matrix ι ι ℂ) = 256 := by
      rw [Algebra.smul_def, map_ofNat, mul_one]
    have h2 : (256:ℂ) • (X * Y) = 256 * (X * Y) := by
      rw [Algebra.smul_def, map_ofNat]
    have h3 : (256:ℂ) • (Y * X) = 256 * (Y * X) := by
      rw [Algebra.smul_def, map_ofNat]
    rw [h1, h2, h3]
    noncomm_ring
  have hsplit : q4Prod X Y - (256:ℂ) • ExpC X Y
      = Rem X Y + (Lin X Y - (256:ℂ) • ExpC X Y) := by
    rw [q4Prod_master, Rem, ← hnum]
    abel
  calc ‖q4Prod X Y - (256:ℂ) • ExpC X Y‖
      = ‖Rem X Y + (Lin X Y - (256:ℂ) • ExpC X Y)‖ := by rw [hsplit]
    _ ≤ ‖Rem X Y‖ + ‖Lin X Y - (256:ℂ) • ExpC X Y‖ := norm_add_le _ _
    _ ≤ 4808 * δ ^ 3 + 512 * δ ^ 3 := add_le_add hRem hL
    _ = 5320 * δ ^ 3 := by ring

set_option maxHeartbeats 800000 in

lemma norm_A_prod_sub_P (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖QuadProd X Y - q4Prod X Y‖ ≤ 8192 * δ ^ 3 := by
  have hX' : ‖X‖ ≤ 1/2 := le_trans hX hδ1
  have hY' : ‖Y‖ ≤ 1/2 := le_trans hY hδ1
  have hXn : ‖-X‖ ≤ 1/2 := by rwa [norm_neg]
  have hYn : ‖-Y‖ ≤ 1/2 := by rwa [norm_neg]
  have Ha1 := norm_exp_four_smul_le X hX'
  have Ha2 := norm_exp_four_smul_le Y hY'
  have Ha3 := norm_exp_four_smul_le (-X) hXn
  have Ha4 := norm_exp_four_smul_le (-Y) hYn
  have Hb1 := norm_q4_le X hX'
  have Hb2 := norm_q4_le Y hY'
  have Hb3 := norm_q4_le (-X) hXn
  have Hb4 := norm_q4_le (-Y) hYn
  have hb1 : ‖Aexp X - q4 X‖ ≤ 4 * δ ^ 3 := by
    have h := norm_Aexp_sub_q4_le X (by linarith [hX, hδ1])
    have h3 : ‖X‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (norm_nonneg X) hX 3
    linarith
  have hb2 : ‖Aexp Y - q4 Y‖ ≤ 4 * δ ^ 3 := by
    have h := norm_Aexp_sub_q4_le Y (by linarith [hY, hδ1])
    have h3 : ‖Y‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (norm_nonneg Y) hY 3
    linarith
  have hb3 : ‖Aexp (-X) - q4 (-X)‖ ≤ 4 * δ ^ 3 := by
    have h := norm_Aexp_sub_q4_le (-X) (by rw [norm_neg]; linarith [hX, hδ1])
    rw [norm_neg] at h
    have h3 : ‖X‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (norm_nonneg X) hX 3
    linarith
  have hb4 : ‖Aexp (-Y) - q4 (-Y)‖ ≤ 4 * δ ^ 3 := by
    have h := norm_Aexp_sub_q4_le (-Y) (by rw [norm_neg]; linarith [hY, hδ1])
    rw [norm_neg] at h
    have h3 : ‖Y‖ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (norm_nonneg Y) hY 3
    linarith
  have h := norm_prod4_sub_le (Aexp X) (Aexp Y) (Aexp (-X)) (Aexp (-Y))
    (q4 X) (q4 Y) (q4 (-X)) (q4 (-Y)) 8 (4 * δ ^ 3)
    (by norm_num) (by positivity) Ha1 Ha2 Ha3 Ha4 Hb1 Hb2 Hb3 Hb4 hb1 hb2 hb3 hb4
  have h' : ‖QuadProd X Y - q4Prod X Y‖ ≤ 4 * ((4 * δ ^ 3) * 8 ^ 3) := h
  calc ‖QuadProd X Y - q4Prod X Y‖ ≤ 4 * ((4 * δ ^ 3) * 8 ^ 3) := h'
    _ = 8192 * δ ^ 3 := by ring

set_option maxHeartbeats 800000 in

theorem exp_commutator_third_order (X Y : Matrix ι ι ℂ) (δ : ℝ)
    (hX : ‖X‖ ≤ δ) (hY : ‖Y‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖NormedSpace.exp X * NormedSpace.exp Y * NormedSpace.exp (-X) * NormedSpace.exp (-Y)
        - NormedSpace.exp (X * Y - Y * X)‖ ≤ 64 * δ ^ 3 := by
  have hA := norm_A_prod_sub_P X Y δ hX hY hδ0 hδ1
  have hP : ‖q4Prod X Y - (256:ℂ) • ExpC X Y‖ ≤ 5320 * δ ^ 3 :=
    norm_P_sub_le X Y δ hX hY hδ0 hδ1
  have hAP : ‖QuadProd X Y - (256:ℂ) • ExpC X Y‖ ≤ 13512 * δ ^ 3 := by
    have h := norm_sub_le_add (QuadProd X Y) (q4Prod X Y) ((256:ℂ) • ExpC X Y)
    linarith [h, hA, hP]
  have hsmul : QuadProd X Y
      = (256:ℂ) • (NormedSpace.exp X * NormedSpace.exp Y
          * NormedSpace.exp (-X) * NormedSpace.exp (-Y)) := by
    rw [QuadProd]
    simp only [Aexp]
    rw [smul_four_prod]
    norm_num
  rw [hsmul] at hAP
  have heq : (256:ℂ) • (NormedSpace.exp X * NormedSpace.exp Y
        * NormedSpace.exp (-X) * NormedSpace.exp (-Y))
      - (256:ℂ) • ExpC X Y
      = (256:ℂ) • (NormedSpace.exp X * NormedSpace.exp Y
          * NormedSpace.exp (-X) * NormedSpace.exp (-Y) - ExpC X Y) := by rw [smul_sub]
  rw [heq, norm_smul, show ‖(256:ℂ)‖ = (256:ℝ) by norm_num] at hAP
  simp only [ExpC] at hAP
  nlinarith [hAP, pow_nonneg hδ0 3]

set_option maxHeartbeats 400000 in

theorem exp_commutator_hermitian (F G : Matrix ι ι ℂ) (hF : F.IsHermitian) (hG : G.IsHermitian)
    (δ : ℝ) (hFδ : ‖F‖ ≤ δ) (hGδ : ‖G‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    ‖NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G)
        * NormedSpace.exp (-(Complex.I • F)) * NormedSpace.exp (-(Complex.I • G))
      - NormedSpace.exp (-(F * G - G * F))‖ ≤ 64 * δ ^ 3 := by
  have hX : ‖Complex.I • F‖ ≤ δ := by
    rw [norm_smul, Complex.norm_I, one_mul]; exact hFδ
  have hY : ‖Complex.I • G‖ ≤ δ := by
    rw [norm_smul, Complex.norm_I, one_mul]; exact hGδ
  have hc : (Complex.I • F) * (Complex.I • G) - (Complex.I • G) * (Complex.I • F)
      = -(F * G - G * F) := by
    rw [smul_mul_smul', smul_mul_smul']
    rw [show Complex.I * Complex.I = -1 from Complex.I_mul_I]
    rw [neg_one_smul, neg_one_smul]
    abel
  have h := exp_commutator_third_order (Complex.I • F) (Complex.I • G) δ hX hY hδ0 hδ1
  rw [hc] at h
  exact h

end Qatlib.Papers.SolovayKitaev05.MainResults.ExponentialCommutator
