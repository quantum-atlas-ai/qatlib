/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Actual finite complex products from squared Euclidean mass

Demand: LinearOptics10 Lemma 64. The full finite AM-GM argument is
applied to the genuine nonnegative squared complex magnitudes.
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.PureStateMath.LinearChange.ProductBound

/-- AM-GM bounds the actual finite product by the nth power of its arithmetic mean. -/
theorem finiteMean {n : ℕ} (hn : n ≠ 0) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i, z i) ≤ ((∑ i, z i)/(n : ℝ))^n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : (0 : ℝ) < ∑ _i : Fin n, (1 : ℝ) := by simpa using hnR
  have he := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin n => (1 : ℝ)) z
    (fun _ _ => by norm_num) hs (fun i _ => hz i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at he
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg fun i _ => hz i) _) he n
  rwa [Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => hz i) hn] at hp

/-- Squared Euclidean mass nK-squared bounds the genuine complex product by K-to-the-n. -/
theorem complexProd {n : ℕ} (y : Fin n → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hy : (∑ i, Complex.normSq (y i)) ≤ (n : ℝ)*K^2) : ‖∏ i, y i‖ ≤ K^n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he := finiteMean hn (fun i => Complex.normSq (y i)) (fun i => Complex.normSq_nonneg _)
  have hm : (∑ i, Complex.normSq (y i))/(n : ℝ) ≤ K^2 := by
    apply (div_le_iff₀ hnR).mpr
    simpa only [mul_comm] using hy
  have hp := he.trans (pow_le_pow_left₀
    (div_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) hnR.le) hm n)
  have hid : (∏ i, Complex.normSq (y i)) = ‖∏ i, y i‖^2 := by
    simp only [Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]
  rw [hid] at hp
  have hkpow : (K^2)^n = (K^n)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  rw [hkpow] at hp
  exact (sq_le_sq₀ (norm_nonneg _) (pow_nonneg hK _)).mp hp

end Qatlib.Foundations.PureStateMath.LinearChange.ProductBound
