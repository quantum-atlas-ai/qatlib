/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma5

open Matrix

theorem pow_entry_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (L : ℕ) (hG : ∀ x y, 0 ≤ G x y) :
    ∀ x y, 0 ≤ (G ^ L) x y := by
  induction L with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ L ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hG z y))

theorem expectedMu_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (L : ℕ) (hG : ∀ x y, 0 ≤ G x y)
    (hden : 0 < ∑ x, ∑ y, (G ^ L) x y) :
    0 ≤ ExpectedMu G L := by
  unfold ExpectedMu
  exact div_nonneg
    (Finset.sum_nonneg (fun x _ =>
      Finset.sum_nonneg (fun y _ => pow_entry_nonneg G (L + 1) hG x y)))
    hden.le

theorem mulVec_pow_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (v : ι → ℝ) (mu : ℝ) (hv : G.mulVec v = mu • v) :
    ∀ L : ℕ, (G ^ L).mulVec v = (mu ^ L) • v := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']

theorem expectedMu_eq_of_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (G : Matrix ι ι ℝ) (mu0 : ℝ) (hmu0 : mu0 ≠ 0)
    (h1 : G.mulVec (fun _ => (1 : ℝ)) = mu0 • (fun _ => (1 : ℝ))) :
    ∀ L : ℕ, ExpectedMu G L = mu0 := by
  have hpow : ∀ L : ℕ,
      (G ^ L).mulVec (fun _ => (1 : ℝ)) = (mu0 ^ L) • (fun _ => (1 : ℝ)) :=
    mulVec_pow_eigen G (fun _ => (1 : ℝ)) mu0 h1
  intro L
  have hrow : ∀ (M : Matrix ι ι ℝ) (c : ℝ),
      M.mulVec (fun _ => (1 : ℝ)) = c • (fun _ => (1 : ℝ)) →
      (∑ x, ∑ y, M x y) = (Fintype.card ι : ℝ) * c := by
    intro M c hM
    calc ∑ x, ∑ y, M x y = ∑ x, M.mulVec (fun _ => (1 : ℝ)) x := by
          simp [Matrix.mulVec, dotProduct]
      _ = ∑ x, (c • (fun _ => (1 : ℝ))) x := by rw [hM]
      _ = ∑ _x : ι, c := by simp
      _ = (Fintype.card ι : ℝ) * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ExpectedMu
  rw [hrow (G ^ (L + 1)) (mu0 ^ (L + 1)) (hpow (L + 1)),
      hrow (G ^ L) (mu0 ^ L) (hpow L)]
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    have hne : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast hne
  have hL : mu0 ^ L ≠ 0 := pow_ne_zero _ hmu0
  rw [pow_succ']
  have hden : (Fintype.card ι : ℝ) * mu0 ^ L ≠ 0 := mul_ne_zero hc hL
  field_simp [hden]

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma5
