/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactDiffuse22.MainResults.Model.SourceModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Batteries.Tactic.Lint

set_option backward.isDefEq.respectTransparency false

/-!
# Condition Number Bound for the Forward-Euler History System Matrix

This module formalizes Lemma 4.4: when the single-step forward-Euler propagation
operator `1 + h • A` is a contraction in spectral norm, the `(m + 1)`-step history
system matrix `eulerSystemMatrix A h m` has spectral condition number at most
`2 * (m + 1)`.

## Main statements

* `source_lemma44`: `opNorm2 (1 + h • A) ≤ 1` implies
  `conditionNumber (eulerSystemMatrix A h m) ≤ 2 * (m + 1)`.

## References

* [Jin, Liu, and Yu, 2022][JinLiuYu2022ReactDiffuse], Section 4, Lemma 4.4,
  Eqs. (4.21)--(4.29), pp. 21--22.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ReactDiffuse22.MainResults.Source
open Qatlib.Papers.ReactDiffuse22.MainResults

/-- **Lemma 4.4**: if the single-step Euler operator satisfies `‖I + hA‖₂ ≤ 1`,
then the `(m + 1)`-step Euler system matrix `L` has condition number at most
`2 * (m + 1)`. -/
theorem source_lemma44
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ℝ) (m : ℕ)
    (hnorm : opNorm2 (1 + h • A) ≤ 1) :
    conditionNumber (eulerSystemMatrix A h m) ≤ 2 * ((m : ℝ) + 1) := by
  classical
  let B : Matrix ι ι ℝ := 1 + h • A
  have hB : ‖B‖ ≤ 1 := hnorm
  let S : Matrix (Fin (m + 1) × ι) (Fin (m + 1) × ι) ℝ :=
    fun p q => if p.1.val = q.1.val + 1 then B p.2 q.2 else 0
  have hL : eulerSystemMatrix A h m = 1 - S := by
    ext p q
    by_cases ht : p.1 = q.1
    · simp [eulerSystemMatrix, S, ht, Matrix.one_apply, Prod.ext_iff]
    · by_cases hs : p.1.val = q.1.val + 1
      · simp [eulerSystemMatrix, S, B, ht, hs, Matrix.one_apply, Prod.ext_iff]
        ring
      · simp [eulerSystemMatrix, S, ht, hs, Prod.ext_iff]
  have hS : ‖S‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (m + 1) × ι)
    let U := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)
    let slice (k : Fin (m + 1)) : EuclideanSpace ℝ ι :=
      WithLp.toLp 2 (fun i => v (k, i))
    have hzero (i : ι) : T S v (0, i) = 0 := by
      change (∑ q, S (0, i) q * v q) = 0
      apply Finset.sum_eq_zero
      intro q _
      simp [S]
    have hsucc (k : Fin m) (i : ι) :
        T S v (k.succ, i) = U B (slice k.castSucc) i := by
      change (∑ q, S (k.succ, i) q * v q) = ∑ j, B i j * v (k.castSucc, j)
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single k.castSucc]
      · simp [S]
      · intro l _ hl
        have ht : k.val ≠ l.val := by
          intro he
          apply hl
          apply Fin.ext
          exact he.symm
        simp [S, ht]
      · simp
    have hslice (k : Fin m) :
        ‖U B (slice k.castSucc)‖ ^ 2 ≤
          ‖slice k.castSucc‖ ^ 2 := by
      have hv := (U B).le_opNorm (slice k.castSucc)
      have hb : ‖U B‖ ≤ 1 := hB
      have hn : ‖U B (slice k.castSucc)‖ ≤
          ‖slice k.castSucc‖ := by
        apply hv.trans
        simpa using (mul_le_mul_of_nonneg_right hb (norm_nonneg (slice k.castSucc)))
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
    have hsq : ‖T S v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_succ]
      simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add]
      calc
        (∑ k : Fin m, ∑ i : ι, (T S v (k.succ, i)) ^ 2) =
            ∑ k : Fin m, ‖U B (slice k.castSucc)‖ ^ 2 := by
          simp_rw [hsucc, EuclideanSpace.real_norm_sq_eq]
        _ ≤ ∑ k : Fin m, ‖slice k.castSucc‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => hslice k
        _ ≤ (∑ k : Fin m, ‖slice k.castSucc‖ ^ 2) + ‖slice (Fin.last m)‖ ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
        _ = ‖v‖ ^ 2 := by
          symm
          rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
          simp only [EuclideanSpace.real_norm_sq_eq]
          rfl
    simpa only [one_mul] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  have hI : ‖(1 : Matrix (Fin (m + 1) × ι) (Fin (m + 1) × ι) ℝ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hpow (r : ℕ) (p q : Fin (m + 1) × ι)
      (hpq : p.1.val < q.1.val + r) : (S ^ r) p q = 0 := by
    induction r generalizing p with
    | zero =>
        have hp : p ≠ q := by intro he; subst p; omega
        simp [hp]
    | succ r ih =>
        rw [pow_succ', Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : p.1.val = k.1.val + 1
        · have hlt : k.1.val < q.1.val + r := by omega
          rw [ih k hlt, mul_zero]
        · simp [S, hk]
  have hnil : S ^ (m + 1) = 0 := by
    ext p q
    exact hpow (m + 1) p q (by have hp := p.1.isLt; omega)
  let R := ∑ r ∈ Finset.range (m + 1), S ^ r
  have hinv : (1 - S)⁻¹ = R := by
    apply Matrix.inv_eq_right_inv
    dsimp [R]
    rw [mul_neg_geom_sum, hnil, sub_zero]
  have hR : ‖R‖ ≤ (m : ℝ) + 1 := by
    have hp (r : ℕ) : ‖S ^ r‖ ≤ 1 := by
      induction r with
      | zero => simpa using hI
      | succ r ih =>
          calc
            ‖S ^ (r + 1)‖ = ‖S ^ r * S‖ := by rw [pow_succ]
            _ ≤ ‖S ^ r‖ * ‖S‖ := norm_mul_le _ _
            _ ≤ 1 * 1 := mul_le_mul ih hS (norm_nonneg _) zero_le_one
            _ = 1 := one_mul _
    calc
      ‖R‖ ≤ ∑ r ∈ Finset.range (m + 1), ‖S ^ r‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ Finset.range (m + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun r _ => hp r
      _ = (m : ℝ) + 1 := by simp
  have hLn : ‖1 - S‖ ≤ 2 := by
    calc
      ‖1 - S‖ ≤ ‖(1 : Matrix (Fin (m + 1) × ι) (Fin (m + 1) × ι) ℝ)‖ + ‖S‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by linarith
  change ‖eulerSystemMatrix A h m‖ * ‖(eulerSystemMatrix A h m)⁻¹‖ ≤ _
  rw [hL, hinv]
  exact mul_le_mul hLn hR (norm_nonneg _) (by norm_num)

#lint only unusedArguments

end Qatlib.Papers.ReactDiffuse22.MainResults.Source
