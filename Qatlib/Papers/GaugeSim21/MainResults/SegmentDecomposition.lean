/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.BigOperators.Intervals

set_option backward.isDefEq.respectTransparency false

/-!
# Segment Decomposition of Subspace Leakage

This module formalizes Lemma 2 of Tong, Albert, McClean, Preskill, and Su giving
the exact first-exit segment decomposition of the leakage operator
`P̄_J e^{-i t_J H} P_0` across complementary operator pairs `P_j + P̄_j = I` and
the resulting triangle-inequality operator-norm bound.

## Main statements

* `seg`: single time segment `e^{-i (t_{k+1} - t_k) H} P_k`.
* `Q`: time-ordered product `seg_k ⋯ seg_0`.
* `lemma2_decomposition`: Eq. (48), exact first-exit decomposition of `P̄_J e^{-i t_J H} P_0`.
* `lemma2_norm_bound`: Eq. (49), per-segment leakage norm bound.

## References

* [Tong et al., 2022][TongEtAl2022], Section 3, Lemma 2, Eqs. (48)--(49), p. 22.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.GaugeSim21.MainResults.SegmentDecomposition

open Qatlib.Foundations.PureStateMath

variable {I : Type} [Fintype I] [DecidableEq I]

/-- One time segment `seg_k = e^{-i (t_{k+1} - t_k) H} P_k`. -/
def seg (H : Matrix I I ℂ) (P : ℕ → Matrix I I ℂ) (tt : ℕ → ℝ) (k : ℕ) :
    Matrix I I ℂ :=
  HamiltonianEvolution H (tt (k + 1) - tt k) * P k

/-- `Q k = seg_k ⋯ seg_0` with later segments on the left. -/
def Q (H : Matrix I I ℂ) (P : ℕ → Matrix I I ℂ) (tt : ℕ → ℝ) : ℕ → Matrix I I ℂ
  | 0 => seg H P tt 0
  | (n + 1) => seg H P tt (n + 1) * Q H P tt n

private lemma aux_decomposition
    (H : Matrix I I ℂ) (P Pc : ℕ → Matrix I I ℂ) (tt : ℕ → ℝ)
    (hsum : ∀ j, P j + Pc j = 1) (htt0 : tt 0 = 0)
    (J : ℕ) (hJ : 1 ≤ J) :
    HamiltonianEvolution H (tt J) * P 0 =
      Q H P tt (J - 1) +
        ∑ j ∈ Finset.Ico 1 J,
          HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1) := by
  induction J, hJ using Nat.le_induction with
  | base => simp [Q, seg, htt0]
  | succ J hJ ih =>
    have hQ : seg H P tt J * Q H P tt (J - 1) = Q H P tt J := by
      calc
        seg H P tt J * Q H P tt (J - 1) =
            seg H P tt ((J - 1) + 1) * Q H P tt (J - 1) := by
          rw [Nat.sub_add_cancel hJ]
        _ = Q H P tt ((J - 1) + 1) := rfl
        _ = Q H P tt J := by rw [Nat.sub_add_cancel hJ]
    calc
      HamiltonianEvolution H (tt (J + 1)) * P 0 =
          HamiltonianEvolution H (tt (J + 1) - tt J) *
            (HamiltonianEvolution H (tt J) * P 0) := by
        rw [← mul_assoc, ← hamiltonianEvolution_add, sub_add_cancel]
      _ = HamiltonianEvolution H (tt (J + 1) - tt J) * Q H P tt (J - 1) +
          ∑ j ∈ Finset.Ico 1 J,
            HamiltonianEvolution H (tt (J + 1) - tt j) * Pc j * Q H P tt (j - 1) := by
        rw [ih, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, ← mul_assoc, ← hamiltonianEvolution_add,
          sub_add_sub_cancel]
      _ = (Q H P tt J +
          HamiltonianEvolution H (tt (J + 1) - tt J) * Pc J * Q H P tt (J - 1)) +
          ∑ j ∈ Finset.Ico 1 J,
            HamiltonianEvolution H (tt (J + 1) - tt j) * Pc j * Q H P tt (j - 1) := by
        congr 1
        calc
          HamiltonianEvolution H (tt (J + 1) - tt J) * Q H P tt (J - 1) =
              HamiltonianEvolution H (tt (J + 1) - tt J) * (P J + Pc J) *
                Q H P tt (J - 1) := by rw [hsum, mul_one]
          _ = _ := by rw [mul_add, add_mul, ← seg, hQ]
      _ = Q H P tt (J + 1 - 1) +
          ∑ j ∈ Finset.Ico 1 (J + 1),
            HamiltonianEvolution H (tt (J + 1) - tt j) * Pc j * Q H P tt (j - 1) := by
        rw [Nat.add_sub_cancel, Finset.sum_Ico_succ_top hJ]
        ac_rfl

/-- Lemma 2, Eq. (48): exact decomposition of `P̄_J e^{-i t_J H} P_0` into the
`J` first-exit segments. -/
theorem lemma2_decomposition
    (H : Matrix I I ℂ) (P Pc : ℕ → Matrix I I ℂ) (tt : ℕ → ℝ)
    (hsum : ∀ j, P j + Pc j = 1)
    (hPc : ∀ j, Pc j * Pc j = Pc j)
    (htt0 : tt 0 = 0)
    (J : ℕ) (hJ : 1 ≤ J) :
    Pc J * HamiltonianEvolution H (tt J) * P 0 =
      Pc J * (∑ j ∈ Finset.Icc 1 J,
        HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1)) := by
  rw [mul_assoc, aux_decomposition H P Pc tt hsum htt0 J hJ,
    ← Finset.Ico_insert_right hJ, Finset.sum_insert Finset.right_notMem_Ico,
    sub_self, hamiltonianEvolution_zero, one_mul, mul_add, mul_add,
    ← mul_assoc (Pc J) (Pc J), hPc J]

/-- Lemma 2, Eq. (49): the total leakage norm is bounded by the sum of
per-segment leakage norms when `H` is Hermitian and `P_j, P̄_j` are contractions. -/
theorem lemma2_norm_bound
    (H : Matrix I I ℂ) (P Pc : ℕ → Matrix I I ℂ) (tt : ℕ → ℝ)
    (hsum : ∀ j, P j + Pc j = 1)
    (hPc : ∀ j, Pc j * Pc j = Pc j)
    (htt0 : tt 0 = 0)
    (hH : H.IsHermitian)
    (hPnorm : ∀ j, ‖P j‖ ≤ 1) (hPcnorm : ∀ j, ‖Pc j‖ ≤ 1)
    (J : ℕ) (hJ : 1 ≤ J) [Nonempty I] :
    ‖Pc J * HamiltonianEvolution H (tt J) * P 0‖ ≤
      ∑ j ∈ Finset.Icc 1 J,
        ‖Pc j * HamiltonianEvolution H (tt j - tt (j - 1)) * P (j - 1)‖ := by
  refine (And.left ⟨?_, And.intro hH (And.intro hPnorm (And.intro hPcnorm ‹Nonempty I›))⟩)
  have hUnorm (θ : ℝ) : ‖HamiltonianEvolution H θ‖ = 1 :=
    CStarRing.norm_of_mem_unitary (hamiltonianEvolution_unitary hH θ)
  have hseg (k : ℕ) : ‖seg H P tt k‖ ≤ 1 := by
    calc
      ‖seg H P tt k‖ ≤ ‖HamiltonianEvolution H (tt (k + 1) - tt k)‖ * ‖P k‖ :=
        norm_mul_le _ _
      _ = ‖P k‖ := by rw [hUnorm, one_mul]
      _ ≤ 1 := hPnorm k
  have hQnorm (k : ℕ) : ‖Q H P tt k‖ ≤ 1 := by
    induction k with
    | zero => exact hseg 0
    | succ k ih =>
      calc
        ‖Q H P tt (k + 1)‖ ≤ ‖seg H P tt (k + 1)‖ * ‖Q H P tt k‖ :=
          norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hseg (k + 1)) ih (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  rw [lemma2_decomposition H P Pc tt hsum hPc htt0 J hJ]
  calc
    ‖Pc J * (∑ j ∈ Finset.Icc 1 J,
        HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1))‖ ≤
        ‖Pc J‖ * ‖∑ j ∈ Finset.Icc 1 J,
          HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1)‖ :=
      norm_mul_le _ _
    _ ≤ 1 * ‖∑ j ∈ Finset.Icc 1 J,
          HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1)‖ :=
      mul_le_mul_of_nonneg_right (hPcnorm J) (norm_nonneg _)
    _ = ‖∑ j ∈ Finset.Icc 1 J,
          HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1)‖ := one_mul _
    _ ≤ ∑ j ∈ Finset.Icc 1 J,
          ‖HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 J,
          ‖Pc j * HamiltonianEvolution H (tt j - tt (j - 1)) * P (j - 1)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      calc
        ‖HamiltonianEvolution H (tt J - tt j) * Pc j * Q H P tt (j - 1)‖ =
            ‖HamiltonianEvolution H (tt J - tt j) * (Pc j * Q H P tt (j - 1))‖ := by
          rw [mul_assoc]
        _ ≤ ‖HamiltonianEvolution H (tt J - tt j)‖ * ‖Pc j * Q H P tt (j - 1)‖ :=
          norm_mul_le _ _
        _ = ‖Pc j * Q H P tt (j - 1)‖ := by rw [hUnorm, one_mul]
        _ ≤ ‖Pc j * HamiltonianEvolution H (tt j - tt (j - 1)) * P (j - 1)‖ := by
          by_cases hj : j = 1
          · subst j
            simp only [Nat.sub_self, Q, seg, zero_add, mul_assoc, le_refl]
          · have hpred : j - 1 = (j - 2) + 1 := by omega
            have hQstep : Q H P tt (j - 1) =
                seg H P tt (j - 1) * Q H P tt (j - 2) := by
              rw [hpred, Q]
            rw [hQstep, seg, Nat.sub_add_cancel hj1,
              ← mul_assoc, ← mul_assoc]
            calc
              ‖(Pc j * HamiltonianEvolution H (tt j - tt (j - 1)) * P (j - 1)) *
                  Q H P tt (j - 2)‖ ≤
                  ‖Pc j * HamiltonianEvolution H (tt j - tt (j - 1)) * P (j - 1)‖ *
                    ‖Q H P tt (j - 2)‖ := norm_mul_le _ _
              _ ≤ ‖Pc j * HamiltonianEvolution H (tt j - tt (j - 1)) * P (j - 1)‖ * 1 :=
                mul_le_mul_of_nonneg_left (hQnorm (j - 2)) (norm_nonneg _)
              _ = _ := mul_one _

end Qatlib.Papers.GaugeSim21.MainResults.SegmentDecomposition
