/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9: telescoping identity and norm bound for unitary products

Source: Tong--Albert--McClean--Preskill--Su, fixed arXiv:2110.06942v2,
Lemma 9 (p.32). For a projection `Π` and unitary operators `U_j, Ũ_j`,
`‖(∏_{j=1}^J Ũ_j − ∏_{j=1}^J U_j) Π‖ ≤ Σ_{j=1}^J ‖(Ũ_j − U_j)(∏_{j'=1}^{j-1} U_{j'}) Π‖`.

We prove the underlying exact identity
`∏ Ũ − ∏ U = Σ_j (Ũ_J⋯Ũ_{j+1})(Ũ_j − U_j)(U_{j-1}⋯U_1)`
and deduce the norm inequality with `‖(Ũ_J⋯Ũ_{j+1})‖ ≤ 1`. The ordered product
`prodR U J = U_J ⋯ U_1` uses the paper's convention (later index on the left,
as in the time-ordered exponential).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.GaugeSim21.MainResults.UnitaryProductTelescope

variable {I : Type} [Fintype I] [DecidableEq I]

/-- `prodR U J = U_J ⋯ U_1` (paper order: larger index on the left). `prodR U 0 = 1`. -/
def prodR (U : ℕ → Matrix I I ℂ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | (n + 1) => U (n + 1) * prodR U n

/-- `upperProd V j J = V_J ⋯ V_{j+1}` if `J > j`, and `1` otherwise. -/
def upperProd (V : ℕ → Matrix I I ℂ) (j : ℕ) : ℕ → Matrix I I ℂ
  | 0 => 1
  | (n + 1) => if n + 1 ≤ j then 1 else V (n + 1) * upperProd V j n

/-- The empty ordered product `prodR U 0` is the identity matrix. -/
@[simp] theorem prodR_zero (U : ℕ → Matrix I I ℂ) : prodR U 0 = 1 := rfl

/-- The ordered product unfolds as `prodR U (n+1) = U (n+1) * prodR U n`. -/
@[simp] theorem prodR_succ (U : ℕ → Matrix I I ℂ) (n : ℕ) :
    prodR U (n + 1) = U (n + 1) * prodR U n := rfl

/-- The empty suffix product `upperProd V j 0` is the identity matrix. -/
@[simp] theorem upperProd_zero (V : ℕ → Matrix I I ℂ) (j : ℕ) :
    upperProd V j 0 = 1 := rfl

/-- When `n+1 ≤ j`, the suffix product `upperProd V j (n+1)` is the identity. -/
theorem upperProd_succ_of_le (V : ℕ → Matrix I I ℂ) (j n : ℕ) (h : n + 1 ≤ j) :
    upperProd V j (n + 1) = 1 := by
  simp [upperProd, h]

/-- When `j < n+1`, the suffix product extends by the factor `V (n+1)` on the left. -/
theorem upperProd_succ_of_lt (V : ℕ → Matrix I I ℂ) (j n : ℕ) (h : ¬ n + 1 ≤ j) :
    upperProd V j (n + 1) = V (n + 1) * upperProd V j n := by
  simp [upperProd, h]

/-- The exact telescoping identity behind Lemma 9 (p.32), before taking norms. -/
theorem telescopes (U V : ℕ → Matrix I I ℂ) (J : ℕ) :
    prodR V J - prodR U J =
      ∑ j ∈ Finset.Icc 1 J, upperProd V j J * (V j - U j) * prodR U (j - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hdecomp : V (J + 1) * prodR V J - U (J + 1) * prodR U J
        = V (J + 1) * (prodR V J - prodR U J) + (V (J + 1) - U (J + 1)) * prodR U J := by
      noncomm_ring
    rw [prodR_succ V J, prodR_succ U J, hdecomp, ih]
    have key : V (J + 1) * (∑ j ∈ Finset.Icc 1 J,
          upperProd V j J * (V j - U j) * prodR U (j - 1))
        = ∑ j ∈ Finset.Icc 1 J,
            upperProd V j (J + 1) * (V j - U j) * prodR U (j - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ J := (Finset.mem_Icc.mp hj).2
      have hlt : ¬ (J + 1) ≤ j := by omega
      rw [upperProd_succ_of_lt V j J hlt]
      noncomm_ring
    have htop : (V (J + 1) - U (J + 1)) * prodR U J
        = upperProd V (J + 1) (J + 1) * (V (J + 1) - U (J + 1)) * prodR U ((J + 1) - 1) := by
      rw [upperProd_succ_of_le V (J + 1) J (by omega)]
      simp
    rw [key, htop]
    rw [show (Finset.Icc 1 (J + 1)) = insert (J + 1) (Finset.Icc 1 J) by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
    abel

/-- Norm of `upperProd` (a suffix product of unitaries) is at most one. -/
theorem norm_upperProd_le_one (V : ℕ → Matrix I I ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup I ℂ) (j : ℕ) [Nonempty I] :
    ∀ J, ‖upperProd V j J‖ ≤ 1
  | 0 => by simp
  | (n + 1) => by
      by_cases h : n + 1 ≤ j
      · rw [upperProd_succ_of_le V j n h]; simp
      · rw [upperProd_succ_of_lt V j n h]
        refine (norm_mul_le _ _).trans ?_
        have h1 : ‖V (n + 1)‖ = 1 := CStarRing.norm_of_mem_unitary (hV (n + 1))
        rw [h1, one_mul]
        exact norm_upperProd_le_one V hV j n

/-- Lemma 9 (p.32): for unitary `U_j, Ũ_j` and any projection `P`, the product
difference is bounded by the sum of the shifted single-factor errors. -/
theorem lemma9_norm_ineq (P : Matrix I I ℂ) (U V : ℕ → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup I ℂ) (J : ℕ) [Nonempty I] :
    ‖(prodR V J - prodR U J) * P‖ ≤
      ∑ j ∈ Finset.Icc 1 J, ‖(V j - U j) * prodR U (j - 1) * P‖ := by
  rw [telescopes U V J, Finset.sum_mul]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hup : ‖upperProd V j J‖ ≤ 1 := norm_upperProd_le_one V hV j J
  have hrepr : (upperProd V j J * (V j - U j) * prodR U (j - 1)) * P
      = upperProd V j J * ((V j - U j) * prodR U (j - 1) * P) := by
    noncomm_ring
  rw [hrepr]
  exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hup)

end Qatlib.Papers.GaugeSim21.MainResults.UnitaryProductTelescope
