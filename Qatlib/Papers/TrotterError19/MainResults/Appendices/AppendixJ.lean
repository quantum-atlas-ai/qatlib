/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
public import Qatlib.Papers.TrotterError19.MainResults.SourceModel

@[expose] public section


/-!
# Fourth-order Suzuki error coefficients

Table 2 of [ChildsEtAl2021Trotter] supplies weights for the spectral norms of
fourfold nested commutators. This module evaluates the coefficient sum and
derives a uniform estimate assuming the weighted error bound in Eq. (320).
It also tabulates the eight coefficients of Eq. (319) for two summands, reduces
their weighted bound to the uniform constant `0.0875 * t ^ 5 * M` on a
non-degenerate register, and proves an unconditional generator-mass bound for
the same single fourth-order Suzuki word.
-/

set_option autoImplicit false
noncomputable section


open scoped Matrix.Norms.L2Operator BigOperators
open Matrix
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
  (recursiveSuzukiWord recursiveSuzukiError recursive_suzuki_actual_simulation_and_cost)
open Qatlib.Concepts.TrotterFormula.SuzukiFourth (suzukiMass)
open Qatlib.Concepts.TrotterFormula.GeneralOrder (general_trotter_mass_nonneg)
open Qatlib.Foundations.PureStateMath (HamiltonianEvolution)
open Qatlib.Papers.TrotterError19.MainResults (NestedCommutator)

namespace Qatlib.Papers.TrotterError19.MainResults.Appendices

section

/-- The coefficients `c_{i,j,k,l,m}` of Table 2 (arXiv:1912.08854v3, p. 74),
indexed from `1` to `3` as in the paper. The table lists the 27 rows
for each of the three innermost pairs `[H₂,H₁]`, `[H₃,H₁]`, `[H₃,H₂]`; the
remaining pairs have coefficient zero. Reversing the inner pair changes the
sign of the nested commutator and preserves its norm. Equal inner indices
give the zero commutator. -/
def tableCoeff (i j k l m : ℕ) : ℝ :=
  match l, m with
  | 2, 1 =>
    match i, j, k with
    | 1, 1, 1 => 0.0047
    | 1, 1, 2 => 0.0057
    | 1, 1, 3 => 0.0057
    | 1, 2, 1 => 0.0046
    | 1, 2, 2 => 0.0074
    | 1, 2, 3 => 0.0082
    | 1, 3, 1 => 0.0046
    | 1, 3, 2 => 0.0070
    | 1, 3, 3 => 0.0082
    | 2, 1, 1 => 0.0150
    | 2, 1, 2 => 0.0161
    | 2, 1, 3 => 0.0161
    | 2, 2, 1 => 0.0239
    | 2, 2, 2 => 0.0315
    | 2, 2, 3 => 0.0303
    | 2, 3, 1 => 0.0179
    | 2, 3, 2 => 0.0232
    | 2, 3, 3 => 0.0259
    | 3, 1, 1 => 0.0204
    | 3, 1, 2 => 0.0225
    | 3, 1, 3 => 0.0225
    | 3, 2, 1 => 0.0423
    | 3, 2, 2 => 0.0585
    | 3, 2, 3 => 0.0502
    | 3, 3, 1 => 0.0423
    | 3, 3, 2 => 0.0681
    | 3, 3, 3 => 0.0648
    | _, _, _ => 0
  | 3, 1 =>
    match i, j, k with
    | 1, 1, 1 => 0.0047
    | 1, 1, 2 => 0.0057
    | 1, 1, 3 => 0.0057
    | 1, 2, 1 => 0.0046
    | 1, 2, 2 => 0.0070
    | 1, 2, 3 => 0.0082
    | 1, 3, 1 => 0.0046
    | 1, 3, 2 => 0.0058
    | 1, 3, 3 => 0.0074
    | 2, 1, 1 => 0.0150
    | 2, 1, 2 => 0.0161
    | 2, 1, 3 => 0.0161
    | 2, 2, 1 => 0.0239
    | 2, 2, 2 => 0.0306
    | 2, 2, 3 => 0.0303
    | 2, 3, 1 => 0.0179
    | 2, 3, 2 => 0.0206
    | 2, 3, 3 => 0.0241
    | 3, 1, 1 => 0.0204
    | 3, 1, 2 => 0.0225
    | 3, 1, 3 => 0.0225
    | 3, 2, 1 => 0.0423
    | 3, 2, 2 => 0.0571
    | 3, 2, 3 => 0.0502
    | 3, 3, 1 => 0.0423
    | 3, 3, 2 => 0.0641
    | 3, 3, 3 => 0.0621
    | _, _, _ => 0
  | 3, 2 =>
    match i, j, k with
    | 1, 1, 1 => 0.0043
    | 1, 1, 2 => 0.0057
    | 1, 1, 3 => 0.0057
    | 1, 2, 1 => 0.0035
    | 1, 2, 2 => 0.0062
    | 1, 2, 3 => 0.0082
    | 1, 3, 1 => 0.0035
    | 1, 3, 2 => 0.0046
    | 1, 3, 3 => 0.0074
    | 2, 1, 1 => 0.0141
    | 2, 1, 2 => 0.0161
    | 2, 1, 3 => 0.0161
    | 2, 2, 1 => 0.0212
    | 2, 2, 2 => 0.0290
    | 2, 2, 3 => 0.0303
    | 2, 3, 1 => 0.0153
    | 2, 3, 2 => 0.0179
    | 2, 3, 3 => 0.0241
    | 3, 1, 1 => 0.0186
    | 3, 1, 2 => 0.0217
    | 3, 1, 3 => 0.0225
    | 3, 2, 1 => 0.0377
    | 3, 2, 2 => 0.0537
    | 3, 2, 3 => 0.0502
    | 3, 3, 1 => 0.0377
    | 3, 3, 2 => 0.0601
    | 3, 3, 3 => 0.0628
    | _, _, _ => 0
  | _, _ => 0

/-- The Table 2 coefficients as a function of five `Fin 3` indices. -/
def cTable (i j k l m : Fin 3) : ℝ :=
  tableCoeff (i.val + 1) (j.val + 1) (k.val + 1) (l.val + 1) (m.val + 1)

end

/-- Every Table 2 coefficient is nonnegative and at most `0.0681`, the
largest printed entry.  This is the sign and size input needed before the
coefficients of Proposition J.2 (Eq. (320)) can be pulled out of a weighted
sum of nested-commutator norms. -/
theorem cTable_nonneg_and_le (i j k l m : Fin 3) :
    0 ≤ cTable i j k l m ∧ cTable i j k l m ≤ 0.0681 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;>
    norm_num [cTable, tableCoeff]

/-- A Table 2 coefficient vanishes unless the last index is strictly
smaller than the fourth index: the only nonzero blocks of Table 2 are the
pairs `(l, m) = (2, 1), (3, 1), (3, 2)` in the paper's one-based indexing,
matching the nested commutators `[H_l, H_m]` with `m < l`. -/
theorem cTable_eq_zero_of_le (i j k : Fin 3) {l m : Fin 3} (h : l ≤ m) :
    cTable i j k l m = 0 := by
  have hv : l.val ≤ m.val := h
  obtain ⟨lv, _hlv⟩ := l
  obtain ⟨mv, _hmv⟩ := m
  interval_cases lv <;> interval_cases mv <;> norm_num [cTable, tableCoeff]

/-- The sum of all `3 ^ 5` Table 2 coefficients is exactly `1.8776`: the
three nonzero blocks contribute `0.6476`, `0.6318`, and `0.5982`. -/
theorem cTable_sum :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, cTable i j k l m) = 1.8776 := by
  norm_num [Fin.sum_univ_three, cTable, tableCoeff]

/-- If every weight `w i j k l m` is at most `M`, then the Table 2
weighted sum is at most `1.8776 * M`. -/
theorem cTable_weighted_sum_le
    (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (M : ℝ)
    (hw : ∀ i j k l m, w i j k l m ≤ M) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, cTable i j k l m * w i j k l m) ≤ 1.8776 * M := by
  calc (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, cTable i j k l m * w i j k l m)
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, cTable i j k l m * M := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro k _
        apply Finset.sum_le_sum; intro l _
        apply Finset.sum_le_sum; intro m _
        exact mul_le_mul_of_nonneg_left (hw i j k l m) (cTable_nonneg_and_le i j k l m).1
    _ = 1.8776 * M := by
        simp only [← Finset.sum_mul]
        rw [cTable_sum]

/-- The spectral norm of `[Hᵢ, [Hⱼ, [Hₖ, [Hₗ, Hₘ]]]]` in Eq. (320). -/
def tableCommutatorNorm {n : Type} [Fintype n] [DecidableEq n]
    (H : Fin 3 → Matrix n n ℂ) (i j k l m : Fin 3) : ℝ :=
  ‖NestedCommutator [H m, H l, H k, H j, H i]‖

/-- The spectral-norm error of one fourth-order Suzuki step for three summands.
The recursion starts with the second-order formula at level zero. -/
def suzukiFourthThreeTermError {n : Type} [Fintype n] [DecidableEq n]
    (H : Fin 3 → Matrix n n ℂ) (t : ℝ) : ℝ :=
  ‖(recursiveSuzukiWord [(-Complex.I) • H 0, (-Complex.I) • H 1, (-Complex.I) • H 2]
      1 t 1).prod - HamiltonianEvolution (∑ j, H j) t‖

/-- Assuming the weighted error bound in Eq. (320) at a nonnegative time,
a single upper bound `M` on the commutator norms gives
`1.8776 * t ^ 5 * M` as an upper bound on the same Suzuki error. -/
theorem suzuki_fourth_error_le_of_table_bound {n : Type} [Fintype n] [DecidableEq n]
    (H : Fin 3 → Matrix n n ℂ) {t M : ℝ}
    (ht : 0 ≤ t) (hw : ∀ i j k l m, tableCommutatorNorm H i j k l m ≤ M)
    (hmain : suzukiFourthThreeTermError H t ≤ t ^ 5 * ∑ i, ∑ j, ∑ k, ∑ l, ∑ m,
      cTable i j k l m * tableCommutatorNorm H i j k l m) :
    suzukiFourthThreeTermError H t ≤ 1.8776 * t ^ 5 * M := by
  refine le_trans hmain ?_
  have h := mul_le_mul_of_nonneg_left (cTable_weighted_sum_le (tableCommutatorNorm H) M hw)
    (pow_nonneg ht 5)
  have e : (1.8776 : ℝ) * t ^ 5 * M = t ^ 5 * (1.8776 * M) := by ring
  rw [e]; exact h

/-- The eight coefficients of Eq. (319) of arXiv:1912.08854v3 (p. 73) for the two-summand
fourth-order Suzuki error, indexed by the three outer factors of the nested commutator
`[Xᵢ, [Xⱼ, [Xₖ, [B, A]]]]` with `X₀ = A` and `X₁ = B`. -/
def twoTermCoeff (i j k : Fin 2) : ℝ :=
  match i.val, j.val, k.val with
  | 0, 0, 0 => 0.0047
  | 0, 0, 1 => 0.0057
  | 0, 1, 0 => 0.0046
  | 0, 1, 1 => 0.0074
  | 1, 0, 0 => 0.0097
  | 1, 0, 1 => 0.0097
  | 1, 1, 0 => 0.0173
  | 1, 1, 1 => 0.0284
  | _, _, _ => 0

/-- Every coefficient of Eq. (319) is nonnegative. -/
theorem twoTermCoeff_nonneg : ∀ i j k : Fin 2, 0 ≤ twoTermCoeff i j k := by
  simp only [Fin.forall_fin_two]
  repeat' apply And.intro
  all_goals norm_num [twoTermCoeff]

/-- Every coefficient of Eq. (319) is at most `0.0284`, the largest printed entry. -/
theorem twoTermCoeff_le : ∀ i j k : Fin 2, twoTermCoeff i j k ≤ 0.0284 := by
  simp only [Fin.forall_fin_two]
  repeat' apply And.intro
  all_goals norm_num [twoTermCoeff]

/-- The sum of the eight coefficients of Eq. (319) is exactly `0.0875`. -/
theorem twoTermCoeff_sum : (∑ i, ∑ j, ∑ k, twoTermCoeff i j k) = 0.0875 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [twoTermCoeff]

/-- If every weight `w i j k` is at most `M`, the coefficient-weighted sum of Eq. (319) is
at most `0.0875 * M`. -/
theorem twoTermCoeff_weighted_sum_le
    (w : Fin 2 → Fin 2 → Fin 2 → ℝ) (M : ℝ)
    (hw : ∀ i j k, w i j k ≤ M) :
    (∑ i, ∑ j, ∑ k, twoTermCoeff i j k * w i j k) ≤ 0.0875 * M := by
  calc (∑ i, ∑ j, ∑ k, twoTermCoeff i j k * w i j k)
      ≤ ∑ i, ∑ j, ∑ k, twoTermCoeff i j k * M := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hw i j k) (twoTermCoeff_nonneg i j k)
    _ = 0.0875 * M := by
        simp only [← Finset.sum_mul]
        rw [twoTermCoeff_sum]

/-- The spectral norm of `[Xᵢ, [Xⱼ, [Xₖ, [B, A]]]]` in Eq. (319), where `X₀ = A` and
`X₁ = B`. -/
def twoTermCommutatorNorm {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (i j k : Fin 2) : ℝ :=
  ‖NestedCommutator [A, B, ![A, B] k, ![A, B] j, ![A, B] i]‖

/-- The spectral-norm error of one fourth-order Suzuki step for `H = A + B`, with the
second-order formula at recursion level zero. -/
def suzukiFourthTwoTermError {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  ‖(recursiveSuzukiWord [(-Complex.I) • A, (-Complex.I) • B] 1 t 1).prod -
    HamiltonianEvolution (A + B) t‖

/-- Assuming the coefficient-weighted error bound of Eq. (319) at a nonnegative time and
on a non-degenerate register, a single upper bound `M` on the eight fourth-order commutator
norms gives the uniform estimate `0.0875 * t ^ 5 * M`; the constant `0.0875` is fixed
outside every quantifier. -/
theorem suzuki_fourth_two_term_error_le_of_comm_bound {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] (A B : Matrix n n ℂ) {t M : ℝ}
    (ht : 0 ≤ t) (hw : ∀ i j k, twoTermCommutatorNorm A B i j k ≤ M)
    (hmain : suzukiFourthTwoTermError A B t ≤ t ^ 5 * ∑ i, ∑ j, ∑ k,
      twoTermCoeff i j k * twoTermCommutatorNorm A B i j k) :
    suzukiFourthTwoTermError A B t ≤ 0.0875 * t ^ 5 * M := by
  refine le_trans hmain ?_
  have h := mul_le_mul_of_nonneg_left
    (twoTermCoeff_weighted_sum_le (twoTermCommutatorNorm A B) M hw) (pow_nonneg ht 5)
  have e : (0.0875 : ℝ) * t ^ 5 * M = t ^ 5 * (0.0875 * M) := by ring
  rw [e]; exact h

/-- A single positive constant `C = 0.0875` bounds the single-step fourth-order Suzuki error
by `C * t ^ 5` whenever the Eq. (319) weighted bound holds and all eight commutator norms are
at most `1` on a non-degenerate register at nonnegative time. -/
theorem suzuki_fourth_two_term_uniform_constant :
    ∃ C > 0, ∀ {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
      (A B : Matrix n n ℂ) (t : ℝ), 0 ≤ t →
      (∀ i j k, twoTermCommutatorNorm A B i j k ≤ 1) →
      (suzukiFourthTwoTermError A B t ≤ t ^ 5 * ∑ i, ∑ j, ∑ k,
        twoTermCoeff i j k * twoTermCommutatorNorm A B i j k) →
      suzukiFourthTwoTermError A B t ≤ C * t ^ 5 := by
  refine ⟨0.0875, by norm_num, ?_⟩
  intro n _ _ _ A B t ht hw hmain
  have h := suzuki_fourth_two_term_error_le_of_comm_bound A B ht hw hmain
  rw [mul_one] at h
  exact h

/-- The unconditional single-step error of the two-term fourth-order Suzuki word from the
general word machinery: with `L = 3 * (‖A‖ + ‖B‖) + ‖A + B‖` the mass of the
anti-Hermitian generators, the error is at most `2 * exp (L * |t|) * (L * |t|) ^ 5 / 5!`. -/
theorem suzuki_fourth_two_term_error_le_mass {n : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    let L := 3 * (‖A‖ + ‖B‖) + ‖A + B‖
    suzukiFourthTwoTermError A B t ≤
      2 * Real.exp (L * |t|) * (L * |t|) ^ 5 / ((5).factorial : ℝ) := by
  dsimp only
  have hanti : ∀ X ∈ [(-Complex.I) • A, (-Complex.I) • B], Xᴴ = -X := by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · rw [Matrix.conjTranspose_smul, hA.eq, ← neg_smul]
      congr 1
      simp
    · rw [Matrix.conjTranspose_smul, hB.eq, ← neg_smul]
      congr 1
      simp
  have hs0 := recursive_suzuki_actual_simulation_and_cost n
    [(-Complex.I) • A, (-Complex.I) • B] 1 1 t hanti (by norm_num)
  have hsum : ([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum =
      (-Complex.I) • (A + B) := by
    simp [smul_add]
  have hev : HamiltonianEvolution (A + B) t =
      NormedSpace.exp (t • ([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum) := by
    rw [hsum]
    unfold HamiltonianEvolution
    congr 1
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  have hm : suzukiMass [(-Complex.I) • A, (-Complex.I) • B] ≤ ‖A‖ + ‖B‖ := by
    have e : ∀ M : Matrix n n ℂ, ‖(-Complex.I) • M‖ ≤ ‖M‖ := by
      intro M
      calc ‖(-Complex.I) • M‖ ≤ ‖(-Complex.I : ℂ)‖ * ‖M‖ := norm_smul_le _ _
        _ = ‖M‖ := by simp
    calc suzukiMass [(-Complex.I) • A, (-Complex.I) • B]
        = ‖(-Complex.I) • A‖ + ‖(-Complex.I) • B‖ := by simp [suzukiMass]
      _ ≤ ‖A‖ + ‖B‖ := add_le_add (e A) (e B)
  have hsum_le : ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖ ≤
      ‖A + B‖ := by
    rw [hsum]
    calc ‖(-Complex.I) • (A + B)‖ ≤ ‖(-Complex.I : ℂ)‖ * ‖A + B‖ := norm_smul_le _ _
      _ = ‖A + B‖ := by simp
  have hm0 : 0 ≤ suzukiMass [(-Complex.I) • A, (-Complex.I) • B] :=
    general_trotter_mass_nonneg _
  have hL : 3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
      ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖ ≤
      3 * (‖A‖ + ‖B‖) + ‖A + B‖ := by
    have h1 : 3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] ≤
        3 * (‖A‖ + ‖B‖) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    exact add_le_add h1 hsum_le
  have hL0 : 0 ≤ 3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
      ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖ :=
    add_nonneg (mul_nonneg (by norm_num) hm0) (norm_nonneg _)
  unfold suzukiFourthTwoTermError
  rw [hev]
  refine hs0.2.2.trans ?_
  simp only [recursiveSuzukiError]
  have ht1 : |t / ((1 : ℕ) : ℝ)| = |t| := by rw [Nat.cast_one, div_one]
  rw [ht1]
  norm_num1
  have hexp : Real.exp
      ((3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
        ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖) * |t|) ≤
      Real.exp ((3 * (‖A‖ + ‖B‖) + ‖A + B‖) * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hL (abs_nonneg t))
  have hpow : ((3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
      ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖) * |t|) ^ 5 ≤
      ((3 * (‖A‖ + ‖B‖) + ‖A + B‖) * |t|) ^ 5 :=
    pow_le_pow_left₀ (mul_nonneg hL0 (abs_nonneg t))
      (mul_le_mul_of_nonneg_right hL (abs_nonneg t)) 5
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc 2 * Real.exp
        ((3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
          ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖) * |t|) *
        ((3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
          ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖) * |t|) ^ 5
      ≤ 2 * Real.exp ((3 * (‖A‖ + ‖B‖) + ‖A + B‖) * |t|) *
        ((3 * suzukiMass [(-Complex.I) • A, (-Complex.I) • B] +
          ‖([(-Complex.I) • A, (-Complex.I) • B] : List (Matrix n n ℂ)).sum‖) * |t|) ^ 5 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (pow_nonneg (mul_nonneg hL0 (abs_nonneg t)) 5)
    _ ≤ 2 * Real.exp ((3 * (‖A‖ + ‖B‖) + ‖A + B‖) * |t|) *
        ((3 * (‖A‖ + ‖B‖) + ‖A + B‖) * |t|) ^ 5 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

end Qatlib.Papers.TrotterError19.MainResults.Appendices
