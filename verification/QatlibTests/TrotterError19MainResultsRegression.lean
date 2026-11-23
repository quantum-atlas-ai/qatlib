module

import Qatlib.Papers.TrotterError19.MainResults.Appendices.AppendixJ
import Qatlib.Papers.TrotterError19.MainResults.Appendices.SecondQuantizedCommutation
import Mathlib.Tactic

/-!
# Consumer regression for the TrotterError19 main-results additions

Exercise the two-summand fourth-order Suzuki error models on a non-degenerate qubit and the
second-quantized commutation rules of Lemma D.3 on the four-dimensional two-mode Fock
space.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace QatlibTests.TrotterError19MainResultsRegression

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.TrotterError19.MainResults.Appendices
open Qatlib.Papers.TrotterError19.MainResults (NestedCommutator NestedCommutator_pair)

/-- The Pauli X matrix on a qubit. -/
private def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Z matrix on a qubit. -/
private def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli X is Hermitian. -/
private theorem X_hermitian : X.IsHermitian := by
  unfold X Matrix.IsHermitian
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]

/-- Pauli Z is Hermitian. -/
private theorem Z_hermitian : Z.IsHermitian := by
  unfold Z Matrix.IsHermitian
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply]

/-- Pauli X is unitary. -/
private theorem X_unitary : X ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]

/-- Pauli Z is unitary. -/
private theorem Z_unitary : Z ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]

/-- Pauli X has unit spectral norm. -/
private theorem X_norm_one : ‖X‖ = 1 := CStarRing.norm_of_mem_unitary X_unitary

/-- Pauli Z has unit spectral norm. -/
private theorem Z_norm_one : ‖Z‖ = 1 := CStarRing.norm_of_mem_unitary Z_unitary

/-- Append one conjugation step to a nonempty nested commutator word: the outermost
commutator with `w` wraps the previous word. -/
private theorem NestedCommutator_append_singleton {I : Type} [Fintype I]
    (A : Matrix I I ℂ) (rest : List (Matrix I I ℂ)) (w : Matrix I I ℂ) :
    NestedCommutator ((A :: rest) ++ [w]) =
      w * NestedCommutator (A :: rest) - NestedCommutator (A :: rest) * w := by
  show List.foldl (fun acc X => X * acc - acc * X) A (rest ++ [w]) = _
  rw [List.foldl_append]
  rfl

/-- The spectral norm of any nested commutator of two factors is at most twice the product
of the factor norms, from submultiplicativity of the operator norm. -/
private theorem norm_NestedCommutator_pair_le (P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖NestedCommutator [P, Q]‖ ≤ 2 * ‖P‖ * ‖Q‖ := by
  rw [NestedCommutator_pair]
  calc ‖Q * P - P * Q‖ ≤ ‖Q * P‖ + ‖P * Q‖ := norm_sub_le _ _
    _ ≤ ‖Q‖ * ‖P‖ + ‖P‖ * ‖Q‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖Q‖ := by ring

/-- Every fourth-order commutator of the Pauli word `H = X + Z` has operator norm at
most `16`: the innermost commutator `[Z, X]` has norm `2` and each of the three outer
conjugation steps at most doubles the bound. -/
private theorem norm_twoTermCommutator_le : ∀ i j k : Fin 2,
    twoTermCommutatorNorm X Z i j k ≤ 16 := by
  have hXZ : ‖NestedCommutator [X, Z]‖ ≤ 2 := by
    refine (norm_NestedCommutator_pair_le X Z).trans ?_
    rw [X_norm_one, Z_norm_one]
    norm_num
  have ht : ∀ i : Fin 2, ‖![X, Z] i‖ = 1 := by
    intro i
    fin_cases i <;> simp [X_norm_one, Z_norm_one]
  have step : ∀ (x N : Matrix (Fin 2) (Fin 2) ℂ) (B : ℝ), ‖x‖ = 1 → ‖N‖ ≤ B →
      ‖NestedCommutator [N, x]‖ ≤ 2 * B := by
    intro x N B hx hN
    calc ‖NestedCommutator [N, x]‖ ≤ 2 * ‖N‖ * ‖x‖ := norm_NestedCommutator_pair_le N x
      _ = 2 * ‖N‖ := by rw [hx, mul_one]
      _ ≤ 2 * B := by nlinarith [hN, norm_nonneg N]
  have hN3 : ∀ k : Fin 2, ‖NestedCommutator [X, Z, ![X, Z] k]‖ ≤ 2 * 2 := by
    intro k
    rw [show [X, Z, ![X, Z] k] = ([X, Z] : List (Matrix (Fin 2) (Fin 2) ℂ)) ++ [![X, Z] k]
      from rfl, NestedCommutator_append_singleton, ← NestedCommutator_pair]
    exact step _ _ _ (ht k) hXZ
  have hN4 : ∀ j k : Fin 2, ‖NestedCommutator [X, Z, ![X, Z] k, ![X, Z] j]‖ ≤ 2 * (2 * 2) := by
    intro j k
    rw [show [X, Z, ![X, Z] k, ![X, Z] j] =
        ([X, Z, ![X, Z] k] : List (Matrix (Fin 2) (Fin 2) ℂ)) ++ [![X, Z] j]
      from rfl, NestedCommutator_append_singleton, ← NestedCommutator_pair]
    exact step _ _ (2 * 2) (ht j) (hN3 k)
  intro i j k
  show ‖NestedCommutator [X, Z, ![X, Z] k, ![X, Z] j, ![X, Z] i]‖ ≤ 16
  rw [show [X, Z, ![X, Z] k, ![X, Z] j, ![X, Z] i] =
      ([X, Z, ![X, Z] k, ![X, Z] j] : List (Matrix (Fin 2) (Fin 2) ℂ)) ++ [![X, Z] i]
    from rfl, NestedCommutator_append_singleton, ← NestedCommutator_pair]
  have hf := step _ _ (2 * (2 * 2)) (ht i) (hN4 j k)
  norm_num at hf
  exact hf

/-- The unconditional single-step fourth-order Suzuki error for `H = X + Z` at any real
time: the generator-mass bound applies with `L ≤ 8`. -/
example (t : ℝ) : suzukiFourthTwoTermError X Z t ≤
    2 * Real.exp (8 * |t|) * (8 * |t|) ^ 5 / 120 := by
  have h := suzuki_fourth_two_term_error_le_mass X Z X_hermitian Z_hermitian t
  have hXZ : ‖X + Z‖ ≤ 2 := (norm_add_le X Z).trans (by rw [X_norm_one, Z_norm_one]; norm_num)
  have hL : 3 * (‖X‖ + ‖Z‖) + ‖X + Z‖ ≤ 8 := by
    rw [X_norm_one, Z_norm_one]
    linarith [hXZ]
  have hL0 : 0 ≤ 3 * (‖X‖ + ‖Z‖) + ‖X + Z‖ := by
    rw [X_norm_one, Z_norm_one]
    positivity
  dsimp only at h
  have hexp : Real.exp ((3 * (‖X‖ + ‖Z‖) + ‖X + Z‖) * |t|) ≤ Real.exp (8 * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hL (abs_nonneg t))
  have hpow : ((3 * (‖X‖ + ‖Z‖) + ‖X + Z‖) * |t|) ^ 5 ≤ (8 * |t|) ^ 5 :=
    pow_le_pow_left₀ (mul_nonneg hL0 (abs_nonneg t))
      (mul_le_mul_of_nonneg_right hL (abs_nonneg t)) 5
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc 2 * Real.exp ((3 * (‖X‖ + ‖Z‖) + ‖X + Z‖) * |t|) *
        ((3 * (‖X‖ + ‖Z‖) + ‖X + Z‖) * |t|) ^ 5
      ≤ 2 * Real.exp (8 * |t|) * ((3 * (‖X‖ + ‖Z‖) + ‖X + Z‖) * |t|) ^ 5 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (pow_nonneg (mul_nonneg hL0 (abs_nonneg t)) 5)
    _ ≤ 2 * Real.exp (8 * |t|) * (8 * |t|) ^ 5 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The uniform constant of Eq. (319) on the non-degenerate qubit: under the weighted
bound hypothesis, the error is at most `0.0875 * t ^ 5 * 16` for every nonnegative time. -/
example {t : ℝ} (ht : 0 ≤ t)
    (hmain : suzukiFourthTwoTermError X Z t ≤ t ^ 5 * ∑ i, ∑ j, ∑ k,
      twoTermCoeff i j k * twoTermCommutatorNorm X Z i j k) :
    suzukiFourthTwoTermError X Z t ≤ 0.0875 * t ^ 5 * 16 :=
  suzuki_fourth_two_term_error_le_of_comm_bound X Z ht norm_twoTermCommutator_le hmain

/-- The uniform constant for the reduction from Eq. (319), quantified before the register,
matrices, and time. -/
example : ∃ C > 0, ∀ {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (A B : Matrix n n ℂ) (t : ℝ), 0 ≤ t →
    (∀ i j k, twoTermCommutatorNorm A B i j k ≤ 1) →
    (suzukiFourthTwoTermError A B t ≤ t ^ 5 * ∑ i, ∑ j, ∑ k,
      twoTermCoeff i j k * twoTermCommutatorNorm A B i j k) →
    suzukiFourthTwoTermError A B t ≤ C * t ^ 5 :=
  suzuki_fourth_two_term_uniform_constant

/-- The anticommutator of the creation and annihilation operators across different
modes: `A₀ A₁^† + A₁^† A₀ = δ₀₁ 1`. -/
example : annihTwo 0 * createTwo 1 + createTwo 1 * annihTwo 0 =
    if (0 : Fin 2) = 1 then 1 else 0 :=
  car_mixed 0 1

/-- The annihilation operators anticommute: `A₀ A₁ + A₁ A₀ = 0`. -/
example : annihTwo 0 * annihTwo 1 + annihTwo 1 * annihTwo 0 = 0 :=
  car_annih 0 1

/-- The exchange rule of Lemma D.3 at `(j, k, l, m) = (0, 1, 1, 0)`:
`[E₀₁, E₁₀] = E₀₀ − E₁₁`. -/
example : numberBilinear 0 1 * numberBilinear 1 0 -
      numberBilinear 1 0 * numberBilinear 0 1 =
    (if (1 : Fin 2) = (1 : Fin 2) then numberBilinear 0 0 else 0) -
      if (0 : Fin 2) = (0 : Fin 2) then numberBilinear 1 1 else 0 :=
  lemmaD3_exchange 0 1 1 0

/-- The number-operator rule of Lemma D.3 at `(j, k, l) = (0, 1, 1)` gives
`[E₀₁, N₁] = E₀₁`. -/
example : numberBilinear 0 1 * numberOp 1 - numberOp 1 * numberBilinear 0 1 =
    numberBilinear 0 1 := by
  simpa using lemmaD3_number 0 1 1

/-- The derivation rule of Lemma D.3 at `(j, k, l, m) = (0, 1, 1, 1)` gives
`[E₀₁, N₁ N₁] = E₀₁ N₁ + N₁ E₀₁`. -/
example : numberBilinear 0 1 * (numberOp 1 * numberOp 1) -
      numberOp 1 * numberOp 1 * numberBilinear 0 1 =
    numberBilinear 0 1 * numberOp 1 + numberOp 1 * numberBilinear 0 1 := by
  simpa using lemmaD3_number_product 0 1 1 1

end QatlibTests.TrotterError19MainResultsRegression
