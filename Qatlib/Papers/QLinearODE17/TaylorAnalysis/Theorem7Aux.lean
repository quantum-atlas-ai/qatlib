/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6Quan

/-!
# Terminal accuracy and Taylor-block norm estimates

This module converts coordinatewise estimates into Euclidean norm bounds and derives
consequences of the terminal accuracy condition. Theorems `taylorV2_error_of_accuracy` and
`taylorV2_terminal_direction` control time-block error and the normalized terminal direction;
positive-order block estimates support the final mass bound. See [BerryEtAl2017ODE] for the
paper's setting.

## Main statements

* `taylor_stateVector_norm_mono`: Coordinatewise norm domination implies domination of the
  associated Euclidean state norms.
* `taylorV2_mass_arithmetic`: The stated total-mass and final-block lower bounds imply `X / sqrt
  (p + 77*m*g²) ≤ Y`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

variable {N : Type} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in

/-- Coordinatewise norm domination implies domination of the associated Euclidean state norms. -/
theorem taylor_stateVector_norm_mono (u v : QState N) (h : ∀ n, ‖u n‖ ≤ ‖v n‖) :
    ‖stateVector u‖ ≤ ‖stateVector v‖ := by
  have hs : ‖stateVector u‖ ^ 2 ≤ ‖stateVector v‖ ^ 2 := by
    rw [stateVector_norm_sq, stateVector_norm_sq]
    exact Finset.sum_le_sum (fun n _ => pow_le_pow_left₀ (norm_nonneg _) (h n) 2)
  nlinarith [norm_nonneg (stateVector u), norm_nonneg (stateVector v)]

omit [DecidableEq N] in

/-- Replacing every coordinate by its nonnegative real norm preserves the Euclidean state norm. -/
theorem taylor_stateVector_norm_abs (u : QState N) :
    ‖stateVector (fun n => (‖u n‖ : ℂ))‖ = ‖stateVector u‖ := by
  have hs : ‖stateVector (fun n => (‖u n‖ : ℂ))‖ ^ 2 = ‖stateVector u‖ ^ 2 := by
    rw [stateVector_norm_sq, stateVector_norm_sq]
    simp [MeasureProb, BornProb]
  nlinarith [norm_nonneg (stateVector (fun n => (‖u n‖ : ℂ))), norm_nonneg (stateVector u)]

omit [DecidableEq N] in

/-- A coordinatewise bound `‖u n‖ ≤ ‖v n‖ + t*‖w n‖`, with `t ≥ 0`, implies the corresponding
bound on Euclidean state norms. -/
theorem taylor_stateVector_norm_affine (u v w : QState N) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ n, ‖u n‖ ≤ ‖v n‖ + t * ‖w n‖) :
    ‖stateVector u‖ ≤ ‖stateVector v‖ + t * ‖stateVector w‖ := by
  let v' : QState N := fun n => (‖v n‖ : ℂ)
  let w' : QState N := fun n => (‖w n‖ : ℂ)
  have hv : ‖stateVector v'‖ = ‖stateVector v‖ := taylor_stateVector_norm_abs v
  have hw : ‖stateVector w'‖ = ‖stateVector w‖ := taylor_stateVector_norm_abs w
  calc ‖stateVector u‖ ≤ ‖stateVector (v' + t • w')‖ := by
        apply taylor_stateVector_norm_mono
        intro n
        have heq : (v' + t • w') n = ((‖v n‖ + t * ‖w n‖ : ℝ) : ℂ) := by
          simp [v', w', Complex.real_smul]
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact h n
    _ ≤ ‖stateVector v'‖ + t * ‖stateVector w'‖ := by
        have htri := norm_add_le (stateVector v') (t • stateVector w')
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at htri
        exact htri
    _ = ‖stateVector v‖ + t * ‖stateVector w‖ := by rw [hv, hw]

/-- For a stable diagonalizable generator and nonnegative time, the reference solution norm is
at most `‖V‖ * ‖V⁻¹‖` times the sum of the initial norm and time times the forcing norm. -/
theorem taylorODESolution_norm_le_diagonalizable (A V D : Matrix N N ℂ)
    (hA : A = V * D * V⁻¹) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (hre : ∀ n, (D n n).re ≤ 0)
    (b x_in : QState N) (t : ℝ) (ht : 0 ≤ t) :
    ‖stateVector (taylorODESolution A b x_in t)‖ ≤
      (‖V‖ * ‖V⁻¹‖) * (‖stateVector x_in‖ + t * ‖stateVector b‖) := by
  have heq : taylorODESolution A b x_in t = V *ᵥ
      (fun n => duhamelCoord (D n n) ((V⁻¹ *ᵥ x_in) n) ((V⁻¹ *ᵥ b) n) t) := by
    rw [taylorODESolution_eq_diag A V D hA hV1 hV2 hd b x_in t]
    congr 1
    funext n
    simp only [neg_mul]
    rfl
  rw [heq]
  have hcoord := taylor_stateVector_norm_affine
    (fun n => duhamelCoord (D n n) ((V⁻¹ *ᵥ x_in) n) ((V⁻¹ *ᵥ b) n) t)
    (V⁻¹ *ᵥ x_in) (V⁻¹ *ᵥ b) t ht
    (fun n => duhamelCoord_norm_le _ _ _ (hre n) t ht)
  calc ‖stateVector (V *ᵥ _)‖ ≤ ‖V‖ * ‖stateVector _‖ := stateVector_mulVec_norm_le _ _
    _ ≤ ‖V‖ * (‖stateVector (V⁻¹ *ᵥ x_in)‖ + t * ‖stateVector (V⁻¹ *ᵥ b)‖) := by
        gcongr
    _ ≤ ‖V‖ * (‖V⁻¹‖ * ‖stateVector x_in‖ + t * (‖V⁻¹‖ * ‖stateVector b‖)) := by
        gcongr
        · exact stateVector_mulVec_norm_le _ _
        · exact stateVector_mulVec_norm_le _ _
    _ = _ := by ring

/-- The stated terminal accuracy condition and nonzero final solution imply `70*m ≤ (k+1)!`. -/
theorem taylorV2_factorial_of_accuracy (m k : ℕ) (A V D : Matrix N N ℂ)
    (h : ℝ) (x_in b : QState N) (hh : 0 < h)
    (hA : A = V * D * V⁻¹) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (hre : ∀ n, (D n n).re ≤ 0)
    (hq : 0 < ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖)
    (hacc : 70 * (‖V‖ * ‖V⁻¹‖) * (m : ℝ) *
        (‖stateVector x_in‖ + (m : ℝ) * h * ‖stateVector b‖) ≤
      (Nat.factorial (k + 1) : ℝ) * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖) :
    70 * m ≤ Nat.factorial (k + 1) := by
  have hgrowth := taylorODESolution_norm_le_diagonalizable A V D hA hV1 hV2 hd hre
    b x_in ((m : ℝ) * h) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hgrowth (by positivity : 0 ≤ 70 * (m : ℝ))
  have hreal : (70 : ℝ) * m ≤ (Nat.factorial (k + 1) : ℝ) := by
    nlinarith
  exact_mod_cast hreal

/-- Under the stated terminal accuracy and stability assumptions, the time-block error at `j ≤
m` is at most `j/(25*m)` times the final exact-solution norm. -/
theorem taylorV2_error_of_accuracy (m k p : ℕ) (A V D : Matrix N N ℂ)
    (h : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hm : 0 < m) (hk : 5 ≤ k) (hp : 0 < p) (hh : 0 < h)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (hA : A = V * D * V⁻¹)
    (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1) (hre : ∀ n, (D n n).re ≤ 0)
    (hM : ‖h • A‖ ≤ 1)
    (hq : 0 < ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖)
    (hacc : 70 * (‖V‖ * ‖V⁻¹‖) * (m : ℝ) *
        (‖stateVector x_in‖ + (m : ℝ) * h * ‖stateVector b‖) ≤
      (Nat.factorial (k + 1) : ℝ) * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖)
    (hx : taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b)
    (j : ℕ) (hj : j ≤ m) :
    ‖stateVector (taylorODESolution A b x_in ((j : ℝ) * h)) -
      stateVector (taylorBlock x (taylorTimeLabel m k p j hj))‖ ≤
        ((j : ℝ) / (25 * m)) * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖ := by
  have hfac70 := taylorV2_factorial_of_accuracy m k A V D h x_in b hh hA hV1 hV2 hd hre hq hacc
  have hfac : 2 * m ≤ Nat.factorial (k + 1) := by omega
  have herr := theorem6V2 N m k p A V D h x_in b x hm hk hp hfac hh hd hA hV1 hV2 hre hM hx j hj
  refine herr.trans ?_
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hF : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
  rw [div_le_iff₀ hF]
  have hscaled := mul_le_mul_of_nonneg_left hacc (by positivity : 0 ≤ (j : ℝ) / (25 * m))
  convert! hscaled using 1
  · field_simp
    ring
  · field_simp

/-- Under the stated terminal accuracy and stability assumptions, the normalized terminal time
block is within `1 / 12` of the normalized final exact solution. -/
theorem taylorV2_terminal_direction (m k p : ℕ) (A V D : Matrix N N ℂ)
    (h : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hm : 0 < m) (hk : 5 ≤ k) (hp : 0 < p) (hh : 0 < h)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (hA : A = V * D * V⁻¹)
    (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1) (hre : ∀ n, (D n n).re ≤ 0)
    (hM : ‖h • A‖ ≤ 1)
    (hq : 0 < ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖)
    (hacc : 70 * (‖V‖ * ‖V⁻¹‖) * (m : ℝ) *
        (‖stateVector x_in‖ + (m : ℝ) * h * ‖stateVector b‖) ≤
      (Nat.factorial (k + 1) : ℝ) * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖)
    (hx : taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b)
 :
    ‖NormedSpace.normalize (stateVector (taylorBlock x (taylorTimeLabel m k p m (by omega)))) -
      NormedSpace.normalize (stateVector (taylorODESolution A b x_in ((m : ℝ) * h)))‖ ≤
        (1 / 12 : ℝ) := by
  let q := ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖
  have herr :=
      taylorV2_error_of_accuracy m k p A V D h x_in b x hm hk hp hh hd hA hV1 hV2 hre hM hq hacc hx m (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : ((m : ℝ) / (25 * m)) * q = q / 25 := by field_simp
  have hclose : ‖stateVector (taylorBlock x (taylorTimeLabel m k p m (by omega))) -
      stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖ ≤ q / 25 := by
    rw [norm_sub_rev]
    exact herr.trans_eq heq
  obtain ⟨_, hnorm⟩ := normalize_error_of_gap hclose (by change q / 25 < q; linarith)
  calc ‖NormedSpace.normalize (stateVector (taylorBlock x (taylorTimeLabel m k p m (by omega)))) -
        NormedSpace.normalize (stateVector (taylorODESolution A b x_in ((m : ℝ) * h)))‖
      ≤ 2 * (q / 25) / q := hnorm
    _ = 2 / 25 := by dsimp [q]; field_simp
    _ ≤ 1 / 12 := by norm_num

/-- Every positive-order Taylor block is the factorial-scaled power `M^(i-1)` applied to the
first-order block. -/
theorem taylorV2_positiveBlockClosed (m k p : ℕ) (M : Matrix N N ℂ)
    (h : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (hk : 1 ≤ k) (a : ℕ) (ha : a < m) :
    ∀ (i : ℕ) (_hi : 1 ≤ i) (hik : i ≤ k),
      taylorBlock x ⟨a * (k + 1) + i, step_label_lt a m k p i ha hik⟩ =
        (Nat.factorial i : ℂ)⁻¹ • (M ^ (i - 1) *ᵥ
          taylorBlock x ⟨a * (k + 1) + 1, step_label_lt a m k p 1 ha hk⟩) := by
  intro i
  induction i with
  | zero => intro hi _; omega
  | succ i ih =>
    intro hi hik
    by_cases hi0 : i = 0
    · subst i
      simp
    have hstep := taylorV2_block_step m k p M h x_in b x hx a (i + 1) ha (by omega) hik
    have hprev : (⟨a * (k + 1) + (i + 1) - 1,
        pred_label_lt a m k p (i + 1) ha hik (by omega)⟩ : Fin (m * (k + 1) + p + 1)) =
        ⟨a * (k + 1) + i, step_label_lt a m k p i ha (by omega)⟩ := by
      apply Fin.ext
      show a * (k + 1) + (i + 1) - 1 = a * (k + 1) + i
      omega
    rw [hprev, ih (by omega) (by omega), if_neg (by omega : i + 1 ≠ 1), add_zero,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hstep
    have hpow : M * M ^ (i - 1) = M ^ i := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hstep, hpow, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv]
    simp only [Nat.add_sub_cancel]

/-- For `‖M‖ ≤ 1`, the norm of the positive-order block `i` is at most `1/i!` times the
first-order block norm. -/
theorem taylorV2_positiveBlock_norm_le (m k p : ℕ) (M : Matrix N N ℂ)
    (h : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (hM : ‖M‖ ≤ 1) (hk : 1 ≤ k) (a : ℕ) (ha : a < m)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    ‖stateVector (taylorBlock x ⟨a * (k + 1) + i, step_label_lt a m k p i ha hik⟩)‖ ≤
      (Nat.factorial i : ℝ)⁻¹ *
        ‖stateVector (taylorBlock x ⟨a * (k + 1) + 1, step_label_lt a m k p 1 ha hk⟩)‖ := by
  rw [taylorV2_positiveBlockClosed m k p M h x_in b x hx hk a ha i hi hik]
  change ‖(Nat.factorial i : ℂ)⁻¹ • stateVector (M ^ (i - 1) *ᵥ _)‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hall : ∀ q : ℕ, ‖M ^ q‖ ≤ 1 := by
    intro q
    induction q with
    | zero =>
      rw [pow_zero, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (fun _ => by simp)
    | succ q ih =>
      rw [pow_succ]
      exact (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_one₀ ih (norm_nonneg M) hM)
  have hpow : ‖M ^ (i - 1)‖ ≤ 1 := hall (i - 1)
  exact (stateVector_mulVec_norm_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hpow)

/-- The stated total-mass and final-block lower bounds imply `X / sqrt (p + 77*m*g²) ≤ Y`. -/
theorem taylorV2_mass_arithmetic (m p : ℕ) (g q X Y : ℝ)
    (hm : 0 < m) (hg : 1 ≤ g) (hq : 0 < q) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hfinal : (24 / 25 : ℝ) * q ≤ Y)
    (hmass : X ^ 2 ≤ ((p : ℝ) + 1) * Y ^ 2 + 70 * m * g ^ 2 * q ^ 2) :
    1 / Real.sqrt ((p : ℝ) + 77 * m * g ^ 2) * X ≤ Y := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hg2 : (1 : ℝ) ≤ g ^ 2 := by nlinarith
  have hmg : (1 : ℝ) ≤ (m : ℝ) * g ^ 2 := by nlinarith
  have h70 : 70 * q ^ 2 ≤ 76 * Y ^ 2 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left h70
    (by positivity : 0 ≤ (m : ℝ) * g ^ 2)
  have hcopy := mul_le_mul_of_nonneg_right hmg (sq_nonneg Y)
  have htotal : X ^ 2 ≤ ((p : ℝ) + 77 * m * g ^ 2) * Y ^ 2 := by nlinarith
  have hD : 0 < (p : ℝ) + 77 * m * g ^ 2 := by positivity
  have hroot := Real.sq_sqrt hD.le
  have hrootpos := Real.sqrt_pos.mpr hD
  have hprod : 0 ≤ Real.sqrt ((p : ℝ) + 77 * m * g ^ 2) * Y := by positivity
  have hs : X ^ 2 ≤ (Real.sqrt ((p : ℝ) + 77 * m * g ^ 2) * Y) ^ 2 := by
    rw [mul_pow, hroot]
    exact htotal
  rw [one_div, inv_mul_le_iff₀ hrootpos]
  nlinarith

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
