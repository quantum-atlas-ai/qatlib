/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# `HeatEquation20.MainResults` — source model

Fixed paper: N. Linden, A. Montanaro, C. Shao, *Quantum vs. classical
algorithms for solving the heat equation*, arXiv:2004.06516v2 (18 June 2020),
27 pp.

This file fixes the objects used by every claim of the paper layer:

* the grid `G = (Z/n)^d` and its shift maps `x ↦ x ± e_i` (Section I A, p. 5);
* the FTCS one-step operator `L` of equation (13), p. 6, in the normalised
  form `Δt = Δx²/(2dα)`;
* the ℓ₂ and ℓ∞ norms on grid vectors;
* the circulant matrix `H` of (A3), p. 27, the Fourier modes of the QFT, and
  the eigenvalues `λ_j = -4 sin²(jπ/n)` of (A4);
* the coefficient matrix `A` of the linear system (38), p. 10 / (B1), p. 28;
* the tridiagonal matrices of Lemma 26 (B20), p. 30 and of (B3)/(B19).

Only definitions and the elementary norm analysis shared by several claims are
put here; each claim has its own file with the theorem statement and the
proof attempt.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators
open Matrix

/-- The spatial grid `G = (Z/n)^d` of the paper (Section I A, p. 5): a
`d`-tuple of positions modulo `n`. -/
abbrev Grid (d n : ℕ) := Fin d → Fin n

/-- The grid point `x` with coordinate `i` increased by one (mod `n`), i.e.
`x + e_i`.  The cyclic increment is `finRotate`, so it is a permutation. -/
def shiftUp {d n : ℕ} [NeZero n] (i : Fin d) (x : Grid d n) : Grid d n :=
  Function.update x i (finRotate n (x i))

/-- The grid point `x` with coordinate `i` decreased by one (mod `n`), i.e.
`x - e_i`; the inverse permutation of `shiftUp i`. -/
def shiftDown {d n : ℕ} [NeZero n] (i : Fin d) (x : Grid d n) : Grid d n :=
  Function.update x i ((finRotate n).symm (x i))

/-- The squared `ℓ₂` norm of a grid vector, `Σ_x u(x)²`. -/
def l2Sq {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ := ∑ x, f x ^ 2

/-- The squared `ℓ₂` norm of the zero vector vanishes. -/
@[simp] lemma l2Sq_zero {ι : Type*} [Fintype ι] : l2Sq (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l2Sq]

/-- The squared `ℓ₂` norm is nonnegative. -/
lemma l2Sq_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) : 0 ≤ l2Sq f := by
  unfold l2Sq
  exact Finset.sum_nonneg fun x _ => sq_nonneg _

/-! ## The FTCS operator (13), p. 6

`ũ(x, t+Δt) = (1 - 2dαΔt/Δx²) ũ(x,t) + (αΔt/Δx²) Σ_i (ũ(x+e_i,t) + ũ(x-e_i,t))`.

The parameter `η` below is `α Δt / Δx²`. -/

/-- The FTCS one-step operator of (13), p. 6, with `η = α Δt / Δx²`. -/
def ftcsStep {d n : ℕ} [NeZero n] (η : ℝ) (u : Grid d n → ℝ) : Grid d n → ℝ :=
  fun x => (1 - 2 * (d : ℝ) * η) * u x
    + η * ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x))

/-- The random-walk step `L` of (13) at the Corollary 2 value
`Δt = Δx²/(2dα)`: the uniform average of the `2d` neighbour shifts. -/
def heatStep {d n : ℕ} [NeZero n] (u : Grid d n → ℝ) : Grid d n → ℝ :=
  fun x => (2 * (d : ℝ))⁻¹ * ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x))

/-- At `Δt = Δx²/(2dα)` the FTCS operator (13) is the random-walk operator. -/
lemma heatStep_eq_ftcsStep_inv {d n : ℕ} [NeZero n] (hd : 0 < d) (u : Grid d n → ℝ) :
    heatStep u = ftcsStep ((2 * (d : ℝ))⁻¹) u := by
  funext x
  unfold heatStep ftcsStep
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcoef : (1 : ℝ) - 2 * (d : ℝ) * (2 * (d : ℝ))⁻¹ = 0 := by
    rw [mul_inv_cancel₀ (by positivity : (2 * (d : ℝ)) ≠ 0)]
    norm_num
  rw [hcoef, zero_mul, zero_add]

/-- Nonnegativity of the random-walk step on nonnegative vectors. -/
lemma heatStep_nonneg {d n : ℕ} [NeZero n] (hd : 0 < d) {u : Grid d n → ℝ}
    (hu : ∀ x, 0 ≤ u x) (x : Grid d n) : 0 ≤ heatStep u x := by
  unfold heatStep
  refine mul_nonneg (by positivity) ?_
  exact Finset.sum_nonneg fun i _ => add_nonneg (hu _) (hu _)

/-- The FTCS operator with `0 ≤ η` and `2dη ≤ 1` is row-stochastic; hence it
does not increase the `ℓ∞` norm.  This is the stochasticity argument of (14),
p. 6. -/
lemma ftcsStep_linfty_le {d n : ℕ} [NeZero n] (hd : 0 < d) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : 2 * (d : ℝ) * η ≤ 1) (u : Grid d n → ℝ) :
    ‖ftcsStep η u‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  have hcoef : 0 ≤ 1 - 2 * (d : ℝ) * η := by linarith
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : |u x| ≤ ‖u‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm u x
  have hsum : |∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x))|
      ≤ (d : ℝ) * (2 * ‖u‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin d, |u (shiftUp i x) + u (shiftDown i x)|
        ≤ ∑ i : Fin d, (‖u‖ + ‖u‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc |u (shiftUp i x) + u (shiftDown i x)|
              = ‖u (shiftUp i x) + u (shiftDown i x)‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖u (shiftUp i x)‖ + ‖u (shiftDown i x)‖ := norm_add_le _ _
            _ ≤ ‖u‖ + ‖u‖ :=
              add_le_add (norm_le_pi_norm _ _) (norm_le_pi_norm _ _)
      _ = (d : ℝ) * (2 * ‖u‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc ‖ftcsStep η u x‖
      = |ftcsStep η u x| := Real.norm_eq_abs _
    _ = |(1 - 2 * (d : ℝ) * η) * u x
          + η * ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x))| := by
        simp only [ftcsStep]
    _ ≤ |(1 - 2 * (d : ℝ) * η) * u x|
          + |η * ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x))| := abs_add_le _ _
    _ ≤ (1 - 2 * (d : ℝ) * η) * ‖u‖ + η * ((d : ℝ) * (2 * ‖u‖)) := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_nonneg hcoef]
          exact mul_le_mul_of_nonneg_left h1 hcoef
        · rw [abs_mul, abs_of_nonneg hη0]
          exact mul_le_mul_of_nonneg_left hsum hη0
    _ = ‖u‖ := by ring

/-- The random-walk step does not increase the `ℓ∞` norm. -/
lemma heatStep_linfty_le {d n : ℕ} [NeZero n] (hd : 0 < d) (u : Grid d n → ℝ) :
    ‖heatStep u‖ ≤ ‖u‖ := by
  rw [heatStep_eq_ftcsStep_inv hd]
  refine ftcsStep_linfty_le hd ((2 * (d : ℝ))⁻¹) (by positivity) ?_ u
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [mul_inv_cancel₀ (by positivity : (2 * (d : ℝ)) ≠ 0)]

/-- The FTCS operator is linear in the vector, for fixed `η`. -/
def ftcsStepLM {d n : ℕ} [NeZero n] (η : ℝ) :
    (Grid d n → ℝ) →ₗ[ℝ] (Grid d n → ℝ) where
  toFun := ftcsStep η
  map_add' a b := by
    funext x
    unfold ftcsStep
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    funext x
    unfold ftcsStep
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hsum : ∑ i : Fin d, (c * a (shiftUp i x) + c * a (shiftDown i x))
        = c * ∑ i : Fin d, (a (shiftUp i x) + a (shiftDown i x)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    ring

/-- The linear map underlying the FTCS step acts as `ftcsStep`. -/
@[simp] lemma ftcsStepLM_apply {d n : ℕ} [NeZero n] (η : ℝ) (u : Grid d n → ℝ) :
    ftcsStepLM η u = ftcsStep η u := rfl

/-! ## The error-accumulation argument of Theorem 1 (p. 6) -/

/-- If a linear step does not increase the `ℓ∞` norm and each exact step
differs from the linear step by at most `η`, then after `m` steps the error is
at most `m η`.  This is the induction (18)–(21), p. 6. -/
theorem error_accumulation {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hT : ∀ v, ‖T v‖ ≤ ‖v‖)
    (u w : ℕ → ι → ℝ) (h0 : w 0 = u 0) (hstep : ∀ k, w (k + 1) = T (w k))
    (η : ℝ) (hη : ∀ k, ‖u (k + 1) - T (u k)‖ ≤ η) (m : ℕ) :
    ‖w m - u m‖ ≤ (m : ℝ) * η := by
  induction m with
  | zero => simp [h0]
  | succ k ih =>
      have hdiff : w (k + 1) - u (k + 1)
          = T (w k) - T (u k) + (T (u k) - u (k + 1)) := by
        rw [hstep k]; abel
      calc ‖w (k + 1) - u (k + 1)‖
          = ‖T (w k) - T (u k) + (T (u k) - u (k + 1))‖ := by rw [hdiff]
        _ ≤ ‖T (w k) - T (u k)‖ + ‖T (u k) - u (k + 1)‖ := norm_add_le _ _
        _ = ‖T (w k - u k)‖ + ‖T (u k) - u (k + 1)‖ := by rw [map_sub]
        _ ≤ ‖w k - u k‖ + η := by
            refine add_le_add (hT _) ?_
            rw [norm_sub_rev]
            exact hη k
        _ ≤ (k : ℝ) * η + η := by linarith
        _ = ((k + 1 : ℕ) : ℝ) * η := by push_cast; ring

/-! ## The circulant matrix `H` of (A3), p. 27, and the eigenvalues (A4) -/

/-- The `n × n` circulant matrix `H` of (A3), p. 27: `-2` on the diagonal and
`1` on the two cyclic neighbours. -/
def pathCirc (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then -2 else if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The eigenvalue `λ_j = -4 sin²(jπ/n)` of `H`, equation (A4), p. 27. -/
def pathEigen (n j : ℕ) : ℝ := -4 * Real.sin ((j : ℝ) * Real.pi / (n : ℝ)) ^ 2

/-- The generalised matrix `A` of (A2), p. 26 acting on grid vectors:
`(Au)(x) = Σ_i (u(x+e_i) + u(x-e_i) - 2u(x))`. -/
def heatGenOp {d n : ℕ} [NeZero n] (u : Grid d n → ℝ) : Grid d n → ℝ :=
  fun x => ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x) - 2 * u x)

/-- Complexification of `heatGenOp`, used to state the Fourier-eigenvector
claim of Lemma 23. -/
def heatGenOpC {d n : ℕ} [NeZero n] (u : Grid d n → ℂ) : Grid d n → ℂ :=
  fun x => ∑ i : Fin d, (u (shiftUp i x) + u (shiftDown i x) - 2 * u x)

/-- The tensor-product Fourier mode `j ↦ (x ↦ ∏_i exp(2πi x_i j_i / n))` of
the QFT that diagonalises `A` (Lemma 23, p. 27). -/
def fourierMode {d n : ℕ} (j : Grid d n) (x : Grid d n) : ℂ :=
  ∏ i : Fin d,
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x i).val : ℂ) * ((j i).val : ℂ)
      / ((n : ℕ) : ℂ))

/-- The matrix of `A` in the standard basis of the grid. -/
def heatGenMat {d n : ℕ} [NeZero n] : Matrix (Grid d n) (Grid d n) ℝ :=
  fun x y => ∑ i : Fin d,
    ((if x = shiftUp i y then 1 else 0) + (if x = shiftDown i y then 1 else 0)
      - (if x = y then 2 else 0))

/-! ## The coefficient matrix `A` of the linear system (38), p. 10 / (B1) -/

/-- The kernel of `L` on the grid: `L_{xy} = (2d)⁻¹ · #{i : y = x ± e_i}`. -/
def heatStepKernel {d n : ℕ} [NeZero n] (x y : Grid d n) : ℝ :=
  (2 * (d : ℝ))⁻¹ * ∑ i : Fin d,
    ((if x = shiftUp i y then 1 else 0) + (if x = shiftDown i y then 1 else 0))

/-- The coefficient matrix `A` of the linear system (38), p. 10, with block
rows indexed by time `Fin m` and block columns by the grid.  The diagonal
blocks are `I`; the block one row below the diagonal is `-L`. -/
def systemMatrix (m d n : ℕ) [NeZero n] :
    Matrix (Fin m × Grid d n) (Fin m × Grid d n) ℝ :=
  fun p q =>
    (if p.1.val = q.1.val ∧ p.2 = q.2 then 1 else 0)
      - (if p.1.val = q.1.val + 1 then heatStepKernel p.2 q.2 else 0)

/-! ## Spectral vocabulary -/

/-- `σ ≥ 0` is a singular value of `A` when `σ²` is an eigenvalue of `AᵀA`. -/
def IsSingularValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (σ : ℝ) : Prop :=
  0 ≤ σ ∧ ∃ v : ι → ℝ, v ≠ 0 ∧ (Aᵀ * A) *ᵥ v = (σ ^ 2) • v

/-- `λ` is an eigenvalue of the real matrix `A`. -/
def IsEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lam : ℝ) : Prop :=
  ∃ v : ι → ℝ, v ≠ 0 ∧ A *ᵥ v = lam • v

/-- `v` is an eigenvector of the complex matrix `A` with eigenvalue `λ`. -/
def IsEigenvectorC {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (lam : ℂ) (v : ι → ℂ) : Prop :=
  v ≠ 0 ∧ A *ᵥ v = lam • v

/-! ## The tridiagonal matrices of Appendix B -/

/-- The `m × m` sub-diagonal shift `S` with `S_{i,j} = 1` iff `i = j+1`. -/
def lowerShift (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i.val = j.val + 1 then 1 else 0

/-- The `m × m` matrix `T` of (B3), p. 28: identity minus the sub-diagonal
shift, i.e. `1` on the diagonal and `-1` below it. -/
def bidiagT (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - lowerShift m

/-- The block-mode matrix `A_j = (1-γ) T + γ I` of (B7), p. 29, and its
multi-dimensional version (B16), p. 30. -/
def blockMode (m : ℕ) (γ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 - γ) • bidiagT m + γ • (1 : Matrix (Fin m) (Fin m) ℝ)

/-- The tridiagonal matrix `f_m` of (B20), p. 30: `λ` on the diagonal and `1`
on the two off-diagonals. -/
def tridiagDet (m : ℕ) (lam : ℝ) : ℝ :=
  (Matrix.of fun i j : Fin m =>
    if i = j then lam else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0).det

/-- The `m × m` matrix `Q_j` of (B19), p. 30: `q` in the top-left corner,
`0` on the remaining diagonal, `1` on the two off-diagonals (including the
`(0,m-1)`/`(m-1,0)` corners). -/
def qMatrix (m : ℕ) (q : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i = j then (if i.val = 0 then q else 0)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val
        ∨ (i.val = 0 ∧ j.val + 1 = m) ∨ (j.val = 0 ∧ i.val + 1 = m) then 1 else 0

/-- The one-dimensional random-walk matrix used for the return probability
`⟨0|L^{2τ}|0⟩` of Appendix D. -/
def heatStepMat1 (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℝ :=
  fun x y => (2 : ℝ)⁻¹ *
    ((if x = y + 1 then 1 else 0) + (if x = y - 1 then 1 else 0))

/-- The return probability `⟨0|L^{2τ}|0⟩ = (L^{2τ})_{00}` of Appendix D. -/
def returnProb (n τ : ℕ) [NeZero n] : ℝ := (heatStepMat1 n ^ (2 * τ)) 0 0

end Qatlib.Papers.HeatEquation20.MainResults
