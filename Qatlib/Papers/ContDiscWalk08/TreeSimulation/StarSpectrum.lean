/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs

/-!
# Eigenvector formulas for weighted stars

The matrix `starMatrix` describes a weighted star with center indexed by `none` and leaves
indexed by `some i`. The module computes its action on the center and leaf directions and proves
the eigenvector equations with eigenvalues given by the positive and negative Euclidean weight
norm, supporting the star analysis of [Childs2010].

## Main statements

* `starMatrix_isHermitian`: the weighted star matrix is Hermitian.
* `starMatrix_mulVec_eigPlus` and `starMatrix_mulVec_eigMinus`: the two explicit eigenvector
  equations when the total weight is nonzero.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.TreeSimulation

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

/-- A sum over `Option (Fin k)` splits into the value at `none` and the sum over the `some`
values. -/
theorem sum_option_eq (k : ℕ) (f : Option (Fin k) → ℂ) :
    (∑ o, f o) = f none + ∑ i : Fin k, f (some i) := by
  rw [univ_option, Finset.sum_insertNone]

/-- Defines the weighted star matrix with center-to-leaf entries given by conjugated weights and
leaf-to-center entries by the weights. -/
def starMatrix (k : ℕ) (w : Fin k → ℂ) : Matrix (Option (Fin k)) (Option (Fin k)) ℂ :=
  fun p q =>
    match p, q with
    | none, none => 0
    | none, some i => (starRingEnd ℂ) (w i)
    | some i, none => w i
    | some _i, some _j => 0

/-- The weighted star matrix is Hermitian. -/
theorem starMatrix_isHermitian (k : ℕ) (w : Fin k → ℂ) :
    (starMatrix k w).IsHermitian := by
  ext p q
  cases p <;> cases q <;> simp [starMatrix, Matrix.conjTranspose_apply]

/-- Defines the basis state supported at the star center. -/
def starCenter (k : ℕ) : QState (Option (Fin k)) := Ket none

/-- Defines the vector with zero center amplitude and leaf amplitudes `w i`. -/
def starLeafVec (k : ℕ) (w : Fin k → ℂ) : QState (Option (Fin k)) :=
  fun p => match p with
    | none => 0
    | some i => w i

/-- The center coordinate of the star matrix acting on a state is the sum of its leaf
coordinates weighted by the conjugated edge weights. -/
theorem starMatrix_mulVec_none (k : ℕ) (w : Fin k → ℂ)
    (φ : QState (Option (Fin k))) :
    (starMatrix k w *ᵥ φ) none = ∑ i : Fin k, (starRingEnd ℂ) (w i) * φ (some i) := by
  rw [Matrix.mulVec, dotProduct, sum_option_eq]
  simp [starMatrix]

/-- The leaf coordinate `j` of the star matrix acting on a state is `w j` times its center
coordinate. -/
theorem starMatrix_mulVec_some (k : ℕ) (w : Fin k → ℂ)
    (φ : QState (Option (Fin k))) (j : Fin k) :
    (starMatrix k w *ᵥ φ) (some j) = w j * φ none := by
  rw [Matrix.mulVec, dotProduct, sum_option_eq]
  simp [starMatrix]

/-- The star matrix maps the center basis state to the vector of leaf weights. -/
theorem starMatrix_mulVec_center (k : ℕ) (w : Fin k → ℂ) :
    starMatrix k w *ᵥ starCenter k
      = fun p => match p with
        | none => 0
        | some i => w i := by
  funext p
  cases p with
  | none =>
    rw [starMatrix_mulVec_none]
    simp [starCenter, Ket]
  | some j =>
    rw [starMatrix_mulVec_some]
    simp [starCenter, Ket]

/-- The star matrix maps the leaf-weight vector to a center-supported vector with amplitude
equal to the sum of squared weight norms. -/
theorem starMatrix_mulVec_leaf (k : ℕ) (w : Fin k → ℂ) :
    starMatrix k w *ᵥ starLeafVec k w
      = fun p => match p with
        | none => ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ)
        | some _ => 0 := by
  funext p
  cases p with
  | none =>
    rw [starMatrix_mulVec_none]
    have hterm : ∀ i : Fin k, (starRingEnd ℂ) (w i) * starLeafVec k w (some i)
        = ((‖w i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      simp only [starLeafVec]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Complex.ofReal_sum]
  | some j =>
    rw [starMatrix_mulVec_some]
    simp [starLeafVec]

/-- Defines the Euclidean norm of the vector of star edge weights. -/
def starWeight (k : ℕ) (w : Fin k → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin k, ‖w i‖ ^ 2)

/-- The square of the star weight equals the sum of squared edge-weight norms. -/
theorem starWeight_sq (k : ℕ) (w : Fin k → ℂ) :
    starWeight k w ^ 2 = ∑ i : Fin k, ‖w i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _i _ => sq_nonneg _))

/-- Over the complex numbers, the star weight multiplied by itself equals the coercion of the
sum of squared edge-weight norms. -/
theorem starWeight_sq_complex (k : ℕ) (w : Fin k → ℂ) :
    ((starWeight k w : ℝ) : ℂ) * ((starWeight k w : ℝ) : ℂ)
      = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  have h := starWeight_sq k w
  have : ((starWeight k w : ℝ) : ℂ) * ((starWeight k w : ℝ) : ℂ)
      = (((starWeight k w) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, h]

/-- If one edge weight is nonzero, the star weight is strictly positive. -/
theorem starWeight_pos (k : ℕ) (w : Fin k → ℂ) (i : Fin k) (hi : w i ≠ 0) :
    0 < starWeight k w := by
  unfold starWeight
  apply Real.sqrt_pos.mpr
  have hterm : 0 < ‖w i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  have hle : ‖w i‖ ^ 2 ≤ ∑ j : Fin k, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin k => ‖w j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- Defines the complex coercion of the real scalar `1 / √2`. -/
def invSqrtTwoC : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- Defines a vector with center amplitude `c` and leaf amplitudes `c * lam⁻¹ * w i`. -/
def starEigenvector (k : ℕ) (w : Fin k → ℂ) (lam c : ℂ) :
    QState (Option (Fin k)) :=
  fun p => match p with
    | none => c
    | some i => c * lam⁻¹ * w i

/-- If nonzero `lam` squares to the sum of squared edge-weight norms, `starEigenvector k w lam
c` satisfies the star matrix eigenvector equation with scalar `lam`. -/
theorem starMatrix_mulVec_eigenvector (k : ℕ) (w : Fin k → ℂ) (lam c : ℂ)
    (hlam_sq : lam * lam = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ)) (hlam0 : lam ≠ 0) :
    starMatrix k w *ᵥ starEigenvector k w lam c
      = lam • starEigenvector k w lam c := by
  funext p
  cases p with
  | none =>
    rw [starMatrix_mulVec_none]
    have hterm : ∀ i : Fin k,
        (starRingEnd ℂ) (w i) * starEigenvector k w lam c (some i)
          = (c * lam⁻¹) * ((starRingEnd ℂ) (w i) * w i) := by
      intro i
      simp only [starEigenvector]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    have hsum : (∑ i : Fin k, (starRingEnd ℂ) (w i) * w i)
        = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [hsum, ← hlam_sq]
    simp only [starEigenvector, Pi.smul_apply, smul_eq_mul]
    rw [show (c * lam⁻¹) * (lam * lam) = lam * c from by
      rw [show (c * lam⁻¹) * (lam * lam) = c * (lam⁻¹ * (lam * lam)) from by ring]
      rw [show lam⁻¹ * (lam * lam) = (lam⁻¹ * lam) * lam from by ring,
        inv_mul_cancel₀ hlam0, one_mul]
      ring]
  | some j =>
    rw [starMatrix_mulVec_some]
    simp only [starEigenvector, Pi.smul_apply, smul_eq_mul]
    rw [show w j * c = lam * (c * lam⁻¹ * w j) from by
      rw [show lam * (c * lam⁻¹ * w j) = c * (lam * lam⁻¹) * w j from by ring,
        mul_inv_cancel₀ hlam0, mul_one]
      ring]

/-- Defines the star vector using positive star weight as eigenvalue parameter and center
amplitude `1 / √2`. -/
def eigPlus (k : ℕ) (w : Fin k → ℂ) : QState (Option (Fin k)) :=
  starEigenvector k w ((starWeight k w : ℝ) : ℂ) invSqrtTwoC

/-- Defines the star vector using negative star weight as eigenvalue parameter and center
amplitude `1 / √2`. -/
def eigMinus (k : ℕ) (w : Fin k → ℂ) : QState (Option (Fin k)) :=
  starEigenvector k w (-((starWeight k w : ℝ) : ℂ)) invSqrtTwoC

/-- For nonzero star weight, `eigPlus k w` satisfies the star matrix eigenvector equation with
eigenvalue `starWeight k w`. See the star spectral calculation in [Childs2010]. -/
theorem starMatrix_mulVec_eigPlus (k : ℕ) (w : Fin k → ℂ)
    (hS : starWeight k w ≠ 0) :
    starMatrix k w *ᵥ eigPlus k w = ((starWeight k w : ℝ) : ℂ) • eigPlus k w :=
  starMatrix_mulVec_eigenvector k w ((starWeight k w : ℝ) : ℂ) invSqrtTwoC
    (starWeight_sq_complex k w) (by exact_mod_cast hS)

/-- For nonzero star weight, `eigMinus k w` satisfies the star matrix eigenvector equation with
eigenvalue `-starWeight k w`. See the star spectral calculation in [Childs2010]. -/
theorem starMatrix_mulVec_eigMinus (k : ℕ) (w : Fin k → ℂ)
    (hS : starWeight k w ≠ 0) :
    starMatrix k w *ᵥ eigMinus k w = (-((starWeight k w : ℝ) : ℂ)) • eigMinus k w := by
  have hcast : -((starWeight k w : ℝ) : ℂ) = ((-(starWeight k w) : ℝ) : ℂ) := by push_cast; ring
  have hsq : (-((starWeight k w : ℝ) : ℂ)) * (-((starWeight k w : ℝ) : ℂ))
      = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast, ← starWeight_sq_complex k w]
    push_cast
    ring
  have hne : -((starWeight k w : ℝ) : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast hS)
  exact starMatrix_mulVec_eigenvector k w (-((starWeight k w : ℝ) : ℂ)) invSqrtTwoC hsq hne

/-- Identifies the two displayed complex coercions of the positive star weight. -/
theorem eigPlus_eigenvalue (k : ℕ) (w : Fin k → ℂ) :
    ((starWeight k w : ℝ) : ℂ) = (starWeight k w : ℂ) := rfl

end Qatlib.Papers.ContDiscWalk08.TreeSimulation
