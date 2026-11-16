/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.SpectralForms.CauchyKernel.FullSpaceCauchy
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceComparison
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpacePositivity

@[expose] public section


/-! # The actual sech damping is a positive unital Schur map

The normalized sech kernel is a positive diagonal rescaling of a finite
Cauchy kernel. This proves positivity for repeated frequency labels and
all complex vectors. The exact source frequency-damping identity then
identifies the actual full damped parent with this positive map.

This is a finite Schur-kernel argument. It does not assert a formalized
Fourier integral or identify an auxiliary integral as physical time.
-/

open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Foundations.PureStateMath


open Qatlib.Foundations.SpectralForms.CauchyKernel

namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {κ : Type*} [Fintype κ]

/-- Full Sech cauchy for the stated finite source data. -/
theorem fullSech_cauchy (s t : ℝ) :
    1 / Real.cosh (s - t) =
      2 * Real.exp s * Real.exp t / (Real.exp (2 * s) + Real.exp (2 * t)) := by
  have h₁ : Real.exp (s - t) * Real.exp s * Real.exp t = Real.exp (2 * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (-(s - t)) * Real.exp s * Real.exp t = Real.exp (2 * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hm : 2 * Real.exp s * Real.exp t * Real.cosh (s - t) =
      Real.exp (2 * s) + Real.exp (2 * t) := by
    rw [Real.cosh_eq]
    linear_combination h₁ + h₂
  apply (div_eq_div_iff (ne_of_gt (Real.cosh_pos (s - t)))
    (ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _)))).2
  simpa only [one_mul] using hm.symm

noncomputable def fullSechKernel (β : ℝ) (ν : κ → ℝ) : Matrix κ κ ℂ :=
  fun i j => ((1 / Real.cosh (β * (ν i - ν j) / 4) : ℝ) : ℂ)

/-- A normalized positive kernel for every real beta and every finite
frequency list. No injectivity condition is needed. -/
theorem fullSechKernel_posSemidef (β : ℝ) (ν : κ → ℝ) :
    (fullSechKernel β ν).PosSemidef := by
  let v : κ → ℂ := fun i => (Real.exp (β * ν i / 4) : ℂ)
  have hr : ((2 : ℂ) • Matrix.vecMulVec v (star v)).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star v).smul (by norm_num)
  have hc := fullCauchyKernel_posSemidef (fun i => Real.exp (β * ν i / 2))
    (fun i => Real.exp_pos (β * ν i / 2))
  convert hr.hadamard hc using 1
  ext i j
  change ((1 / Real.cosh (β * (ν i - ν j) / 4) : ℝ) : ℂ) =
    (2 : ℂ) * ((Real.exp (β * ν i / 4) : ℂ) *
      star (Real.exp (β * ν j / 4) : ℂ)) *
        ((1 / (Real.exp (β * ν i / 2) + Real.exp (β * ν j / 2)) : ℝ) : ℂ)
  simp only [Complex.star_def, Complex.conj_ofReal]
  have he := fullSech_cauchy (β * ν i / 4) (β * ν j / 4)
  rw [show β * ν i / 4 - β * ν j / 4 = β * (ν i - ν j) / 4 by ring,
    show 2 * (β * ν i / 4) = β * ν i / 2 by ring,
    show 2 * (β * ν j / 4) = β * ν j / 2 by ring] at he
  have he' : 1 / Real.cosh (β * (ν i - ν j) / 4) =
      2 * Real.exp (β * ν i / 4) * Real.exp (β * ν j / 4) *
        (1 / (Real.exp (β * ν i / 2) + Real.exp (β * ν j / 2))) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using he
  have hec := congrArg (fun r : ℝ => (r : ℂ)) he'
  push_cast at hec ⊢
  simpa only [mul_assoc] using! hec

noncomputable def fullSechSchur (β : ℝ) (ν : κ → ℝ) (M : Matrix κ κ ℂ) :
    Matrix κ κ ℂ := fullSechKernel β ν ⊙ M

/-- Full Sech Schur pos Semidef for the stated finite source data. -/
theorem fullSechSchur_posSemidef (β : ℝ) (ν : κ → ℝ) {M : Matrix κ κ ℂ}
    (hM : M.PosSemidef) : (fullSechSchur β ν M).PosSemidef :=
  (fullSechKernel_posSemidef β ν).hadamard hM

omit [Fintype κ] in
/-- Full Sech Schur sub smul for the stated finite source data. -/
theorem fullSechSchur_sub_smul (β : ℝ) (ν : κ → ℝ)
    (M N : Matrix κ κ ℂ) (c : ℂ) :
    fullSechSchur β ν (M - c • N) =
      fullSechSchur β ν M - c • fullSechSchur β ν N := by
  ext i j
  simp only [fullSechSchur, Matrix.hadamard_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

omit [Fintype κ] in
/-- Full Sech Kernel diagonal for the stated finite source data. -/
theorem fullSechKernel_diagonal (β : ℝ) (ν : κ → ℝ) (i : κ) :
    fullSechKernel β ν i i = 1 := by
  simp [fullSechKernel]

omit [Fintype κ] in
/-- Normalization of the finite positive Schur map. -/
theorem fullSechSchur_one [DecidableEq κ] (β : ℝ) (ν : κ → ℝ) :
    fullSechSchur β ν (1 : Matrix κ κ ℂ) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [fullSechSchur, Matrix.hadamard_apply, fullSechKernel_diagonal]
  · simp [fullSechSchur, Matrix.hadamard_apply, hij]

omit [Fintype κ] in
/-- A vector supported on the zero-frequency coordinates has its rank-one
matrix fixed by the actual normalized kernel, including off-diagonal entries. -/
theorem fullSechSchur_rankOne_fixed (β : ℝ) (ν : κ → ℝ) (g : κ → ℂ)
    (hg : ∀ i, g i ≠ 0 → ν i = 0) :
    fullSechSchur β ν (Matrix.vecMulVec g (star g)) =
      Matrix.vecMulVec g (star g) := by
  ext i j
  by_cases hi : g i = 0
  · simp [fullSechSchur, Matrix.hadamard_apply, Matrix.vecMulVec, hi]
  · by_cases hj : g j = 0
    · simp [fullSechSchur, Matrix.hadamard_apply, Matrix.vecMulVec, hj]
    · simp [fullSechSchur, fullSechKernel, Matrix.hadamard_apply,
        hg i hi, hg j hj]

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- The physical factor-two damping equals the normalized hyperbolic secant. -/
theorem fullSource_damping (β ω : ℝ) :
    2 * phaseKernel β ω = 1 / Real.cosh (β * ω / 4) := by
  unfold phaseKernel
  ring

/-- Exact identification of the complete source Gram with the positive
sech map; all matrix-unit coordinates and transition labels are retained. -/
theorem fullGramMatrix_damped_eq_sechSchur (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) :
    fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A =
      fullSechSchur β (fullNu lam) (fullGramMatrix lam β (fun _ => 1) A) := by
  ext p q
  rw [fullGramMatrix_kernel_entry, fullSource_damping]
  have hn : β * (fullNu lam q - fullNu lam p) / 4 =
      -(β * (fullNu lam p - fullNu lam q) / 4) := by ring
  rw [hn, Real.cosh_neg]
  rfl

/-- Full Gram Matrix damped pos Semidef for the stated finite source data. -/
theorem fullGramMatrix_damped_posSemidef {β : ℝ} (hβ : 0 < β)
    (lam : Fin D → ℝ)
    (A : ι → Operator D) :
    (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A).PosSemidef := by
  rw [fullGramMatrix_damped_eq_sechSchur]
  exact fullSechSchur_posSemidef β (fullNu lam)
    (fullGramMatrix_plain_posSemidef hβ lam A)


end Qatlib.Concepts.GibbsSource.SourceForms
