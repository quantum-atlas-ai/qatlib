/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceSechSchur
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapGeometry

@[expose] public section


/-! # Sech damping preserves the full Gibbs-complement lower bound

The positive unital Schur map fixes the Gibbs rank-one matrix because every
nonzero Gibbs coordinate has zero operator frequency. Therefore it fixes
the normalized Gibbs-complement matrix and preserves every plain-parent
lower bound by that matrix. This does not assert the operator inequality
`Hg >= H0`.
-/

open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Foundations.PureStateMath



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The complement is fixed without requiring a normalization premise on
g. Nonzero g is needed when interpreting this matrix as an orthogonal
projection, but not for this exact identity. -/
theorem fullSechSchur_gibbsComplement_fixed (β : ℝ) (ν : κ → ℝ) (g : κ → ℂ)
    (hg : ∀ i, g i ≠ 0 → ν i = 0) :
    fullSechSchur β ν (fullGibbsComplement g) = fullGibbsComplement g := by
  unfold fullGibbsComplement
  rw [fullSechSchur_sub_smul, fullSechSchur_one,
    fullSechSchur_rankOne_fixed β ν g hg]

/-- Positive Schur transport of any lower bound on the full complex
Gibbs complement. The premise is a plain bound, not the desired damped bound. -/
theorem fullSechSchur_lowerBound (β : ℝ) (ν : κ → ℝ) (g : κ → ℂ)
    (hg : ∀ i, g i ≠ 0 → ν i = 0) (M : Matrix κ κ ℂ) (δ : ℝ)
    (hbound : (M - (δ : ℂ) • fullGibbsComplement g).PosSemidef) :
    (fullSechSchur β ν M - (δ : ℂ) • fullGibbsComplement g).PosSemidef := by
  have hp := fullSechSchur_posSemidef β ν hbound
  simpa only [fullSechSchur_sub_smul, fullSechSchur_gibbsComplement_fixed β ν g hg]
    using hp

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- The complete Gibbs matrix is diagonal, so every nonzero coordinate has
zero operator frequency. Degenerate off-diagonal frequencies cause no issue. -/
theorem fullGibbsVector_frequency_zero (lam : Fin D → ℝ) (β : ℝ) (p : FullCoord D)
    (hp : fullGibbsVector lam β p ≠ 0) : fullNu lam p = 0 := by
  by_cases hdiag : p.1 = p.2
  · simp [fullNu, hdiag]
  · exfalso
    apply hp
    simp [fullGibbsVector, fullVec, fullGibbsMatrix, hdiag]

/-- Full Gram Matrix damped lower Bound for the stated finite source data. -/
theorem fullGramMatrix_damped_lowerBound (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (δ : ℝ)
    (hbound : (fullGramMatrix lam β (fun _ => 1) A -
      (δ : ℂ) • fullGibbsComplement (fullGibbsVector lam β)).PosSemidef) :
    (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A -
      (δ : ℂ) • fullGibbsComplement (fullGibbsVector lam β)).PosSemidef := by
  rw [fullGramMatrix_damped_eq_sechSchur]
  exact fullSechSchur_lowerBound β (fullNu lam) (fullGibbsVector lam β)
    (fullGibbsVector_frequency_zero lam β) _ δ hbound


end Qatlib.Concepts.GibbsSource.SourceForms
