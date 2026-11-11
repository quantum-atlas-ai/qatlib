/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Prop2Arboricity

/-!
# Assembling norm bounds from star decompositions

Proves spectral-norm estimates for sums and complex entrywise absolute-value matrices. The
theorem `prop2_of_star_decomposition` establishes `prop2Statement` from a supplied
absolute-value decomposition, exact component norm identities, and a bound on their total
maximum-column norm. See [ChildsKothari2010] for the surrounding analysis.

## Main statements

* `specNorm_le_specNorm_absComplex`: The spectral norm of a complex matrix is at most that of
  its complex entrywise absolute-value matrix.
* `specNorm_sum_le`: The spectral norm of a finite sum of matrices is at most the sum of their
  spectral norms.
* `prop2_of_star_decomposition`: Given the stated absolute-value decomposition, component norm
  identities, and bound `∑ l, mcnNorm (S l) ≤ 2 * k * mcnNorm H`, the three inequalities in
  `prop2Statement H hH hk` hold.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The spectral norm of a complex matrix is at most that of its complex entrywise
absolute-value matrix [ChildsKothari2010]. -/
lemma specNorm_le_specNorm_absComplex (H : Matrix ι ι ℂ) :
    specNorm H ≤ specNorm ((absMatrix H).map Complex.ofReal) := by
  set A : Matrix ι ι ℂ := (absMatrix H).map Complex.ofReal with hAdef
  have hR : 0 ≤ specNorm A := specNorm_nonneg _
  rw [specNorm_eq_l2, ← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun v => ?_
  have hdelC : (⇑(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H) v
      = (EuclideanSpace.equiv ι ℂ).symm (H *ᵥ v.ofLp) := by
    apply WithLp.ofLp_injective
    simp [Matrix.ofLp_toEuclideanCLM]
  rw [hdelC]

  set w : ι → ℂ := fun j => (‖v.ofLp j‖ : ℂ) with hw
  have hra : ∀ i : ι, 0 ≤ ∑ j, absMatrix H i j * ‖v.ofLp j‖ :=
    fun i => Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hAeval : ∀ i, (A *ᵥ w) i = (((∑ j, absMatrix H i j * ‖v.ofLp j‖) : ℝ) : ℂ) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hAdef, hw, Matrix.map_apply]
    push_cast
    rfl
  have hdom :
      ‖(EuclideanSpace.equiv ι ℂ).symm (H *ᵥ v.ofLp)‖
        ≤ ‖(EuclideanSpace.equiv ι ℂ).symm (A *ᵥ w)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have hcomp : ‖(H *ᵥ v.ofLp) i‖ ≤ ∑ j, absMatrix H i j * ‖v.ofLp j‖ := by
      change ‖∑ j, H i j * v.ofLp j‖ ≤ ∑ j, absMatrix H i j * ‖v.ofLp j‖
      calc ‖∑ j, H i j * v.ofLp j‖ ≤ ∑ j, ‖H i j * v.ofLp j‖ := norm_sum_le _ _
        _ = ∑ j, absMatrix H i j * ‖v.ofLp j‖ := by simp [absMatrix]
    have hsq : ‖(H *ᵥ v.ofLp) i‖ ^ 2 ≤ (∑ j, absMatrix H i j * ‖v.ofLp j‖) ^ 2 := by
      nlinarith [norm_nonneg ((H *ᵥ v.ofLp) i), hcomp, hra i]
    have hnormA : ‖(A *ᵥ w) i‖ = ∑ j, absMatrix H i j * ‖v.ofLp j‖ := by
      rw [hAeval i, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hra i)]
    have hleft : ((EuclideanSpace.equiv ι ℂ).symm (H *ᵥ v.ofLp)).ofLp = H *ᵥ v.ofLp := rfl
    have hright : ((EuclideanSpace.equiv ι ℂ).symm (A *ᵥ w)).ofLp = A *ᵥ w := rfl
    rw [hleft, hright, hnormA]
    exact hsq
  have hstep :
      ‖(EuclideanSpace.equiv ι ℂ).symm (A *ᵥ w)‖ ≤ specNorm A * ‖(EuclideanSpace.equiv ι ℂ).symm w‖ :=
    specNorm_mulVec A ((WithLp.toLp 2 w) : EuclideanSpace ℂ ι)
  have hveq :
      ‖(EuclideanSpace.equiv ι ℂ).symm w‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hw, Complex.norm_real]
  exact hdom.trans (hstep.trans_eq (by rw [hveq]))

/-- The spectral norm of a finite sum of matrices is at most the sum of their spectral norms
[ChildsKothari2010]. -/
lemma specNorm_sum_le {m : ℕ} (S : Fin m → Matrix ι ι ℂ) :
    specNorm (∑ l, S l) ≤ ∑ l, specNorm (S l) := by
  rw [specNorm_eq_l2]
  calc ‖∑ l, S l‖ ≤ ∑ l, ‖S l‖ := norm_sum_le _ _
    _ = ∑ l, specNorm (S l) := by simp [specNorm_eq_l2]

/-- An entrywise additive decomposition of absolute-value matrices remains additive after
mapping the real entries into the complex numbers [ChildsKothari2010]. -/
lemma absMatrix_map_sum {m : ℕ} (H : Matrix ι ι ℂ) (S : Fin m → Matrix ι ι ℂ)
    (h : ∀ i j, absMatrix H i j = ∑ l, absMatrix (S l) i j) :
    (absMatrix H).map Complex.ofReal
      = ∑ l, ((absMatrix (S l)).map Complex.ofReal) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, h]
  push_cast
  rfl

/-- Given the stated absolute-value decomposition, component norm identities, and bound `∑ l,
mcnNorm (S l) ≤ 2 * k * mcnNorm H`, the three inequalities in `prop2Statement H hH hk` hold
[ChildsKothari2010]. -/
theorem prop2_of_star_decomposition
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) {k m : ℕ}
    (hk : GraphArboricityLE (matrixGraph H) k)
    (S : Fin m → Matrix ι ι ℂ)
    (habs : ∀ i j, absMatrix H i j = ∑ l, absMatrix (S l) i j)
    (hstar : ∀ l, specNorm ((absMatrix (S l)).map Complex.ofReal) = mcnNorm (S l))
    (hcount : (∑ l, mcnNorm (S l)) ≤ 2 * (k : ℝ) * mcnNorm H) :
    prop2Statement H hH hk := by
  have habsC : (absMatrix H).map Complex.ofReal
      = ∑ l, ((absMatrix (S l)).map Complex.ofReal) := absMatrix_map_sum H S habs
  have h1 : specNorm ((absMatrix H).map Complex.ofReal) ≤ 2 * (k : ℝ) * mcnNorm H := by
    rw [habsC]
    calc specNorm (∑ l, (absMatrix (S l)).map Complex.ofReal)
        ≤ ∑ l, specNorm ((absMatrix (S l)).map Complex.ofReal) := specNorm_sum_le _
      _ = ∑ l, mcnNorm (S l) := by simp [hstar]
      _ ≤ 2 * (k : ℝ) * mcnNorm H := hcount
  have h2 : specNorm ((absMatrix H).map Complex.ofReal) ≤ 2 * (k : ℝ) * specNorm H := by
    refine h1.trans ?_
    have hm : mcnNorm H ≤ specNorm H := mcnNorm_le_specNorm H
    have hk0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    nlinarith [hm, hk0, mcnNorm_nonneg H]
  have h3 : specNorm H ≤ 2 * (k : ℝ) * mcnNorm H :=
    (specNorm_le_specNorm_absComplex H).trans h1
  exact ⟨h1, h2, h3⟩

end Qatlib.Papers.NonSparseHam09.MainResults
