/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceRayleighGap
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGibbs

@[expose] public section


/-! # Independence of the Gibbs direction's normalization

The physical full-space Gibbs vector is unnormalized. Its orthogonal unit
set, exact Rayleigh minimum, and variance agree with those for the
normalized square root of the source Gibbs density matrix.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι]

/-- Full Unit Orthogonal smul for the stated finite source data. -/
theorem fullUnitOrthogonal_smul (g : ι → ℂ) (c : ℂ) (hc : c ≠ 0) :
    fullUnitOrthogonal (c • g) = fullUnitOrthogonal g := by
  have hcs : star c ≠ 0 := by
    intro h
    apply hc
    simpa only [star_star, star_zero] using congrArg star h
  ext z
  simp only [fullUnitOrthogonal, Set.mem_ofPred_eq, star_smul, smul_dotProduct,
    smul_eq_mul, mul_eq_zero, hcs, false_or]

/-- Full Rayleigh Gap smul g for the stated finite source data. -/
theorem fullRayleighGap_smul_g (M : Matrix ι ι ℂ) (g : ι → ℂ)
    (c : ℂ) (hc : c ≠ 0) : fullRayleighGap M (c • g) = fullRayleighGap M g := by
  rw [fullRayleighGap, fullUnitOrthogonal_smul g c hc, fullRayleighGap]

/-- Full Variance smul g for the stated finite source data. -/
theorem fullVariance_smul_g (g z : ι → ℂ) (c : ℂ) (hc : c ≠ 0) :
    fullVariance (c • g) z = fullVariance g z := by
  have hcn : Complex.normSq c ≠ 0 := fun h => hc (Complex.normSq_eq_zero.mp h)
  have hcs : Complex.normSq (star c) = Complex.normSq c := by
    simp only [Complex.normSq_eq_norm_sq, norm_star]
  simp only [fullVariance, fullNormSq_smul, star_smul, smul_dotProduct,
    smul_eq_mul, Complex.normSq_mul, hcs]
  by_cases hg : fullNormSq g = 0
  · simp [hg]
  · field_simp [hcn, hg]

/-- Full Gibbs Vector eq smul sqrt for the stated finite source data. -/
theorem fullGibbsVector_eq_smul_sqrt {D : ℕ} [Nonempty (Fin D)]
    (lam : Fin D → ℝ) (β : ℝ) :
    fullGibbsVector lam β = (Real.sqrt (fullGibbsPartition lam β) : ℂ) •
      fullVec (CFC.sqrt (gibbsDiag lam β)) := by
  rw [fullGibbsVector, fullGibbsMatrix_eq_smul_sqrt]
  rfl

/-- Full Gibbs Variance eq hs Var for the stated finite source data. -/
theorem fullGibbsVariance_eq_hsVar {D : ℕ} [Nonempty (Fin D)]
    (lam : Fin D → ℝ) (β : ℝ) (X : Operator D) :
    fullVariance (fullGibbsVector lam β) (fullVec X) =
      hsVar (CFC.sqrt (gibbsDiag lam β)) X := by
  have hc : (Real.sqrt (fullGibbsPartition lam β) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (fullGibbsPartition_pos lam β))
  rw [fullGibbsVector_eq_smul_sqrt, fullVariance_smul_g _ _ _ hc, fullVariance_fullVec]

/-- Full Gibbs Rayleigh Gap eq normalized for the stated finite source data. -/
theorem fullGibbsRayleighGap_eq_normalized {D : ℕ} [Nonempty (Fin D)]
    (M : Matrix (FullCoord D) (FullCoord D) ℂ) (lam : Fin D → ℝ) (β : ℝ) :
    fullRayleighGap M (fullGibbsVector lam β) =
      fullRayleighGap M (fullVec (CFC.sqrt (gibbsDiag lam β))) := by
  have hc : (Real.sqrt (fullGibbsPartition lam β) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (fullGibbsPartition_pos lam β))
  rw [fullGibbsVector_eq_smul_sqrt, fullRayleighGap_smul_g _ _ _ hc]

end Qatlib.Concepts.GibbsSource.SourceForms
