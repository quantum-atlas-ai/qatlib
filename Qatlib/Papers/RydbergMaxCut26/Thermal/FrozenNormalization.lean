/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Thermal.GibbsSpectral
import Qatlib.Concepts.MatrixExpTrace.GibbsNorm

/-!
# Gibbs normalization from the frozen operator results

The Hermitian scaling used in the matrix Gibbs exponential allows the frozen operator
normalization results to be applied directly to `gibbsMatrix` and `gibbsState`. For a nonempty
finite index type, the partition function is positive and the normalized Gibbs matrix is a
density matrix for every real temperature parameter. See [CrostaSaubanereHuber2026].

## Main statements

* `frozen_actual_gibbs_positive`: proves positivity of the Gibbs matrix and its partition
  function.
* `frozen_based_gibbs_density`: proves positivity and trace one of the normalized state.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.RydbergMaxCut26.Thermal.Spectral

namespace Qatlib.Papers.RydbergMaxCut26.Thermal.Normalization
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- Multiplying a Hermitian matrix by the real scalar `-1 / T` preserves Hermitian symmetry. -/
theorem scaled_hermitian (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    ((-1/T:ℝ) • H).IsHermitian := hH.smul (R:=ℝ) (IsSelfAdjoint.all _)

/-- For a Hermitian matrix on a nonempty finite index type, `gibbsMatrix H T` is positive
semidefinite and `partition H T` is positive. -/
theorem frozen_actual_gibbs_positive [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsMatrix H T).PosSemidef ∧ 0<partition H T := by
  exact ⟨Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_posSemidef
      ((-1/T:ℝ) • H) (scaled_hermitian H hH T),
    Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos
      ((-1/T:ℝ) • H) (scaled_hermitian H hH T)⟩

/-- For a Hermitian matrix on a nonempty finite index type, the Gibbs state is positive
semidefinite and has trace one by the frozen operator normalization results; see
[CrostaSaubanereHuber2026]. -/
theorem frozen_based_gibbs_density [Nonempty I] (H : Matrix I I ℂ) (hH : H.IsHermitian) (T : ℝ) :
    (gibbsState H T).PosSemidef ∧ (gibbsState H T).trace=1 := by
  have hp := frozen_actual_gibbs_positive H hH T
  refine ⟨hp.1.smul (inv_nonneg.mpr hp.2.le),?_⟩
  have ht : (gibbsMatrix H T).trace=(partition H T:ℂ) := by
    rw [gibbs_trace H hH T,partition_spectral H hH T]
  rw [gibbsState,Matrix.trace_smul,ht,Complex.real_smul,← Complex.ofReal_mul,
    inv_mul_cancel₀ hp.2.ne']
  rfl

end Qatlib.Papers.RydbergMaxCut26.Thermal.Normalization
