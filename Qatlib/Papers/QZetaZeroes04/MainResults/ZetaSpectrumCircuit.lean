/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
import Qatlib.Papers.QZetaZeroes04.MainResults.FermatCircuitCost

/-!
# A unitary with normalized zeta-root eigenvalues

This module proves that `ZetaHypersurface.zetaCircuit`, the diagonal matrix built from
normalized reciprocal roots, is unitary and has the prescribed coordinate eigenvectors. These
spectral conclusions formalize the unitary spectrum associated with Theorem 3 of [VanDam2004]
from the data stored in `ZetaHypersurface`.

The result `fermat_zeta_cost_annotation` assigns the abstract operation cost from
`FermatCircuitCost.algorithm1Cost` to this diagonal unitary and bounds that annotation
polynomially. `fermat_zeta_annotated_unitary` packages the spectral statement and the cost
annotation in one existence result.

## Main statements

* `zetaRoot_norm` and `eigenPhase_norm`: the reciprocal-root radius and unit-norm phases.
* `zetaCircuit_mem_unitaryGroup`: unitarity of the diagonal matrix.
* `fermat_zeta_spectrum`: a unitary with the normalized roots as coordinate eigenvalues.
* `fermat_zeta_annotated_unitary`: the spectrum together with a polynomial size annotation.

## References

* [van Dam, 2004][VanDam2004]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.ZetaSpectrumCircuit

open Matrix
open Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
open scoped BigOperators

variable (H : ZetaHypersurface)

/-- Every reciprocal root stored in `H` has norm equal to the inverse of `rootRadius H.q H.n`. -/
theorem zetaRoot_norm (j : Fin H.rootCount) :
    ‖H.zetaRoot j‖ = (rootRadius H.q H.n)⁻¹ := by
  unfold ZetaHypersurface.zetaRoot
  rw [one_div, norm_inv, H.alpha_norm j]

/-- Each normalized reciprocal-root value `H.eigenPhase j` has complex norm one. -/
theorem eigenPhase_norm (j : Fin H.rootCount) : ‖H.eigenPhase j‖ = 1 := by
  unfold ZetaHypersurface.eigenPhase
  rw [norm_div]
  have hz : ‖H.zetaRoot j‖ ≠ 0 := by
    rw [zetaRoot_norm H j]
    exact inv_ne_zero (ne_of_gt (rootRadius_pos H.q_ge_two))
  have hcast : ‖((‖H.zetaRoot j‖ : ℝ) : ℂ)‖ = ‖H.zetaRoot j‖ := by
    rw [Complex.norm_real]
    exact abs_of_nonneg (norm_nonneg _)
  rw [hcast]
  exact div_self hz

/-- Identifies `H.eigenPhase j` with `H.zetaRoot j` divided by its norm, viewed as a complex
scalar. -/
theorem eigenPhase_eq_normalized (j : Fin H.rootCount) :
    H.eigenPhase j = H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ) := rfl

/-- The diagonal matrix `H.zetaCircuit` is unitary because each of its diagonal phases has norm
one. -/
theorem zetaCircuit_mem_unitaryGroup :
    H.zetaCircuit ∈ Matrix.unitaryGroup (Fin H.rootCount) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold ZetaHypersurface.zetaCircuit
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  have hfun : (fun i => H.eigenPhase i * star H.eigenPhase i) = fun _ => (1 : ℂ) := by
    funext j
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h1 : ‖H.eigenPhase j‖ = 1 := eigenPhase_norm H j
    rw [h1]
    norm_num
  rw [hfun]
  exact Matrix.diagonal_one

/-- Multiplication by `H.zetaCircuit` scales a vector supported at coordinate `j` by the
corresponding phase `H.eigenPhase j`. -/
theorem zetaCircuit_mulVec_single (j : Fin H.rootCount) (x : ℂ) :
    H.zetaCircuit *ᵥ Pi.single j x = Pi.single j (H.eigenPhase j * x) := by
  unfold ZetaHypersurface.zetaCircuit
  exact diagonal_mulVec_single H.eigenPhase j x

/-- The coordinate vector supported at `j` with value one is an eigenvector of `H.zetaCircuit`
with eigenvalue `H.eigenPhase j`. -/
theorem zetaCircuit_eigenpair (j : Fin H.rootCount) :
    H.zetaCircuit *ᵥ Pi.single j (1 : ℂ) =
      H.eigenPhase j • Pi.single j (1 : ℂ) := by
  rw [zetaCircuit_mulVec_single, mul_one]
  rw [← Pi.single_smul' j (H.eigenPhase j) (1 : ℂ)]
  simp

/-- There exists a unitary matrix whose coordinate eigenvectors have eigenvalues equal to the
normalized reciprocal roots of `H`. The diagonal construction supplies the spectral
conclusion associated with Theorem 3 of [VanDam2004]. -/
theorem fermat_zeta_spectrum :
    ∃ (U : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ),
      U ∈ Matrix.unitaryGroup (Fin H.rootCount) ℂ ∧
      (∀ j : Fin H.rootCount,
        U *ᵥ Pi.single j (1 : ℂ) =
          (H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ)) • Pi.single j (1 : ℂ)) := by
  refine ⟨H.zetaCircuit, zetaCircuit_mem_unitaryGroup H, ?_⟩
  intro j
  rw [zetaCircuit_eigenpair, eigenPhase_eq_normalized]

/-- The diagonal zeta unitary has a polynomial cost annotation using `algorithm1Cost` as its
size, with coefficient 16 and exponent 3. This supplies the assigned-cost conclusion used
for Theorem 3 of [VanDam2004]. -/
theorem fermat_zeta_cost_annotation :
    HasPolynomialCostAnnotation H H.zetaCircuit := by
  refine ⟨⟨FermatCircuitCost.algorithm1Cost H.n (Nat.log 2 H.q), H.zetaCircuit,
    zetaCircuit_mem_unitaryGroup H⟩, 16, 3, by norm_num, by norm_num, rfl, ?_⟩
  have hq : 1 ≤ Nat.log 2 H.q :=
    Nat.le_log_of_pow_le (by norm_num) (by simpa using H.q_ge_two)
  have hm : 1 ≤ Nat.log 2 H.m :=
    Nat.le_log_of_pow_le (by norm_num) (by simpa using H.m_ge_two)
  exact FermatCircuitCost.algorithm1Cost_poly H.n (Nat.log 2 H.q) (Nat.log 2 H.m)
    H.n_ge_one hq hm

/-- There exists a unitary with the normalized reciprocal roots as coordinate eigenvalues and
with a polynomial cost annotation. This combines the spectral and assigned-size conclusions
for the Theorem 3 setting of [VanDam2004]. -/
theorem fermat_zeta_annotated_unitary :
    ∃ (U : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ),
      U ∈ Matrix.unitaryGroup (Fin H.rootCount) ℂ ∧
      (∀ j : Fin H.rootCount,
        U *ᵥ Pi.single j (1 : ℂ) =
          (H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ)) • Pi.single j (1 : ℂ)) ∧
      HasPolynomialCostAnnotation H U := by
  refine ⟨H.zetaCircuit, zetaCircuit_mem_unitaryGroup H, ?_,
    fermat_zeta_cost_annotation H⟩
  intro j
  rw [zetaCircuit_eigenpair, eigenPhase_eq_normalized]

end Qatlib.Papers.QZetaZeroes04.MainResults.ZetaSpectrumCircuit
