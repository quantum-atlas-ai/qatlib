/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
import Qatlib.Papers.QZetaZeroes04.MainResults.FermatCircuitCost
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.ZetaSpectrumCircuit

open Matrix
open Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
open scoped BigOperators

variable (H : ZetaHypersurface)

theorem zetaRoot_norm (j : Fin H.rootCount) :
    ‖H.zetaRoot j‖ = (rootRadius H.q H.n)⁻¹ := by
  unfold ZetaHypersurface.zetaRoot
  rw [one_div, norm_inv, H.alpha_norm j]

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

theorem eigenPhase_eq_normalized (j : Fin H.rootCount) :
    H.eigenPhase j = H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ) := rfl

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

theorem zetaCircuit_mulVec_single (j : Fin H.rootCount) (x : ℂ) :
    H.zetaCircuit *ᵥ Pi.single j x = Pi.single j (H.eigenPhase j * x) := by
  unfold ZetaHypersurface.zetaCircuit
  exact diagonal_mulVec_single H.eigenPhase j x

theorem zetaCircuit_eigenpair (j : Fin H.rootCount) :
    H.zetaCircuit *ᵥ Pi.single j (1 : ℂ) =
      H.eigenPhase j • Pi.single j (1 : ℂ) := by
  rw [zetaCircuit_mulVec_single, mul_one]
  rw [← Pi.single_smul' j (H.eigenPhase j) (1 : ℂ)]
  simp

theorem fermat_zeta_spectrum :
    ∃ (U : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ),
      U ∈ Matrix.unitaryGroup (Fin H.rootCount) ℂ ∧
      (∀ j : Fin H.rootCount,
        U *ᵥ Pi.single j (1 : ℂ) =
          (H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ)) • Pi.single j (1 : ℂ)) := by
  refine ⟨H.zetaCircuit, zetaCircuit_mem_unitaryGroup H, ?_⟩
  intro j
  rw [zetaCircuit_eigenpair, eigenPhase_eq_normalized]

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
