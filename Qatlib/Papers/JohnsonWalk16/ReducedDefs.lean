/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.BasisExact.Transport
import Qatlib.Foundations.WalkReduction.CubicSpectrum.FourBlock
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.JohnsonWalk16.ReducedDefs
open Qatlib.Foundations.WalkReduction

theorem complete_basis_conjugation {n : ℝ} (hn : 6 ≤ n) (γ : ℝ) :
    (BasisExact.sourceBasis n).transpose * BasisExact.sourceBasis n = 1 ∧
    (BasisExact.sourceBasis n)⁻¹ * FourDefs.hamiltonian γ n * BasisExact.sourceBasis n =
      BasisExact.changed γ n ∧ (BasisExact.changed γ n).IsHermitian :=
  ⟨BasisExact.sourceBasis_orthogonal hn,BasisExact.changed_inverse hn γ,
    BasisExact.changed_hermitian γ n⟩

theorem exact_restored_coupling {n γ : ℝ} (hn : 6 ≤ n) (hγ : 0 < γ) :
    BasisExact.changed γ n 0 1 ≠ 0 := BasisExact.changed_marked_r_ne_zero hγ.ne' hn

theorem candidate_leading_eigenvalue {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 4 → ℝ, Module.End.HasEigenvector
        (CubicSpectrum.leadingFour (CubicSpectrum.gammaC n) n).toLin' lam v :=
  CubicSpectrum.leadingFour_nearby hn

theorem reported_normalization_ratio_failure :
    (1:ℝ)*Real.sqrt (1/9) ≠ FourDefs.adjacency 6 2 3 := by
  change (1:ℝ)*Real.sqrt (1/9) ≠ 3*Real.sqrt (6-5)
  norm_num [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 9]

end Qatlib.Papers.JohnsonWalk16.ReducedDefs
