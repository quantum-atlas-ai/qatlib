/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.BasisExact.Transport
import Qatlib.Foundations.WalkReduction.CubicSpectrum.FourBlock

/-!
# Exact basis change and leading spectral support

This module collects exact facts about the four-dimensional Johnson search Hamiltonian and its
changed basis. It records orthogonality, Hermitian conjugation, a restored coupling, a nearby
eigenvalue at the candidate rate, and a counterexample to the printed normalization ratio. See
[Wong2016].

## Main statements

* `complete_basis_conjugation`: For n ≥ 6, the source basis has transpose times itself equal to
  the identity, conjugates the Hamiltonian to `BasisExact.changed`, and yields a Hermitian
  matrix.
* `candidate_leading_eigenvalue`: For n ≥ 6, the leading four-dimensional matrix at the
  candidate rate has a real eigenvalue within 54/n² of −1 − 1/(2n).

## References

* [Wong, 2016][Wong2016]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.JohnsonWalk16.ReducedDefs
open Qatlib.Foundations.WalkReduction

/-- For n ≥ 6, the source basis has transpose times itself equal to the identity, conjugates the
Hamiltonian to `BasisExact.changed`, and yields a Hermitian matrix; see [Wong2016]. -/
theorem complete_basis_conjugation {n : ℝ} (hn : 6 ≤ n) (γ : ℝ) :
    (BasisExact.sourceBasis n).transpose * BasisExact.sourceBasis n = 1 ∧
    (BasisExact.sourceBasis n)⁻¹ * FourDefs.hamiltonian γ n * BasisExact.sourceBasis n =
      BasisExact.changed γ n ∧ (BasisExact.changed γ n).IsHermitian :=
  ⟨BasisExact.sourceBasis_orthogonal hn,BasisExact.changed_inverse hn γ,
    BasisExact.changed_hermitian γ n⟩

/-- For n ≥ 6 and positive jumping rate, the changed Hamiltonian has a nonzero entry coupling
coordinates zero and one; see [Wong2016]. -/
theorem exact_restored_coupling {n γ : ℝ} (hn : 6 ≤ n) (hγ : 0 < γ) :
    BasisExact.changed γ n 0 1 ≠ 0 := BasisExact.changed_marked_r_ne_zero hγ.ne' hn

/-- For n ≥ 6, the leading four-dimensional matrix at the candidate rate has a real eigenvalue
within 54/n² of −1 − 1/(2n); see [Wong2016]. -/
theorem candidate_leading_eigenvalue {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 4 → ℝ, Module.End.HasEigenvector
        (CubicSpectrum.leadingFour (CubicSpectrum.gammaC n) n).toLin' lam v :=
  CubicSpectrum.leadingFour_nearby hn

/-- At n = 6, the printed normalization value √(1/9) differs from entry (2, 3) of
`FourDefs.adjacency`; see [Wong2016]. -/
theorem reported_normalization_ratio_failure :
    (1:ℝ)*Real.sqrt (1/9) ≠ FourDefs.adjacency 6 2 3 := by
  change (1:ℝ)*Real.sqrt (1/9) ≠ 3*Real.sqrt (6-5)
  norm_num [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 9]

end Qatlib.Papers.JohnsonWalk16.ReducedDefs
