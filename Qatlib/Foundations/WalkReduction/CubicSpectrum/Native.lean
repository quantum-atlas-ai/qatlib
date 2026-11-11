/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.CubicSpectrum.Roots
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Native eigenvectors from cubic roots

This module converts zeros of `charPoly` into nonzero eigenvectors of the reduced matrix
`Hred0`. At the critical coupling `gammaC n`, it combines this correspondence with the cubic
root bound to produce an eigenvalue near `-1 - 1 / (2 * n)` for `n ≥ 6`.

The mathematical background is discussed in [Wong2016].

## Main statements

* `root_native_eigenvector`: obtains a nonzero eigenvector from a cubic root.
* `nearby_native_eigenvalue`: realizes the nearby root as a matrix eigenvalue.

## References

* [Wong, 2016][Wong2016]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.WalkReduction.CubicSpectrum

/-- For nonnegative `n`, every real zero of `charPoly γ lam n` has a corresponding nonzero
eigenvector of `Hred0 γ n` with eigenvalue `lam`. -/
theorem root_native_eigenvector {γ lam n : ℝ} (hn : 0 ≤ n)
    (hlam : charPoly γ lam n = 0) :
    ∃ v : Fin 3 → ℝ, Module.End.HasEigenvector (Hred0 γ n).toLin' lam v := by
  have hd : (Matrix.scalar (Fin 3) lam - Hred0 γ n).det = 0 := by
    rw [charPoly_eq_det hn,hlam,neg_zero]
  obtain ⟨v,hv,he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨v,?_⟩
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff]
  refine ⟨?_,hv⟩
  have he' : lam • v - (Hred0 γ n).mulVec v = 0 := by
    ext i
    have hi := congrFun he i
    simpa only [Matrix.sub_mulVec,Pi.sub_apply,Matrix.scalar_apply,Matrix.mulVec_diagonal,
      Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hi
  exact (sub_eq_zero.mp he').symm

/-- For `n ≥ 6`, the reduced matrix at `gammaC n` has a real eigenvalue within `54 / n ^ 2` of
`-1 - 1 / (2 * n)` and a corresponding nonzero eigenvector. -/
theorem nearby_native_eigenvalue {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 3 → ℝ, Module.End.HasEigenvector (Hred0 (gammaC n) n).toLin' lam v := by
  obtain ⟨lam,hlam,hbound⟩ := lambda_u_exists hn
  exact ⟨lam,hbound,root_native_eigenvector (by linarith) hlam⟩

end Qatlib.Foundations.WalkReduction.CubicSpectrum
