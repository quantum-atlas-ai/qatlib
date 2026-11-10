/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.CubicSpectrum.Roots
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.WalkReduction.CubicSpectrum

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

theorem nearby_native_eigenvalue {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 3 → ℝ, Module.End.HasEigenvector (Hred0 (gammaC n) n).toLin' lam v := by
  obtain ⟨lam,hlam,hbound⟩ := lambda_u_exists hn
  exact ⟨lam,hbound,root_native_eigenvector (by linarith) hlam⟩

end Qatlib.Foundations.WalkReduction.CubicSpectrum
