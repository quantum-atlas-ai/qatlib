/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.PurificationErrors
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.PurifErrors
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Purification

theorem actual_lemma32 {I O P : Type*} [Fintype I] [Fintype O] [Fintype P]
    [DecidableEq I] (V : Matrix O I ℂ) (Phi E : Matrix I P ℂ) (alpha : I → ℂ)
    (delta : ℝ) (hd : 0 ≤ delta)
    (horth : ∀ i j, ∑ p, Phi i p * star (Phi j p) = if i=j then 1 else 0)
    (herr : ∀ i j, ∑ p, Phi i p * star (E j p) = 0)
    (halpha : ∀ i, 1-delta ≤ ‖alpha i‖^2)
    (hnorm : ∑ o, ∑ p, ‖(V * Phi) o p‖^2 = 1)
    (hnorm' : ∑ o, ∑ p, ‖(V * (Matrix.diagonal alpha * Phi + E)) o p‖^2 = 1) :
    Matrix.traceNorm (reduced (V * Phi) -
      reduced (V * (Matrix.diagonal alpha * Phi + E))) / 2 ≤ delta := by
  have hPhi : Phi * Phiᴴ = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using horth i j
  have hE : Phi * Eᴴ = 0 := by
    ext i j
    exact herr i j
  exact orthogonal_errors_distance V Phi E alpha delta hd hPhi hE halpha hnorm hnorm'

end Qatlib.Papers.AmpInvReqTang26.PurifErrors
