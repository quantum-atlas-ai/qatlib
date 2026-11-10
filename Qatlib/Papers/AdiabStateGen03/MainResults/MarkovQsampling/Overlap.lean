/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling

open Qatlib.Papers.AdiabStateGen03.MainResults
open WithLp

variable {n : ℕ}

lemma ketOfDist_toLp (π : Dim n → ℝ) :
    ketOfDist π = toLp 2 (fun i => (Real.sqrt (π i) : ℂ)) := rfl

theorem norm_ketOfDist_sq (π : Dim n → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    ‖ketOfDist π‖ ^ 2 = ∑ i, π i := by
  rw [ketOfDist_toLp, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (hπ i)]

theorem inner_ketOfDist_eq_sum (p q : Dim n → ℝ) :
    ⟪ketOfDist p, ketOfDist q⟫_ℂ
      = ((∑ i, Real.sqrt (p i) * Real.sqrt (q i) : ℝ) : ℂ) := by
  rw [ketOfDist_toLp p, ketOfDist_toLp q, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

theorem slowlyVarying_overlap_eq_inner {T : ℕ} (π : Fin (T + 1) → Dim n → ℝ)
    (hπ : ∀ t i, 0 ≤ π t i) (t : Fin T) :
    (⟪ketOfDist (π (Fin.castSucc t)), ketOfDist (π t.succ)⟫_ℂ).re
      = ∑ i, Real.sqrt (π (Fin.castSucc t) i * π t.succ i) := by
  rw [inner_ketOfDist_eq_sum]
  simp only [Complex.ofReal_re]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Real.sqrt_mul (hπ (Fin.castSucc t) i)]

end Qatlib.Papers.AdiabStateGen03.MainResults.MarkovQsampling
