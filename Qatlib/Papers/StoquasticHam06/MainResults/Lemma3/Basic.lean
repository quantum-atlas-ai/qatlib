/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma3

theorem stoquastic_of_termwise (d : LHData) (h : d.IsTermwiseStoquastic) :
    d.IsStoquastic := by
  intro x y hxy
  show d.toRealH x y ≤ 0
  unfold LHData.toRealH QMatrix.toReal
  have hH : d.H x y = ∑ a, d.term a x y := by
    unfold LHData.H
    simp only [Finset.sum_apply]
  rw [hH]
  push_cast
  exact Finset.sum_nonpos (fun a _ => h a x y hxy)

theorem termwise_of_diag (d : LHData)
    (hdiag : ∀ (a : Fin d.m) (x y : Sigma d.n), x ≠ y → d.term a x y = 0) :
    d.IsTermwiseStoquastic := by
  intro a x y hxy
  unfold QMatrix.toReal
  rw [hdiag a x y hxy]
  simp

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma3
