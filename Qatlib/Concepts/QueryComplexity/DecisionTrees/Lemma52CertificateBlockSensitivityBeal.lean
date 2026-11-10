/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DecisionTrees.Lemma52CertificateBlockSensitivityStat
import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityCertificateTree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

theorem lemma52CertificateBlockSensitivity : Lemma52CertificateBlockSensitivity := by
  intro N f
  constructor
  · apply Finset.sup_le
    intro n hn
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
    exact certificateSizeAt_le_global f x
  · apply Finset.sup_le
    intro n hn
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨S, hS, hbound⟩ := bounded_certificate f x
    exact (certificateSizeAt_le hS).trans hbound

end Qatlib.Concepts.QueryComplexity.DecisionTrees
