/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityDominanceCorollaryStat
import Qatlib.Concepts.QueryComplexity.DecisionTrees.SensitivityCertificateTree
import Qatlib.Concepts.QueryComplexity.DecisionTrees.Lemma52CertificateBlockSensitivityBeal
import Qatlib.Concepts.QueryComplexity.DecisionTrees.Lemma53DetCertificateBlockBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open scoped Classical

theorem sensitivityDominanceCorollary : SensitivityDominanceCorollary := by
  intro N f
  obtain ⟨t, ht, hb⟩ := lemma53DeterministicCertificateBlock N f
  have hD : deterministicQueryComplexity f ≤ t.MaxQueries := by
    apply Nat.sInf_le
    exact Set.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩
  have hC := lemma52CertificateBlockSensitivity N f
  calc
    deterministicQueryComplexity f ≤ t.MaxQueries := hD
    _ ≤ oneCertificateComplexity f * blockSensitivity f := hb
    _ ≤ blockSensitivity f ^ 2 * blockSensitivity f :=
      Nat.mul_le_mul_right _ (hC.1.trans hC.2)
    _ = blockSensitivity f ^ 3 := by ring

end Qatlib.Concepts.QueryComplexity.DecisionTrees
