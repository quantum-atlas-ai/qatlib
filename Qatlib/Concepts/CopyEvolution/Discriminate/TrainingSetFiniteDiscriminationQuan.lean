/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationStat
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod


set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

theorem trainingSetFiniteDiscrimination : TrainingSetFiniteDiscrimination := by
  intro d m₁ m₂ M n γ φ ψ V x hm₁ hm₂ hM hn hγ hγ1 hφ hψ hV hs hgap
  have hρ := pureStateMixture_density d m₁ φ hφ hm₁
  have hσ := pureStateMixture_density d m₂ ψ hψ hm₂
  have h := finiteCopyHelstromDiscrimination d M n γ (pureStateMixture d m₁ φ)
    (pureStateMixture d m₂ ψ) V x hM hn hγ hγ1 hρ hσ hV hs hgap
  exact ⟨hρ, hσ, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Qatlib.Concepts.CopyEvolution.Discriminate
