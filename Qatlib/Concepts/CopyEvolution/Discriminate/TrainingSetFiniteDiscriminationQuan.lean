/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationStat
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan

/-!
# Finite-copy discrimination of training mixtures

This module proves `TrainingSetFiniteDiscrimination` for two nonempty families of normalized
states, allowing different training-set sizes. Their uniform mixtures are density operators, and
a spectral gap for their difference gives a finite-copy discrimination success lower bound equal
to the Helstrom value minus `twoSpeciesSignErrorBudget`.

The proof specializes finite-copy Helstrom discrimination to these mixtures and retains the
explicit QPE resource tuple. This formalizes the training-set application described in
[LloydMohseniRebentrost2014].

## Main statements

* `trainingSetFiniteDiscrimination`: density mixtures, finite-copy discrimination success, and
  resource counts.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

/-- Finite-copy discrimination of the uniform mixtures of two nonempty normalized training sets
achieves the Helstrom value up to `twoSpeciesSignErrorBudget`, under the stated spectral
gap, with the specified resources. This implements the training-set discrimination
application of [LloydMohseniRebentrost2014]. -/
theorem trainingSetFiniteDiscrimination : TrainingSetFiniteDiscrimination := by
  intro d m₁ m₂ M n γ φ ψ V x hm₁ hm₂ hM hn hγ hγ1 hφ hψ hV hs hgap
  have hρ := pureStateMixture_density d m₁ φ hφ hm₁
  have hσ := pureStateMixture_density d m₂ ψ hψ hm₂
  have h := finiteCopyHelstromDiscrimination d M n γ (pureStateMixture d m₁ φ)
    (pureStateMixture d m₂ ψ) V x hM hn hγ hγ1 hρ hσ hV hs hgap
  exact ⟨hρ, hσ, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Qatlib.Concepts.CopyEvolution.Discriminate
