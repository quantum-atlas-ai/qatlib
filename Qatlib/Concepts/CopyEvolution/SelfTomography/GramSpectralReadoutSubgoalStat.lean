/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyPureReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopySpectralReadout

/-!
# The Gram spectral-readout specification

This module defines `GramSpectralReadoutSubgoal`, the eventwise accuracy and resource
specification for fresh-copy QPE on a Gram density operator. The comparison law weights QPE
kernel probabilities by the eigenvalues in a unitary spectral decomposition.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `GramSpectralReadoutSubgoal`: error at most `8 * (M - 1) * π² / n` and exact fresh-copy
  resource counts.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix

/-- The proposition that fresh-copy QPE on a normalized Gram density operator approximates every
spectral label event within `8 * (M - 1) * π² / n`, using `(M - 1) * n` copies, gates, and
discards. -/
def GramSpectralReadoutSubgoal : Prop :=
  ∀ (r d M n : ℕ) (ψ : Fin r → QState (Fin d)), (∀ i, Normalized (ψ i)) →
    ∀ (w : Fin r → ℝ), (∀ i, 0 ≤ w i) → (∑ i, (w i) ^ 2 = 1) →
    2 ≤ M → 0 < n →
    ∀ (V : Operator r), V ∈ Matrix.unitaryGroup (Fin r) ℂ →
    ∀ (eig : Fin r → ℝ),
      gramMatrix ψ w = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ →
      ∀ (E : Finset (Fin M)),
        |(∑ z ∈ E, copyQPELabelMass r M (copyQPEOutput r M n (gramMatrix ψ w)) z) -
            (∑ i, eig i * (∑ z ∈ E, ‖qpeKernel M (-eig i / 2) z‖ ^ 2))| ≤
          8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) ∧
        copyQPEResources r M n = ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0)

end Qatlib.Concepts.CopyEvolution.SelfTomography
