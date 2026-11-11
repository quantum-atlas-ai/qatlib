/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.TwoSpeciesCopyPhaseReadout

/-!
# Specification of two-species discrimination identities

This module defines `TwoSpeciesDiscriminationSubgoal`, a proposition collecting the spectral and
finite-copy properties used for discrimination of two uniform training mixtures. It compares QPE
event masses with the spectral mixture of kernels at phases `-x j / 2` and specifies an error at
most `32 * (M - 1) * π ^ 2 / n` together with resource counts.

The proposition also records pure-state reconstruction, squared-overlap weights, the Hermitian
idempotent positive spectral projector, its Born probability, spectral magnitude bounds, and
orthogonality at eigenvalues `±1`. These are ingredients of the copy-based discrimination
application in [LloydMohseniRebentrost2014].

## Main statements

* `TwoSpeciesDiscriminationSubgoal`: the combined finite-copy event and spectral-identity
  specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.Discriminate

open Matrix

set_option autoImplicit false

/-- The proposition collecting finite-copy QPE event accuracy and resources for two uniform
training mixtures, together with basis and Born-weight identities. It also requires a
positive spectral projector, spectral magnitude bounds, and orthogonality at difference
eigenvalues `±1`. -/
def TwoSpeciesDiscriminationSubgoal : Prop :=
  ∀ (d m M n : ℕ) (φ ψ : Fin m → QState (Fin d)),
    (∀ i, Normalized (φ i)) → (∀ i, Normalized (ψ i)) → 0 < m → 2 ≤ M → 0 < n →
    ∀ (V : Operator d), V ∈ Matrix.unitaryGroup (Fin d) ℂ →
    ∀ (x : Fin d → ℝ),
      pureStateMixture d m φ - pureStateMixture d m ψ =
        V * Matrix.diagonal (fun j => (x j : ℂ)) * Vᴴ →
      ∀ (χ : QState (Fin d)), Normalized χ →
      ∀ (E : Finset (Fin M)),
        |(∑ z ∈ E, copyQPELabelMass d M
            (twoSpeciesQPEOutput d M n (pureStateMixture d m φ)
              (pureStateMixture d m ψ) (outerProduct χ)) z) -
          (∑ j, ((Vᴴ * outerProduct χ * V) j j).re *
            (∑ z ∈ E, ‖qpeKernel M (-x j / 2) z‖ ^ 2))| ≤
          32 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) ∧
        twoSpeciesQPEResources M n =
          (2 * (M - 1) * n, 2 * (M - 1) * n, 2 * (M - 1) * n, 0) ∧
        outerProduct χ = V * Matrix.of (fun j k =>
          Inner (fun a => V a j) χ * star (Inner (fun a => V a k) χ)) * Vᴴ ∧
        (∀ j, ((Vᴴ * outerProduct χ * V) j j).re = ‖Inner (fun a => V a j) χ‖ ^ 2) ∧
        (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), outerProduct (fun a => V a j)) *
            (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), outerProduct (fun a => V a j)) =
          (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), outerProduct (fun a => V a j)) ∧
        (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), outerProduct (fun a => V a j))ᴴ =
          (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), outerProduct (fun a => V a j)) ∧
        (Matrix.trace ((∑ j ∈ Finset.univ.filter (fun j => 0 < x j),
            outerProduct (fun a => V a j)) * outerProduct χ)).re =
          ∑ j ∈ Finset.univ.filter (fun j => 0 < x j), ‖Inner (fun a => V a j) χ‖ ^ 2 ∧
        (∀ j, |x j| ≤ 1) ∧
        (∀ j, x j = 1 → ∀ i, Inner (ψ i) (fun a => V a j) = 0) ∧
        (∀ j, x j = -1 → ∀ i, Inner (φ i) (fun a => V a j) = 0)

end Qatlib.Concepts.CopyEvolution.Discriminate
