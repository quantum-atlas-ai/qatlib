/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

/-!
# Sine-envelope phase-concentration specification

`AppendixA3PhaseConcentration` states the geometric-sum identity, normalization, fourth-power
probability tail, and explicit scaled second-moment bound for the sine-envelope kernel. It
provides a single proposition for the phase-estimation estimates associated with Appendix A.3 of
[HarrowHassidimLloyd2009].

## Main statements

* `AppendixA3PhaseConcentration`: the conjunction of the four kernel properties.

## References

* [Harrow et al., 2009, Appendix A.3][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix
open scoped Real

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

/-- The conjunction of the sine-envelope kernel's geometric identity, normalization,
fourth-power tail estimate, and explicit second-moment bound corresponding to [Harrow et
al., Appendix A.3][HarrowHassidimLloyd2009]. -/
def AppendixA3PhaseConcentration : Prop :=
  (∀ (M : ℕ) (φ : ℝ) (z : Fin M), 2 ≤ M →
      Complex.exp (Complex.I * (sinEnvelopeDelta M φ z + Real.pi) / (M : ℝ)) ≠ 1 →
      Complex.exp (Complex.I * (sinEnvelopeDelta M φ z - Real.pi) / (M : ℝ)) ≠ 1 →
      sinEnvelopeKernel M φ z =
        ((Real.sqrt 2 : ℂ) / (2 * Complex.I * (M : ℝ))) *
          (Complex.exp (Complex.I * Real.pi / (2 * (M : ℝ))) *
              sinEnvelopeGeoSum M (sinEnvelopeDelta M φ z + Real.pi) -
            Complex.exp (-(Complex.I * Real.pi / (2 * (M : ℝ)))) *
              sinEnvelopeGeoSum M (sinEnvelopeDelta M φ z - Real.pi))) ∧
  (∀ (M : ℕ) (φ : ℝ), 2 ≤ M →
      ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖ ^ 2 = 1) ∧
  (∀ (M : ℕ) (φ : ℝ) (z : Fin M), 2 ≤ M →
      1 / (M : ℝ) ≤ phaseDistance φ ((z.val : ℝ) / (M : ℝ)) →
      ‖sinEnvelopeKernel M φ z‖ ^ 2 ≤
        10 / ((M : ℝ) ^ 4 * phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ^ 4)) ∧
  (∀ (M : ℕ) (φ : ℝ), 2 ≤ M →
      ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖ ^ 2 *
          (2 * Real.pi * (M : ℝ) * phaseDistance φ ((z.val : ℝ) / (M : ℝ))) ^ 2 ≤
        4 * Real.pi ^ 2 + 40 * Real.pi ^ 4 / 3)

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
