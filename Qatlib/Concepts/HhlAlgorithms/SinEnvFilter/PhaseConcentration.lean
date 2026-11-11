/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.AppendixA3PhaseConcentrationHarr

/-!
# Phase concentration for the sine-envelope kernel

The `source_A3` theorems expose the sine-envelope kernel's geometric identity, normalization,
fourth-power tail, and bounded scaled second moment. `source_appendixA3_phase_concentration`
combines these results into the proposition associated with Appendix A.3 of
[HarrowHassidimLloyd2009].

## Main statements

* `source_A3_kernel_far_label_tail`: the far-label probability decays as inverse fourth power of
  circular phase distance.
* `source_A3_kernel_second_moment`: the scaled error has a uniform explicit second-moment bound.
* `source_appendixA3_phase_concentration`: the combined concentration specification holds.

## References

* [Harrow et al., 2009, Appendix A.3][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.PhaseConcentration

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open scoped Real

/-- Away from the two exceptional geometric ratios, the sine-envelope kernel is the stated
difference of shifted geometric sums; see [Harrow et al., Appendix
A.3][HarrowHassidimLloyd2009]. -/
theorem source_A3_kernel_geometric_identity (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hp : Complex.exp (Complex.I * (sinEnvelopeDelta M φ z + Real.pi) / (M : ℝ)) ≠ 1)
    (hm : Complex.exp (Complex.I * (sinEnvelopeDelta M φ z - Real.pi) / (M : ℝ)) ≠ 1) :
    sinEnvelopeKernel M φ z =
      ((Real.sqrt 2 : ℂ) / (2 * Complex.I * (M : ℝ))) *
        (Complex.exp (Complex.I * Real.pi / (2 * (M : ℝ))) *
            sinEnvelopeGeoSum M (sinEnvelopeDelta M φ z + Real.pi) -
          Complex.exp (-(Complex.I * Real.pi / (2 * (M : ℝ)))) *
            sinEnvelopeGeoSum M (sinEnvelopeDelta M φ z - Real.pi)) :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_geometric_identity
    M φ z hM hp hm

/-- For `M ≥ 2`, the squared moduli of the sine-envelope phase-estimation kernel sum to one; see
[Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem source_A3_kernel_normalized (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖ ^ 2 = 1 :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_normalized
    M φ hM

/-- At circular phase distance at least `1 / M`, the kernel probability is at most `10 / (M^4 *
phaseDistance^4)`; see [Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem source_A3_kernel_far_label_tail (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hr : 1 / (M : ℝ) ≤ phaseDistance φ ((z.val : ℝ) / (M : ℝ))) :
    ‖sinEnvelopeKernel M φ z‖ ^ 2 ≤
      10 / ((M : ℝ) ^ 4 * phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ^ 4) :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_far_label_tail
    M φ z hM hr

/-- The kernel's second moment in the scaled circular phase error is at most `4 * π^2 + 40 * π^4
/ 3`; see [Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem source_A3_kernel_second_moment (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖ ^ 2 *
        (2 * Real.pi * (M : ℝ) * phaseDistance φ ((z.val : ℝ) / (M : ℝ))) ^ 2 ≤
      4 * Real.pi ^ 2 + 40 * Real.pi ^ 4 / 3 :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_second_moment
    M φ hM

/-- Packages the kernel identity, normalization, tail, and second-moment estimates as
`AppendixA3PhaseConcentration`; see [Harrow et al., Appendix A.3][HarrowHassidimLloyd2009]. -/
theorem source_appendixA3_phase_concentration : AppendixA3PhaseConcentration :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.appendixA3PhaseConcentration

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.PhaseConcentration
