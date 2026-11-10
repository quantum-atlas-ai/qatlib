/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.AppendixA3PhaseConcentrationHarr
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

theorem source_A3_kernel_normalized (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖ ^ 2 = 1 :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_normalized
    M φ hM

theorem source_A3_kernel_far_label_tail (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hr : 1 / (M : ℝ) ≤ phaseDistance φ ((z.val : ℝ) / (M : ℝ))) :
    ‖sinEnvelopeKernel M φ z‖ ^ 2 ≤
      10 / ((M : ℝ) ^ 4 * phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ^ 4) :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_far_label_tail
    M φ z hM hr

theorem source_A3_kernel_second_moment (M : ℕ) (φ : ℝ) (hM : 2 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖ ^ 2 *
        (2 * Real.pi * (M : ℝ) * phaseDistance φ ((z.val : ℝ) / (M : ℝ))) ^ 2 ≤
      4 * Real.pi ^ 2 + 40 * Real.pi ^ 4 / 3 :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_second_moment
    M φ hM

theorem source_appendixA3_phase_concentration : AppendixA3PhaseConcentration :=
  Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.appendixA3PhaseConcentration

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.PhaseConcentration
