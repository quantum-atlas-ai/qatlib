/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# AdiabBounds06 — explicit gap-bound expressions (Theorem 3, Theorem 4)

Source: Jansen–Seiler–Ruskai, *Bounds for the adiabatic approximation with
applications to quantum computation*, fixed **arXiv:quant-ph/0603175v3 (8 Nov 2007)**,
Theorem 3 p. 4–5 and Theorem 4 p. 5.

This file only records the paper's explicit `A(s)` bound expressions (`upperBound`,
`A_gap`, `A_gap4`) as definitions, so that later work can state the theorems against
a stable interface.  The asymptotic statements themselves (Eq. (6) with these
`A(s)`) are **not** formalized here: they depend on the Volterra iteration of
Lemmas 3, 4 and the chain of estimates of Lemma 8, which are outside the scope of
the present formalization.  No theorem about these expressions is asserted.

Boundary: finite-dimensional matrices; definitions only.
-/

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder Interval

namespace Qatlib.Papers.AdiabBounds06.MainResults

open Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

/-- The paper's "upper bound" notation `f|u.b. = f(0) + f(s)`. -/
def upperBound (f : ℝ → ℝ) (s : ℝ) : ℝ := f 0 + f s

/-- `A(s)` of Theorem 3, in the explicit upper-bound form
`(1/τ)(m‖Ḣ‖/g²)|u.b. + (1/τ)∫₀^s (m‖Ḧ‖/g² + 7m√m ‖Ḣ‖²/g³)`. -/
def A_gap (τ : ℝ) (m g : ℝ → ℝ)
    (Hdot Hddot : ℝ → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : ℝ :=
  (1 / τ) * upperBound (fun u => m u * ‖Hdot u‖ / (g u) ^ 2) s
  + (1 / τ) * ∫ t in (0 : ℝ)..s,
      (m t * ‖Hddot t‖ / (g t) ^ 2
        + 7 * m t * Real.sqrt (m t) * ‖Hdot t‖ ^ 2 / (g t) ^ 3)

/-- `A(s)` of Theorem 4: the leading `(mh/(τg²))|u.b.` term plus a `C/τ²` remainder
transcribed from the rendered display (the exact powers `h²/g^k` are OCR-ambiguous). -/
def A_gap4 (τ C : ℝ) (m g h : ℝ → ℝ) (s : ℝ) : ℝ :=
  (1 / τ) * upperBound (fun u => m u * h u / (g u) ^ 2) s
  + (C / τ ^ 2) *
      (upperBound (fun u => (h u) ^ 2 / (g u) ^ 4) s
        + (h 0) ^ 2 / (g 0) ^ 2
        + ∫ t in (0 : ℝ)..s, ((h t) ^ 2 / (g t) ^ 3 + (h t) ^ 2 / (g t) ^ 5))

end Qatlib.Papers.AdiabBounds06.MainResults
