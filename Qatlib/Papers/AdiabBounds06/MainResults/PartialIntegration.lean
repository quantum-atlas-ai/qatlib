/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.Twiddle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# AdiabBounds06 — Volterra iterates (Lemma 4 interface)

Source: Jansen–Seiler–Ruskai, *Bounds for the adiabatic approximation with
applications to quantum computation*, fixed **arXiv:quant-ph/0603175v3 (8 Nov 2007)**,
Lemma 4 p. 8.

This file records only the recursive Volterra-iterate construction `A_j` of Lemma 4
as a definition, so that later work can state the `O(1/τ^m)` estimate against a
stable interface.  The partial-integration identity (Lemma 3) and the asymptotic
estimate of Lemma 4 are **not** formalized here; they require Bochner/interval
integral calculus and the differentiation of `U_τ^A(s)† X(s) U_τ^A(s)`, which are
outside the scope of the present formalization.  No theorem is asserted.

Boundary: finite-dimensional matrices; definition only.
-/

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder Interval

namespace Qatlib.Papers.AdiabBounds06.MainResults

open Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

/-- The nested Volterra integral `A_j` of Lemma 4, defined by recursion on the list of
kernels `[X₁, …, X_j]`.  The innermost factor is `P₀ Ω(u) P₀`, and each level inserts
`Q₀` and integrates from `0` to the current upper limit. -/
def volterraIterate (Q0 P0 : Matrix (Fin n) (Fin n) ℂ)
    (Omega : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    List (ℝ → Matrix (Fin n) (Fin n) ℂ) → ℝ → Matrix (Fin n) (Fin n) ℂ
  | [], u => P0 * Omega u * P0
  | f :: fs, u => Q0 * ∫ s in (0 : ℝ)..u, f s * volterraIterate Q0 P0 Omega fs s

end Qatlib.Papers.AdiabBounds06.MainResults
