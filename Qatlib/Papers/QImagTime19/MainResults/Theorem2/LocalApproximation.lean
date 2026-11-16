/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Papers.QImagTime19.MainResults.LinearSpaceStep
public import Qatlib.Papers.QImagTime19.MainResults.QLanczosBound.QLanczosVariational
public import Qatlib.Papers.QImagTime19.MainResults.SourceModel

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open Qatlib.Papers.QImagTime19.MainResults

namespace Qatlib.Papers.QImagTime19.MainResults

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The qubit count of Theorem 2, Eq. (37), written in the literal paper form
`k(2C)^d ln^d(2√2 n (|S| + C ln^d(8nC(2C)^{d+1}ε^{-1})))` is the same real
number as `k ν^d` with `ν` the width `theorem2DomainWidth`. -/
theorem theorem2QubitCount_paper_form (k : ℕ) (C : ℝ) (d n S : ℕ) (ε : ℝ) :
    (k : ℝ) * (theorem2DomainWidth C d n S ε) ^ d =
      (k : ℝ) * (2 * C) ^ d *
        (Real.log (2 * Real.sqrt 2 * (n : ℝ) *
          ((S : ℝ) + C * (Real.log (8 * (n : ℝ) * C * (2 * C) ^ (d + 1) / ε)) ^ d))) ^ d := by
  rw [theorem2DomainWidth, mul_pow]
  ring

/-- Reindex a density matrix along a relabelling of the register. -/
def reindexMatrix {κ : Type*} (e : ι ≃ κ) (ρ : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  fun i j => ρ (e.symm i) (e.symm j)

/-- The trace-distance closeness of reduced states on every region of at most
`S` sites (Eq. (38)).  A region is modelled abstractly by a factor `α` of the
register (`ι ≃ α × β`) with `Fintype.card α ≤ S`; connectedness of the region
in the paper is a geometric property of the concrete register and is not used
by the estimate. -/
def ReducedTraceDistanceLe (ψ φ : State ι) (S : ℕ) (ε : ℝ) : Prop :=
  ∀ (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : ι ≃ α × β), Fintype.card α ≤ S →
    traceDist (partialTraceRight (reindexMatrix e (pureDensity ψ)))
      (partialTraceRight (reindexMatrix e (pureDensity φ))) ≤ ε

end

end Qatlib.Papers.QImagTime19.MainResults
