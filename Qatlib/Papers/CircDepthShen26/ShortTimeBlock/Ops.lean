/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Shared operators for the short-time block construction

Fixed source: arXiv:2610.01839v2, Section 2 (ordered local products, Eqs. (22)-(23))
and Eq. (88) (record fields).  This file collects the operators and the bookkeeping
structures used by the construction-level claims of `ShortTimeBlock`, so that the
per-claim modules can state their conclusions without repeating definitions.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped BigOperators

/-- The ordered product `D(y_{N-1}) ⋯ D(y_0)` of Eq. (23). -/
def orderedProduct {v N : ℕ} {Y : Type*}
    (D : Y → Matrix (Fin v) (Fin v) ℂ) (y : Fin N → Y) :
    Matrix (Fin v) (Fin v) ℂ :=
  ((List.ofFn (fun u : Fin N => D (y u))).reverse).prod

/-- The stage product of Eq. (22): the last product-formula stage acts first. -/
def stageProduct {v L : ℕ} (V : Fin L → Matrix (Fin v) (Fin v) ℂ) :
    Matrix (Fin v) (Fin v) ℂ :=
  ((List.ofFn V).reverse).prod

/-- Block-diagonal assembly of ordered local products over a basis of records:
the `(r, x) → (r', y)` entry is the ordered product for the record `r` when
`r = r'`, and zero otherwise.  This is the action of Lemma 6/Corollary 13 on
the data register, with the record register left in its basis value. -/
def recordsBlockDiag {v N : ℕ} {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : Y → Matrix (Fin v) (Fin v) ℂ) :
    Matrix ((Fin N → Y) × Fin v) ((Fin N → Y) × Fin v) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then orderedProduct D p.1 p.2 q.2 else 0

/-- The action of Lemma 6 (Eq. (23)): the ordered data product dressed with the
record-dependent phase `e^{i ∑_u φ(y_u)}`. -/
def recordsBlockDiagPhase {v N : ℕ} {Y : Type*} [Fintype Y] [DecidableEq Y]
    (φ : Y → ℝ) (D : Y → Matrix (Fin v) (Fin v) ℂ) :
    Matrix ((Fin N → Y) × Fin v) ((Fin N → Y) × Fin v) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then
      Complex.exp (Complex.I * (((∑ u : Fin N, φ (p.1 u) : ℝ) : ℂ))) *
        orderedProduct D p.1 p.2 q.2
    else 0

/-- The fixed local circuit assumptions of Eq. (21): an insertion stage plus a
fixed number `L` of product-formula stages.  The paper fixes one such local
implementation for the whole construction; its number of stages is the only
combinatorial parameter used by the global compilation bounds. -/
structure LocalCircuitAssumptions where
  /-- Number of product-formula stages `L` in the local block. -/
  stages : ℕ
  /-- The local product formula has at least one stage. -/
  stages_pos : 0 < stages

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
