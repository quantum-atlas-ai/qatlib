/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourceClassicalEntryEstimation

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.ClassicalEstimation

/-- A classical procedure that outputs an approximate matrix entry together with the
declared classical effort; no execution relation is included. -/
structure ClassicalEstimator (N : ℕ) where
  /-- A proposed approximation of the `(i,j)` entry. -/
  estimate : Fin N → Fin N → ℂ
  /-- Unverified classical-effort annotation. -/
  cost : ℝ

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma14_classicalEntryEstimation`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma14_classicalEntryEstimation_statement
    (n K : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (f : ℝ → ℂ) (p : Polynomial ℝ) (ε : ℝ)
    (hs : 0 < s) (hε : 0 < ε) (hdeg : p.natDegree ≤ K)
    (happrox : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      ‖f x - ((p.eval x : ℝ) : ℂ)‖ ≤ ε)
    (i j : Fin (2 ^ n)) : Prop :=
    ∃ E : ClassicalEstimator (2 ^ n),
      PolyKPolyN E.cost K n ∧
      ‖E.estimate i j -
          hermFun h.A h.hermitian (fun y => f (y / (s : ℝ))) i j‖ ≤ ε

end Qatlib.Papers.FreeFermion24.MainResults.ClassicalEstimation
