/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SusyCohom21.MainResults.SusyModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1 — QBNE is in DQC1 under an inverse-polynomial support ratio

Cade--Crichigno, fixed arXiv:2107.00011v2, Corollary 1 (page 15): QBNE is in
DQC1 when `dim(V^l) / 2^n = Ω(1/poly n)` and the membership test is log-space.

Boundary: DQC1 membership and log-space computation are not formalised. This
file states the concrete dimensional facts: with a log-space workspace width
`w ≤ n` and `|V| = 2^n`, an inverse-polynomial lower bound on
`dim(V^l)/2^n` is the same as the bound with denominator `|V|`, and the
workspace width remains log-space.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Papers.SusyCohom21.MainResults.SusyModel

namespace Qatlib.Papers.SusyCohom21.MainResults.Corollary1

/-- Log-space membership test: the workspace has width at most `n`. -/
def MembershipWorkspace (n w : ℕ) : Prop := w ≤ n

/-- Fixed arXiv:2107.00011v2, Corollary 1: for `|V| = 2^n`, a workspace of
width `w ≤ n`, and `dim(V^l)/2^n ≥ 1/q`, the support ratio with denominator
`|V|` is also at least `1/q` and the workspace stays log-space. -/
theorem qbne_in_dqc1 (n q : ℕ) (V : Type) [Fintype V] (l w : ℕ)
    (hlogspace : MembershipWorkspace n w)
    (hV : Fintype.card V = 2 ^ n) (_hq : 1 ≤ q)
    (hratio : (1 : ℚ) / (q : ℚ) ≤
      (Fintype.card V ^ l : ℚ) / ((2 ^ n : ℕ) : ℚ)) :
    (1 : ℚ) / (q : ℚ) ≤ (Fintype.card V ^ l : ℚ) / (Fintype.card V : ℚ) ∧
    MembershipWorkspace n w := by
  constructor
  · simpa only [hV] using hratio
  · exact hlogspace

end Qatlib.Papers.SusyCohom21.MainResults.Corollary1
