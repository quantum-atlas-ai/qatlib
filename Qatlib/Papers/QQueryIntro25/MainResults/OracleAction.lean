/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QQueryIntro25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# OracleAction — Lemma 21 (basis action of the quantum oracle)

Fixed source: arXiv:2508.08852v1, Section 3.1 (printed p. 9).

Lemma 21 states `O_x |i,b⟩ = (1 − x_i)|i,b⟩ + x_i |i,b⊕1⟩`.  Since `x_i ∈ {0,1}`,
this says that the oracle flips the target qubit `b` exactly when `x_i = 1`; in
Boolean terms `|i,b⟩ ↦ |i, b ⊕ x_i⟩`.  The frozen library already proves the
amplitude-level action `applyGate_workspaceBitOracle_mk` and the single-qubit
action `applyGate_bitOracleOn_ket`; this module records the resulting basis-state
identity.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QQueryIntro25.MainResults

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- **Lemma 21, XOR form** (arXiv:2508.08852v1, printed p. 9).  On a basis state
`|i,b⟩` (with an arbitrary workspace register `w`), the quantum oracle to `x`
maps `|i,b⟩` to `|i, b ⊕ x_i⟩`. -/
theorem lemma21_oracle_action_xor (x : I → Bool) (i : I) (b : Bool) (w : W) :
    ApplyGate (workspaceBitOracle (W := W) x) (Ket (((i, b), w) : (I × Bool) × W)) =
      Ket (((i, b ^^ x i), w) : (I × Bool) × W) := by
  funext q
  obtain ⟨⟨j, c⟩, u⟩ := q
  rw [applyGate_workspaceBitOracle_mk]
  simp only [ket_apply]
  by_cases hu : u = w
  · subst hu
    by_cases hj : j = i
    · subst hj
      cases h : x j <;> simp [h]
    · simp [hj]
  · simp [hu]

/-- **Lemma 21** (arXiv:2508.08852v1, printed p. 9).  On a basis state `|i,b⟩`
(with an arbitrary workspace register `w`), the quantum oracle to `x` acts by
toggling the target qubit precisely when `x i = true`.  This is the Boolean form
of the paper's `(1 − x_i)|i,b⟩ + x_i |i,b⊕1⟩`, since `x_i ∈ {0,1}`: when
`x i = false` the state is unchanged and when `x i = true` the target bit is
flipped. -/
theorem lemma21_oracle_action (x : I → Bool) (i : I) (b : Bool) (w : W) :
    ApplyGate (workspaceBitOracle (W := W) x) (Ket (((i, b), w) : (I × Bool) × W)) =
      (if x i then Ket (((i, !b), w) : (I × Bool) × W)
       else Ket (((i, b), w) : (I × Bool) × W)) := by
  rw [lemma21_oracle_action_xor]
  cases h : x i <;> cases b <;> simp [h]

end Qatlib.Papers.QQueryIntro25.MainResults
