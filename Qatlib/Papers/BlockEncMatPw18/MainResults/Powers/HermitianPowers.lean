/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# HermitianPowers

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Powers

/-- Legacy numeric resource metadata. No circuit or implementation relation is
contained in this record; specifications require a separate `Realizes` contract. -/
structure PowerCircuitCost where
  ancilla : ℕ
  cost : ℝ
  error : ℝ

/-- `κ ^ (1 + c)` as a real power, the scale appearing in Lemma 9. -/
def kappaPow (κ c : ℝ) : ℝ := Real.rpow κ (1 + c)

/-- **Statement only — not proved in Qatlib.** Resource specification for `lemma9_negative_powers`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def lemma9_negative_powers_statement
    (α : ℝ) (a : ℕ) (T_U κ c ε δ : ℝ)
    (hκ : 2 ≤ κ) (hc : 0 < c) (hε : 0 < ε)
    (hδ : δ < ε / (kappaPow κ c * (1 + c) *
      (Real.log (kappaPow κ c / ε)) ^ 3))
    (Realizes : PowerCircuitCost → Prop) : Prop :=
    ∃ (C : ℝ) (c' : PowerCircuitCost), Realizes c' ∧ 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (α * κ * ((a : ℝ) + T_U) * (1 + c) *
        (Real.log (kappaPow κ c / ε)) ^ 2)

/-- **Statement only — not proved in Qatlib.** Resource specification for `lemma10_positive_powers`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def lemma10_positive_powers_statement
    (α : ℝ) (a : ℕ) (T_U κ c ε δ : ℝ)
    (hκ : 2 ≤ κ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε)
    (hδ : δ < ε / (κ * (Real.log (κ / ε)) ^ 3))
    (Realizes : PowerCircuitCost → Prop) : Prop :=
    ∃ (C : ℝ) (c' : PowerCircuitCost), Realizes c' ∧ 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (α * κ * ((a : ℝ) + T_U) * (Real.log (κ / ε)) ^ 2)

/-- **Statement only — not proved in Qatlib.** Resource specification for `cor54_negative_powers_via_controlled_simulation`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def cor54_negative_powers_via_controlled_simulation_statement
    (κ c ε : ℝ) (a : ℕ) (hκ : 2 ≤ κ) (hc : 0 < c) (hε : 0 < ε)
    (Realizes : PowerCircuitCost → Prop) : Prop :=
    ∃ (C : ℝ) (c' : PowerCircuitCost), Realizes c' ∧ 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (κ * max 1 c * (Real.log (kappaPow κ c / ε)) ^ 2)

/-- **Statement only — not proved in Qatlib.** Resource specification for `cor55_positive_powers_via_controlled_simulation`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def cor55_positive_powers_via_controlled_simulation_statement
    (κ c ε : ℝ) (a : ℕ) (hκ : 2 ≤ κ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε)
    (Realizes : PowerCircuitCost → Prop) : Prop :=
    ∃ (C : ℝ) (c' : PowerCircuitCost), Realizes c' ∧ 0 < C ∧ c'.error ≤ ε ∧
      c'.cost ≤ C * (κ * Real.log (κ / ε) * Real.log (1 / ε))

end Qatlib.Papers.BlockEncMatPw18.MainResults.Powers
