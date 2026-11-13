/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Contracts for two-unitary linear combinations

This module defines the original matrix-level register operators and proposition contracts
associated with Lemma 2 of [ChildsWiebe2012]. `lemma2Circuit` combines the register-masked
operators `rotGate` and `ctrlGate`, and `lemma2FailureProb` sums the mass of the designated
failure branch.

`Lemma2Fiber`, `Lemma2NearbyFailure`, `Lemma2NearbyFailureCrude`, and `Lemma2CircuitUnitary`
specify desired identities and bounds for these definitions.

## Main statements

* `Lemma2Fiber`: specifies the two output fibers.
* `Lemma2NearbyFailure`: specifies a failure bound from a uniform unitary-difference estimate.
* `Lemma2CircuitUnitary`: specifies unitarity of the original circuit definition.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real symmetric two-by-two matrix with diagonal entries `sqrt (κ / (κ + 1))` and its
negative, and off-diagonal entries `1 / sqrt (κ + 1)`. -/
noncomputable def vKappa (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b b' =>
    ((if b = 0 then
        (if b' = 0 then Real.sqrt (κ / (κ + 1)) else (Real.sqrt (κ + 1))⁻¹)
      else
        (if b' = 0 then (Real.sqrt (κ + 1))⁻¹ else -(Real.sqrt (κ / (κ + 1)))) : ℝ) : ℂ)

/-- Lifts a system matrix to the joint register by preserving the entire Boolean ancilla string. -/
noncomputable def liftSys (k : ℕ) (U : Matrix I I ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then U p.2 q.2 else 0

/-- The register-masked matrix whose entry is the selected-bit entry of `V` when the entire
input and output ancilla strings agree, and zero otherwise. -/
noncomputable def rotGate (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then V (if p.1 i then 1 else 0) (if q.1 i then 1 else 0) else 0

/-- The matrix selecting `Cx` or `Cy` according to the selected output bit, with entries masked
to equal input and output ancilla strings. -/
noncomputable def ctrlGate (k : ℕ) (i : Fin k)
    (Cx Cy : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 i then Cy else Cx) p q else 0

/-- Composes `rotGate` for `V`, the register-masked controlled matrix, and `rotGate` for the
adjoint of `V`. -/
noncomputable def lcuLevelGate (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  rotGate k i Vᴴ * (ctrlGate k i Cx Cy * rotGate k i V)

/-- The one-ancilla circuit expression obtained from `lcuLevelGate`, `vKappa`, and the lifted
system matrices `Ua` and `Ub`. -/
noncomputable def lemma2Circuit (κ : ℝ) (Ua Ub : Matrix I I ℂ) :
    Matrix ((Fin 1 → Bool) × I) ((Fin 1 → Bool) × I) ℂ :=
  lcuLevelGate 1 ⟨0, by omega⟩ (vKappa κ) (liftSys 1 Ua) (liftSys 1 Ub)

/-- The singleton ancilla outcome consisting of the constant true bit string. -/
def lemma2FailSet : Finset (Fin 1 → Bool) :=
  {(fun _ => true : Fin 1 → Bool)}

/-- The state produced by `lemma2Circuit` from the constant false ancilla and the input system
state. -/
noncomputable def lemma2Output (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) :
    QState ((Fin 1 → Bool) × I) :=
  ApplyGate (lemma2Circuit κ Ua Ub) (TensorState (Ket (fun _ => false)) ψ)

/-- The measurement mass of `lemma2Output` on the constant true ancilla outcome, summed over all
system indices. -/
noncomputable def lemma2FailureProb (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) : ℝ :=
  MeasureProb (lemma2Output κ Ua Ub ψ) (lemma2FailSet ×ˢ Finset.univ)

/-- The proposition specifying a weighted-sum false-ancilla fiber and a `sqrt κ / (κ + 1)`
multiple of `(Ua - Ub)` on the true-ancilla fiber for the original circuit. -/
def Lemma2Fiber : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I,
        (∀ x : I, lemma2Output κ Ua Ub ψ (fun _ => false, x)
            = ((((κ : ℂ) / (κ + 1)) • Ua + (((1 : ℂ) / (κ + 1)) • Ub)) *ᵥ ψ) x)
        ∧ (∀ x : I, lemma2Output κ Ua Ub ψ (fun _ => true, x)
            = (((((Real.sqrt κ / (κ + 1) : ℝ) : ℂ)) • (Ua - Ub)) *ᵥ ψ) x)

/-- The proposition bounding the original circuit failure mass by `κ * Δ ^ 2 / (κ + 1) ^ 2` when
`(Ua - Ub)` has squared norm at most `Δ ^ 2` on every normalized input. -/
def Lemma2NearbyFailure : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ Δ : ℝ, 0 ≤ Δ →
        (∀ φ : QState I, Normalized φ → (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
        ∀ ψ : QState I, Normalized ψ →
          lemma2FailureProb κ Ua Ub ψ ≤ κ * Δ ^ 2 / (κ + 1) ^ 2

/-- The proposition bounding the original circuit failure mass by `4 * κ / (κ + 1) ^ 2` for
nonnegative `κ`, unitary branches, and normalized inputs. -/
def Lemma2NearbyFailureCrude : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I, Normalized ψ →
        lemma2FailureProb κ Ua Ub ψ ≤ 4 * κ / (κ + 1) ^ 2

/-- The proposition that the original one-ancilla circuit is unitary for nonnegative `κ` and
unitary system branches. -/
def Lemma2CircuitUnitary : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      lemma2Circuit κ Ua Ub ∈ Matrix.unitaryGroup ((Fin 1 → Bool) × I) ℂ

end Qatlib.Papers.HamLCUSim12.LCUDeferred
