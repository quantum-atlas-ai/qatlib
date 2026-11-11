/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUContracts

/-!
# Deferred signed LCU contracts

This module defines the legacy deferred circuit `cwProtocol`, its output `cwOutput`, and the
Born mass `cwFailureProb` outside the all-zero ancilla outcome. The construction groups positive
and negative coefficients into chains, then combines the positive chain with the negated
negative chain, following the signed LCU setting of Theorem 3 in [ChildsWiebe2012].

`Theorem3LCUFiber` and `Theorem3LCUFailure` are proposition contracts specifying the desired
success amplitude and failure estimate for these legacy definitions.

## Main statements

- `chainGate`, `chainFold`, and `chainCircuit` define the legacy weighted chain construction.
* `cwChainList` assigns coefficient terms to ancilla positions, and `cwProtocol` combines the
  two sign groups.
* `Theorem3LCUFiber` specifies the signed sum divided by total absolute coefficient mass on the
  zero ancilla fiber.
* `Theorem3LCUFailure` specifies the bound `k * Δ^2 / 4 + 4 * R / (R + 1)^2`, where `R` is the
  positive-to-negative coefficient mass ratio.

## References

- [Childs and Wiebe, 2012][ChildsWiebe2012], Theorem 3.
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Defines one legacy LCU level combining the accumulated circuit with the lifted system
matrix, using `vKappa (W / w)` on the selected ancilla bit. -/
noncomputable def chainGate (k : ℕ) (bit : Fin k) (W w : ℝ)
    (acc : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) (U : Matrix I I ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  lcuLevelGate k bit (vKappa (W / w)) acc (liftSys k U)

/-- Folds a list of legacy weighted LCU levels, adding each weight to the running total and
updating the accumulator to `chainGate k bit W w acc U * acc`. -/
noncomputable def chainFold (k : ℕ) (W : ℝ)
    (acc : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    List (Fin k × (ℝ × Matrix I I ℂ)) → Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ
  | [] => acc
  | (bit, w, U) :: rest =>
      chainFold k (W + w) (chainGate k bit W w acc U * acc) rest

/-- Builds the legacy chain from the first lifted system matrix and its weight, using the
identity for an empty list. -/
noncomputable def chainCircuit (k : ℕ) :
    List (Fin k × (ℝ × Matrix I I ℂ)) → Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ
  | [] => 1
  | (_bit, w, U) :: rest => chainFold k w (liftSys k U) rest

/-- Lists the weighted matrices indexed by `S`, assigning the term at list position `j` to
ancilla bit `(off + j) % (k + 1)`. -/
noncomputable def cwChainList (k off : ℕ) (wt : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ)
    (S : Finset (Fin (k+1))) : List (Fin (k+1) × (ℝ × Matrix I I ℂ)) :=
  S.toList.mapIdx fun j q =>
    (⟨(off + j) % (k+1), Nat.mod_lt _ (Nat.succ_pos k)⟩, (wt q, U q))

/-- Defines the legacy signed LCU circuit by combining the positive-coefficient chain with the
negated absolute-weight negative chain, using the ratio of their masses as the rotation
parameter. -/
noncomputable def cwProtocol (k : ℕ) (c : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ) :
    Matrix ((Fin (k+1) → Bool) × I) ((Fin (k+1) → Bool) × I) ℂ :=
  let a := (Finset.univ.filter fun q : Fin (k+1) => 0 < c q).card
  let sPos := ∑ q : Fin (k+1), if 0 < c q then c q else 0
  let sNeg := ∑ q : Fin (k+1), if c q < 0 then |c q| else 0
  lcuLevelGate (k+1) ⟨a % (k+1), Nat.mod_lt _ (Nat.succ_pos k)⟩ (vKappa (sPos / sNeg))
    (chainCircuit (k+1) (cwChainList k 0 c U (Finset.univ.filter fun q => 0 < c q)))
    (-(chainCircuit (k+1) (cwChainList k a (fun q => |c q|) U
      (Finset.univ.filter fun q => c q < 0))))

/-- The all-zero Boolean ancilla string on `k + 1` bits. -/
def cwZero (k : ℕ) : Fin (k+1) → Bool := fun _ => false

/-- Applies the legacy signed LCU protocol to the tensor product of the zero ancilla basis state
and the system input `ψ`. -/
noncomputable def cwOutput (k : ℕ) (c : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ)
    (ψ : QState I) : QState ((Fin (k+1) → Bool) × I) :=
  ApplyGate (cwProtocol k c U) (TensorState (Ket (cwZero k)) ψ)

/-- The Born mass of the legacy output on all ancilla strings other than `cwZero k`, summed over
every system outcome. -/
noncomputable def cwFailureProb (k : ℕ) (c : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ)
    (ψ : QState I) : ℝ :=
  MeasureProb (cwOutput k c U ψ)
    (((Finset.univ (α := Fin (k+1) → Bool)).erase (cwZero k)) ×ˢ Finset.univ)

/-- The contract requiring the legacy zero ancilla fiber to equal the signed matrix sum applied
to any input, divided by total absolute coefficient mass. It specifies a Theorem 3 property
of [ChildsWiebe2012] under unitary payloads, nonzero coefficients of both signs, and `1 ≤
k`. -/
def Theorem3LCUFiber : Prop :=
  ∀ (k : ℕ) (I : Type) [Fintype I] [DecidableEq I], 1 ≤ k →
    ∀ (U : Fin (k+1) → Matrix I I ℂ), (∀ q, U q ∈ Matrix.unitaryGroup I ℂ) →
      ∀ (c : Fin (k+1) → ℝ), (∀ q, c q ≠ 0) → (∃ q, 0 < c q) → (∃ q, c q < 0) →
        ∀ ψ : QState I, ∀ x : I,
          cwOutput k c U ψ (cwZero k, x)
            = (((∑ q, c q • U q)) *ᵥ ψ) x / (∑ q, |c q|)

/-- The contract requiring legacy failure probability to be at most `k * Δ^2 / 4 + 4 * R / (R +
1)^2`, with `R` the positive-to-negative coefficient mass ratio. Its hypotheses include
normalized input, unitary payloads, nonzero coefficients of both signs, and the uniform
pairwise squared-distance bound of Theorem 3 in [ChildsWiebe2012]. -/
def Theorem3LCUFailure : Prop :=
  ∀ (k : ℕ) (I : Type) [Fintype I] [DecidableEq I], 1 ≤ k →
    ∀ (U : Fin (k+1) → Matrix I I ℂ), (∀ q, U q ∈ Matrix.unitaryGroup I ℂ) →
      ∀ (c : Fin (k+1) → ℝ), (∀ q, c q ≠ 0) → (∃ q, 0 < c q) → (∃ q, c q < 0) →
        ∀ Δ : ℝ, 0 ≤ Δ →
          (∀ q q' : Fin (k+1), ∀ φ : QState I, Normalized φ →
            (∑ x : I, ‖((U q - U q') *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
          ∀ ψ : QState I, Normalized ψ →
            cwFailureProb k c U ψ ≤
              (k : ℝ) * Δ ^ 2 / 4
                + 4 * ((∑ q, if 0 < c q then c q else 0) / (∑ q, if c q < 0 then |c q| else 0))
                    / ((∑ q, if 0 < c q then c q else 0) / (∑ q, if c q < 0 then |c q| else 0)
                      + 1) ^ 2

end Qatlib.Papers.HamLCUSim12.LCUDeferred
