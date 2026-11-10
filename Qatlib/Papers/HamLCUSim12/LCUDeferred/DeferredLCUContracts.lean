/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUContracts
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

open Matrix

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def chainGate (k : ℕ) (bit : Fin k) (W w : ℝ)
    (acc : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) (U : Matrix I I ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  lcuLevelGate k bit (vKappa (W / w)) acc (liftSys k U)

noncomputable def chainFold (k : ℕ) (W : ℝ)
    (acc : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    List (Fin k × (ℝ × Matrix I I ℂ)) → Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ
  | [] => acc
  | (bit, w, U) :: rest =>
      chainFold k (W + w) (chainGate k bit W w acc U * acc) rest

noncomputable def chainCircuit (k : ℕ) :
    List (Fin k × (ℝ × Matrix I I ℂ)) → Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ
  | [] => 1
  | (_bit, w, U) :: rest => chainFold k w (liftSys k U) rest

noncomputable def cwChainList (k off : ℕ) (wt : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ)
    (S : Finset (Fin (k+1))) : List (Fin (k+1) × (ℝ × Matrix I I ℂ)) :=
  S.toList.mapIdx fun j q =>
    (⟨(off + j) % (k+1), Nat.mod_lt _ (Nat.succ_pos k)⟩, (wt q, U q))

noncomputable def cwProtocol (k : ℕ) (c : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ) :
    Matrix ((Fin (k+1) → Bool) × I) ((Fin (k+1) → Bool) × I) ℂ :=
  let a := (Finset.univ.filter fun q : Fin (k+1) => 0 < c q).card
  let sPos := ∑ q : Fin (k+1), if 0 < c q then c q else 0
  let sNeg := ∑ q : Fin (k+1), if c q < 0 then |c q| else 0
  lcuLevelGate (k+1) ⟨a % (k+1), Nat.mod_lt _ (Nat.succ_pos k)⟩ (vKappa (sPos / sNeg))
    (chainCircuit (k+1) (cwChainList k 0 c U (Finset.univ.filter fun q => 0 < c q)))
    (-(chainCircuit (k+1) (cwChainList k a (fun q => |c q|) U
      (Finset.univ.filter fun q => c q < 0))))

def cwZero (k : ℕ) : Fin (k+1) → Bool := fun _ => false

noncomputable def cwOutput (k : ℕ) (c : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ)
    (ψ : QState I) : QState ((Fin (k+1) → Bool) × I) :=
  ApplyGate (cwProtocol k c U) (TensorState (Ket (cwZero k)) ψ)

noncomputable def cwFailureProb (k : ℕ) (c : Fin (k+1) → ℝ) (U : Fin (k+1) → Matrix I I ℂ)
    (ψ : QState I) : ℝ :=
  MeasureProb (cwOutput k c U ψ)
    (((Finset.univ (α := Fin (k+1) → Bool)).erase (cwZero k)) ×ˢ Finset.univ)

def Theorem3LCUFiber : Prop :=
  ∀ (k : ℕ) (I : Type) [Fintype I] [DecidableEq I], 1 ≤ k →
    ∀ (U : Fin (k+1) → Matrix I I ℂ), (∀ q, U q ∈ Matrix.unitaryGroup I ℂ) →
      ∀ (c : Fin (k+1) → ℝ), (∀ q, c q ≠ 0) → (∃ q, 0 < c q) → (∃ q, c q < 0) →
        ∀ ψ : QState I, ∀ x : I,
          cwOutput k c U ψ (cwZero k, x)
            = (((∑ q, c q • U q)) *ᵥ ψ) x / (∑ q, |c q|)

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
