/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib

open Matrix

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def vKappa (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun b b' =>
    ((if b = 0 then
        (if b' = 0 then Real.sqrt (κ / (κ + 1)) else (Real.sqrt (κ + 1))⁻¹)
      else
        (if b' = 0 then (Real.sqrt (κ + 1))⁻¹ else -(Real.sqrt (κ / (κ + 1)))) : ℝ) : ℂ)

noncomputable def liftSys (k : ℕ) (U : Matrix I I ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then U p.2 q.2 else 0

noncomputable def rotGate (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then V (if p.1 i then 1 else 0) (if q.1 i then 1 else 0) else 0

noncomputable def ctrlGate (k : ℕ) (i : Fin k)
    (Cx Cy : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 i then Cy else Cx) p q else 0

noncomputable def lcuLevelGate (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ :=
  rotGate k i Vᴴ * (ctrlGate k i Cx Cy * rotGate k i V)

noncomputable def lemma2Circuit (κ : ℝ) (Ua Ub : Matrix I I ℂ) :
    Matrix ((Fin 1 → Bool) × I) ((Fin 1 → Bool) × I) ℂ :=
  lcuLevelGate 1 ⟨0, by omega⟩ (vKappa κ) (liftSys 1 Ua) (liftSys 1 Ub)

def lemma2FailSet : Finset (Fin 1 → Bool) :=
  {(fun _ => true : Fin 1 → Bool)}

noncomputable def lemma2Output (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) :
    QState ((Fin 1 → Bool) × I) :=
  ApplyGate (lemma2Circuit κ Ua Ub) (TensorState (Ket (fun _ => false)) ψ)

noncomputable def lemma2FailureProb (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) : ℝ :=
  MeasureProb (lemma2Output κ Ua Ub ψ) (lemma2FailSet ×ˢ Finset.univ)

def Lemma2Fiber : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I,
        (∀ x : I, lemma2Output κ Ua Ub ψ (fun _ => false, x)
            = ((((κ : ℂ) / (κ + 1)) • Ua + (((1 : ℂ) / (κ + 1)) • Ub)) *ᵥ ψ) x)
        ∧ (∀ x : I, lemma2Output κ Ua Ub ψ (fun _ => true, x)
            = (((((Real.sqrt κ / (κ + 1) : ℝ) : ℂ)) • (Ua - Ub)) *ᵥ ψ) x)

def Lemma2NearbyFailure : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ Δ : ℝ, 0 ≤ Δ →
        (∀ φ : QState I, Normalized φ → (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
        ∀ ψ : QState I, Normalized ψ →
          lemma2FailureProb κ Ua Ub ψ ≤ κ * Δ ^ 2 / (κ + 1) ^ 2

def Lemma2NearbyFailureCrude : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I, Normalized ψ →
        lemma2FailureProb κ Ua Ub ψ ≤ 4 * κ / (κ + 1) ^ 2

def Lemma2CircuitUnitary : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      lemma2Circuit κ Ua Ub ∈ Matrix.unitaryGroup ((Fin 1 → Bool) × I) ℂ

end Qatlib.Papers.HamLCUSim12.LCUDeferred
