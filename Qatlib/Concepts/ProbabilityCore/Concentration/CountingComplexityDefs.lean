/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCountingDefs
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.CountingClasses.ClassTransport

def CcHashJointZero {L ℓ : ℕ} (s : EcHashSeed L ℓ) (w w' : Fin L → Bool) : Prop :=
  EcHashZero s w ∧ EcHashZero s w'

noncomputable def CcHashJointZeroCount {L : ℕ} (ℓ : ℕ) (w w' : Fin L → Bool) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if CcHashJointZero s w w' then 1 else 0

def CcRowParity {L : ℕ} (v row : Fin L → Bool) : Bool :=
  ∑ j, (row j && v j)

def CcRowParityDiff {L : ℕ} (w w' row : Fin L → Bool) : Bool :=
  CcRowParity w row + CcRowParity w' row

def CcMatrixParityAgree {L ℓ : ℕ} (w w' : Fin L → Bool)
    (mat : Fin ℓ → Fin L → Bool) : Prop :=
  ∀ i, CcRowParityDiff w w' (mat i) = false

def CcWitnessDiff {L : ℕ} (w w' : Fin L → Bool) : Fin L → Bool :=
  fun j => w j ^^ w' j

def CcWitnessDiffNonzero {L : ℕ} (w w' : Fin L → Bool) : Prop :=
  ∃ j, CcWitnessDiff w w' j = true

def CcFlipAt {L : ℕ} (row : Fin L → Bool) (j₀ : Fin L) : Fin L → Bool :=
  fun j => if j = j₀ then !row j else row j

noncomputable def CcEstimate {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : ℕ :=
  2 ^ ℓ * EcRelFiberCount R s

noncomputable def CcGoodSeed {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : Prop :=
  EcRelCount R ≤ 2 * CcEstimate R s

noncomputable def CcBadSeed {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : Prop :=
  ¬ CcGoodSeed R s

noncomputable def CcGoodSeedCount {L ℓ : ℕ} (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if CcGoodSeed R s then 1 else 0

noncomputable def CcBadSeedCount {L ℓ : ℕ} (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if CcBadSeed R s then 1 else 0

def CcFailureBudget {ℓ : ℕ} (m : ℕ) (ε : ℝ) : Prop :=
  0 < ε ∧ 4 * ((2 : ℝ) ^ ℓ - 1) ≤ ε * (m : ℝ)

noncomputable def CcRowEvenCount {L : ℕ} (d : Fin L → Bool) : ℕ :=
  ∑ r : Fin L → Bool, if CcRowParity d r = false then 1 else 0

noncomputable def CcRowOddCount {L : ℕ} (d : Fin L → Bool) : ℕ :=
  ∑ r : Fin L → Bool, if CcRowParity d r = true then 1 else 0

noncomputable def CcMatrixEvenCount {L : ℕ} (ℓ : ℕ) (d : Fin L → Bool) : ℕ :=
  ∑ mat : Fin ℓ → Fin L → Bool, if (∀ i, CcRowParity d (mat i) = false) then 1 else 0

noncomputable def CcPairZeroCount {L : ℕ} (ℓ : ℕ) (w w' : Fin L → Bool) : ℕ :=
  if w = w' then 2 ^ (ℓ * L) else 2 ^ (ℓ * (L - 1))

noncomputable def CcEstimateDevSq {L : ℕ} (ℓ : ℕ) (R : Set (Fin L → Bool)) : ℝ :=
  ∑ s : EcHashSeed L ℓ,
    ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2

noncomputable def CcFailureCount {L : ℕ} (ℓ : ℕ) (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ,
    if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2 then 1 else 0

noncomputable def CcFailureProb {L : ℕ} (ℓ : ℕ) (R : Set (Fin L → Bool)) : ℝ :=
  (CcFailureCount ℓ R : ℝ) / ((2 : ℝ) ^ (ℓ * L + ℓ))

def CcInputBits (x : List Bool) : ℕ := (EcEncode x).length

def CcBitTime {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ :=
  (EcChargeOf P A ρ x t).time + CcInputBits x + (EcChargeOf P A ρ x t).outputBits

def CcSamplerRandomBits (L ℓ : ℕ) : ℕ := L + ℓ * L + ℓ

def CcSamplerBitTime (L ℓ addrBits queries outputBits : ℕ) : ℕ :=
  CcSamplerRandomBits L ℓ + queries * (2 * addrBits + 2) + outputBits

noncomputable def CcThresholdBadSeedCount {L : ℕ} (ℓ : ℕ) (τ : ℝ) (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then 1 else 0

def CcSamplerEventSet {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (Ev : Out → Bool) :
    Set (Fin L → Bool) := fun r => Ev (Sam.O r) = true

noncomputable def CcSamplerEventProb {L : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (Ev : Out → Bool) : ℝ :=
  (EcRelCount (CcSamplerEventSet Sam Ev) : ℝ) / ((2 : ℝ) ^ L)

end Qatlib.Concepts.ProbabilityCore.Concentration
