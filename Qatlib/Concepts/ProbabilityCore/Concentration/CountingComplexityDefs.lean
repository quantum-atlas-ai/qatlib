/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCountingDefs

/-!
# Definitions for hash-based approximate counting

`CcEstimate` rescales the size of a zero-hash fiber to estimate a finite relation count. This
module defines Boolean parity tests, joint-zero counts, seed quality predicates, squared
deviations, and relative or absolute error events. These quantities support a classical counting
counterpart to the estimation tasks in [BrassardEtAl2002].

`CcSamplerEventSet` and `CcSamplerEventProb` express sampler events as subsets of uniform random
seeds. `CcBitTime` and `CcSamplerBitTime` add explicit input, output, randomness, and
oracle-access charges.

## Main statements

* `CcFailureBudget`: a positive error budget with the required count-to-hash-size inequality.
* `CcEstimateDevSq`: the total squared deviation over all hash seeds.
* `CcFailureProb`: the fraction of seeds with error greater than half the true count.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- Both specified witnesses hash to zero under the same affine Boolean hash seed. -/
def CcHashJointZero {L ℓ : ℕ} (s : EcHashSeed L ℓ) (w w' : Fin L → Bool) : Prop :=
  EcHashZero s w ∧ EcHashZero s w'

/-- The number of affine Boolean hash seeds that send both specified witnesses to zero. -/
noncomputable def CcHashJointZeroCount {L : ℕ} (ℓ : ℕ) (w w' : Fin L → Bool) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if CcHashJointZero s w w' then 1 else 0

/-- The Boolean parity of the coordinatewise conjunction of a vector with a row. -/
def CcRowParity {L : ℕ} (v row : Fin L → Bool) : Bool :=
  ∑ j, (row j && v j)

/-- The Boolean sum of the row parities of two witnesses. -/
def CcRowParityDiff {L : ℕ} (w w' row : Fin L → Bool) : Bool :=
  CcRowParity w row + CcRowParity w' row

/-- The two witnesses have equal parity in every matrix row, expressed by vanishing parity
differences. -/
def CcMatrixParityAgree {L ℓ : ℕ} (w w' : Fin L → Bool)
    (mat : Fin ℓ → Fin L → Bool) : Prop :=
  ∀ i, CcRowParityDiff w w' (mat i) = false

/-- The pointwise exclusive-or of two Boolean witnesses. -/
def CcWitnessDiff {L : ℕ} (w w' : Fin L → Bool) : Fin L → Bool :=
  fun j => w j ^^ w' j

/-- The pointwise exclusive-or of two witnesses has a coordinate equal to `true`. -/
def CcWitnessDiffNonzero {L : ℕ} (w w' : Fin L → Bool) : Prop :=
  ∃ j, CcWitnessDiff w w' j = true

/-- Flips one specified coordinate of a Boolean row and preserves all other coordinates. -/
def CcFlipAt {L : ℕ} (row : Fin L → Bool) (j₀ : Fin L) : Fin L → Bool :=
  fun j => if j = j₀ then !row j else row j

/-- The zero-hash fiber count of the relation multiplied by `2 ^ ℓ`. -/
noncomputable def CcEstimate {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : ℕ :=
  2 ^ ℓ * EcRelFiberCount R s

/-- The seed estimate is large enough that twice the estimate is at least the true relation
count. -/
noncomputable def CcGoodSeed {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : Prop :=
  EcRelCount R ≤ 2 * CcEstimate R s

/-- The seed fails the lower-estimate condition `CcGoodSeed`. -/
noncomputable def CcBadSeed {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : Prop :=
  ¬ CcGoodSeed R s

/-- The number of hash seeds satisfying `CcGoodSeed` for the relation. -/
noncomputable def CcGoodSeedCount {L ℓ : ℕ} (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if CcGoodSeed R s then 1 else 0

/-- The number of hash seeds failing `CcGoodSeed` for the relation. -/
noncomputable def CcBadSeedCount {L ℓ : ℕ} (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if CcBadSeed R s then 1 else 0

/-- The error parameter is positive and satisfies `4 * (2 ^ ℓ - 1) ≤ ε * m` over the real
numbers. -/
def CcFailureBudget {ℓ : ℕ} (m : ℕ) (ε : ℝ) : Prop :=
  0 < ε ∧ 4 * ((2 : ℝ) ^ ℓ - 1) ≤ ε * (m : ℝ)

/-- The number of Boolean rows whose parity against the given vector is `false`. -/
noncomputable def CcRowEvenCount {L : ℕ} (d : Fin L → Bool) : ℕ :=
  ∑ r : Fin L → Bool, if CcRowParity d r = false then 1 else 0

/-- The number of Boolean rows whose parity against the given vector is `true`. -/
noncomputable def CcRowOddCount {L : ℕ} (d : Fin L → Bool) : ℕ :=
  ∑ r : Fin L → Bool, if CcRowParity d r = true then 1 else 0

/-- The number of Boolean matrices with `ℓ` rows, each having even parity against the given
vector. -/
noncomputable def CcMatrixEvenCount {L : ℕ} (ℓ : ℕ) (d : Fin L → Bool) : ℕ :=
  ∑ mat : Fin ℓ → Fin L → Bool, if (∀ i, CcRowParity d (mat i) = false) then 1 else 0

/-- The piecewise value `2 ^ (ℓ * L)` for equal witnesses and `2 ^ (ℓ * (L - 1))` for distinct
witnesses. -/
noncomputable def CcPairZeroCount {L : ℕ} (ℓ : ℕ) (w w' : Fin L → Bool) : ℕ :=
  if w = w' then 2 ^ (ℓ * L) else 2 ^ (ℓ * (L - 1))

/-- The sum over all hash seeds of squared real deviations between the estimate and the true
relation count. -/
noncomputable def CcEstimateDevSq {L : ℕ} (ℓ : ℕ) (R : Set (Fin L → Bool)) : ℝ :=
  ∑ s : EcHashSeed L ℓ,
    ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2

/-- The number of hash seeds whose absolute estimation error exceeds half the true relation
count. -/
noncomputable def CcFailureCount {L : ℕ} (ℓ : ℕ) (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ,
    if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2 then 1 else 0

/-- The relative-error failure count divided by the total hash-seed count `2 ^ (ℓ * L + ℓ)`. -/
noncomputable def CcFailureProb {L : ℕ} (ℓ : ℕ) (R : Set (Fin L → Bool)) : ℝ :=
  (CcFailureCount ℓ R : ℝ) / ((2 : ℝ) ^ (ℓ * L + ℓ))

/-- The length of the encoded Boolean input `EcEncode x`. -/
def CcInputBits (x : List Bool) : ℕ := (EcEncode x).length

/-- The charged execution time plus the encoded input length and the charged output-bit count. -/
def CcBitTime {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) : ℕ :=
  (EcChargeOf P A ρ x t).time + CcInputBits x + (EcChargeOf P A ρ x t).outputBits

/-- The random-bit budget `L + ℓ * L + ℓ` for a sampler seed and an affine hash seed. -/
def CcSamplerRandomBits (L ℓ : ℕ) : ℕ := L + ℓ * L + ℓ

/-- The sampler random-bit budget plus `queries * (2 * addrBits + 2)` and the output-bit count. -/
def CcSamplerBitTime (L ℓ addrBits queries outputBits : ℕ) : ℕ :=
  CcSamplerRandomBits L ℓ + queries * (2 * addrBits + 2) + outputBits

/-- The number of hash seeds whose absolute estimation error is strictly greater than the real
threshold `τ`. -/
noncomputable def CcThresholdBadSeedCount {L : ℕ} (ℓ : ℕ) (τ : ℝ) (R : Set (Fin L → Bool)) : ℕ :=
  ∑ s : EcHashSeed L ℓ, if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then 1 else 0

/-- The set of sampler seeds whose output satisfies the Boolean event predicate. -/
def CcSamplerEventSet {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (Ev : Out → Bool) :
    Set (Fin L → Bool) := fun r => Ev (Sam.O r) = true

/-- The fraction of the `2 ^ L` sampler seeds whose output satisfies the event predicate. -/
noncomputable def CcSamplerEventProb {L : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (Ev : Out → Bool) : ℝ :=
  (EcRelCount (CcSamplerEventSet Sam Ev) : ℝ) / ((2 : ℝ) ^ L)

end Qatlib.Concepts.ProbabilityCore.Concentration
