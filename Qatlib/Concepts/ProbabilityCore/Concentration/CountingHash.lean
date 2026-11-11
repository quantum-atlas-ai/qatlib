/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.CountingComplexity
import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCountingDefs

/-!
# Hash seed tapes and counting costs

`ecSeedTapeEquiv` identifies affine Boolean hash seeds with fixed length bit tapes. Collision
counts and counting failure probabilities are transported across this equivalence, while
explicit programs account for random bits, oracle queries, and seed storage.

These constructions supply concrete sampling and cost data for approximate counting, a setting
also studied through amplitude estimation in [BrassardEtAl2002].

## Main statements

* `ecCollProb_eq`: the exact average count of distinct pairs in the zero fiber.
* `ecTapeFailureProb_le_eps`: transport of the counting failure budget to random tapes.
* `frontier2`: polynomial time, random bit, time charge, and stored seed guarantees.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.ProbabilityCore.Concentration.CountingHash

open scoped Classical BigOperators
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCounting
open Qatlib

/-- The row major index of a hash matrix entry lies within the seed tape. -/
private theorem ecTapeMat_lt (L ℓ : ℕ) (i : Fin ℓ) (j : Fin L) :
    i.val * L + j.val < ℓ * L + ℓ := by
  have h1 : i.val * L + j.val < i.val * L + L := by
    have := Fin.is_lt j
    omega
  have h2 : i.val * L + L = (i.val + 1) * L := by
    rw [Nat.add_mul]
    simp
  have h3 : (i.val + 1) * L ≤ ℓ * L :=
    Nat.mul_le_mul_right L (by
      have := Fin.is_lt i
      omega)
  omega

/-- The index of an affine offset bit lies within the seed tape. -/
private theorem ecTapeOff_lt (L ℓ : ℕ) (i : Fin ℓ) :
    ℓ * L + i.val < ℓ * L + ℓ := by
  have := Fin.is_lt i
  omega

/-- Read an affine Boolean hash seed from its matrix and offset bits on a tape. -/
def ecSeedOfTape (L ℓ : ℕ) (t : Fin (EcHashSeedBits L ℓ) → Bool) : EcHashSeed L ℓ :=
  ((fun (i : Fin ℓ) (j : Fin L) => t ⟨i.val * L + j.val, ecTapeMat_lt L ℓ i j⟩),
   fun (i : Fin ℓ) => t ⟨ℓ * L + i.val, ecTapeOff_lt L ℓ i⟩)

/-- Serialize the matrix and offset bits of an affine Boolean hash seed. -/
def ecTapeOfSeed (L ℓ : ℕ) (s : EcHashSeed L ℓ) : Fin (EcHashSeedBits L ℓ) → Bool :=
  fun k =>
    if h : k.val < ℓ * L then
      s.1 ⟨k.val / L, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩
        ⟨k.val % L, Nat.mod_lt _
          (Nat.pos_of_ne_zero (by rintro rfl; simp at h))⟩
    else
      s.2 ⟨k.val - ℓ * L, by
        have hk := Fin.is_lt k
        simp only [EcHashSeedBits] at hk
        omega⟩

/-- Serializing the seed read from a tape recovers that tape. -/
theorem ecTapeOfSeed_seedOfTape (L ℓ : ℕ) (t : Fin (EcHashSeedBits L ℓ) → Bool) :
    ecTapeOfSeed L ℓ (ecSeedOfTape L ℓ t) = t := by
  funext k
  have hk := Fin.is_lt k
  simp only [EcHashSeedBits] at hk
  by_cases h : k.val < ℓ * L
  · have hdm := Nat.div_add_mod k.val L
    rw [Nat.mul_comm] at hdm
    have hfin : (⟨k.val / L * L + k.val % L, by omega⟩ : Fin (ℓ * L + ℓ)) = k :=
      Fin.val_injective hdm
    simp only [ecTapeOfSeed, dif_pos h, ecSeedOfTape]
    exact congrArg t hfin
  · have hle : ℓ * L ≤ k.val := by omega
    have hval : ℓ * L + (k.val - ℓ * L) = k.val := by omega
    have hlt : ℓ * L + (k.val - ℓ * L) < ℓ * L + ℓ := by omega
    have hfin : (⟨ℓ * L + (k.val - ℓ * L), hlt⟩ : Fin (ℓ * L + ℓ)) = k :=
      Fin.val_injective hval
    simp only [ecTapeOfSeed, dif_neg h, ecSeedOfTape]
    exact congrArg t hfin

/-- Reading a serialized seed recovers the original seed. -/
theorem ecSeedOfTape_tapeOfSeed (L ℓ : ℕ) (s : EcHashSeed L ℓ) :
    ecSeedOfTape L ℓ (ecTapeOfSeed L ℓ s) = s := by
  have hmat : (ecSeedOfTape L ℓ (ecTapeOfSeed L ℓ s)).1 = s.1 := by
    funext i j
    have hL : 0 < L := by
      have := Fin.is_lt j
      omega
    have hdiv : (i.val * L + j.val) / L = i.val := by
      rw [Nat.add_comm, Nat.mul_comm i.val L, Nat.add_mul_div_left _ _ hL,
        Nat.div_eq_of_lt (Fin.is_lt j)]
      omega
    have hmod : (i.val * L + j.val) % L = j.val := by
      rw [Nat.add_comm, Nat.mul_comm i.val L, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (Fin.is_lt j)]
    have hltL : i.val * L + j.val < ℓ * L := by
      have h1 : i.val * L + j.val < i.val * L + L := by
        have := Fin.is_lt j
        omega
      have h2 : i.val * L + L = (i.val + 1) * L := by
        rw [Nat.add_mul]
        simp
      have h3 : (i.val + 1) * L ≤ ℓ * L :=
        Nat.mul_le_mul_right L (by
          have := Fin.is_lt i
          omega)
      omega
    show (ecTapeOfSeed L ℓ s) ⟨i.val * L + j.val, ecTapeMat_lt L ℓ i j⟩ = s.1 i j
    simp only [ecTapeOfSeed, dif_pos hltL]
    exact congrArg₂ s.1 (Fin.val_injective hdiv) (Fin.val_injective hmod)
  have hoff : (ecSeedOfTape L ℓ (ecTapeOfSeed L ℓ s)).2 = s.2 := by
    funext i
    have hnl : ¬ (ℓ * L + i.val < ℓ * L) := by
      have := Fin.is_lt i
      omega
    show (ecTapeOfSeed L ℓ s) ⟨ℓ * L + i.val, ecTapeOff_lt L ℓ i⟩ = s.2 i
    simp only [ecTapeOfSeed, dif_neg hnl]
    exact congrArg s.2 (Fin.val_injective (Nat.add_sub_cancel_left _ _))
  exact Prod.ext_iff.mpr ⟨hmat, hoff⟩

/-- The equivalence between fixed length Boolean seed tapes and affine hash seeds. -/
def ecSeedTapeEquiv (L ℓ : ℕ) : (Fin (EcHashSeedBits L ℓ) → Bool) ≃ EcHashSeed L ℓ where
  toFun := ecSeedOfTape L ℓ
  invFun := ecTapeOfSeed L ℓ
  left_inv := ecTapeOfSeed_seedOfTape L ℓ
  right_inv := ecSeedOfTape_tapeOfSeed L ℓ

/-- The number of ordered distinct pairs in the relation that both lie in the zero hash fiber. -/
noncomputable def ecCollCount {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) : ℕ :=
  ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
    if R w ∧ R w' ∧ w ≠ w' ∧ CcHashJointZero s w w' then 1 else 0

/-- The square of the zero fiber size splits into its diagonal count and its distinct pair
count. -/
theorem ecFiberSq_eq_fiber_add_coll {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) :
    EcRelFiberCount R s ^ 2 = EcRelFiberCount R s + ecCollCount R s := by
  classical
  have hfib : EcRelFiberCount R s
      = ∑ w : Fin L → Bool, (if R w ∧ EcHashZero s w then 1 else 0) :=
    ecRelFiberCount_eq_sum R s
  have hsq : EcRelFiberCount R s ^ 2
      = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := by
    rw [hfib, pow_two, Finset.sum_mul_sum]
  rw [hsq]
  have hdiag : ∀ w : Fin L → Bool,
      (if R w ∧ EcHashZero s w then 1 else 0) * (if R w ∧ EcHashZero s w then 1 else 0)
        = (if R w ∧ EcHashZero s w then 1 else 0) := by
    intro w
    by_cases h : R w ∧ EcHashZero s w <;> simp [h]
  have hoff : ∀ w w' : Fin L → Bool, (hw' : w' ≠ w) →
      (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0)
        = if R w ∧ R w' ∧ w ≠ w' ∧ CcHashJointZero s w w' then 1 else 0 := by
    intro w w' hw'
    have hw : w ≠ w' := hw'.symm
    unfold CcHashJointZero
    by_cases h1 : R w <;> by_cases h2 : EcHashZero s w <;>
      by_cases h3 : R w' <;> by_cases h4 : EcHashZero s w' <;>
      simp [h1, h2, h3, h4, hw]
  have hrow : ∀ w : Fin L → Bool,
      (∑ w' : Fin L → Bool,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
      = (if R w ∧ EcHashZero s w then 1 else 0)
        + ∑ w' : Fin L → Bool,
            if R w ∧ R w' ∧ w ≠ w' ∧ CcHashJointZero s w w' then 1 else 0 := by
    intro w
    have h1 := Finset.sum_erase_add Finset.univ
      (fun w' : Fin L → Bool =>
        (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
      (Finset.mem_univ w)
    have h2 := Finset.sum_erase_add Finset.univ
      (fun w' : Fin L → Bool =>
        if R w ∧ R w' ∧ w ≠ w' ∧ CcHashJointZero s w w' then 1 else 0)
      (Finset.mem_univ w)
    have hself : (if R w ∧ R w ∧ w ≠ w ∧ CcHashJointZero s w w then 1 else 0) = 0 :=
      if_neg (fun hc => hc.2.2.1 rfl)
    rw [← h1, ← h2]
    try simp only []
    rw [hdiag w, hself, Nat.add_zero]
    rw [Finset.sum_congr rfl (fun w' hw' => hoff w w' (Finset.mem_erase.mp hw').1)]
    omega
  rw [Finset.sum_congr rfl (fun w _ => hrow w), Finset.sum_add_distrib, hfib]
  rfl

/-- Summing distinct pair counts over all seeds gives `(EcRelCount R ^ 2 - EcRelCount R) * 2 ^
(ℓ * (L - 1))`. -/
theorem ecCollCount_sum {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    (∑ s : EcHashSeed L ℓ, ecCollCount R s)
      = (EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1)) := by
  have h1 := ccFiberSq_sum (L := L) (ℓ := ℓ) R
  have h2 := ecRelFiberCount_sum (L := L) (ℓ := ℓ) R
  have h3 : (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s ^ 2)
      = (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s) + ∑ s : EcHashSeed L ℓ, ecCollCount R s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => ecFiberSq_eq_fiber_add_coll R s)
  rw [h3] at h1
  omega

/-- The uniform seed average of the distinct pair count is `m * (m - 1) / 2 ^ (2 * ℓ)`, where `m
= EcRelCount R` is viewed as real. -/
theorem ecCollProb_eq {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ((∑ s : EcHashSeed L ℓ, ecCollCount R s : ℝ) / (2 : ℝ) ^ (ℓ * L + ℓ))
      = (EcRelCount R : ℝ) * ((EcRelCount R : ℝ) - 1) / (2 : ℝ) ^ (2 * ℓ) := by
  classical
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hm1 : EcRelCount R ≤ 1 := by
      unfold EcRelCount
      have hcard := Finset.card_le_card
        (Finset.filter_subset (fun w : Fin 0 → Bool => R w) Finset.univ)
      simp only [Finset.card_univ, card_fin_fun_bool] at hcard
      omega
    rcases Nat.lt_or_ge (EcRelCount R) 1 with hlt | hge
    · have hm0 : EcRelCount R = 0 := Nat.lt_one_iff.mp hlt
      have hzero : (∑ s : EcHashSeed 0 ℓ, ecCollCount R s) = 0 := by
        have hsum := ecCollCount_sum (L := 0) (ℓ := ℓ) R
        rw [hm0] at hsum
        norm_num at hsum
        exact Finset.sum_eq_zero (fun i _ => hsum i)
      rw [hm0, ← Nat.cast_sum, hzero]
      norm_num
    · have hm1' : EcRelCount R = 1 := Nat.le_antisymm hm1 hge
      have hzero : (∑ s : EcHashSeed 0 ℓ, ecCollCount R s) = 0 := by
        have hsum := ecCollCount_sum (L := 0) (ℓ := ℓ) R
        rw [hm1'] at hsum
        norm_num at hsum
        exact Finset.sum_eq_zero (fun i _ => hsum i)
      rw [hm1', ← Nat.cast_sum, hzero]
      norm_num
  · have hm_le : EcRelCount R ≤ EcRelCount R ^ 2 := by
      rcases Nat.eq_zero_or_pos (EcRelCount R) with h0 | h0
      · simp [h0]
      · have hh := Nat.mul_le_mul (le_refl (EcRelCount R)) (by omega : 1 ≤ EcRelCount R)
        simpa [pow_two, Nat.mul_one] using hh
    have hpow : (2 : ℝ) ^ (ℓ * L + ℓ)
        = (2 : ℝ) ^ (ℓ * (L - 1)) * (2 : ℝ) ^ (2 * ℓ) := by
      rw [← pow_add]
      congr 1
      have h1 : (L - 1) + 2 = L + 1 := by omega
      have e1 := Nat.mul_add ℓ (L - 1) 2
      have e2 := Nat.mul_add ℓ L 1
      simp only [Nat.mul_one] at e2
      rw [h1] at e1
      omega
    have hcast : (((EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1)) : ℕ) : ℝ)
        = (EcRelCount R : ℝ) * ((EcRelCount R : ℝ) - 1) * (2 : ℝ) ^ (ℓ * (L - 1)) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hm_le]
      push_cast
      ring
    rw [← Nat.cast_sum, ecCollCount_sum, hcast, hpow]
    have hA : ((2 : ℝ) ^ (ℓ * (L - 1))) ≠ 0 := by positivity
    have hB : ((2 : ℝ) ^ (2 * ℓ)) ≠ 0 := by positivity
    field_simp

/-- The sampler random bit budget is the input length plus the hash seed length. -/
theorem ccSamplerRandomBits_eq (L ℓ : ℕ) :
    CcSamplerRandomBits L ℓ = L + EcHashSeedBits L ℓ := by
  unfold CcSamplerRandomBits EcHashSeedBits
  omega

/-- Express the sampler bit time as random bit generation, query charges, and output bits. -/
theorem ccSamplerBitTime_seedBits (L ℓ addrBits queries outputBits : ℕ) :
    CcSamplerBitTime L ℓ addrBits queries outputBits
      = (L + EcHashSeedBits L ℓ) + queries * (2 * addrBits + 2) + outputBits := by
  unfold CcSamplerBitTime
  rw [ccSamplerRandomBits_eq]

/-- Count seed tapes whose counting estimate differs from the relation size by more than half
that size. -/
noncomputable def ecTapeFailureCount (L ℓ : ℕ) (R : Set (Fin L → Bool)) : ℕ :=
  ∑ t : Fin (EcHashSeedBits L ℓ) → Bool,
    if |(CcEstimate R (ecSeedOfTape L ℓ t) : ℝ) - (EcRelCount R : ℝ)|
      > (EcRelCount R : ℝ) / 2 then 1 else 0

/-- The fraction of seed tapes for which the counting estimate has relative error greater than
one half. -/
noncomputable def ecTapeFailureProb (L ℓ : ℕ) (R : Set (Fin L → Bool)) : ℝ :=
  (ecTapeFailureCount L ℓ R : ℝ) / ((2 : ℝ) ^ (EcHashSeedBits L ℓ))

/-- Tape based and seed based counting failure counts agree. -/
theorem ecTapeFailureCount_eq {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ecTapeFailureCount L ℓ R = CcFailureCount ℓ R := by
  unfold ecTapeFailureCount CcFailureCount
  exact Fintype.sum_equiv (ecSeedTapeEquiv L ℓ) _ _ (fun _ => rfl)

/-- Tape based and seed based counting failure probabilities agree. -/
theorem ecTapeFailureProb_eq {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ecTapeFailureProb L ℓ R = CcFailureProb ℓ R := by
  unfold ecTapeFailureProb CcFailureProb
  rw [ecTapeFailureCount_eq]
  rfl

/-- For a nonempty relation, the tape failure probability is at most the prescribed counting
failure budget. -/
theorem ecTapeFailureProb_le_eps {L ℓ : ℕ} (R : Set (Fin L → Bool))
    (hm : 0 < EcRelCount R) {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount R) ε) :
    ecTapeFailureProb L ℓ R ≤ ε := by
  rw [ecTapeFailureProb_eq]
  exact ccFailureProb_le_eps R hm hb

/-- Combine the tape failure bound, exact collision sum and average, and sampler random bit
identity. -/
theorem frontier1 {L ℓ : ℕ} (R : Set (Fin L → Bool)) (hm : 0 < EcRelCount R)
    {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount R) ε) :
    ecTapeFailureProb L ℓ R ≤ ε
      ∧ (∑ s : EcHashSeed L ℓ, ecCollCount R s)
          = (EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1))
      ∧ ((∑ s : EcHashSeed L ℓ, ecCollCount R s : ℝ) / (2 : ℝ) ^ (ℓ * L + ℓ))
          = (EcRelCount R : ℝ) * ((EcRelCount R : ℝ) - 1) / (2 : ℝ) ^ (2 * ℓ)
      ∧ CcSamplerRandomBits L ℓ = L + EcHashSeedBits L ℓ :=
  ⟨ecTapeFailureProb_le_eps R hm hb, ecCollCount_sum R, ecCollProb_eq R,
    ccSamplerRandomBits_eq L ℓ⟩

/-- Count Boolean tapes whose decoded hash seed satisfies a given predicate. -/
noncomputable def ecTapeSeedCount {L ℓ : ℕ} (P : EcHashSeed L ℓ → Prop) : ℕ :=
  ∑ t : Fin (EcHashSeedBits L ℓ) → Bool, if P (ecSeedOfTape L ℓ t) then 1 else 0

/-- Counting tapes with a seed predicate equals counting the seeds satisfying that predicate. -/
theorem ecTapeSeedCount_eq {L ℓ : ℕ} (P : EcHashSeed L ℓ → Prop) :
    ecTapeSeedCount P = ∑ s : EcHashSeed L ℓ, if P s then 1 else 0 := by
  unfold ecTapeSeedCount
  exact Fintype.sum_equiv (ecSeedTapeEquiv L ℓ) _ _ (fun _ => rfl)

/-- Tape enumeration recovers the count of good counting seeds. -/
theorem ecTapeGoodSeedCount_eq {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ecTapeSeedCount (L := L) (ℓ := ℓ) (fun s => CcGoodSeed (L := L) (ℓ := ℓ) R s)
      = CcGoodSeedCount (L := L) (ℓ := ℓ) R := by
  rw [ecTapeSeedCount_eq]
  rfl

/-- Tape enumeration recovers the count of bad counting seeds. -/
theorem ecTapeBadSeedCount_eq {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ecTapeSeedCount (L := L) (ℓ := ℓ) (fun s => CcBadSeed (L := L) (ℓ := ℓ) R s)
      = CcBadSeedCount (L := L) (ℓ := ℓ) R := by
  rw [ecTapeSeedCount_eq]
  rfl

/-- Tape enumeration recovers the number of seeds whose counting error exceeds `τ`. -/
theorem ecTapeThresholdBadSeedCount_eq {L : ℕ} (ℓ : ℕ) (τ : ℝ)
    (R : Set (Fin L → Bool)) :
    ecTapeSeedCount (L := L) (ℓ := ℓ)
        (fun s => |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ)
      = CcThresholdBadSeedCount ℓ τ R := by
  rw [ecTapeSeedCount_eq]
  rfl

/-- The time charge for generating random bits, performing the query blocks, and writing and
moving past output bits. -/
def ecChargeMachineTime (L ℓ addrBits queries outputBits : ℕ) : ℕ :=
  L + EcHashSeedBits L ℓ + queries * (2 * addrBits + 2) + 2 * outputBits

/-- A program that generates the budgeted random bits, performs fixed query blocks, writes zero
output bits, and accepts. -/
def ecSamplerChargeMachine (L ℓ addrBits queries outputBits : ℕ) :
    CcProgram (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits) where
  states := fun i =>
    if h : (i : ℕ) < L then
      CcAct.coinFlip ⟨(i : ℕ) + 1, by omega⟩ ⟨(i : ℕ) + 1, by omega⟩
    else if h : (i : ℕ) < L + EcHashSeedBits L ℓ then
      CcAct.coinFlip ⟨(i : ℕ) + 1, by omega⟩ ⟨(i : ℕ) + 1, by omega⟩
    else if h : (i : ℕ) < L + EcHashSeedBits L ℓ + queries * (addrBits + 1) then
      if ((i : ℕ) - (L + EcHashSeedBits L ℓ)) % (addrBits + 1) < addrBits then
        CcAct.queryPush ⟨(i : ℕ) + 1, by omega⟩
      else
        CcAct.oracleCall ⟨(i : ℕ) + 1, by omega⟩ ⟨(i : ℕ) + 1, by omega⟩
    else if h : (i : ℕ) < L + EcHashSeedBits L ℓ + queries * (addrBits + 1)
        + 2 * outputBits then
      if ((i : ℕ) - (L + EcHashSeedBits L ℓ + queries * (addrBits + 1))) % 2 = 0 then
        CcAct.write false ⟨(i : ℕ) + 1, by omega⟩
      else
        CcAct.moveR ⟨(i : ℕ) + 1, by omega⟩
    else CcAct.accept

/-- A state in the random bit phase performs a coin flip and advances to the next state. -/
private theorem ecChargeMachine_coinAct (L ℓ addrBits queries outputBits : ℕ)
    {i : ℕ} (hi : i < L + EcHashSeedBits L ℓ) :
    (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        ⟨i, by omega⟩ = CcAct.coinFlip ⟨i + 1, by omega⟩ ⟨i + 1, by omega⟩ := by
  simp only [ecSamplerChargeMachine]
  by_cases hL : i < L
  · rw [dif_pos hL]
  · rw [dif_neg hL, dif_pos (by omega)]

/-- A state in the address portion of a query block pushes a query bit. -/
private theorem ecChargeMachine_pushAct (L ℓ addrBits queries outputBits : ℕ)
    {i : ℕ} (h1 : ¬ i < L) (h2 : ¬ i < L + EcHashSeedBits L ℓ)
    (h3 : i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1))
    (hm : (i - (L + EcHashSeedBits L ℓ)) % (addrBits + 1) < addrBits) :
    (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        ⟨i, by omega⟩ = CcAct.queryPush ⟨i + 1, by omega⟩ := by
  simp only [ecSamplerChargeMachine]
  rw [dif_neg h1, dif_neg h2, dif_pos h3, if_pos hm]

/-- The last state of a query block makes an oracle call. -/
private theorem ecChargeMachine_callAct (L ℓ addrBits queries outputBits : ℕ)
    {i : ℕ} (h1 : ¬ i < L) (h2 : ¬ i < L + EcHashSeedBits L ℓ)
    (h3 : i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1))
    (hm : ¬ (i - (L + EcHashSeedBits L ℓ)) % (addrBits + 1) < addrBits) :
    (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        ⟨i, by omega⟩ = CcAct.oracleCall ⟨i + 1, by omega⟩ ⟨i + 1, by omega⟩ := by
  simp only [ecSamplerChargeMachine]
  rw [dif_neg h1, dif_neg h2, dif_pos h3, if_neg hm]

/-- An even offset in the output phase writes a false bit. -/
private theorem ecChargeMachine_writeAct (L ℓ addrBits queries outputBits : ℕ)
    {i : ℕ} (h1 : ¬ i < L) (h2 : ¬ i < L + EcHashSeedBits L ℓ)
    (h3 : ¬ i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1))
    (h4 : i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)
    (hm : (i - (L + EcHashSeedBits L ℓ + queries * (addrBits + 1))) % 2 = 0) :
    (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        ⟨i, by omega⟩ = CcAct.write false ⟨i + 1, by omega⟩ := by
  simp only [ecSamplerChargeMachine]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4, if_pos hm]

/-- An odd offset in the output phase moves the tape head to the right. -/
private theorem ecChargeMachine_moveAct (L ℓ addrBits queries outputBits : ℕ)
    {i : ℕ} (h1 : ¬ i < L) (h2 : ¬ i < L + EcHashSeedBits L ℓ)
    (h3 : ¬ i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1))
    (h4 : i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)
    (hm : ¬ (i - (L + EcHashSeedBits L ℓ + queries * (addrBits + 1))) % 2 = 0) :
    (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        ⟨i, by omega⟩ = CcAct.moveR ⟨i + 1, by omega⟩ := by
  simp only [ecSamplerChargeMachine]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4, if_neg hm]

/-- The final state of the charge program accepts. -/
private theorem ecChargeMachine_acceptAct (L ℓ addrBits queries outputBits : ℕ)
    {i : ℕ} (hi : i ≤ L + EcHashSeedBits L ℓ + queries * (addrBits + 1)
      + 2 * outputBits)
    (h1 : ¬ i < L) (h2 : ¬ i < L + EcHashSeedBits L ℓ)
    (h3 : ¬ i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1))
    (h4 : ¬ i < L + EcHashSeedBits L ℓ + queries * (addrBits + 1)
      + 2 * outputBits) :
    (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        ⟨i, by omega⟩ = CcAct.accept := by
  simp only [ecSamplerChargeMachine]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]

/-- During random bit generation, the state, time, coin count, and coin index equal the number
of steps, with no head movement or queries. -/
private theorem ecChargeMachine_afterCoins (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ∀ t ≤ L + EcHashSeedBits L ℓ,
      ((ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).state
          : ℕ) = t
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).time = t
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).coins = t
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).coinIdx = t
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).head = 0
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).queries = 0
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).queryBits = 0
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t).query = [] := by
  intro t ht
  induction t with
  | zero =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih (by omega)
    have hnS : n < L + EcHashSeedBits L ℓ := by omega
    have hst : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x n).state
        = ⟨n, by omega⟩ := Fin.val_injective h1
    have hact : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x n).state
        = CcAct.coinFlip ⟨n + 1, by omega⟩ ⟨n + 1, by omega⟩ := by
      rw [hst]
      exact ecChargeMachine_coinAct L ℓ addrBits queries outputBits hnS
    have hstep : ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x (n + 1)
        = ccStep (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ
            (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x n) := rfl
    rw [hstep]
    simp only [ccStep]
    rw [hact]
    simp only [h2, h3, h4, h5, h6, h7, h8]
    split_ifs <;> exact ⟨rfl, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- After `n` query blocks, the state, time, head position, coin usage, and query counters have
their prescribed values, and the query buffer is empty. -/
private theorem ecChargeMachine_blocks (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ∀ n ≤ queries,
      ((ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).state : ℕ)
        = L + EcHashSeedBits L ℓ + n * (addrBits + 1)
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).time
          = L + EcHashSeedBits L ℓ + n * (2 * addrBits + 2)
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).coins
          = L + EcHashSeedBits L ℓ
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).coinIdx
          = L + EcHashSeedBits L ℓ
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).head
          = n * addrBits
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).queries = n
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).queryBits
          = n * addrBits
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + n * (addrBits + 1))).query = [] := by
  intro n hn
  induction n with
  | zero =>
    have h0 := (ecChargeMachine_afterCoins L ℓ addrBits queries outputBits A ρ x)
      (L + EcHashSeedBits L ℓ) (Nat.le_refl _)
    simpa only [Nat.zero_mul, Nat.add_zero] using h0
  | succ m ihm =>
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := ihm (by omega)
    have hmQ : m < queries := by omega
    have hpush : ∀ k ≤ addrBits,
      ((ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).state : ℕ)
          = L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).head
            = m * addrBits + k
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).query.length = k
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).time
            = L + EcHashSeedBits L ℓ + m * (2 * addrBits + 2) + k
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).queries = m
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).queryBits
            = m * addrBits
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).coins
            = L + EcHashSeedBits L ℓ
        ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + k)).coinIdx
            = L + EcHashSeedBits L ℓ := by
      intro k hk
      induction k with
      | zero =>
        simpa only [Nat.add_zero] using
          ⟨g1, g5, by rw [g8]; rfl, g2, g6, g7, g3, g4⟩
      | succ j ihj =>
        obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := ihj (by omega)
        have hjA : j < addrBits := by omega
        have hsub : (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j)
              - (L + EcHashSeedBits L ℓ)
            = m * (addrBits + 1) + j := by omega
        have hmod : ((L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j)
              - (L + EcHashSeedBits L ℓ)) % (addrBits + 1)
            = j % (addrBits + 1) := by
          rw [hsub, Nat.mul_comm m (addrBits + 1),
            Nat.add_comm ((addrBits + 1) * m) j, Nat.add_mul_mod_self_left]
        have hmodlt : ((L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j)
              - (L + EcHashSeedBits L ℓ)) % (addrBits + 1) < addrBits := by
          rw [hmod]
          have h1 := Nat.mod_le j (addrBits + 1)
          omega
        have hlt : m * (addrBits + 1) + j < queries * (addrBits + 1) := by
          have e1 : m * (addrBits + 1) + j < m * (addrBits + 1) + (addrBits + 1) := by omega
          have e2 : m * (addrBits + 1) + (addrBits + 1) = (m + 1) * (addrBits + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
          have e3 : (m + 1) * (addrBits + 1) ≤ queries * (addrBits + 1) :=
            Nat.mul_le_mul_right (addrBits + 1) (by omega)
          omega
        have hst : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j)).state
            = ⟨L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j, by omega⟩ :=
          Fin.val_injective p1
        have hact : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
              (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
                (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j)).state
            = CcAct.queryPush ⟨L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j + 1,
                by omega⟩ := by
          rw [hst]
          exact ecChargeMachine_pushAct L ℓ addrBits queries outputBits
            (by omega) (by omega) (by omega) hmodlt
        have hstep : ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + (j + 1))
            = ccStep (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ
                (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
                  (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + j)) := rfl
        rw [hstep]
        simp only [ccStep]
        rw [hact]
        simp only [p2, p3, p4, p5, p6, p7, p8, List.length_append, List.length_singleton]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | rfl | trivial
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hpush addrBits (Nat.le_refl _)
    have hsub : (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits)
          - (L + EcHashSeedBits L ℓ)
        = m * (addrBits + 1) + addrBits := by omega
    have hmod : ((L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits)
          - (L + EcHashSeedBits L ℓ)) % (addrBits + 1)
        = addrBits % (addrBits + 1) := by
      rw [hsub, Nat.mul_comm m (addrBits + 1),
        Nat.add_comm ((addrBits + 1) * m) addrBits, Nat.add_mul_mod_self_left]
    have hmodn : ¬ ((L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits)
          - (L + EcHashSeedBits L ℓ)) % (addrBits + 1) < addrBits := by
      rw [hmod, Nat.mod_eq_of_lt (by omega : addrBits < addrBits + 1)]
      omega
    have hlt : m * (addrBits + 1) + addrBits < queries * (addrBits + 1) := by
      have e1 : m * (addrBits + 1) + addrBits
          < m * (addrBits + 1) + (addrBits + 1) := by omega
      have e2 : m * (addrBits + 1) + (addrBits + 1) = (m + 1) * (addrBits + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have e3 : (m + 1) * (addrBits + 1) ≤ queries * (addrBits + 1) :=
        Nat.mul_le_mul_right (addrBits + 1) (by omega)
      omega
    have hst : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits)).state
        = ⟨L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits, by omega⟩ :=
      Fin.val_injective q1
    have hact : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
          (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits)).state
        = CcAct.oracleCall ⟨L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits + 1,
              by omega⟩
            ⟨L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits + 1, by omega⟩ := by
      rw [hst]
      exact ecChargeMachine_callAct L ℓ addrBits queries outputBits
        (by omega) (by omega) (by omega) hmodn
    have heqf : L + EcHashSeedBits L ℓ + m * (addrBits + 1) + (addrBits + 1)
        = L + EcHashSeedBits L ℓ + (m + 1) * (addrBits + 1) := by
      have e1 : m * (addrBits + 1) + (addrBits + 1) = (m + 1) * (addrBits + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    have hstep : ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + (m + 1) * (addrBits + 1))
        = ccStep (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ
            (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits)) := by
      rw [← heqf]
      rfl
    have htime : L + EcHashSeedBits L ℓ + m * (2 * addrBits + 2) + addrBits + (addrBits + 2)
        = L + EcHashSeedBits L ℓ + (m + 1) * (2 * addrBits + 2) := by
      have e1 : m * (2 * addrBits + 2) + (2 * addrBits + 2)
          = (m + 1) * (2 * addrBits + 2) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    have hqb : m * addrBits + addrBits = (m + 1) * addrBits := by
      rw [Nat.add_mul, Nat.one_mul]
    have hs2 : L + EcHashSeedBits L ℓ + m * (addrBits + 1) + addrBits + 1
        = L + EcHashSeedBits L ℓ + (m + 1) * (addrBits + 1) := by
      have e1 : m * (addrBits + 1) + (addrBits + 1) = (m + 1) * (addrBits + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hstep]
    simp only [ccStep]
    rw [hact]
    simp only [q2, q3, q4, q5, q6, q7, q8]
    split_ifs
    · exact ⟨hs2, by omega, trivial, trivial, hqb, trivial, hqb, trivial⟩
    · exact ⟨hs2, by omega, trivial, trivial, hqb, trivial, hqb, trivial⟩

/-- After `j` output write and move pairs, the state, time, head position, and resource counters
have their prescribed values. -/
private theorem ecChargeMachine_output (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ∀ j ≤ outputBits,
      ((ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).state : ℕ)
        = L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).time
          = L + EcHashSeedBits L ℓ + queries * (2 * addrBits + 2) + 2 * j
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).coins
          = L + EcHashSeedBits L ℓ
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).coinIdx
          = L + EcHashSeedBits L ℓ
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).head
          = queries * addrBits + j
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).queries
          = queries
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).queryBits
          = queries * addrBits
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * j)).query = [] := by
  intro j hj
  induction j with
  | zero =>
    have h0 := (ecChargeMachine_blocks L ℓ addrBits queries outputBits A ρ x)
      queries (Nat.le_refl _)
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using h0
  | succ i ihi =>
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := ihi (by omega)
    have hst1 : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i)).state
        = ⟨L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i, by omega⟩ :=
      Fin.val_injective o1
    have hact1 : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
          (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i)).state
        = CcAct.write false
            ⟨L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1, by omega⟩ := by
      rw [hst1]
      exact ecChargeMachine_writeAct L ℓ addrBits queries outputBits
        (by omega) (by omega) (by omega) (by omega) (by omega)
    have hstep1 : ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)
        = ccStep (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ
            (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i)) := rfl
    have hmid :
        ((ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).state : ℕ)
          = L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).time
          = L + EcHashSeedBits L ℓ + queries * (2 * addrBits + 2) + 2 * i + 1
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).coins
          = L + EcHashSeedBits L ℓ
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).coinIdx
          = L + EcHashSeedBits L ℓ
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).head
          = queries * addrBits + i
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).queries
          = queries
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).queryBits
          = queries * addrBits
      ∧ (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).query = [] := by
      rw [hstep1]
      simp only [ccStep]
      rw [hact1]
      simp only [o2, o3, o4, o5, o6, o7, o8]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hmid
    have hst2 : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).state
        = ⟨L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1, by omega⟩ :=
      Fin.val_injective m1
    have hact2 : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
          (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)).state
        = CcAct.moveR
            ⟨L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 2, by omega⟩ := by
      rw [hst2]
      exact ecChargeMachine_moveAct L ℓ addrBits queries outputBits
        (by omega) (by omega) (by omega) (by omega) (by omega)
    have hstep2 : ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * (i + 1))
        = ccStep (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ
            (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1)) := by
      rw [show L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * (i + 1)
          = (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 1) + 1 from by omega]
      rfl
    rw [hstep2]
    simp only [ccStep]
    rw [hact2]
    simp only [m2, m3, m4, m5, m6, m7, m8]
    have hs2o : L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * i + 2
        = L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * (i + 1) := by omega
    refine ⟨hs2o, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- The charge program configuration remains fixed after its final accepting state is reached. -/
private theorem ecChargeMachine_frozen (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ∀ t ≥ L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits,
      ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x t
        = ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits) := by
  intro t ht
  induction t with
  | zero =>
    exact congrArg (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x)
      (Nat.le_zero.mp ht).symm
  | succ n ihn =>
    rcases Nat.lt_or_ge (L + EcHashSeedBits L ℓ + queries * (addrBits + 1)
        + 2 * outputBits) (n + 1) with hlt | hge
    · have hstep : ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (n + 1)
          = ccStep (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ
              (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x n) := rfl
      have hout := ecChargeMachine_output L ℓ addrBits queries outputBits A ρ x
        outputBits (Nat.le_refl _)
      have hstF : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).state
          = ⟨L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits, by omega⟩ :=
        Fin.val_injective hout.1
      have hacc : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
            (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).state
          = CcAct.accept := by
        rw [hstF]
        exact ecChargeMachine_acceptAct L ℓ addrBits queries outputBits (Nat.le_refl _)
          (by omega) (by omega) (by omega) (by omega)
      have hn : L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits ≤ n := by omega
      rw [hstep, ihn hn]
      simp only [ccStep]
      rw [hacc]
    · have heq : L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits
          = n + 1 := by omega
      exact congrArg (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x)
        heq.symm

/-- The charge program accepts after its random bit, query, and output phases. -/
theorem ecSamplerChargeMachine_halts (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    ccResult (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
      (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits) = some true := by
  have hout := ecChargeMachine_output L ℓ addrBits queries outputBits A ρ x
    outputBits (Nat.le_refl _)
  have hstF : (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
        (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).state
      = ⟨L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits, by omega⟩ :=
    Fin.val_injective hout.1
  have hacc : (ecSamplerChargeMachine L ℓ addrBits queries outputBits).states
        (ccRun (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).state
      = CcAct.accept := by
    rw [hstF]
    exact ecChargeMachine_acceptAct L ℓ addrBits queries outputBits (Nat.le_refl _)
      (by omega) (by omega) (by omega) (by omega)
  simp only [ccResult]
  rw [hacc]

/-- Compute the complete time, query, query bit, coin, and head charge of the finished program. -/
theorem ecSamplerChargeMachine_charge (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    (EcChargeOf (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
        (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits))
      = ⟨CcSamplerBitTime L ℓ addrBits queries outputBits + outputBits, queries,
          queries * addrBits, CcSamplerRandomBits L ℓ, queries * addrBits + outputBits⟩ := by
  have hout := ecChargeMachine_output L ℓ addrBits queries outputBits A ρ x
    outputBits (Nat.le_refl _)
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hout
  have hT : L + EcHashSeedBits L ℓ + queries * (2 * addrBits + 2) + 2 * outputBits
      = CcSamplerBitTime L ℓ addrBits queries outputBits + outputBits := by
    simp only [CcSamplerBitTime]
    rw [ccSamplerRandomBits_eq]
    omega
  have hO : (ccOutput (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
        (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).length
      = queries * addrBits + outputBits := by
    simp only [ccOutput, List.length_map, List.length_range]
    exact o5
  simp only [EcChargeOf, ccTime, ccQueries, ccQueryBits, ccCoinsRead]
  rw [o2, hT, o6, o7, o3, ccSamplerRandomBits_eq, hO]

/-- The charge program satisfies `CcPolyTime` with the displayed constant bound and exponent
zero. -/
theorem ecSamplerChargeMachine_polytime (L ℓ addrBits queries outputBits : ℕ) :
    CcPolyTime (ecSamplerChargeMachine L ℓ addrBits queries outputBits)
      (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1) 0 := by
  intro A ρ x
  have hfr := ecChargeMachine_frozen L ℓ addrBits queries outputBits A ρ x
    (2 * (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1))
    (by omega)
  have hb : (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1)
      * x.length ^ 0
      + (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1)
      = 2 * (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1) := by
    rw [pow_zero, Nat.mul_one]
    omega
  rw [hb]
  constructor
  · have hrc : ccResult (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (2 * (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1))
        = ccResult (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits) := by
      simp only [ccResult]
      rw [hfr]
    rw [hrc, ecSamplerChargeMachine_halts L ℓ addrBits queries outputBits A ρ x]
    simp
  · have htc : ccTime (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (2 * (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1))
        = ccTime (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits) := by
      simp only [ccTime]
      rw [hfr]
    rw [htc]
    have hout := ecChargeMachine_output L ℓ addrBits queries outputBits A ρ x
      outputBits (Nat.le_refl _)
    have hrel : queries * (2 * addrBits + 2) = 2 * (queries * (addrBits + 1)) := by
      ring
    simp only [ccTime, hout.2.1]
    omega

/-- The finished charge program uses exactly `CcSamplerRandomBits L ℓ` coins. -/
theorem ecSamplerChargeMachine_coins (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    (EcChargeOf (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
        (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).coins
      = CcSamplerRandomBits L ℓ := by
  rw [ecSamplerChargeMachine_charge L ℓ addrBits queries outputBits A ρ x]

/-- The finished program time charge is at least the sampler bit time budget. -/
theorem ecSamplerChargeMachine_time_ge (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    CcSamplerBitTime L ℓ addrBits queries outputBits
      ≤ (EcChargeOf (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).time := by
  rw [ecSamplerChargeMachine_charge L ℓ addrBits queries outputBits A ρ x]
  exact Nat.le_add_right _ _

/-- The sampler bit time budget is bounded by the program's `CcBitTime` at completion. -/
theorem ecSamplerChargeMachine_bitTime_ge (L ℓ addrBits queries outputBits : ℕ)
    (A : List Bool → Bool) (ρ : ℕ → Bool) (x : List Bool) :
    CcSamplerBitTime L ℓ addrBits queries outputBits
      ≤ CcBitTime (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
          (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits) := by
  simp only [CcBitTime]
  rw [ecSamplerChargeMachine_charge L ℓ addrBits queries outputBits A ρ x]
  show CcSamplerBitTime L ℓ addrBits queries outputBits
      ≤ CcSamplerBitTime L ℓ addrBits queries outputBits + outputBits + CcInputBits x
          + (queries * addrBits + outputBits)
  omega

/-- A program that writes each random seed bit to the tape, advances the head, and finally
accepts. -/
def ecSeedStoreMachine (L ℓ : ℕ) : CcProgram (4 * EcHashSeedBits L ℓ) where
  states := fun i =>
    if h : (i : ℕ) < 4 * EcHashSeedBits L ℓ then
      if hm : (i : ℕ) % 4 = 0 then
        CcAct.coinFlip ⟨(i : ℕ) + 1, by omega⟩ ⟨(i : ℕ) + 2, by omega⟩
      else if hm : (i : ℕ) % 4 = 1 then
        CcAct.write true ⟨(i : ℕ) + 2, by omega⟩
      else if hm : (i : ℕ) % 4 = 2 then
        CcAct.write false ⟨(i : ℕ) + 1, by omega⟩
      else
        CcAct.moveR ⟨(i : ℕ) + 1, by omega⟩
    else CcAct.accept

/-- The final seed storage state accepts. -/
private theorem ecSeedStoreMachine_acceptAct (L ℓ : ℕ) {i : ℕ}
    (hi : i ≤ 4 * EcHashSeedBits L ℓ) (h : ¬ i < 4 * EcHashSeedBits L ℓ) :
    (ecSeedStoreMachine L ℓ).states ⟨i, by omega⟩ = CcAct.accept := by
  simp only [ecSeedStoreMachine]
  rw [dif_neg h]

/-- After storing `i` seed bits, the first `i` tape cells contain those random bits and all
counters and remaining tape cells have the stated values. -/
private theorem ecSeedStoreMachine_run (L ℓ : ℕ) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) :
    ∀ i ≤ EcHashSeedBits L ℓ,
      ((ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).state : ℕ) = 4 * i
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).time = 3 * i
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).coins = i
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).coinIdx = i
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).head = i
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).queries = 0
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).queryBits = 0
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).query = []
      ∧ ∀ k, (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * i)).tape k
          = if k < i then ρ k else x.getD k false := by
  intro i hi
  induction i with
  | zero =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro k
    show (ccInit (4 * EcHashSeedBits L ℓ) x).tape k = if k < 0 then ρ k else x.getD k false
    simp
    rfl
  | succ n ihn =>
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := ihn (by omega)
    rw [show 3 * (n + 1) = 3 * n + 3 from by omega]
    have hst1 : (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n)).state
        = ⟨4 * n, by omega⟩ := Fin.val_injective r1
    have hact1 : (ecSeedStoreMachine L ℓ).states
          (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n)).state
        = CcAct.coinFlip ⟨4 * n + 1, by omega⟩ ⟨4 * n + 2, by omega⟩ := by
      rw [hst1]
      simp only [ecSeedStoreMachine]
      rw [dif_pos (by omega), dif_pos (by omega)]
    have hstep1 : ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)
        = ccStep (ecSeedStoreMachine L ℓ) A ρ
            (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n)) := rfl
    have hmid1 :
        ((ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state : ℕ)
          = (if ρ n then 4 * n + 1 else 4 * n + 2)
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).time = 3 * n + 1
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).coins = n + 1
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).coinIdx = n + 1
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).head = n
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).queries = 0
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).queryBits = 0
      ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).query = []
      ∧ ∀ k, (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).tape k
          = if k < n then ρ k else x.getD k false := by
      rw [hstep1]
      simp only [ccStep]
      rw [hact1]
      simp only [r2, r3, r4, r5, r6, r7, r8]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | rfl | trivial | exact fun k => r9 k | (split_ifs <;> rfl)
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hmid1
    have hnS : n < EcHashSeedBits L ℓ := by omega
    by_cases hc : ρ n = true
    · have hst1' : ((ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state : ℕ)
          = 4 * n + 1 := by
        rw [m1, hc]
        simp
      have hact2 : (ecSeedStoreMachine L ℓ).states
            (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state
          = CcAct.write true ⟨4 * n + 3, by omega⟩ := by
        rw [show (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state
              = ⟨4 * n + 1, by omega⟩ from Fin.val_injective hst1']
        simp only [ecSeedStoreMachine]
        rw [dif_pos (by omega), dif_neg (by omega), dif_pos (by omega)]
      have hstep2 : ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)
          = ccStep (ecSeedStoreMachine L ℓ) A ρ
              (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)) := by
        show ccRun (ecSeedStoreMachine L ℓ) A ρ x ((3 * n + 1) + 1) = _
        rfl
      have hmid2 :
          ((ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).state : ℕ) = 4 * n + 3
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).time = 3 * n + 2
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).coins = n + 1
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).coinIdx = n + 1
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).head = n
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).queries = 0
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).queryBits = 0
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).query = []
        ∧ ∀ k, (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).tape k
            = if k = n then true else if k < n then ρ k else x.getD k false := by
        rw [hstep2]
        simp only [ccStep]
        rw [hact2]
        simp only [m2, m3, m4, m5, m6, m7, m8, m9]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
          fun _ => trivial⟩
      have hact3 : (ecSeedStoreMachine L ℓ).states
            (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).state
          = CcAct.moveR ⟨4 * n + 4, by omega⟩ := by
        rw [show (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).state
              = ⟨4 * n + 3, by omega⟩ from Fin.val_injective hmid2.1]
        simp only [ecSeedStoreMachine]
        rw [dif_pos (by omega), dif_neg (by omega), dif_neg (by omega),
          dif_neg (by omega)]
      have hstep3 : ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 3)
          = ccStep (ecSeedStoreMachine L ℓ) A ρ
              (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)) := by
        show ccRun (ecSeedStoreMachine L ℓ) A ρ x ((3 * n + 2) + 1) = _
        rfl
      rw [hstep3]
      simp only [ccStep]
      rw [hact3]
      obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hmid2
      simp only [w2, w3, w4, w5, w6, w7, w8]
      refine ⟨show (4 * n + 4 : ℕ) = 4 * (n + 1) from by omega, trivial, trivial,
        trivial, trivial, trivial, trivial, trivial, ?_⟩
      intro k
      rw [w9 k]
      rcases Nat.lt_trichotomy k n with h | h | h
      · have hne : k ≠ n := by omega
        have h3 : k < n + 1 := by omega
        simp [h, hne, h3]
      · subst h
        simp [hc]
      · have hne : k ≠ n := by omega
        have h1 : ¬(k < n) := by omega
        have h2 : ¬(k < n + 1) := by omega
        simp [hne, h1, h2]
    · have hst1' : ((ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state : ℕ)
          = 4 * n + 2 := by
        rw [m1, if_neg hc]
      have hact2 : (ecSeedStoreMachine L ℓ).states
            (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state
          = CcAct.write false ⟨4 * n + 3, by omega⟩ := by
        rw [show (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)).state
              = ⟨4 * n + 2, by omega⟩ from Fin.val_injective hst1']
        simp only [ecSeedStoreMachine]
        rw [dif_pos (by omega), dif_neg (by omega), dif_neg (by omega),
          dif_pos (by omega)]
      have hstep2 : ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)
          = ccStep (ecSeedStoreMachine L ℓ) A ρ
              (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 1)) := by
        show ccRun (ecSeedStoreMachine L ℓ) A ρ x ((3 * n + 1) + 1) = _
        rfl
      have hmid2 :
          ((ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).state : ℕ) = 4 * n + 3
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).time = 3 * n + 2
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).coins = n + 1
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).coinIdx = n + 1
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).head = n
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).queries = 0
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).queryBits = 0
        ∧ (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).query = []
        ∧ ∀ k, (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).tape k
            = if k = n then false else if k < n then ρ k else x.getD k false := by
        rw [hstep2]
        simp only [ccStep]
        rw [hact2]
        simp only [m2, m3, m4, m5, m6, m7, m8, m9]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
          fun _ => trivial⟩
      have hact3 : (ecSeedStoreMachine L ℓ).states
            (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).state
          = CcAct.moveR ⟨4 * n + 4, by omega⟩ := by
        rw [show (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)).state
              = ⟨4 * n + 3, by omega⟩ from Fin.val_injective hmid2.1]
        simp only [ecSeedStoreMachine]
        rw [dif_pos (by omega), dif_neg (by omega), dif_neg (by omega),
          dif_neg (by omega)]
      have hstep3 : ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 3)
          = ccStep (ecSeedStoreMachine L ℓ) A ρ
              (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * n + 2)) := by
        show ccRun (ecSeedStoreMachine L ℓ) A ρ x ((3 * n + 2) + 1) = _
        rfl
      rw [hstep3]
      simp only [ccStep]
      rw [hact3]
      obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hmid2
      simp only [w2, w3, w4, w5, w6, w7, w8]
      refine ⟨show (4 * n + 4 : ℕ) = 4 * (n + 1) from by omega, trivial,
        trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
      intro k
      rw [w9 k]
      rcases Nat.lt_trichotomy k n with h | h | h
      · have hne : k ≠ n := by omega
        have h3 : k < n + 1 := by omega
        simp [h, hne, h3]
      · subst h
        simp [hc]
      · have hne : k ≠ n := by omega
        have h1 : ¬(k < n) := by omega
        have h2 : ¬(k < n + 1) := by omega
        simp [hne, h1, h2]

/-- The seed storage configuration remains fixed after all seed bits have been stored. -/
private theorem ecSeedStoreMachine_frozen (L ℓ : ℕ) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) :
    ∀ t ≥ 3 * EcHashSeedBits L ℓ,
      ccRun (ecSeedStoreMachine L ℓ) A ρ x t
        = ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ) := by
  intro t ht
  induction t with
  | zero =>
    exact congrArg (ccRun (ecSeedStoreMachine L ℓ) A ρ x) (Nat.le_zero.mp ht).symm
  | succ n ihn =>
    rcases Nat.lt_or_ge (3 * EcHashSeedBits L ℓ) (n + 1) with hlt | hge
    · have hstep : ccRun (ecSeedStoreMachine L ℓ) A ρ x (n + 1)
          = ccStep (ecSeedStoreMachine L ℓ) A ρ
              (ccRun (ecSeedStoreMachine L ℓ) A ρ x n) := rfl
      have hrun := ecSeedStoreMachine_run L ℓ A ρ x (EcHashSeedBits L ℓ) (Nat.le_refl _)
      have hstF : (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ)).state
          = ⟨4 * EcHashSeedBits L ℓ, by omega⟩ := Fin.val_injective hrun.1
      have hacc : (ecSeedStoreMachine L ℓ).states
            (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ)).state
          = CcAct.accept := by
        rw [hstF]
        exact ecSeedStoreMachine_acceptAct L ℓ (Nat.le_refl _)
          (by omega)
      have hn : 3 * EcHashSeedBits L ℓ ≤ n := by omega
      rw [hstep, ihn hn]
      simp only [ccStep]
      rw [hacc]
    · have heq : 3 * EcHashSeedBits L ℓ = n + 1 := by omega
      exact congrArg (ccRun (ecSeedStoreMachine L ℓ) A ρ x) heq.symm

/-- The seed storage program accepts after three steps per seed bit. -/
theorem ecSeedStoreMachine_halts (L ℓ : ℕ) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) :
    ccResult (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ) = some true := by
  have hrun := ecSeedStoreMachine_run L ℓ A ρ x (EcHashSeedBits L ℓ) (Nat.le_refl _)
  have hstF : (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ)).state
      = ⟨4 * EcHashSeedBits L ℓ, by omega⟩ := Fin.val_injective hrun.1
  have hacc : (ecSeedStoreMachine L ℓ).states
        (ccRun (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ)).state
      = CcAct.accept := by
    rw [hstF]
    exact ecSeedStoreMachine_acceptAct L ℓ (Nat.le_refl _) (by omega)
  simp only [ccResult]
  rw [hacc]

/-- The seed storage program consumes exactly the hash seed length in coins. -/
theorem ecSeedStoreMachine_coins (L ℓ : ℕ) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) :
    (EcChargeOf (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ)).coins
      = EcHashSeedBits L ℓ := by
  have hrun := ecSeedStoreMachine_run L ℓ A ρ x (EcHashSeedBits L ℓ) (Nat.le_refl _)
  simp only [EcChargeOf, ccCoinsRead, hrun.2.2.1]

/-- The finished seed storage tape contains the supplied seed bits followed by the original
input tape. -/
theorem ecSeedStoreMachine_tape (L ℓ : ℕ) (A : List Bool → Bool) (x : List Bool)
    (t : Fin (EcHashSeedBits L ℓ) → Bool) (k : ℕ) :
    (ccRun (ecSeedStoreMachine L ℓ) A (ccCoinString t) x
        (3 * EcHashSeedBits L ℓ)).tape k
      = if h : k < EcHashSeedBits L ℓ then t ⟨k, h⟩ else x.getD k false := by
  have hrun := ecSeedStoreMachine_run L ℓ A (ccCoinString t) x
    (EcHashSeedBits L ℓ) (Nat.le_refl _)
  rw [hrun.2.2.2.2.2.2.2.2 k]
  by_cases hk : k < EcHashSeedBits L ℓ
  · rw [if_pos hk]
    simp only [ccCoinString, dif_pos hk]
  · rw [if_neg hk, dif_neg hk]

/-- Decoding the stored tape recovers the seed decoded from the supplied coin string. -/
theorem ecSeedStoreMachine_seed (L ℓ : ℕ) (A : List Bool → Bool) (x : List Bool)
    (t : Fin (EcHashSeedBits L ℓ) → Bool) :
    ecSeedOfTape L ℓ (fun k : Fin (EcHashSeedBits L ℓ) =>
      (ccRun (ecSeedStoreMachine L ℓ) A (ccCoinString t) x
        (3 * EcHashSeedBits L ℓ)).tape k.val)
      = ecSeedOfTape L ℓ t := by
  have hfun : (fun k : Fin (EcHashSeedBits L ℓ) =>
      (ccRun (ecSeedStoreMachine L ℓ) A (ccCoinString t) x
        (3 * EcHashSeedBits L ℓ)).tape k.val) = t := by
    funext k
    rw [ecSeedStoreMachine_tape L ℓ A x t k.val, dif_pos (Fin.is_lt k)]
  rw [hfun]

/-- The seed storage program satisfies `CcPolyTime` with bound `3 * EcHashSeedBits L ℓ + 1` and
exponent zero. -/
theorem ecSeedStoreMachine_polytime (L ℓ : ℕ) :
    CcPolyTime (ecSeedStoreMachine L ℓ) (3 * EcHashSeedBits L ℓ + 1) 0 := by
  intro A ρ x
  have hfr := ecSeedStoreMachine_frozen L ℓ A ρ x
    (2 * (3 * EcHashSeedBits L ℓ + 1)) (by omega)
  have hb : (3 * EcHashSeedBits L ℓ + 1) * x.length ^ 0 + (3 * EcHashSeedBits L ℓ + 1)
      = 2 * (3 * EcHashSeedBits L ℓ + 1) := by
    rw [pow_zero, Nat.mul_one]
    omega
  rw [hb]
  constructor
  · have hrc : ccResult (ecSeedStoreMachine L ℓ) A ρ x (2 * (3 * EcHashSeedBits L ℓ + 1))
        = ccResult (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ) := by
      simp only [ccResult]
      rw [hfr]
    rw [hrc, ecSeedStoreMachine_halts L ℓ A ρ x]
    simp
  · have htc : ccTime (ecSeedStoreMachine L ℓ) A ρ x (2 * (3 * EcHashSeedBits L ℓ + 1))
        = ccTime (ecSeedStoreMachine L ℓ) A ρ x (3 * EcHashSeedBits L ℓ) := by
      simp only [ccTime]
      rw [hfr]
    rw [htc]
    have hrun := ecSeedStoreMachine_run L ℓ A ρ x (EcHashSeedBits L ℓ) (Nat.le_refl _)
    simp only [ccTime, hrun.2.1]
    omega

/-- Combine the charge program's polynomial time, exact coin usage, and time lower bound with
correctness of stored seed decoding. -/
theorem frontier2 (L ℓ addrBits queries outputBits : ℕ) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) :
    CcPolyTime (ecSamplerChargeMachine L ℓ addrBits queries outputBits)
      (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits + 1) 0
      ∧ (EcChargeOf (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
            (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).coins
        = CcSamplerRandomBits L ℓ
      ∧ CcSamplerBitTime L ℓ addrBits queries outputBits
          ≤ (EcChargeOf (ecSamplerChargeMachine L ℓ addrBits queries outputBits) A ρ x
              (L + EcHashSeedBits L ℓ + queries * (addrBits + 1) + 2 * outputBits)).time
      ∧ ∀ t : Fin (EcHashSeedBits L ℓ) → Bool,
          ecSeedOfTape L ℓ (fun k : Fin (EcHashSeedBits L ℓ) =>
            (ccRun (ecSeedStoreMachine L ℓ) A (ccCoinString t) x
              (3 * EcHashSeedBits L ℓ)).tape k.val)
            = ecSeedOfTape L ℓ t :=
  ⟨ecSamplerChargeMachine_polytime L ℓ addrBits queries outputBits,
    ecSamplerChargeMachine_coins L ℓ addrBits queries outputBits A ρ x,
    ecSamplerChargeMachine_time_ge L ℓ addrBits queries outputBits A ρ x,
    fun t => ecSeedStoreMachine_seed L ℓ A x t⟩

end Qatlib.Concepts.ProbabilityCore.Concentration.CountingHash
