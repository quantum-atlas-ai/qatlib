/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.CountingComplexityDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCounting
import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCountingDefs

/-!
# Hash-based counting estimates and failure bounds

This module proves exact first and second moments for `CcEstimate`, a rescaled zero-fiber count
for affine Boolean hashes. A coordinate-flip bijection gives balanced row parities and the
pairwise joint-zero counts needed for the variance calculation.

The variance yields threshold and relative-error failure bounds, which are transported to
sampler output fibers and events. Explicit bit-time inequalities account for oracle access.
These classical counting estimates complement the quantum counting and estimation tasks of
[BrassardEtAl2002].

## Main statements

* `ccPairIndependence`: joint-zero counts factor for distinct witnesses.
* `ccEstimateDevSq_eq`: the exact sum of squared deviations of the estimator.
* `ccFailureProb_le_eps`: a failure budget bounds relative-error failure probability.
* `ccSamplerEventSet_failure_prob`: the same failure bound applies to sampler events.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCounting
open Qatlib.Concepts.CountingClasses.ClassTransport

/-- A relation of positive finite count contains a witness. -/
private theorem ecRelCount_pos {L : ℕ} (R : Set (Fin L → Bool)) (h : EcRelCount R > 0) :
    ∃ w : Fin L → Bool, R w := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.mp h
  exact ⟨w, (Finset.mem_filter.mp hw).2⟩

/-- A relation of count zero has zero zero-hash fiber count for every seed. -/
private theorem ecRelFiberCount_eq_zero_of_count_zero {L ℓ : ℕ} (R : Set (Fin L → Bool))
    (h : EcRelCount R = 0) (s : EcHashSeed L ℓ) : EcRelFiberCount R s = 0 := by
  classical
  have hcard : (Finset.univ.filter (fun w : Fin L → Bool => R w)).card = 0 := by
    unfold EcRelCount at h
    exact h
  unfold EcRelFiberCount
  rw [ecCard_eq_sum]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : R w
  · have hpos : 0 < (Finset.univ.filter (fun w : Fin L → Bool => R w)).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
    omega
  · simp [hw]

/-- The sum of the rescaled estimates over all hash seeds equals the relation count times `2 ^
(ℓ * L + ℓ)`. -/
theorem ccEstimate_sum {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ∑ s : EcHashSeed L ℓ, CcEstimate R s = EcRelCount R * 2 ^ (ℓ * L + ℓ) := by
  classical
  have h := ecRelFiberCount_sum (L := L) (ℓ := ℓ) R
  calc ∑ s : EcHashSeed L ℓ, CcEstimate R s
      = ∑ s : EcHashSeed L ℓ, (2 ^ ℓ * EcRelFiberCount R s) := by
        apply Fintype.sum_congr
          (f := fun s => CcEstimate R s) (g := fun s => 2 ^ ℓ * EcRelFiberCount R s)
          (fun s => rfl)
    _ = 2 ^ ℓ * (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s) := by
        rw [← Finset.mul_sum]
    _ = 2 ^ ℓ * (EcRelCount R * 2 ^ (ℓ * L)) := by rw [h]
    _ = EcRelCount R * 2 ^ (ℓ * L + ℓ) := by
      calc 2 ^ ℓ * (EcRelCount R * 2 ^ (ℓ * L))
          = EcRelCount R * (2 ^ ℓ * 2 ^ (ℓ * L)) := by ac_rfl
        _ = EcRelCount R * 2 ^ (ℓ + ℓ * L) := by rw [pow_add]
        _ = EcRelCount R * 2 ^ (ℓ * L + ℓ) := by rw [Nat.add_comm]

/-- A seed is good exactly when twice its estimate is at least the true relation count. -/
theorem ccGoodSeed_iff {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) :
    CcGoodSeed R s ↔ EcRelCount R ≤ 2 * CcEstimate R s := Iff.rfl

/-- Every hash seed is either good or bad for the specified relation. -/
theorem ccGoodSeed_or_bad {L ℓ : ℕ} (R : Set (Fin L → Bool)) (s : EcHashSeed L ℓ) :
    CcGoodSeed R s ∨ CcBadSeed R s := by
  by_cases h : CcGoodSeed R s
  · exact Or.inl h
  · exact Or.inr h

/-- There exists a hash seed whose estimate is at least the true relation count. -/
theorem ccBestSeed_estimate {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    ∃ s : EcHashSeed L ℓ, EcRelCount R ≤ CcEstimate R s := by
  obtain ⟨s, h1, _⟩ := ecRelFiberCount_best (L := L) (ℓ := ℓ) R
  exact ⟨s, h1⟩

/-- A relation of count zero has no bad hash seeds. -/
theorem ccNoBadSeed_of_zero_count {L ℓ : ℕ} (R : Set (Fin L → Bool))
    (h : EcRelCount R = 0) : CcBadSeedCount (L := L) (ℓ := ℓ) R = 0 := by
  classical
  unfold CcBadSeedCount
  rw [Finset.sum_eq_zero]
  intro s _
  have h1 : EcRelFiberCount R s = 0 := ecRelFiberCount_eq_zero_of_count_zero R h s
  have hgood : CcGoodSeed R s := by
    rw [ccGoodSeed_iff]
    simp [CcEstimate, h1, h]
  simp [hgood, CcBadSeed]

/-- For a relation of positive count, at most half of the hash seeds give an estimate at least
twice the true count. -/
theorem ccOverEstimate_count_le_half {L ℓ : ℕ} (R : Set (Fin L → Bool))
    (hm : 0 < EcRelCount R) :
    2 * (∑ s : EcHashSeed L ℓ, if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)
      ≤ 2 ^ (ℓ * L + ℓ) := by
  classical
  have hterm : ∀ s : EcHashSeed L ℓ,
      (if 2 * EcRelCount R ≤ CcEstimate R s then 2 * EcRelCount R else 0)
        ≤ CcEstimate R s := by
    intro s
    by_cases hs : 2 * EcRelCount R ≤ CcEstimate R s
    · rw [if_pos hs]
      exact hs
    · rw [if_neg hs]
      exact Nat.zero_le _
  have h1 : (∑ s ∈ (Finset.univ : Finset (EcHashSeed L ℓ)),
        (if 2 * EcRelCount R ≤ CcEstimate R s then 2 * EcRelCount R else 0))
      ≤ ∑ s ∈ (Finset.univ : Finset (EcHashSeed L ℓ)), CcEstimate R s := by
    refine Finset.sum_le_sum ?_
    intro s _
    exact hterm s
  have h2a : (∑ s : EcHashSeed L ℓ,
        (if 2 * EcRelCount R ≤ CcEstimate R s then 2 * EcRelCount R else 0))
      = ∑ s : EcHashSeed L ℓ,
        (2 * EcRelCount R * (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)) := by
    refine Fintype.sum_congr
      (fun s => (if 2 * EcRelCount R ≤ CcEstimate R s then 2 * EcRelCount R else 0))
      (fun s => 2 * EcRelCount R * (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)) ?_
    intro s
    by_cases hs : 2 * EcRelCount R ≤ CcEstimate R s <;> simp [hs]
  have h2b : (∑ s : EcHashSeed L ℓ,
        (2 * EcRelCount R * (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)))
      = 2 * EcRelCount R * (∑ s : EcHashSeed L ℓ,
        (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)) := by
    rw [← Finset.mul_sum]
  have h2 : (∑ s : EcHashSeed L ℓ,
        (if 2 * EcRelCount R ≤ CcEstimate R s then 2 * EcRelCount R else 0))
      = 2 * EcRelCount R * (∑ s : EcHashSeed L ℓ,
        (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)) :=
    h2a.trans h2b
  have h3 : 2 * EcRelCount R * (∑ s : EcHashSeed L ℓ,
        (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0))
      ≤ EcRelCount R * 2 ^ (ℓ * L + ℓ) := by
    have hB : (∑ s : EcHashSeed L ℓ, CcEstimate R s) = EcRelCount R * 2 ^ (ℓ * L + ℓ) :=
      ccEstimate_sum (L := L) (ℓ := ℓ) R
    have h' : 2 * EcRelCount R * (∑ s : EcHashSeed L ℓ,
          (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0))
        ≤ ∑ s : EcHashSeed L ℓ, CcEstimate R s := by
      rw [← h2]
      exact h1
    rw [hB] at h'
    exact h'
  have h4 : EcRelCount R * (2 * (∑ s : EcHashSeed L ℓ,
        (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0)))
      ≤ EcRelCount R * 2 ^ (ℓ * L + ℓ) := by
    have h' := h3
    rw [show 2 * EcRelCount R * (∑ s : EcHashSeed L ℓ,
          (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0))
        = EcRelCount R * (2 * (∑ s : EcHashSeed L ℓ,
          (if 2 * EcRelCount R ≤ CcEstimate R s then 1 else 0))) by ac_rfl] at h'
    exact h'
  exact Nat.le_of_mul_le_mul_left h4 hm

/-- Boolean exclusive-or equals addition in the Boolean additive structure. -/
private theorem ccBool_add_xor (a b : Bool) : (a ^^ b) = (a + b) := by
  cases a <;> cases b <;> decide

/-- Boolean negation equals exclusive-or with `true`. -/
private theorem ccBool_not_xor (b : Bool) : (!b) = (b ^^ true) := by
  cases b <;> decide

/-- Exclusive-or with `false` preserves a Boolean value. -/
private theorem ccBool_xor_false (b : Bool) : (b ^^ false) = b := by
  cases b <;> decide

/-- The Boolean value `false` is the additive zero. -/
private theorem ccBool_false_zero : (false : Bool) = 0 := by decide

/-- Adding a Boolean value to itself gives `false`. -/
private theorem ccBool_add_self (b : Bool) : (b + b) = false := by
  cases b <;> decide

/-- Boolean conjunction distributes over exclusive-or in its left argument. -/
private theorem ccBool_and_xor_l (a b c : Bool) :
    ((a ^^ b) && c) = ((a && c) ^^ (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Boolean conjunction distributes over exclusive-or in its right argument. -/
private theorem ccBool_and_xor_r (a b c : Bool) :
    (c && (a ^^ b)) = ((c && a) ^^ (c && b)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The exclusive-or of two Boolean values is `false` exactly when they are equal. -/
private theorem ccBool_xor_eq_false (u v : Bool) : (u ^^ v) = false ↔ u = v := by
  cases u <;> cases v <;> decide

/-- A finite sum of pointwise Boolean exclusive-ors equals the exclusive-or of the two finite
sums. -/
private theorem ccSumXor {L : ℕ} (a b : Fin L → Bool) :
    (∑ j : Fin L, (a j ^^ b j)) = ((∑ j : Fin L, a j) ^^ (∑ j : Fin L, b j)) := by
  classical
  have h1 : (∑ j : Fin L, (a j ^^ b j)) = (∑ j : Fin L, (a j + b j)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (ccBool_add_xor (a j) (b j)).symm
  rw [h1, Finset.sum_add_distrib]
  exact (ccBool_add_xor _ _).symm

/-- An affine Boolean hash vanishes on a witness exactly when every offset bit equals the
corresponding row parity. -/
theorem ccEcHashZero_iff {L ℓ : ℕ} (mat : Fin ℓ → Fin L → Bool) (off : Fin ℓ → Bool)
    (w : Fin L → Bool) :
    EcHashZero (mat, off) w ↔ ∀ i : Fin ℓ, off i = CcRowParity w (mat i) := by
  constructor
  · intro h i
    have hx := h i
    have hxor : (CcRowParity w (mat i) ^^ off i) = false := by
      show Bool.xor (∑ j : Fin L, (mat i j && w j)) (off i) = false
      exact hx
    exact ((ccBool_xor_eq_false _ _).mp hxor).symm
  · intro h i
    have hxor : (CcRowParity w (mat i) ^^ off i) = false :=
      (ccBool_xor_eq_false _ _).mpr ((h i).symm)
    show Bool.xor (∑ j : Fin L, (mat i j && w j)) (off i) = false
    exact hxor

/-- The difference of two witness row parities equals the row parity of their pointwise
exclusive-or. -/
theorem ccRowParity_diff {L : ℕ} (w w' row : Fin L → Bool) :
    CcRowParityDiff w w' row = CcRowParity (CcWitnessDiff w w') row := by
  classical
  have h1 : (∑ j : Fin L, (row j && CcWitnessDiff w w' j))
      = ∑ j : Fin L, ((row j && w j) ^^ (row j && w' j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [CcWitnessDiff]
    exact ccBool_and_xor_r _ _ _
  have h2 : (∑ j : Fin L, ((row j && w j) ^^ (row j && w' j)))
      = ((∑ j : Fin L, (row j && w j)) ^^ (∑ j : Fin L, (row j && w' j))) := ccSumXor _ _
  unfold CcRowParityDiff CcRowParity
  rw [h1, h2]
  exact (ccBool_add_xor _ _).symm

/-- The pointwise exclusive-or of two witnesses is everywhere `false` exactly when the witnesses
are equal. -/
theorem ccWitnessDiff_eq_zero_iff {L : ℕ} (w w' : Fin L → Bool) :
    (∀ j : Fin L, CcWitnessDiff w w' j = false) ↔ w = w' := by
  constructor
  · intro h
    funext j
    have hx : (w j ^^ w' j) = false := by
      show Bool.xor (w j) (w' j) = false
      exact h j
    exact (ccBool_xor_eq_false _ _).mp hx
  · intro h j
    subst h
    simp [CcWitnessDiff]

/-- Two witnesses have agreeing matrix parities exactly when every matrix row has even parity
against their difference. -/
theorem ccMatrixParityAgree_iff {L ℓ : ℕ} (w w' : Fin L → Bool)
    (mat : Fin ℓ → Fin L → Bool) :
    CcMatrixParityAgree w w' mat ↔
      ∀ i : Fin ℓ, CcRowParity (CcWitnessDiff w w') (mat i) = false := by
  constructor
  · intro h i
    exact (ccRowParity_diff w w' (mat i)).symm ▸ h i
  · intro h i
    exact (ccRowParity_diff w w' (mat i)) ▸ h i

/-- Flipping a row coordinate where the witness difference is `true` negates its row parity. -/
theorem ccRowParity_flip {L : ℕ} (d row : Fin L → Bool) (j₀ : Fin L)
    (hd : d j₀ = true) :
    CcRowParity d (CcFlipAt row j₀) = !CcRowParity d row := by
  classical
  unfold CcRowParity
  have hflip : ∀ j : Fin L,
      CcFlipAt row j₀ j = (row j ^^ (if j = j₀ then true else false)) := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [CcFlipAt]
      exact ccBool_not_xor (row j)
    · rw [CcFlipAt, if_neg hj]
      rw [if_neg hj]
      exact (ccBool_xor_false _).symm
  have h1 : (∑ j : Fin L, (CcFlipAt row j₀ j && d j))
      = (∑ j : Fin L, ((row j ^^ (if j = j₀ then true else false)) && d j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hflip j]
  have h2 : (∑ j : Fin L, ((row j ^^ (if j = j₀ then true else false)) && d j))
      = (∑ j : Fin L, ((row j && d j) ^^ ((if j = j₀ then true else false) && d j))) := by
    apply Finset.sum_congr rfl
    intro j _
    exact ccBool_and_xor_l _ _ _
  rw [h1, h2, ccSumXor]
  have hsingle : (∑ j : Fin L, ((if j = j₀ then true else false) && d j)) = d j₀ := by
    have hconv : (∑ j : Fin L, ((if j = j₀ then true else false) && d j))
        = ∑ j : Fin L, (if j = j₀ then d j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = j₀
      · subst hj
        simp
      · rw [if_neg hj, if_neg hj]
        exact ccBool_false_zero
    rw [hconv]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin L)) j₀ (fun j => d j)]
    simp
  rw [hsingle, hd]
  symm
  exact ccBool_not_xor _

/-- Flipping a Boolean row twice at the same coordinate returns the original row. -/
theorem ccFlipAt_involutive {L : ℕ} (row : Fin L → Bool) (j₀ : Fin L) :
    CcFlipAt (CcFlipAt row j₀) j₀ = row := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    simp [CcFlipAt]
  · simp [CcFlipAt, hj]

/-- Two witnesses both hash to zero exactly when the offset matches the first witness parities
and the two witnesses have agreeing matrix parities. -/
theorem ccJointZero_iff {L ℓ : ℕ} (mat : Fin ℓ → Fin L → Bool) (off : Fin ℓ → Bool)
    (w w' : Fin L → Bool) :
    CcHashJointZero (mat, off) w w' ↔
      (∀ i : Fin ℓ, off i = CcRowParity w (mat i)) ∧ CcMatrixParityAgree w w' mat := by
  constructor
  · intro h
    constructor
    · exact (ccEcHashZero_iff mat off w).mp h.1
    · intro i
      have hw := (ccEcHashZero_iff mat off w).mp h.1 i
      have hw' := (ccEcHashZero_iff mat off w').mp h.2 i
      have hdiff : CcRowParityDiff w w' (mat i) = false := by
        unfold CcRowParityDiff
        rw [← hw, ← hw']
        exact ccBool_add_self _
      exact hdiff
  · intro h
    constructor
    · exact (ccEcHashZero_iff mat off w).mpr h.1
    · apply (ccEcHashZero_iff mat off w').mpr
      intro i
      have hdiff := h.2 i
      unfold CcRowParityDiff at hdiff
      have hxor : (CcRowParity w (mat i) ^^ CcRowParity w' (mat i)) = false := by
        rw [ccBool_add_xor]
        exact hdiff
      have heq : CcRowParity w (mat i) = CcRowParity w' (mat i) :=
        (ccBool_xor_eq_false (CcRowParity w (mat i)) (CcRowParity w' (mat i))).mp hxor
      have hw := h.1 i
      rw [hw]
      exact heq

/-- Every Boolean value equals either `false` or `true`. -/
private theorem ccBool_eq_false_or_true (v : Bool) : v = false ∨ v = true := by
  cases v with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/-- A Boolean value equal to `false` is unequal to `true`. -/
private theorem ccBool_ne_true_of_eq_false {v : Bool} (h : v = false) : v ≠ true := by
  intro h2
  rw [h] at h2
  exact Bool.noConfusion h2

/-- A Boolean value equal to `true` is unequal to `false`. -/
private theorem ccBool_ne_false_of_eq_true {v : Bool} (h : v = true) : v ≠ false := by
  intro h2
  rw [h] at h2
  exact Bool.noConfusion h2

/-- Every row parity is either `false` or `true`. -/
private theorem ccRowParity_eq_false_or_true {L : ℕ} (d row : Fin L → Bool) :
    CcRowParity d row = false ∨ CcRowParity d row = true :=
  ccBool_eq_false_or_true (CcRowParity d row)

/-- Flipping a row at a coordinate where the tested vector is `true` interchanges even and odd
parity. -/
private theorem ccFlipAt_swap_parity {L : ℕ} (d : Fin L → Bool) (j₀ : Fin L)
    (hd : d j₀ = true) (row : Fin L → Bool) :
    (CcRowParity d row = false → CcRowParity d (CcFlipAt row j₀) = true) ∧
      (CcRowParity d row = true → CcRowParity d (CcFlipAt row j₀) = false) := by
  have h := ccRowParity_flip d row j₀ hd
  constructor
  · intro hr
    rw [h, hr]
    rfl
  · intro hr
    rw [h, hr]
    rfl

/-- For a vector with a `true` coordinate, the sets of rows of even and odd parity have equal
cardinality. -/
private theorem ccRowParity_flip_bij {L : ℕ} (d : Fin L → Bool) (j₀ : Fin L)
    (hd : d j₀ = true) :
    (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = false)).card
      = (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = true)).card := by
  refine Finset.card_bij (i := fun (r : Fin L → Bool) _ => CcFlipAt r j₀) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ccFlipAt_swap_parity d j₀ hd r).1 (Finset.mem_filter.mp hr).2
  · intro a₁ ha₁ a₂ ha₂ hEq
    have hEq' : CcFlipAt a₁ j₀ = CcFlipAt a₂ j₀ := hEq
    calc a₁ = CcFlipAt (CcFlipAt a₁ j₀) j₀ := (ccFlipAt_involutive a₁ j₀).symm
      _ = CcFlipAt (CcFlipAt a₂ j₀) j₀ := by rw [hEq']
      _ = a₂ := ccFlipAt_involutive a₂ j₀
  · intro b hb
    refine ⟨CcFlipAt b j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact (ccFlipAt_swap_parity d j₀ hd b).2 (Finset.mem_filter.mp hb).2
    · exact ccFlipAt_involutive b j₀

/-- For a nonzero Boolean vector, exactly `2 ^ (L - 1)` rows have even parity against it. -/
theorem ccRowEvenCount_eq {L : ℕ} (d : Fin L → Bool) (hd : ∃ j : Fin L, d j = true) :
    CcRowEvenCount d = 2 ^ (L - 1) := by
  classical
  obtain ⟨j₀, hdj₀⟩ := hd
  have hL : 0 < L := by
    have hj := j₀.isLt
    omega
  have hbij := ccRowParity_flip_bij d j₀ hdj₀
  have htotal : (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = false)).card
      + (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = true)).card
      = 2 ^ L := by
    have h1 := ecCard_eq_sum (fun r : Fin L → Bool => CcRowParity d r = false)
    have h2 := ecCard_eq_sum (fun r : Fin L → Bool => CcRowParity d r = true)
    rw [h1, h2]
    calc (∑ r : Fin L → Bool, (if CcRowParity d r = false then 1 else 0))
        + (∑ r : Fin L → Bool, (if CcRowParity d r = true then 1 else 0))
        = ∑ r : Fin L → Bool,
            ((if CcRowParity d r = false then 1 else 0)
              + (if CcRowParity d r = true then 1 else 0)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ r : Fin L → Bool, 1 := by
            apply Finset.sum_congr rfl
            intro r _
            rcases ccRowParity_eq_false_or_true d r with hr | hr
            · rw [if_pos hr, if_neg (ccBool_ne_true_of_eq_false hr)]
            · rw [if_neg (ccBool_ne_false_of_eq_true hr), if_pos hr]
      _ = 2 ^ L := by
            calc (∑ r : Fin L → Bool, 1) = (Finset.univ : Finset (Fin L → Bool)).card := by
                  symm
                  exact Finset.card_eq_sum_ones _
              _ = Fintype.card (Fin L → Bool) := Finset.card_univ
              _ = 2 ^ L := card_fin_fun_bool L
  have h2 : 2 * (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = false)).card
      = 2 ^ L := by
    rw [hbij]
    omega
  have hpow : 2 ^ L = 2 ^ (L - 1) * 2 := by
    have hL1 : L = (L - 1) + 1 := by omega
    have h2 : 2 ^ L = 2 ^ (L - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hL1
    rw [h2, Nat.pow_succ]
  have hcard : (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = false)).card
      = 2 ^ (L - 1) := by omega
  unfold CcRowEvenCount
  exact (ecCard_eq_sum (fun r : Fin L → Bool => CcRowParity d r = false)).symm.trans hcard

/-- For a nonzero Boolean vector, exactly `2 ^ (L - 1)` rows have odd parity against it. -/
theorem ccRowOddCount_eq {L : ℕ} (d : Fin L → Bool) (hd : ∃ j : Fin L, d j = true) :
    CcRowOddCount d = 2 ^ (L - 1) := by
  classical
  obtain ⟨j₀, hdj₀⟩ := hd
  have hbij := ccRowParity_flip_bij d j₀ hdj₀
  have hodd : CcRowOddCount d
      = (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = true)).card := by
    unfold CcRowOddCount
    exact (ecCard_eq_sum (fun r : Fin L → Bool => CcRowParity d r = true)).symm
  have heven : (Finset.univ.filter (fun r : Fin L → Bool => CcRowParity d r = false)).card
      = CcRowEvenCount d := by
    unfold CcRowEvenCount
    exact ecCard_eq_sum (fun r : Fin L → Bool => CcRowParity d r = false)
  rw [hodd, ← hbij, heven]
  exact ccRowEvenCount_eq d ⟨j₀, hdj₀⟩

/-- For a nonzero Boolean vector, exactly `2 ^ (ℓ * (L - 1))` matrices have even parity against
it in every row. -/
theorem ccMatrixEvenCount_eq {L ℓ : ℕ} (d : Fin L → Bool) (hd : ∃ j : Fin L, d j = true) :
    CcMatrixEvenCount ℓ d = 2 ^ (ℓ * (L - 1)) := by
  classical
  have hrow : CcRowEvenCount d = 2 ^ (L - 1) := ccRowEvenCount_eq d hd
  have hterm : ∀ x : Fin ℓ → (Fin L → Bool),
      (∏ i : Fin ℓ, (if CcRowParity d (x i) = false then 1 else 0))
        = (if (∀ i : Fin ℓ, CcRowParity d (x i) = false) then 1 else 0) := by
    intro x
    by_cases h : ∀ i : Fin ℓ, CcRowParity d (x i) = false
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i _
      rw [if_pos (h i)]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [if_neg hi]
  have hprod := Fintype.prod_sum (ι := Fin ℓ) (κ := fun _ => (Fin L → Bool))
    (f := fun (_ : Fin ℓ) (r : Fin L → Bool) =>
      (if CcRowParity d r = false then 1 else 0 : ℕ))
  have hmatrix : CcMatrixEvenCount ℓ d = (CcRowEvenCount d) ^ ℓ := by
    calc CcMatrixEvenCount ℓ d
        = ∑ x : Fin ℓ → (Fin L → Bool),
            (if (∀ i : Fin ℓ, CcRowParity d (x i) = false) then 1 else 0) := rfl
      _ = ∑ x : Fin ℓ → (Fin L → Bool),
            (∏ i : Fin ℓ, (if CcRowParity d (x i) = false then 1 else 0)) := by
            apply Fintype.sum_congr
            intro x
            exact (hterm x).symm
      _ = ∏ i : Fin ℓ,
            (∑ r : Fin L → Bool, (if CcRowParity d r = false then 1 else 0)) := by
            rw [← hprod]
      _ = ∏ i : Fin ℓ, CcRowEvenCount d := by
            apply Finset.prod_congr rfl
            intro i _
            rfl
      _ = (CcRowEvenCount d) ^ ℓ := by
            rw [Finset.prod_const]
            congr 1
            exact Finset.card_univ.trans (Fintype.card_fin ℓ)
  rw [hmatrix, hrow]
  calc (2 ^ (L - 1)) ^ ℓ = 2 ^ ((L - 1) * ℓ) := (Nat.pow_mul 2 (L - 1) ℓ).symm
    _ = 2 ^ (ℓ * (L - 1)) := by rw [Nat.mul_comm]

/-- Exactly one Boolean offset vector agrees at every coordinate with a specified Boolean
vector. -/
private theorem ccOffsetUnique {ℓ : ℕ} (g : Fin ℓ → Bool) :
    (∑ off : Fin ℓ → Bool, if (∀ i : Fin ℓ, off i = g i) then 1 else 0) = 1 := by
  classical
  have hconv : (∑ off : Fin ℓ → Bool, if (∀ i : Fin ℓ, off i = g i) then 1 else 0)
      = (∑ off : Fin ℓ → Bool, if off = g then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro off _
    by_cases hc : ∀ i : Fin ℓ, off i = g i
    · have ho : off = g := funext hc
      simp [ho]
    · have ho : off ≠ g := (funext_iff.not).mpr hc
      simp [hc, ho]
  rw [hconv]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin ℓ → Bool)) g (fun _ => 1)]
  simp

/-- The number of hash seeds vanishing on both witnesses equals the piecewise count
`CcPairZeroCount`. -/
theorem ccHashJointZeroCount_eq {L ℓ : ℕ} (w w' : Fin L → Bool) :
    CcHashJointZeroCount ℓ w w' = CcPairZeroCount ℓ w w' := by
  classical
  by_cases hww : w = w'
  · subst hww
    have hconv : (∑ s : EcHashSeed L ℓ, if CcHashJointZero s w w then 1 else 0)
        = (∑ s : EcHashSeed L ℓ, if EcHashZero s w then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      have hiff : CcHashJointZero s w w ↔ EcHashZero s w := by
        unfold CcHashJointZero
        exact and_self_iff
      rw [hiff]
    unfold CcHashJointZeroCount
    rw [hconv, ecHashZero_seed_sum w]
    simp [CcPairZeroCount]
  · have hoff : ∀ (mat : Fin ℓ → Fin L → Bool),
        (∑ off : Fin ℓ → Bool,
          if (∀ i : Fin ℓ, off i = CcRowParity w (mat i))
            ∧ CcMatrixParityAgree w w' mat then 1 else 0)
        = (if CcMatrixParityAgree w w' mat then 1 else 0) := by
      intro mat
      by_cases hag : CcMatrixParityAgree w w' mat
      · rw [if_pos hag]
        have hstep : (∑ off : Fin ℓ → Bool,
            if (∀ i : Fin ℓ, off i = CcRowParity w (mat i))
              ∧ CcMatrixParityAgree w w' mat then 1 else 0)
            = (∑ off : Fin ℓ → Bool,
              if (∀ i : Fin ℓ, off i = CcRowParity w (mat i)) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro off _
          by_cases hc : ∀ i : Fin ℓ, off i = CcRowParity w (mat i)
          · rw [if_pos (And.intro hc hag), if_pos hc]
          · rw [if_neg (fun h => hc h.1), if_neg hc]
        rw [hstep]
        exact ccOffsetUnique (fun i => CcRowParity w (mat i))
      · rw [if_neg hag]
        apply Finset.sum_eq_zero
        intro off _
        rw [if_neg (fun h => hag h.2)]
    have hmain : CcHashJointZeroCount ℓ w w'
        = ∑ mat : Fin ℓ → Fin L → Bool,
            (if CcMatrixParityAgree w w' mat then 1 else 0) := by
      unfold CcHashJointZeroCount
      calc (∑ s : EcHashSeed L ℓ, if CcHashJointZero s w w' then 1 else 0)
          = ∑ mat : Fin ℓ → Fin L → Bool, ∑ off : Fin ℓ → Bool,
              (if CcHashJointZero (mat, off) w w' then 1 else 0) := Fintype.sum_prod_type _
        _ = ∑ mat : Fin ℓ → Fin L → Bool, ∑ off : Fin ℓ → Bool,
              (if (∀ i : Fin ℓ, off i = CcRowParity w (mat i))
                ∧ CcMatrixParityAgree w w' mat then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro mat _
          apply Finset.sum_congr rfl
          intro off _
          simp only [ccJointZero_iff]
        _ = ∑ mat : Fin ℓ → Fin L → Bool,
              (if CcMatrixParityAgree w w' mat then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro mat _
          exact hoff mat
    have hagree : (∑ mat : Fin ℓ → Fin L → Bool,
          (if CcMatrixParityAgree w w' mat then 1 else 0))
        = ∑ mat : Fin ℓ → Fin L → Bool,
          (if (∀ i : Fin ℓ, CcRowParity (CcWitnessDiff w w') (mat i) = false)
            then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro mat _
      by_cases h : CcMatrixParityAgree w w' mat
      · rw [if_pos h, if_pos ((ccMatrixParityAgree_iff w w' mat).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((ccMatrixParityAgree_iff w w' mat).mpr hh))]
    have hnotall : ¬ (∀ j : Fin L, CcWitnessDiff w w' j = false) := by
      intro h
      exact hww ((ccWitnessDiff_eq_zero_iff w w').mp h)
    obtain ⟨j, hj⟩ : ∃ j : Fin L, CcWitnessDiff w w' j = true := by
      by_cases hex : ∃ j : Fin L, CcWitnessDiff w w' j = true
      · exact hex
      · refine False.elim (hnotall ?_)
        intro j'
        by_cases hj' : CcWitnessDiff w w' j' = true
        · exact (hex ⟨j', hj'⟩).elim
        · rcases ccBool_eq_false_or_true (CcWitnessDiff w w' j') with h1 | h1
          · exact h1
          · exact (hj' h1).elim
    have hfinal : (∑ mat : Fin ℓ → Fin L → Bool,
          (if (∀ i : Fin ℓ, CcRowParity (CcWitnessDiff w w') (mat i) = false)
            then 1 else 0))
        = 2 ^ (ℓ * (L - 1)) :=
      ccMatrixEvenCount_eq (CcWitnessDiff w w') ⟨j, hj⟩
    rw [hmain, hagree, hfinal]
    simp [CcPairZeroCount, hww]

/-- For distinct witnesses, their joint-zero seed count times the total seed count equals the
square of the single-witness zero count. -/
theorem ccPairIndependence {L ℓ : ℕ} (w w' : Fin L → Bool) (hww : w ≠ w') :
    CcHashJointZeroCount ℓ w w' * 2 ^ (ℓ * L + ℓ) = (2 ^ (ℓ * L)) ^ 2 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp (fun h => hww (funext h))
  have hL : 0 < L := by
    have hj' := j.isLt
    omega
  have hcount : CcHashJointZeroCount ℓ w w' = 2 ^ (ℓ * (L - 1)) := by
    rw [ccHashJointZeroCount_eq w w']
    simp [CcPairZeroCount, hww]
  rw [hcount]
  calc 2 ^ (ℓ * (L - 1)) * 2 ^ (ℓ * L + ℓ) = 2 ^ (ℓ * (L - 1) + (ℓ * L + ℓ)) := by
        rw [← pow_add]
    _ = 2 ^ (ℓ * L * 2) := by
      have hL1 : L - 1 + 1 = L := by omega
      have h1 : ℓ * (L - 1) + ℓ = ℓ * L := by
        calc ℓ * (L - 1) + ℓ = ℓ * ((L - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = ℓ * L := by rw [hL1]
      have h2 : ℓ * (L - 1) + (ℓ * L + ℓ) = ℓ * L * 2 := by omega
      rw [h2]
    _ = (2 ^ (ℓ * L)) ^ 2 := Nat.pow_mul 2 (ℓ * L) 2

/-- Bit time covers twice the query count, the query-bit charge, the encoded input length, and
the output-bit charge. -/
theorem ccBitTime_charge {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    2 * (EcChargeOf P A ρ x t).queries + (EcChargeOf P A ρ x t).queryBits
      + CcInputBits x + (EcChargeOf P A ρ x t).outputBits
      ≤ CcBitTime P A ρ x t := by
  have h := EcCharge_sound P A ρ x t
  unfold CcBitTime
  omega

/-- Bit time is at least the underlying charged execution time. -/
theorem ccBitTime_ge_time {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) :
    (EcChargeOf P A ρ x t).time ≤ CcBitTime P A ρ x t := by
  unfold CcBitTime
  omega

/-- The encoded input length is the original Boolean-list length plus one. -/
theorem ccInputBits_eq {x : List Bool} : CcInputBits x = x.length + 1 := by
  unfold CcInputBits
  rw [EcEncode_length]

/-- An execution with at least one oracle query has charged time at least two. -/
theorem ccOracleCall_not_free {q : ℕ} (P : CcProgram q) (A : List Bool → Bool) (ρ : ℕ → Bool)
    (x : List Bool) (t : ℕ) (hq : 0 < (EcChargeOf P A ρ x t).queries) :
    2 ≤ (EcChargeOf P A ρ x t).time := by
  have h := EcCharge_sound P A ρ x t
  omega

/-- Twice the oracle query count is bounded by charged execution time. -/
theorem ccOracleCall_queries_le_half {q : ℕ} (P : CcProgram q) (A : List Bool → Bool)
    (ρ : ℕ → Bool) (x : List Bool) (t : ℕ) :
    2 * (EcChargeOf P A ρ x t).queries ≤ (EcChargeOf P A ρ x t).time :=
  EcCharge_queries_le_half_time P A ρ x t

/-- The indicator sum for a sampler output equals the cardinality of its seed fiber. -/
theorem ccSampler_exact {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    (∑ r : Fin L → Bool, if Sam.O r = y then 1 else 0)
      = (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card := by
  classical
  rw [← ecCard_eq_sum]

/-- The sum of estimates for a sampler output fiber equals its cardinality times the total
number of hash seeds. -/
theorem ccSampler_estimate_sum {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    ∑ s : EcHashSeed L ℓ, CcEstimate (EcSamplerSeedSet Sam y) s
      = (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card
        * 2 ^ (ℓ * L + ℓ) := by
  classical
  have h := ccEstimate_sum (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y)
  rw [ecSamplerSeedSet_card] at h
  exact h

/-- Every sampler output fiber possesses a hash seed whose estimate is at least the fiber
cardinality. -/
theorem ccSampler_good_seed {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    ∃ s : EcHashSeed L ℓ,
      (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card
        ≤ CcEstimate (EcSamplerSeedSet Sam y) s := by
  classical
  obtain ⟨s, h1, _⟩ := ecRelFiberCount_best (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y)
  rw [ecSamplerSeedSet_card] at h1
  exact ⟨s, h1⟩

/-- Summing the estimates of a sampler output fiber gives its cardinality multiplied by `2 ^ (ℓ
* L + ℓ)`. -/
theorem ccSampler_average_case {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    (∑ s : EcHashSeed L ℓ, CcEstimate (EcSamplerSeedSet Sam y) s)
      = (Finset.univ.filter (fun r : Fin L → Bool => Sam.O r = y)).card
        * 2 ^ (ℓ * L + ℓ) := by
  exact ccSampler_estimate_sum (L := L) (ℓ := ℓ) Sam y

/-- The natural-number indicator of membership in a relation. -/
private noncomputable def ccInd {L : ℕ} (R : Set (Fin L → Bool)) (w : Fin L → Bool) : ℕ :=
  if R w then 1 else 0

/-- Summing the membership indicator over all witnesses gives the relation count. -/
private theorem ccInd_eq_sum {L : ℕ} (R : Set (Fin L → Bool)) :
    (∑ w : Fin L → Bool, ccInd R w) = EcRelCount R := by
  rw [ecRelCount_eq_sum R]
  rfl

/-- The natural-number membership indicator is idempotent under multiplication. -/
private theorem ccInd_mul_self {L : ℕ} (R : Set (Fin L → Bool)) (w : Fin L → Bool) :
    ccInd R w * ccInd R w = ccInd R w := by
  by_cases h : R w <;> simp [ccInd, h]

/-- A double sum weighted by the equality indicator reduces to the sum of its diagonal terms. -/
private theorem ccDiagSum {L : ℕ} (g : (Fin L → Bool) → (Fin L → Bool) → ℕ) :
    (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, g w w' * (if w = w' then 1 else 0))
      = ∑ w : Fin L → Bool, g w w := by
  apply Fintype.sum_congr
  intro w
  calc (∑ w' : Fin L → Bool, g w w' * (if w = w' then 1 else 0))
      = ∑ w' : Fin L → Bool, (if w' = w then g w w' else 0) := by
        apply Fintype.sum_congr
        intro w'
        by_cases h : w = w'
        · subst h
          simp
        · simp [h, Ne.symm h]
    _ = g w w := by
        rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin L → Bool)) w (fun w' => g w w')]
        simp

/-- The sum over seeds of two relation-and-zero-hash indicators equals the product of the
relation indicators and the joint-zero seed count. -/
private theorem ccJointFiberSum {L ℓ : ℕ} (R : Set (Fin L → Bool)) (w w' : Fin L → Bool) :
    (∑ s : EcHashSeed L ℓ,
        (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
      = (if R w then 1 else 0) * (if R w' then 1 else 0) * CcHashJointZeroCount ℓ w w' := by
  classical
  by_cases hw : R w
  · by_cases hw' : R w'
    · have hconv : ∀ s : EcHashSeed L ℓ,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0)
            = (if EcHashZero s w ∧ EcHashZero s w' then 1 else 0) := by
        intro s
        simp only [hw, hw', true_and]
        by_cases h1 : EcHashZero s w <;> by_cases h2 : EcHashZero s w' <;> simp [h1, h2]
      calc (∑ s : EcHashSeed L ℓ,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
          = ∑ s : EcHashSeed L ℓ, (if EcHashZero s w ∧ EcHashZero s w' then 1 else 0) := by
              apply Fintype.sum_congr
              intro s
              exact hconv s
        _ = CcHashJointZeroCount ℓ w w' := by
              unfold CcHashJointZeroCount CcHashJointZero
              apply Fintype.sum_congr
              intro s
              by_cases h : EcHashZero s w ∧ EcHashZero s w' <;> simp [h]
        _ = (if R w then 1 else 0) * (if R w' then 1 else 0) * CcHashJointZeroCount ℓ w w' := by
              simp [hw, hw']
    · have hzero : ∀ s : EcHashSeed L ℓ,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) = 0 := by
        intro s
        simp [hw']
      calc (∑ s : EcHashSeed L ℓ,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
          = 0 := by
              apply Finset.sum_eq_zero
              intro s _
              exact hzero s
        _ = (if R w then 1 else 0) * (if R w' then 1 else 0) * CcHashJointZeroCount ℓ w w' := by
              simp [hw, hw']
  · have hzero : ∀ s : EcHashSeed L ℓ,
        (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) = 0 := by
      intro s
      simp [hw]
    calc (∑ s : EcHashSeed L ℓ,
        (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
        = 0 := by
            apply Finset.sum_eq_zero
            intro s _
            exact hzero s
        _ = (if R w then 1 else 0) * (if R w' then 1 else 0) * CcHashJointZeroCount ℓ w w' := by
            simp [hw]

/-- A finite sum of pointwise sums of natural numbers splits into the two separate sums. -/
private theorem ccSumAdd1 {α : Type} [Fintype α] (p q : α → ℕ) :
    (∑ a, (p a + q a)) = (∑ a, p a) + (∑ a, q a) := by
  have h : ∀ s : Finset α, (Finset.sum s (fun a => p a + q a))
      = (Finset.sum s (fun a => p a)) + (Finset.sum s (fun a => q a)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [ih]
        omega
  simpa using h (Finset.univ)

/-- Summing the affine expression `A * b s + (B * c s + E)` distributes over its variable terms
and multiplies the constant term by the number of indices. -/
private theorem ccSumPoly {α : Type} [Fintype α] (A B E : ℝ) (b c : α → ℝ) :
    (∑ s : α, (A * b s + (B * c s + E)))
      = A * (∑ s : α, b s) + (B * (∑ s : α, c s) + E * (∑ _s : α, 1)) := by
  have h : ∀ s : Finset α, (Finset.sum s (fun s => A * b s + (B * c s + E)))
      = A * (Finset.sum s (fun s => b s))
        + (B * (Finset.sum s (fun s => c s)) + E * (Finset.sum s (fun _ => 1))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [ih]
        ring
  simpa using h (Finset.univ)

/-- A constant natural-number factor can be taken outside a double sum over Boolean witnesses. -/
private theorem ccSumConst2 {L : ℕ} (A : ℕ) (f : (Fin L → Bool) → (Fin L → Bool) → ℕ) :
    (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, A * f w w')
      = A * (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, f w w') := by
  calc (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, A * f w w')
      = ∑ w : Fin L → Bool, A * (∑ w' : Fin L → Bool, f w w') := by
        apply Fintype.sum_congr
        intro w
        exact (Finset.mul_sum (Finset.univ : Finset (Fin L → Bool)) (fun w' => f w w') A).symm
    _ = A * (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, f w w') := by
        exact (Finset.mul_sum (Finset.univ : Finset (Fin L → Bool))
          (fun w => ∑ w' : Fin L → Bool, f w w') A).symm

/-- A double sum of pointwise sums over Boolean witnesses splits into the two double sums. -/
private theorem ccSumAdd2 {L : ℕ} (p q : (Fin L → Bool) → (Fin L → Bool) → ℕ) :
    (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, (p w w' + q w w'))
      = (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, p w w')
        + (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, q w w') := by
  calc (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, (p w w' + q w w'))
      = ∑ w : Fin L → Bool,
          ((∑ w' : Fin L → Bool, p w w') + (∑ w' : Fin L → Bool, q w w')) := by
        apply Fintype.sum_congr
        intro w
        exact ccSumAdd1 (fun w' => p w w') (fun w' => q w w')
    _ = (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, p w w')
        + (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, q w w') := by
        exact ccSumAdd1 (fun w => ∑ w' : Fin L → Bool, p w w')
          (fun w => ∑ w' : Fin L → Bool, q w w')

/-- The sum of squared zero-hash fiber sizes is `m * 2 ^ (ℓ * L) + (m² - m) * 2 ^ (ℓ * (L -
1))`, where `m` is the relation count. -/
theorem ccFiberSq_sum {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s ^ 2)
      = EcRelCount R * 2 ^ (ℓ * L) + (EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1)) := by
  classical
  have hsquare : ∀ s : EcHashSeed L ℓ,
      EcRelFiberCount R s ^ 2
        = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := by
    intro s
    have hn := ecRelFiberCount_eq_sum R s
    calc EcRelFiberCount R s ^ 2
        = EcRelFiberCount R s * EcRelFiberCount R s := by rw [pow_two]
        _ = (∑ w : Fin L → Bool, (if R w ∧ EcHashZero s w then 1 else 0))
            * (∑ w' : Fin L → Bool, (if R w' ∧ EcHashZero s w' then 1 else 0)) := by rw [hn]
        _ = ∑ w : Fin L → Bool, (if R w ∧ EcHashZero s w then 1 else 0)
            * (∑ w' : Fin L → Bool, (if R w' ∧ EcHashZero s w' then 1 else 0)) := by
            rw [← Finset.sum_mul]
        _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := by
            apply Fintype.sum_congr
            intro w
            rw [Finset.mul_sum]
  have hswap : (∑ s : EcHashSeed L ℓ, ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
              (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
      = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, ∑ s : EcHashSeed L ℓ,
              (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := by
    calc (∑ s : EcHashSeed L ℓ, ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0))
        = ∑ w : Fin L → Bool, ∑ s : EcHashSeed L ℓ, ∑ w' : Fin L → Bool,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, ∑ s : EcHashSeed L ℓ,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := by
            apply Fintype.sum_congr
            intro w
            exact Finset.sum_comm
  have hD1 : (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
        ccInd R w * ccInd R w' * (if w = w' then 1 else 0)) = EcRelCount R := by
    calc (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          ccInd R w * ccInd R w' * (if w = w' then 1 else 0))
        = ∑ w : Fin L → Bool, ccInd R w * ccInd R w :=
          ccDiagSum (fun w w' => ccInd R w * ccInd R w')
      _ = ∑ w : Fin L → Bool, ccInd R w := by
            apply Fintype.sum_congr
            intro w
            exact ccInd_mul_self R w
      _ = EcRelCount R := ccInd_eq_sum R
  have hTotal : (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
        ccInd R w * ccInd R w')
      = EcRelCount R * EcRelCount R := by
    calc (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, ccInd R w * ccInd R w')
        = ∑ w : Fin L → Bool, ccInd R w * (∑ w' : Fin L → Bool, ccInd R w') := by
            apply Fintype.sum_congr
            intro w
            rw [Finset.mul_sum]
        _ = (∑ w : Fin L → Bool, ccInd R w) * (∑ w' : Fin L → Bool, ccInd R w') := by
            calc (∑ w : Fin L → Bool, ccInd R w * (∑ w' : Fin L → Bool, ccInd R w'))
                = ∑ w : Fin L → Bool, (∑ w' : Fin L → Bool, ccInd R w') * ccInd R w := by
                    apply Fintype.sum_congr
                    intro w
                    exact (mul_comm _ _)
              _ = (∑ w' : Fin L → Bool, ccInd R w') * (∑ w : Fin L → Bool, ccInd R w) := by
                    exact (Finset.mul_sum (Finset.univ : Finset (Fin L → Bool))
                      (fun w => ccInd R w) (∑ w' : Fin L → Bool, ccInd R w')).symm
              _ = (∑ w : Fin L → Bool, ccInd R w) * (∑ w' : Fin L → Bool, ccInd R w') := by
                    exact (mul_comm _ _)
        _ = EcRelCount R * EcRelCount R := by rw [ccInd_eq_sum R]
  have hpoint : ∀ w w' : Fin L → Bool,
      ccInd R w * ccInd R w' * (if w = w' then 0 else 1)
        = ccInd R w * ccInd R w' - ccInd R w * ccInd R w' * (if w = w' then 1 else 0) := by
    intro w w'
    by_cases h : w = w'
    · subst h
      simp
    · simp [h]
  have hD2 : (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
        ccInd R w * ccInd R w' * (if w = w' then 0 else 1))
      = EcRelCount R ^ 2 - EcRelCount R := by
    have hsplit : (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          ccInd R w * ccInd R w' * (if w = w' then 0 else 1))
        + (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          ccInd R w * ccInd R w' * (if w = w' then 1 else 0))
        = (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, ccInd R w * ccInd R w') := by
      have hterm : ∀ w w' : Fin L → Bool,
          ccInd R w * ccInd R w' * (if w = w' then 0 else 1)
            + ccInd R w * ccInd R w' * (if w = w' then 1 else 0)
            = ccInd R w * ccInd R w' := by
        intro w w'
        by_cases h : w = w'
        · subst h
          simp
        · simp [h]
      calc (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            ccInd R w * ccInd R w' * (if w = w' then 0 else 1))
          + (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            ccInd R w * ccInd R w' * (if w = w' then 1 else 0))
          = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            (ccInd R w * ccInd R w' * (if w = w' then 0 else 1)
              + ccInd R w * ccInd R w' * (if w = w' then 1 else 0)) := by
            exact (ccSumAdd2
              (fun w w' => ccInd R w * ccInd R w' * (if w = w' then 0 else 1))
              (fun w w' => ccInd R w * ccInd R w' * (if w = w' then 1 else 0))).symm
        _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, ccInd R w * ccInd R w' := by
            apply Fintype.sum_congr
            intro w
            apply Fintype.sum_congr
            intro w'
            exact hterm w w'
    have hsub : EcRelCount R
        + (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          ccInd R w * ccInd R w' * (if w = w' then 0 else 1))
        = EcRelCount R ^ 2 := by
      rw [hD1] at hsplit
      rw [hTotal] at hsplit
      rw [← pow_two] at hsplit
      omega
    omega
  calc (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s ^ 2)
      = ∑ s : EcHashSeed L ℓ, ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := by
          apply Fintype.sum_congr
          intro s
          exact hsquare s
      _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool, ∑ s : EcHashSeed L ℓ,
          (if R w ∧ EcHashZero s w then 1 else 0) * (if R w' ∧ EcHashZero s w' then 1 else 0) := hswap
      _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          (if R w then 1 else 0) * (if R w' then 1 else 0) * CcHashJointZeroCount ℓ w w' := by
          apply Fintype.sum_congr
          intro w
          apply Fintype.sum_congr
          intro w'
          exact ccJointFiberSum R w w'
      _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          (if R w then 1 else 0) * (if R w' then 1 else 0) * CcPairZeroCount ℓ w w' := by
          apply Fintype.sum_congr
          intro w
          apply Fintype.sum_congr
          intro w'
          rw [ccHashJointZeroCount_eq w w']
      _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          ccInd R w * ccInd R w' * (if w = w' then 2 ^ (ℓ * L) else 2 ^ (ℓ * (L - 1))) := by
          apply Fintype.sum_congr
          intro w
          apply Fintype.sum_congr
          intro w'
          by_cases h : R w <;> by_cases h' : R w' <;>
            simp [ccInd, h, h', CcPairZeroCount]
      _ = ∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
          (2 ^ (ℓ * L) * (ccInd R w * ccInd R w' * (if w = w' then 1 else 0))
            + 2 ^ (ℓ * (L - 1)) * (ccInd R w * ccInd R w' * (if w = w' then 0 else 1))) := by
          have hterm : ∀ w w' : Fin L → Bool,
              ccInd R w * ccInd R w' * (if w = w' then 2 ^ (ℓ * L) else 2 ^ (ℓ * (L - 1)))
                = 2 ^ (ℓ * L) * (ccInd R w * ccInd R w' * (if w = w' then 1 else 0))
                  + 2 ^ (ℓ * (L - 1)) * (ccInd R w * ccInd R w' * (if w = w' then 0 else 1)) := by
            intro w w'
            have hsplit : (if w = w' then 2 ^ (ℓ * L) else 2 ^ (ℓ * (L - 1)))
                = 2 ^ (ℓ * L) * (if w = w' then 1 else 0)
                  + 2 ^ (ℓ * (L - 1)) * (if w = w' then 0 else 1) := by
              by_cases h : w = w'
              · subst h
                simp
              · simp [h]
            rw [hsplit, mul_add]
            ac_rfl
          apply Fintype.sum_congr
          intro w
          apply Fintype.sum_congr
          intro w'
          exact hterm w w'
      _ = (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            2 ^ (ℓ * L) * (ccInd R w * ccInd R w' * (if w = w' then 1 else 0)))
          + (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            2 ^ (ℓ * (L - 1)) * (ccInd R w * ccInd R w' * (if w = w' then 0 else 1))) := by
          exact ccSumAdd2
            (fun w w' => 2 ^ (ℓ * L) * (ccInd R w * ccInd R w' * (if w = w' then 1 else 0)))
            (fun w w' => 2 ^ (ℓ * (L - 1)) * (ccInd R w * ccInd R w' * (if w = w' then 0 else 1)))
      _ = 2 ^ (ℓ * L) * (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            ccInd R w * ccInd R w' * (if w = w' then 1 else 0))
          + 2 ^ (ℓ * (L - 1)) * (∑ w : Fin L → Bool, ∑ w' : Fin L → Bool,
            ccInd R w * ccInd R w' * (if w = w' then 0 else 1)) := by
          exact congrArg₂ (· + ·)
            (ccSumConst2 (2 ^ (ℓ * L))
              (fun w w' => ccInd R w * ccInd R w' * (if w = w' then 1 else 0)))
            (ccSumConst2 (2 ^ (ℓ * (L - 1)))
              (fun w w' => ccInd R w * ccInd R w' * (if w = w' then 0 else 1)))
      _ = 2 ^ (ℓ * L) * EcRelCount R
          + 2 ^ (ℓ * (L - 1)) * (EcRelCount R ^ 2 - EcRelCount R) := by
          rw [hD1, hD2]
      _ = EcRelCount R * 2 ^ (ℓ * L)
          + (EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1)) := by
          have h1 : 2 ^ (ℓ * L) * EcRelCount R = EcRelCount R * 2 ^ (ℓ * L) := mul_comm _ _
          have h2 : 2 ^ (ℓ * (L - 1)) * (EcRelCount R ^ 2 - EcRelCount R)
              = (EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1)) := mul_comm _ _
          rw [h1, h2]

/-- Under the three stated product identities, the quadratic second-moment expression simplifies
to `mr * (Ar - 1) * Nr`. -/
private theorem ccVarAlgebra {Ar Br Cr Nr mr : ℝ}
    (h1 : (Ar * Ar) * (mr * Br) = (Nr * Ar) * mr)
    (h2 : (Ar * Ar) * ((mr ^ 2 - mr) * Cr) = Nr * (mr ^ 2 - mr))
    (h3 : (-2 * Ar * mr) * (mr * Br) = (-2 * Nr * mr) * mr) :
    (Ar * Ar) * (mr * Br + (mr ^ 2 - mr) * Cr) + ((-2 * Ar * mr) * (mr * Br) + mr ^ 2 * Nr)
      = mr * (Ar - 1) * Nr := by
  calc (Ar * Ar) * (mr * Br + (mr ^ 2 - mr) * Cr)
          + ((-2 * Ar * mr) * (mr * Br) + mr ^ 2 * Nr)
      = (Ar * Ar) * (mr * Br) + (Ar * Ar) * ((mr ^ 2 - mr) * Cr)
          + ((-2 * Ar * mr) * (mr * Br) + mr ^ 2 * Nr) := by ring
    _ = (Nr * Ar) * mr + Nr * (mr ^ 2 - mr) + ((-2 * Nr * mr) * mr + mr ^ 2 * Nr) := by
          rw [h1, h2, h3]
    _ = mr * (Ar - 1) * Nr := by ring

/-- The total squared deviation of the rescaled estimator equals `m * (2 ^ ℓ - 1) * 2 ^ (ℓ * L +
ℓ)`, where `m` is the true relation count. -/
theorem ccEstimateDevSq_eq {L ℓ : ℕ} (R : Set (Fin L → Bool)) :
    CcEstimateDevSq ℓ R
      = (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
  classical
  have hcast1 : (∑ s : EcHashSeed L ℓ, (EcRelFiberCount R s : ℝ))
      = (EcRelCount R : ℝ) * ((2 : ℝ) ^ (ℓ * L)) := by
    have h := ecRelFiberCount_sum (L := L) (ℓ := ℓ) R
    exact_mod_cast h
  have h1sq : ∀ n : ℕ, n ≤ n * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hh := Nat.mul_le_mul (le_refl n) (by omega : 1 ≤ n)
      simpa [Nat.mul_one] using hh
  have hge : EcRelCount R ≤ EcRelCount R ^ 2 := by
    have h2 : EcRelCount R ^ 2 = EcRelCount R * EcRelCount R := pow_two _
    rw [h2]
    exact h1sq _
  have hD : Nat.cast (EcRelCount R ^ 2 - EcRelCount R)
      = (EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ) := by
    rw [Nat.cast_sub hge, Nat.cast_pow]
  have hcast2 : (∑ s : EcHashSeed L ℓ, (EcRelFiberCount R s : ℝ) ^ 2)
      = (EcRelCount R : ℝ) * ((2 : ℝ) ^ (ℓ * L))
        + ((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) * ((2 : ℝ) ^ (ℓ * (L - 1))) := by
    have h := ccFiberSq_sum (L := L) (ℓ := ℓ) R
    have h' : (Nat.cast (∑ s : EcHashSeed L ℓ, EcRelFiberCount R s ^ 2) : ℝ)
        = (Nat.cast (EcRelCount R * 2 ^ (ℓ * L)
            + (EcRelCount R ^ 2 - EcRelCount R) * 2 ^ (ℓ * (L - 1))) : ℝ) := by
      exact congrArg (fun x : ℕ => (x : ℝ)) h
    rw [Nat.cast_sum] at h'
    have hconv : ∀ s : EcHashSeed L ℓ,
        ((EcRelFiberCount R s : ℝ) ^ 2) = (Nat.cast (EcRelFiberCount R s ^ 2) : ℝ) := by
      intro s
      exact (Nat.cast_pow (EcRelFiberCount R s) 2).symm
    calc (∑ s : EcHashSeed L ℓ, (EcRelFiberCount R s : ℝ) ^ 2)
        = ∑ s : EcHashSeed L ℓ, (Nat.cast (EcRelFiberCount R s ^ 2) : ℝ) := by
            apply Fintype.sum_congr
            intro s
            exact hconv s
      _ = (EcRelCount R : ℝ) * ((2 : ℝ) ^ (ℓ * L))
          + ((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) * ((2 : ℝ) ^ (ℓ * (L - 1))) := by
            rw [h']
            rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow]
            rw [hD]
            simp
  have hcard : (∑ s : EcHashSeed L ℓ, (1 : ℝ)) = (2 : ℝ) ^ (ℓ * L + ℓ) := by
    have h := Fintype.card_ecHashSeed L ℓ
    calc (∑ s : EcHashSeed L ℓ, (1 : ℝ)) = (Fintype.card (EcHashSeed L ℓ) : ℝ) := by
            simp
        _ = (2 : ℝ) ^ (ℓ * L + ℓ) := by exact_mod_cast h
  have hterm : ∀ s : EcHashSeed L ℓ,
      ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2
        = (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * ((EcRelFiberCount R s : ℝ) ^ 2)
          + ((-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ) * (EcRelFiberCount R s : ℝ))
            + (EcRelCount R : ℝ) ^ 2) := by
    intro s
    have hcast : (CcEstimate R s : ℝ) = (2 : ℝ) ^ ℓ * (EcRelFiberCount R s : ℝ) := by
      unfold CcEstimate
      rw [Nat.cast_mul, Nat.cast_pow]
      simp
    rw [hcast]
    ring
  have hArBr : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * L) = (2 : ℝ) ^ (ℓ * L + ℓ) := by
    calc (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * L) = (2 : ℝ) ^ (ℓ * L) * (2 : ℝ) ^ ℓ := mul_comm _ _
      _ = (2 : ℝ) ^ (ℓ * L + ℓ) := by rw [← pow_add]
  have hmain : (∑ s : EcHashSeed L ℓ, ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2)
      = (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
    calc (∑ s : EcHashSeed L ℓ, ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2)
        = ∑ s : EcHashSeed L ℓ,
            ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * ((EcRelFiberCount R s : ℝ) ^ 2)
              + ((-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ) * (EcRelFiberCount R s : ℝ))
                + (EcRelCount R : ℝ) ^ 2)) := by
              apply Fintype.sum_congr
              intro s
              exact hterm s
        _ = (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * (∑ s : EcHashSeed L ℓ, (EcRelFiberCount R s : ℝ) ^ 2)
            + ((-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ))
                * (∑ s : EcHashSeed L ℓ, (EcRelFiberCount R s : ℝ))
              + (EcRelCount R : ℝ) ^ 2 * (∑ s : EcHashSeed L ℓ, (1 : ℝ))) := by
              exact ccSumPoly ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ)
                (-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ)) ((EcRelCount R : ℝ) ^ 2)
                (fun s => (EcRelFiberCount R s : ℝ) ^ 2) (fun s => (EcRelFiberCount R s : ℝ))
        _ = (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
              rw [hcast2, hcast1, hcard]
              by_cases hL : 0 < L
              · have hL1 : L - 1 + 1 = L := by omega
                have hmul : ℓ * (L - 1) + ℓ = ℓ * L := by
                  calc ℓ * (L - 1) + ℓ = ℓ * ((L - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
                    _ = ℓ * L := by rw [hL1]
                have hAr2Cr : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * (L - 1))
                    = (2 : ℝ) ^ (ℓ * L + ℓ) := by
                  have hstep : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * (L - 1))
                      = (2 : ℝ) ^ (ℓ + ℓ + ℓ * (L - 1)) := by
                        rw [← pow_add, ← pow_add]
                  have hexp : ℓ + ℓ + ℓ * (L - 1) = ℓ * L + ℓ := by
                    calc ℓ + ℓ + ℓ * (L - 1) = ℓ + (ℓ * (L - 1) + ℓ) := by omega
                      _ = ℓ + ℓ * L := by rw [hmul]
                      _ = ℓ * L + ℓ := by omega
                  rw [hstep, hexp]
                have h1 : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ
                      * ((EcRelCount R : ℝ) * (2 : ℝ) ^ (ℓ * L))
                    = ((2 : ℝ) ^ (ℓ * L + ℓ)) * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ) := by
                  have hstep : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ
                      * ((EcRelCount R : ℝ) * (2 : ℝ) ^ (ℓ * L))
                      = (2 : ℝ) ^ ℓ * ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * L)) * (EcRelCount R : ℝ) := by
                        ring
                  rw [hstep, hArBr]
                  ring
                have h2 : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ
                      * (((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) * (2 : ℝ) ^ (ℓ * (L - 1)))
                    = (2 : ℝ) ^ (ℓ * L + ℓ)
                      * ((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) := by
                  have hstep : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ
                      * (((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) * (2 : ℝ) ^ (ℓ * (L - 1)))
                      = ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * (L - 1)))
                        * ((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) := by
                        ring
                  rw [hstep, hAr2Cr]
                have h3 : (-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ))
                      * ((EcRelCount R : ℝ) * (2 : ℝ) ^ (ℓ * L))
                    = (-2 * (2 : ℝ) ^ (ℓ * L + ℓ) * (EcRelCount R : ℝ)) * (EcRelCount R : ℝ) := by
                  have hstep : (-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ))
                      * ((EcRelCount R : ℝ) * (2 : ℝ) ^ (ℓ * L))
                      = (-2 * ((2 : ℝ) ^ ℓ * (2 : ℝ) ^ (ℓ * L)) * (EcRelCount R : ℝ))
                        * (EcRelCount R : ℝ) := by
                        ring
                  rw [hstep, hArBr]
                exact ccVarAlgebra h1 h2 h3
              · have hL0 : L = 0 := by omega
                subst hL0
                have hcard1 : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by
                  rw [Finset.card_univ, card_fin_fun_bool]
                  simp
                have hm_le : EcRelCount R ≤ 1 := by
                  have hle : (Finset.univ.filter (fun w : Fin 0 → Bool => R w)).card
                      ≤ (Finset.univ : Finset (Fin 0 → Bool)).card :=
                    Finset.card_le_card (Finset.filter_subset _ _)
                  rw [hcard1] at hle
                  exact hle
                have hmR2 : (EcRelCount R : ℝ) ^ 2 = (EcRelCount R : ℝ) := by
                  rcases Nat.eq_zero_or_pos (EcRelCount R) with h | h
                  · rw [h]
                    simp
                  · have h1 : EcRelCount R = 1 := by
                      have hh := hm_le
                      omega
                    rw [h1]
                    simp
                have hBr0 : (2 : ℝ) ^ (ℓ * 0) = 1 := by simp
                have hCr0 : (2 : ℝ) ^ (ℓ * (0 - 1)) = 1 := by simp
                have hNr0 : (2 : ℝ) ^ (ℓ * 0 + ℓ) = (2 : ℝ) ^ ℓ := by simp
                have h1 : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ
                      * ((EcRelCount R : ℝ) * (2 : ℝ) ^ (ℓ * 0))
                    = ((2 : ℝ) ^ (ℓ * 0 + ℓ)) * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ) := by
                  rw [hBr0, hNr0]
                  ring
                have h2 : (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ
                      * (((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) * (2 : ℝ) ^ (ℓ * (0 - 1)))
                    = (2 : ℝ) ^ (ℓ * 0 + ℓ)
                      * ((EcRelCount R : ℝ) ^ 2 - (EcRelCount R : ℝ)) := by
                  rw [hCr0, hNr0, hmR2]
                  ring
                have h3 : (-2 * (2 : ℝ) ^ ℓ * (EcRelCount R : ℝ))
                      * ((EcRelCount R : ℝ) * (2 : ℝ) ^ (ℓ * 0))
                    = (-2 * (2 : ℝ) ^ (ℓ * 0 + ℓ) * (EcRelCount R : ℝ)) * (EcRelCount R : ℝ) := by
                  rw [hBr0, hNr0]
                  ring
                exact ccVarAlgebra h1 h2 h3
  show CcEstimateDevSq ℓ R = _
  rw [CcEstimateDevSq]
  exact hmain

/-- For positive relation count `m`, the relative-error failure count times `m` is at most `4 *
(2 ^ ℓ - 1) * 2 ^ (ℓ * L + ℓ)`. -/
theorem ccFailureCount_bound {L ℓ : ℕ} (R : Set (Fin L → Bool)) (hm : 0 < EcRelCount R) :
    (CcFailureCount ℓ R : ℝ) * (EcRelCount R : ℝ)
      ≤ 4 * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
  classical
  have hmR : (0 : ℝ) < (EcRelCount R : ℝ) := by exact_mod_cast hm
  have hsq : ∀ x : ℝ, |x| > (EcRelCount R : ℝ) / 2 →
      ((EcRelCount R : ℝ) / 2) ^ 2 < x ^ 2 := by
    intro x hx
    have h2 := mul_self_lt_mul_self (show (0 : ℝ) ≤ (EcRelCount R : ℝ) / 2 by positivity) hx
    nlinarith [sq_abs x]
  have hlower : ∀ s : EcHashSeed L ℓ,
      ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2
        ≥ (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
            then (EcRelCount R : ℝ) ^ 2 / 4 else 0) := by
    intro s
    by_cases hb : |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
    · rw [if_pos hb]
      have h3 := hsq ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) hb
      have h4 : ((EcRelCount R : ℝ) / 2) ^ 2 = (EcRelCount R : ℝ) ^ 2 / 4 := by ring
      linarith
    · rw [if_neg hb]
      exact sq_nonneg _
  have hsumlower : (∑ s : EcHashSeed L ℓ, ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2)
      ≥ (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
            then (EcRelCount R : ℝ) ^ 2 / 4 else 0)) := by
    exact Finset.sum_le_sum (fun s _ => hlower s)
  have hbad : (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
            then (EcRelCount R : ℝ) ^ 2 / 4 else 0))
      = (CcFailureCount ℓ R : ℝ) * ((EcRelCount R : ℝ) ^ 2 / 4) := by
    calc (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
            then (EcRelCount R : ℝ) ^ 2 / 4 else 0))
        = ∑ s : EcHashSeed L ℓ,
          ((if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
            then 1 else 0) * ((EcRelCount R : ℝ) ^ 2 / 4)) := by
              apply Fintype.sum_congr
              intro s
              by_cases h :
                  |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
              · simp [h]
              · simp [h]
        _ = (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
            then (1 : ℝ) else 0)) * ((EcRelCount R : ℝ) ^ 2 / 4) := by
              exact (Finset.sum_mul (Finset.univ : Finset (EcHashSeed L ℓ))
                (fun s => if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)|
                    > (EcRelCount R : ℝ) / 2 then (1 : ℝ) else 0)
                ((EcRelCount R : ℝ) ^ 2 / 4)).symm
        _ = (CcFailureCount ℓ R : ℝ) * ((EcRelCount R : ℝ) ^ 2 / 4) := by
              have hstep : (∑ s : EcHashSeed L ℓ, (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)|
                  > (EcRelCount R : ℝ) / 2 then (1 : ℝ) else 0))
                  = (CcFailureCount ℓ R : ℝ) := by
                unfold CcFailureCount
                rw [Nat.cast_sum]
                apply Fintype.sum_congr
                intro s
                by_cases h :
                    |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > (EcRelCount R : ℝ) / 2
                · simp [h]
                · simp [h]
              rw [hstep]
  have hmain : (∑ s : EcHashSeed L ℓ, ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2)
      = (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
    exact ccEstimateDevSq_eq (L := L) (ℓ := ℓ) R
  have hstep : (CcFailureCount ℓ R : ℝ) * ((EcRelCount R : ℝ) ^ 2 / 4)
      ≤ (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
    have hx := hsumlower
    rw [hbad] at hx
    rw [hmain] at hx
    linarith
  nlinarith

/-- For a positive relation count satisfying `CcFailureBudget`, the failure count is at most `ε`
times the total number of hash seeds. -/
theorem ccFailureRate_le_eps {L ℓ : ℕ} (R : Set (Fin L → Bool)) (hm : 0 < EcRelCount R)
    {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount R) ε) :
    (CcFailureCount ℓ R : ℝ) ≤ ε * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
  classical
  have hmR : (0 : ℝ) < (EcRelCount R : ℝ) := by exact_mod_cast hm
  have hN : (0 : ℝ) ≤ (2 : ℝ) ^ (ℓ * L + ℓ) := by positivity
  have h3 := ccFailureCount_bound (L := L) (ℓ := ℓ) R hm
  have hb' : 4 * (((2 : ℝ) ^ ℓ) - 1) ≤ ε * (EcRelCount R : ℝ) := hb.2
  nlinarith

/-- For a positive relation count satisfying `CcFailureBudget`, the probability of error greater
than half the true count is at most `ε`. -/
theorem ccFailureProb_le_eps {L ℓ : ℕ} (R : Set (Fin L → Bool)) (hm : 0 < EcRelCount R)
    {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount R) ε) :
    CcFailureProb ℓ R ≤ ε := by
  classical
  have hmR : (0 : ℝ) < (EcRelCount R : ℝ) := by exact_mod_cast hm
  have hN : (0 : ℝ) < (2 : ℝ) ^ (ℓ * L + ℓ) := by positivity
  have h1 := ccFailureRate_le_eps (L := L) (ℓ := ℓ) R hm hb
  unfold CcFailureProb
  rw [div_le_iff₀ hN]
  linarith

/-- A sampler output fiber count equals its output probability multiplied by `2 ^ L`. -/
theorem ccSampler_output_prob_count {L : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    (EcRelCount (EcSamplerSeedSet Sam y) : ℝ) = (2 : ℝ) ^ L * EcSamplerProb Sam y := by
  classical
  rw [ecSamplerSeedSet_card, ecSamplerProb_count]
  field_simp
  push_cast
  ring

/-- The uniform mean of the hash estimates for a sampler output fiber equals its output
probability multiplied by `2 ^ L`. -/
theorem ccSampler_estimate_expectation {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    (∑ s : EcHashSeed L ℓ, CcEstimate (EcSamplerSeedSet Sam y) s)
        / ((2 : ℝ) ^ (ℓ * L + ℓ))
      = (2 : ℝ) ^ L * EcSamplerProb Sam y := by
  classical
  have hone := ccSampler_output_prob_count Sam y
  rw [ecSamplerSeedSet_card] at hone
  rw [ccSampler_estimate_sum, Nat.cast_mul, Nat.cast_pow]
  field_simp
  rw [hone]
  ring

/-- Every sampler output fiber possesses a good hash seed, whose estimate is at least half the
fiber count. -/
theorem ccSampler_good_seed_multiplicative {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (y : Out) :
    ∃ s : EcHashSeed L ℓ, CcGoodSeed (EcSamplerSeedSet Sam y) s := by
  classical
  have hbest := ccBestSeed_estimate (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y)
  refine ⟨hbest.choose, ?_⟩
  show EcRelCount (EcSamplerSeedSet Sam y)
      ≤ 2 * CcEstimate (EcSamplerSeedSet Sam y) hbest.choose
  have h1 : EcRelCount (EcSamplerSeedSet Sam y)
      ≤ CcEstimate (EcSamplerSeedSet Sam y) hbest.choose := hbest.choose_spec
  have h2 : CcEstimate (EcSamplerSeedSet Sam y) hbest.choose
      ≤ 2 * CcEstimate (EcSamplerSeedSet Sam y) hbest.choose := by
    have hnn : CcEstimate (EcSamplerSeedSet Sam y) hbest.choose
        ≤ CcEstimate (EcSamplerSeedSet Sam y) hbest.choose
          + CcEstimate (EcSamplerSeedSet Sam y) hbest.choose :=
      Nat.le_add_right _ _
    exact hnn.trans_eq (Nat.two_mul _).symm
  exact Nat.le_trans h1 h2

/-- For a positive sampler output fiber count satisfying the failure budget, the failure count
is at most `ε` times the number of hash seeds. -/
theorem ccSampler_failure_rate {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out)
    (hm : 0 < EcRelCount (EcSamplerSeedSet Sam y))
    {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount (EcSamplerSeedSet Sam y)) ε) :
    (CcFailureCount ℓ (EcSamplerSeedSet Sam y) : ℝ) ≤ ε * ((2 : ℝ) ^ (ℓ * L + ℓ)) :=
  ccFailureRate_le_eps (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y) hm hb

/-- For a positive sampler output fiber count satisfying the failure budget, its relative-error
failure probability is at most `ε`. -/
theorem ccSampler_failure_prob {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out)
    (hm : 0 < EcRelCount (EcSamplerSeedSet Sam y))
    {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount (EcSamplerSeedSet Sam y)) ε) :
    CcFailureProb ℓ (EcSamplerSeedSet Sam y) ≤ ε :=
  ccFailureProb_le_eps (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y) hm hb

/-- For positive relation count `m` and threshold `τ > 0`, the number of seeds with absolute
error above `τ`, multiplied by `τ²`, is at most `m * (2 ^ ℓ - 1) * 2 ^ (ℓ * L + ℓ)`. -/
theorem ccBadSeedCount_bound {L ℓ : ℕ} (R : Set (Fin L → Bool)) (hm : 0 < EcRelCount R)
    (τ : ℝ) (hτ : 0 < τ) :
    (CcThresholdBadSeedCount ℓ τ R : ℝ) * τ ^ 2
      ≤ (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
  classical
  have hmR : (0 : ℝ) < (EcRelCount R : ℝ) := by exact_mod_cast hm
  have hsq : ∀ x : ℝ, |x| > τ → τ ^ 2 < x ^ 2 := by
    intro x hx
    have h2 := mul_self_lt_mul_self (le_of_lt hτ) hx
    nlinarith [sq_abs x]
  have hlower : ∀ s : EcHashSeed L ℓ,
      ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2
        ≥ (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then τ ^ 2 else 0) := by
    intro s
    by_cases hb : |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ
    · rw [if_pos hb]
      have h3 := hsq ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) hb
      linarith
    · rw [if_neg hb]
      exact sq_nonneg _
  have hsumlower : (∑ s : EcHashSeed L ℓ, ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2)
      ≥ (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then τ ^ 2 else 0)) := by
    exact Finset.sum_le_sum (fun s _ => hlower s)
  have hbad : (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then τ ^ 2 else 0))
      = (CcThresholdBadSeedCount ℓ τ R : ℝ) * τ ^ 2 := by
    calc (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then τ ^ 2 else 0))
        = ∑ s : EcHashSeed L ℓ,
          ((if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then 1 else 0) * τ ^ 2) := by
            apply Fintype.sum_congr
            intro s
            by_cases h : |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ
            · simp [h]
            · simp [h]
        _ = (∑ s : EcHashSeed L ℓ,
          (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ then (1 : ℝ) else 0)) * τ ^ 2 := by
              exact (Finset.sum_mul (Finset.univ : Finset (EcHashSeed L ℓ))
                (fun s => if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ
                    then (1 : ℝ) else 0)
                (τ ^ 2)).symm
        _ = (CcThresholdBadSeedCount ℓ τ R : ℝ) * τ ^ 2 := by
              have hstep : (∑ s : EcHashSeed L ℓ, (if |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)|
                  > τ then (1 : ℝ) else 0)) = (CcThresholdBadSeedCount ℓ τ R : ℝ) := by
                unfold CcThresholdBadSeedCount
                rw [Nat.cast_sum]
                apply Fintype.sum_congr
                intro s
                by_cases h : |(CcEstimate R s : ℝ) - (EcRelCount R : ℝ)| > τ
                · simp [h]
                · simp [h]
              rw [hstep]
  have hmain : (∑ s : EcHashSeed L ℓ, ((CcEstimate R s : ℝ) - (EcRelCount R : ℝ)) ^ 2)
      = (EcRelCount R : ℝ) * (((2 : ℝ) ^ ℓ) - 1) * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
    exact ccEstimateDevSq_eq (L := L) (ℓ := ℓ) R
  have hx := hsumlower
  rw [hbad] at hx
  rw [hmain] at hx
  linarith

/-- The total squared deviation for a sampler output fiber equals its count times `(2 ^ ℓ - 1) *
2 ^ (ℓ * L + ℓ)`. -/
theorem ccSampler_estimate_devSq {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out) (y : Out) :
    CcEstimateDevSq ℓ (EcSamplerSeedSet Sam y)
      = (EcRelCount (EcSamplerSeedSet Sam y) : ℝ) * (((2 : ℝ) ^ ℓ) - 1)
        * ((2 : ℝ) ^ (ℓ * L + ℓ)) := by
  exact ccEstimateDevSq_eq (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y)

/-- For a positive sampler output fiber count and positive threshold, the threshold failure
count times the squared threshold is bounded by the total squared deviation formula. -/
theorem ccSampler_bad_seed_count_bound {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (y : Out) (hm : 0 < EcRelCount (EcSamplerSeedSet Sam y)) (τ : ℝ) (hτ : 0 < τ) :
    (CcThresholdBadSeedCount ℓ τ (EcSamplerSeedSet Sam y) : ℝ) * τ ^ 2
      ≤ (EcRelCount (EcSamplerSeedSet Sam y) : ℝ) * (((2 : ℝ) ^ ℓ) - 1)
        * ((2 : ℝ) ^ (ℓ * L + ℓ)) :=
  ccBadSeedCount_bound (L := L) (ℓ := ℓ) (EcSamplerSeedSet Sam y) hm τ hτ

/-- For any real threshold, the counts of sampler-fiber hash estimates with error at most the
threshold and error above it sum to the total hash-seed count. -/
theorem ccSampler_good_seed_count {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (y : Out) (τ : ℝ) :
    (∑ s : EcHashSeed L ℓ,
        if |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
            - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| ≤ τ then 1 else 0)
      + (CcThresholdBadSeedCount ℓ τ (EcSamplerSeedSet Sam y) : ℝ)
        = (2 : ℝ) ^ (ℓ * L + ℓ) := by
  classical
  have hsplit : (∑ s : EcHashSeed L ℓ,
        if |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
            - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| ≤ τ then 1 else 0)
      + (∑ s : EcHashSeed L ℓ,
        if |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
            - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| > τ then 1 else 0)
      = (∑ s : EcHashSeed L ℓ, (1 : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro s
    by_cases h :
        |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
          - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| ≤ τ
    · simp [h]
    · have h' :
        |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
          - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| > τ := by
        by_contra hc
        have := le_of_not_gt hc
        linarith
      simp [h', h]
  have hbad : (∑ s : EcHashSeed L ℓ,
        if |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
            - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| > τ then 1 else 0)
      = (CcThresholdBadSeedCount ℓ τ (EcSamplerSeedSet Sam y) : ℝ) := by
    unfold CcThresholdBadSeedCount
    rw [Nat.cast_sum]
    apply Fintype.sum_congr
    intro s
    by_cases h :
        |(CcEstimate (EcSamplerSeedSet Sam y) s : ℝ)
          - (EcRelCount (EcSamplerSeedSet Sam y) : ℝ)| > τ
    · simp [h]
    · simp [h]
  rw [hbad] at hsplit
  have hcard : (∑ _s : EcHashSeed L ℓ, (1 : ℝ)) = (2 : ℝ) ^ (ℓ * L + ℓ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_ecHashSeed, nsmul_eq_mul, mul_one,
      Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard] at hsplit
  linarith

/-- The seed count of a sampler event is the sum of the output-fiber counts over outputs where
the event predicate is true. -/
theorem ccSamplerEventSet_count {L : ℕ} {Out : Type} [Fintype Out] (Sam : EcSampler L Out)
    (Ev : Out → Bool) :
    EcRelCount (CcSamplerEventSet Sam Ev)
      = ∑ y : Out, if Ev y = true then
          (∑ r : Fin L → Bool, if Sam.O r = y then 1 else 0) else 0 := by
  classical
  have hconv : (∑ w : Fin L → Bool, if CcSamplerEventSet Sam Ev w then 1 else 0)
      = (∑ w : Fin L → Bool, if Ev (Sam.O w) = true then 1 else 0) := by
    apply Fintype.sum_congr
    intro w
    by_cases h : Ev (Sam.O w) = true
    · simp [h, CcSamplerEventSet]
    · simp [h, CcSamplerEventSet]
  have hcard : EcRelCount (CcSamplerEventSet Sam Ev)
      = (∑ r : Fin L → Bool, if Ev (Sam.O r) = true then 1 else 0) := by
    rw [ecRelCount_eq_sum]
    exact hconv
  have h := ecSamplerEventCount Sam Ev
  rw [← hcard] at h
  exact h

/-- A sampler event probability is the sum of its accepted output-fiber counts divided by `2 ^
L`. -/
theorem ccSamplerEventSet_prob {L : ℕ} {Out : Type} [Fintype Out] (Sam : EcSampler L Out)
    (Ev : Out → Bool) :
    CcSamplerEventProb Sam Ev
      = ((∑ y : Out, if Ev y = true then
          (∑ r : Fin L → Bool, if Sam.O r = y then 1 else 0) else 0) : ℝ)
        / ((2 : ℝ) ^ L) := by
  classical
  unfold CcSamplerEventProb
  rw [ccSamplerEventSet_count Sam Ev]
  norm_cast

/-- The sum of hash estimates for a sampler event equals its seed count times the number of hash
seeds. -/
theorem ccSamplerEventSet_estimate_mean {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (Ev : Out → Bool) :
    (∑ s : EcHashSeed L ℓ, CcEstimate (CcSamplerEventSet Sam Ev) s)
      = EcRelCount (CcSamplerEventSet Sam Ev) * 2 ^ (ℓ * L + ℓ) := by
  exact ccEstimate_sum (L := L) (ℓ := ℓ) (CcSamplerEventSet Sam Ev)

/-- A sampler event with positive seed count and the stated failure budget has relative-error
failure probability at most `ε`. -/
theorem ccSamplerEventSet_failure_prob {L ℓ : ℕ} {Out : Type} (Sam : EcSampler L Out)
    (Ev : Out → Bool) (hm : 0 < EcRelCount (CcSamplerEventSet Sam Ev))
    {ε : ℝ} (hb : CcFailureBudget (ℓ := ℓ) (EcRelCount (CcSamplerEventSet Sam Ev)) ε) :
    CcFailureProb ℓ (CcSamplerEventSet Sam Ev) ≤ ε :=
  ccFailureProb_le_eps (L := L) (ℓ := ℓ) (CcSamplerEventSet Sam Ev) hm hb

/-- Sampler bit time covers all random bits, `2 * addrBits + 1` units per query, and the
output-bit count. -/
theorem ccSamplerBitTime_lower (L ℓ addrBits queries outputBits : ℕ) :
    CcSamplerRandomBits L ℓ + queries * (2 * addrBits + 1) + outputBits
      ≤ CcSamplerBitTime L ℓ addrBits queries outputBits := by
  unfold CcSamplerBitTime
  have h1 : queries * (2 * addrBits + 1) ≤ queries * (2 * addrBits + 2) :=
    Nat.mul_le_mul_left queries (by omega)
  omega

end Qatlib.Concepts.ProbabilityCore.Concentration
