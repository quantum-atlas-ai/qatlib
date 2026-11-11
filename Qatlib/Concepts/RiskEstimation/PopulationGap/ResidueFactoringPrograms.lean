/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms

/-!
# Residue based factoring attempt laws

This module defines the classical and quantum branches of residue based factoring attempts in
the setting of [Shor1997]. A bit string either fails bounded residue decoding, produces a
nonunit residue for classical greatest common divisor extraction, or selects a unit with two
modular order samples.

`residueAttemptLaw` proves normalization of the resulting finite distribution when the bit
register covers all residues. The final definitions record a candidate single attempt bound and
the repeated program's success probability after preprocessing.

## Main definitions and statements

* `residueClassicalFactor`: extraction of a proper greatest common divisor.
* `residue_coprime_card`: coprime residues and units have equal cardinality.
* `residueAttemptLaw`: the normalized attempt distribution.
* `shorResidueProgramSuccessProb`: preprocessing and repeated attempt success probability.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib.Concepts.PeriodSampling.OrderRecovery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib
open scoped Classical

/-- The register width expression `Nat.log2 N` plus one exactly when `N` exceeds `2 ^ Nat.log2
N`. -/
def shorResidueBits (N : ℕ) : ℕ :=
  Nat.log2 N + if 2 ^ Nat.log2 N < N then 1 else 0

/-- Decodes a bounded bit string and maps a successful result into `ZMod N`. -/
def decodeResidue (N k : ℕ) [NeZero N] (b : Reg k) : Option (ZMod N) :=
  (decodeBoundedBits k N b).map fun i => (i : ZMod N)

/-- Returns the greatest common divisor of a residue representative and `N` when it is a proper
nontrivial divisor, and returns none otherwise. -/
def residueClassicalFactor (N : ℕ) [NeZero N] (y : ZMod N) : Option ℕ :=
  if 1 < Nat.gcd y.val N ∧ Nat.gcd y.val N < N then some (Nat.gcd y.val N)
  else none

/-- Converts a residue with representative coprime to `N` into a unit, returning none otherwise. -/
def residueCoprimeUnit (N : ℕ) [NeZero N] (y : ZMod N) : Option (ZMod N)ˣ :=
  if h : Nat.Coprime y.val N then some (ZMod.unitOfCoprime y.val h) else none

/-- The number of residues with representatives coprime to `N` equals the cardinality of the
unit group of `ZMod N`. -/
theorem residue_coprime_card (N : ℕ) [NeZero N] :
    (Finset.univ.filter fun y : ZMod N => Nat.Coprime y.val N).card
      = Fintype.card (ZMod N)ˣ := by
  classical
  have hval : ∀ (y : ZMod N) (hy : Nat.Coprime y.val N),
      ((ZMod.unitOfCoprime y.val hy : (ZMod N)ˣ) : ZMod N) = y := by
    intro y hy
    rw [ZMod.coe_unitOfCoprime]
    apply ZMod.val_injective
    simp
  have e : {y : ZMod N // Nat.Coprime y.val N} ≃ (ZMod N)ˣ :=
    { toFun := fun y => ZMod.unitOfCoprime (ZMod.val (y : ZMod N)) y.property
      invFun := fun u => ⟨(u : ZMod N), ZMod.val_coe_unit_coprime u⟩
      left_inv := fun y => Subtype.ext
        (hval (y : ZMod N) y.property)
      right_inv := fun u =>
        Units.ext (hval (u : ZMod N) (ZMod.val_coe_unit_coprime u)) }
  have hsub : (Finset.univ.filter fun y : ZMod N => Nat.Coprime y.val N).card
      = Fintype.card {y : ZMod N | Nat.Coprime y.val N} :=
    (Fintype.card_ofFinset _ (fun x => by simp)).symm
  rw [hsub]
  exact Fintype.card_congr e

/-- The sum type of failed bit strings, classical residue outcomes, and unit indexed pairs of
modular order samples. -/
abbrev residueAttemptOutcome (N M k : ℕ) :=
  Reg k ⊕ ZMod N ⊕ ((ZMod N)ˣ × Fin M × Fin M)

/-- The event that the classical or quantum branch extracts a factor; failed bit decoding is
never successful. -/
def residueAttemptSuccessEvent (N M k : ℕ) [NeZero N]
    (t : residueAttemptOutcome N M k) : Prop :=
  match t with
  | Sum.inl _ => False
  | Sum.inr (Sum.inl y) => (residueClassicalFactor N y).isSome
  | Sum.inr (Sum.inr (a, y, z)) => (attemptFactor N M a (y, z)).isSome

instance instDecidableResidueAttemptSuccess (N M k : ℕ) [NeZero N] :
    DecidablePred (residueAttemptSuccessEvent N M k) := fun t => by
  unfold residueAttemptSuccessEvent
  cases t with
  | inl b => exact instDecidableFalse
  | inr t' =>
    cases t' with
    | inl y => exact inferInstanceAs (Decidable ((residueClassicalFactor N y).isSome = true))
    | inr ayz =>
      obtain ⟨a, y, z⟩ := ayz
      exact inferInstanceAs (Decidable ((attemptFactor N M a (y, z)).isSome = true))

/-- The event that at least one of the `R` attempts succeeds. -/
def residueAttemptRepSuccess (N M k R : ℕ) [NeZero N]
    (ω : Fin R → residueAttemptOutcome N M k) : Prop :=
  ∃ j : Fin R, residueAttemptSuccessEvent N M k (ω j)

instance instDecidableResidueAttemptRepSuccess (N M k R : ℕ) [NeZero N] :
    DecidablePred (residueAttemptRepSuccess N M k R) := fun ω =>
  Fintype.decidableExistsFintype (α := Fin R)
    (p := fun j => residueAttemptSuccessEvent N M k (ω j))

/-- The branchwise mass of a residue attempt, scaled by `2 ^ (-k)` and using two independent
modular order probabilities on the unit branch. -/
noncomputable def residueAttemptMass (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (t : residueAttemptOutcome N M k) : ℝ :=
  ((2 ^ k : ℝ))⁻¹ *
    match t with
    | Sum.inl b => if decodeResidue N k b = none then 1 else 0
    | Sum.inr (Sum.inl y) => if Nat.Coprime y.val N then 0 else 1
    | Sum.inr (Sum.inr (a, y, z)) =>
        (modularOrderLaw N M a hM).prob y * (modularOrderLaw N M a hM).prob z

/-- The normalized finite distribution of residue attempts when `N ≤ 2 ^ k` and the modular
order sample space is nonempty. -/
noncomputable def residueAttemptLaw (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (hk : N ≤ 2 ^ k) :
    FinDist (residueAttemptOutcome N M k) where
  prob := residueAttemptMass N M k hM
  nonneg := by
    intro t
    rcases t with b | y | ⟨a, y, z⟩ <;> unfold residueAttemptMass
    · by_cases hb : decodeResidue N k b = none
      · simp [hb]
      · simp [hb]
    · by_cases hc : Nat.Coprime y.val N <;> simp [hc] <;> positivity
    · exact mul_nonneg (by positivity)
        (mul_nonneg ((modularOrderLaw N M a hM).nonneg y)
          ((modularOrderLaw N M a hM).nonneg z))
  sum_one := by
    classical
    have hle : N ≤ 2 ^ k := hk
    have hfib := bounded_bit_decoder_fibers k N hle
    have hncard : (Finset.univ.filter
        (fun b : Reg k => decodeResidue N k b = none)).card
        = (Finset.univ.filter
            (fun b : Reg k => decodeBoundedBits k N b = none)).card := by
      rw [Finset.filter_congr
        (p := fun b : Reg k => decodeResidue N k b = none)
        (q := fun b : Reg k => decodeBoundedBits k N b = none)
        (fun b _ => by
          unfold decodeResidue
          cases h : decodeBoundedBits k N b with
          | none => simp [h]
          | some i => simp [h])]
    have hleft : ∑ b : Reg k, residueAttemptMass N M k hM (Sum.inl b)
        = ((2 ^ k - N : ℕ) : ℝ) / 2 ^ k := by
      unfold residueAttemptMass
      rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) =>
        show ((2 ^ k : ℝ))⁻¹ * (if decodeResidue N k b = none then 1 else 0)
            = (if decodeResidue N k b = none then 1 else 0) / 2 ^ k from
          by
            by_cases hb : decodeResidue N k b = none <;>
              simp [hb, div_eq_inv_mul],
        ← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one, hncard, hfib.2, Nat.cast_sub hle]
    have hmid : ∑ y : ZMod N, residueAttemptMass N M k hM (Sum.inr (Sum.inl y))
        = ((N - Fintype.card (ZMod N)ˣ : ℕ) : ℝ) / 2 ^ k := by
      have hsplit : ∀ y : ZMod N,
          residueAttemptMass N M k hM (Sum.inr (Sum.inl y))
            = (if Nat.Coprime y.val N then (0 : ℝ) else 1) / 2 ^ k := by
        intro y
        unfold residueAttemptMass
        by_cases hc : Nat.Coprime y.val N <;> simp [hc, div_eq_inv_mul]
      rw [Finset.sum_congr rfl (fun y _ => hsplit y), ← Finset.sum_div]
      have hsum : ∑ y : ZMod N,
          (if Nat.Coprime y.val N then (0 : ℝ) else 1)
          = ((Finset.univ.filter
              (fun y : ZMod N => ¬ Nat.Coprime y.val N)).card : ℝ) := by
        have hflip : ∀ y : ZMod N, (if Nat.Coprime y.val N then (0 : ℝ) else 1)
            = if ¬ Nat.Coprime y.val N then (1 : ℝ) else 0 := fun y => by
          by_cases hc : Nat.Coprime y.val N <;> simp [hc]
        rw [Finset.sum_congr rfl (fun y _ => hflip y),
          ← Finset.sum_filter
            (f := fun _ : ZMod N => (1 : ℝ))
            (p := fun y : ZMod N => ¬ Nat.Coprime y.val N),
          Finset.sum_const, nsmul_eq_mul, mul_one]
      have hnc : (Finset.univ.filter
          (fun y : ZMod N => Nat.Coprime y.val N)).card
          + (Finset.univ.filter
              (fun y : ZMod N => ¬ Nat.Coprime y.val N)).card = N := by
        rw [Finset.card_filter_add_card_filter_not
              (p := fun y : ZMod N => Nat.Coprime y.val N),
            Finset.card_univ, ZMod.card N]
      rw [residue_coprime_card N] at hnc
      have hnonc : (Finset.univ.filter
          (fun y : ZMod N => ¬ Nat.Coprime y.val N)).card
          = N - Fintype.card (ZMod N)ˣ := by omega
      rw [hsum, hnonc]
    have hrow : ∀ (a : (ZMod N)ˣ) (y : Fin M),
        ∑ z : Fin M, residueAttemptMass N M k hM (Sum.inr (Sum.inr (a, (y, z))))
          = (modularOrderLaw N M a hM).prob y * ((2 ^ k : ℝ))⁻¹ := by
      intro a y
      rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) =>
        show residueAttemptMass N M k hM (Sum.inr (Sum.inr (a, (y, z))))
            = (modularOrderLaw N M a hM).prob y *
                ((modularOrderLaw N M a hM).prob z * ((2 ^ k : ℝ))⁻¹) from
          by unfold residueAttemptMass; ring,
        ← Finset.mul_sum, ← Finset.sum_mul, (modularOrderLaw N M a hM).sum_one]
      ring
    have hinner : ∀ a : (ZMod N)ˣ,
        ∑ yz : Fin M × Fin M,
            residueAttemptMass N M k hM (Sum.inr (Sum.inr (a, yz)))
        = ((2 ^ k : ℝ))⁻¹ := by
      intro a
      rw [Fintype.sum_prod_type,
        Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hrow a y,
        ← Finset.sum_mul, (modularOrderLaw N M a hM).sum_one]
      ring
    have hright : ∑ q : (ZMod N)ˣ × Fin M × Fin M,
          residueAttemptMass N M k hM (Sum.inr (Sum.inr q))
        = ((Fintype.card (ZMod N)ˣ : ℕ) : ℝ) / 2 ^ k := by
      rw [Fintype.sum_prod_type,
        Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
          show ∑ yz : Fin M × Fin M,
              residueAttemptMass N M k hM (Sum.inr (Sum.inr (a, yz)))
              = ((2 ^ k : ℝ))⁻¹ from hinner a,
        Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hleft, hmid, hright]
    have hcu : Fintype.card (ZMod N)ˣ ≤ N := by
      rw [← residue_coprime_card N]
      calc (Finset.univ.filter fun y : ZMod N => Nat.Coprime y.val N).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = N := ZMod.card N
    rw [← add_div, ← add_div, ← Nat.cast_add, Nat.sub_add_cancel hcu,
      ← Nat.cast_add, Nat.sub_add_cancel hle,
      Nat.cast_pow]
    push_cast
    exact div_self (pow_ne_zero k (by norm_num : ((2 : ℝ)) ≠ 0))

/-- Counts residues whose representatives have a proper nontrivial greatest common divisor with
`N`. -/
def residueGcdProperCount (N : ℕ) [NeZero N] : ℕ :=
  (Finset.univ.filter fun y : ZMod N =>
    1 < Nat.gcd y.val N ∧ Nat.gcd y.val N < N).card

/-- The single attempt bound expression combining proper greatest common divisor residues, unit
count, prime factor count, and the order sampling constant. -/
noncomputable def shorResidueAttemptBound (N k : ℕ) [NeZero N] : ℝ :=
  ((residueGcdProperCount N : ℝ) +
      (Fintype.card (ZMod N)ˣ : ℝ) *
        (1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ))) *
        ((8 / Real.pi ^ 2) ^ 2 / 4)) / 2 ^ k

/-- The program success probability, equal to one for preprocessing factor output and otherwise
to the probability of at least one successful residue attempt. -/
noncomputable def shorResidueProgramSuccessProb (N R k M : ℕ) [NeZero N]
    (hM : 0 < M) (hk : N ≤ 2 ^ k) : ℝ :=
  match shorPreprocess N with
  | ShorPreResult.factor _ => 1
  | ShorPreResult.residue =>
      (residueAttemptLaw N M k hM hk).probEvent
        (residueAttemptRepSuccess N M k R)

end Qatlib.Concepts.RiskEstimation.PopulationGap
