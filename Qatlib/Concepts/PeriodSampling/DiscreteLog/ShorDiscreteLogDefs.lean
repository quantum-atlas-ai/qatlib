/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
public import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider
public import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplier
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixAccess.RitzPipeline Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.CircuitImpl.ReflectionCompile Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.MatrixAccess.RitzPipeline

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.PeriodSampling.DiscreteLog

open Qatlib
open scoped Classical BigOperators

structure DlogSampleRecord (m t : ℕ) where

  cprime : Fin t → ℤ

  dprime : Fin t → ℤ

def dlogSampleCongruent (m : ℕ) (r : ℤ) {t : ℕ} (rec : DlogSampleRecord m t) : Prop :=
  ∀ i, Int.ModEq (m : ℤ) (rec.dprime i + r * rec.cprime i) 0

def dlogBasePrimes (m : ℕ) : Finset ℕ := m.primeFactors

def dlogMaxPrimePower (m ℓ : ℕ) : ℕ := ℓ ^ m.factorization ℓ

def dlogSmallBasePrimes (m : ℕ) : Finset ℕ :=
  (dlogBasePrimes m).filter fun ℓ => ℓ ≤ 18

def dlogLargeBasePrimes (m : ℕ) : Finset ℕ :=
  (dlogBasePrimes m).filter fun ℓ => 18 < ℓ

def dlogPrimeCandidates (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) (ℓ : ℕ) : Finset ℕ :=
  (Finset.range (dlogMaxPrimePower m ℓ)).filter fun ρ =>
    ∀ i, Int.ModEq (dlogMaxPrimePower m ℓ : ℤ)
      (rec.dprime i + (ρ : ℤ) * rec.cprime i) 0

def dlogCrtMerge (m : ℕ) (choice : ℕ → ℕ) : ℕ :=
  (Nat.chineseRemainderOfFinset choice (fun ℓ => dlogMaxPrimePower m ℓ)
    (dlogBasePrimes m)
    (by
      intro ℓ hℓ
      have hprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
      have hne : m ≠ 0 := (Nat.mem_primeFactors.mp hℓ).2.2
      unfold dlogMaxPrimePower
      exact pow_ne_zero _ hprime.ne_zero)
    (by
      intro a ha b hb hab
      have hpa : a.Prime := Nat.prime_of_mem_primeFactors ha
      have hpb : b.Prime := Nat.prime_of_mem_primeFactors hb
      have hcop : Nat.Coprime a b := (Nat.coprime_primes hpa hpb).2 hab
      exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hcop))).val

def dlogMergedCandidates (p : ℕ) (g x : ZMod p) {t : ℕ}
    (rec : DlogSampleRecord (p - 1) t) : Finset ℕ :=
  (Finset.range (p - 1)).filter fun r' =>
    (∀ ℓ ∈ dlogBasePrimes (p - 1),
        r' % dlogMaxPrimePower (p - 1) ℓ ∈ dlogPrimeCandidates (p - 1) rec ℓ) ∧
      g ^ r' = x

def dlogEnumerationCost (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) : ℕ :=
  ∏ ℓ ∈ dlogBasePrimes m, (dlogPrimeCandidates m rec ℓ).card

def dlogSmallEnumerationCost (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) : ℕ :=
  ∏ ℓ ∈ dlogSmallBasePrimes m, (dlogPrimeCandidates m rec ℓ).card

def dlogEventMass {X : Type} [Fintype X] (law : FinDist X) (G : X → Prop)
    [DecidablePred G] : ℝ :=
  ∑ x, if G x then law.prob x else 0

def dlogConditionalMarginal {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y) (y : Y) : ℝ :=
  (∑ x, if π x = y ∧ G x then law.prob x else 0) / dlogEventMass law G

def dlogUniformGoodDivisibilityTransport {X : Type} [Fintype X] [DecidableEq X]
    (μ ν : FinDist X) (E : X → Prop) [DecidablePred E] : Prop :=
  μ.expect (fun x => if E x then (1 : ℝ) else 0) ≤
    ν.expect (fun x => if E x then (1 : ℝ) else 0)

def dlogUniformGoodPointwiseTransport {X : Type} [Fintype X] [DecidableEq X]
    (μ ν : FinDist X) : Prop :=
  ∀ x, μ.prob x ≤ ν.prob x

def dlogConditionalLaw {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (G : X → Prop) [DecidablePred G] (π : X → Y)
    (hmass : 0 < dlogEventMass law G) : FinDist Y where
  prob y := dlogConditionalMarginal law G π y
  nonneg y := by
    unfold dlogConditionalMarginal
    exact div_nonneg
      (Finset.sum_nonneg fun x _ => by
        split_ifs
        · exact law.nonneg x
        · exact le_rfl)
      (le_of_lt hmass)
  sum_one := by
    classical
    unfold dlogConditionalMarginal
    have hsum : (∑ y, ∑ x, if π x = y ∧ G x then law.prob x else 0)
        = ∑ x, if G x then law.prob x else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hsingle : (∑ y ∈ (Finset.univ : Finset Y),
            (if π x = y ∧ G x then law.prob x else 0))
          = (if π x = π x ∧ G x then law.prob x else 0) :=
        Finset.sum_eq_single (π x) (fun b _ hb => by
          have hne : ¬(π x = b) := fun h => hb h.symm
          simp [hne])
          (fun h => absurd (Finset.mem_univ _) h)
      rw [hsingle]
      simp
    calc
      (∑ y, (∑ x, if π x = y ∧ G x then law.prob x else 0) / dlogEventMass law G)
          = (∑ y, ∑ x, if π x = y ∧ G x then law.prob x else 0) / dlogEventMass law G := by
            rw [Finset.sum_div]
      _ = (∑ x, if G x then law.prob x else 0) / dlogEventMass law G := by rw [hsum]
      _ = 1 := by
        rw [dlogEventMass]
        exact div_self hmass.ne'

structure DlogGroupEncoding (p x q : ℕ) where

  pBits : ℕ

  xBits : ℕ

  qBits : ℕ

  hp : p < 2 ^ pBits

  hx : x < 2 ^ xBits

  hq : q < 2 ^ qBits

  hinvert : Nat.Coprime x p

def dlogEmbedGate {n m : ℕ} (off : ℕ) (h : off + n ≤ m) :
    LocalQFTGate n → LocalQFTGate m
  | .h a => .h ⟨a.val + off, by omega⟩
  | .cp a c k neg =>
      .cp ⟨a.val + off, by omega⟩ ⟨c.val + off, by omega⟩ k neg
  | .swap a b => .swap ⟨a.val + off, by omega⟩ ⟨b.val + off, by omega⟩

def dlogReadoutProgram (n : ℕ) : List (LocalQFTGate (2 * n)) :=
  (localQFT n).map (dlogEmbedGate (off := n) (by omega)) ++
  (localQFT n).map (dlogEmbedGate (off := 0) (by omega))

def dlogGoodIndexCard {X : Type} [Fintype X] (G : X → Prop) [DecidablePred G] : ℕ :=
  (Finset.univ.filter G).card

def dlogAvoidMass {X : Type} [Fintype X] (law : FinDist X) (G : X → Prop)
    [DecidablePred G] (B : X → Prop) [DecidablePred B] : ℝ :=
  (∑ x, if G x ∧ ¬ B x then law.prob x else 0) / dlogEventMass law G

def dlogEscapeProbability (p q w : ℕ) : ℝ :=
  (((q / 12 : ℕ) : ℝ) - (((p - 1) / w + 1 : ℕ) : ℝ)) *
    ((p - 1 : ℝ) / (20 * (q : ℝ)^2))

def dlogUniformEscapeProbability (p q : ℕ) : ℝ :=
  dlogEscapeProbability p q 19

def dlogPinningBudget (W : Finset ℕ) (δ : ℝ) : ℕ :=
  Nat.floor ((2 * (W.card : ℝ) - 1) / δ) + 1

def dlogBasePrimeList (m : ℕ) : List ℕ := (dlogBasePrimes m).sort

def dlogCrtCombinations (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) :
    List ℕ → (ℕ → ℕ) → List ℕ
  | [], choice => [dlogCrtMerge m choice]
  | ℓ :: rest, choice =>
      (dlogPrimeCandidates m rec ℓ).toList.flatMap fun ρ =>
        dlogCrtCombinations m rec rest (fun l => if l = ℓ then ρ else choice l)

def dlogCrtCandidateList (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t)
    (choice : ℕ → ℕ) : List ℕ :=
  dlogCrtCombinations m rec (dlogBasePrimeList m) choice

def dlogVerifiedCandidates (p : ℕ) (g x : ZMod p) {t : ℕ}
    (rec : DlogSampleRecord (p - 1) t) : List ℕ :=
  (dlogCrtCandidateList (p - 1) rec (fun _ => 0)).filter fun r' => g ^ r' = x

def dlogMultiplierGcd {t m : ℕ} (rec : DlogSampleRecord m t) : ℕ :=
  (Finset.univ : Finset (Fin t)).gcd fun i => (rec.cprime i).natAbs

def dlogCommonValuation (ℓ cap : ℕ) {t m : ℕ} (rec : DlogSampleRecord m t) : ℕ :=
  let G := dlogMultiplierGcd rec
  if G = 0 then cap else min cap (G.factorization ℓ)

def dlogPrimePowerCandidates (ℓ α : ℕ) {t m : ℕ} (rec : DlogSampleRecord m t) : Finset ℕ :=
  (Finset.range (ℓ ^ α)).filter fun ρ =>
    ∀ i, Int.ModEq (ℓ ^ α : ℤ) (rec.dprime i + (ρ : ℤ) * rec.cprime i) 0

def dlogPinningHypothesis (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) : Prop :=
  ∀ ℓ ∈ dlogBasePrimes m, ∃ i, ¬ ((ℓ : ℤ) ∣ rec.cprime i)

def dlogLargePinningHypothesis (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) : Prop :=
  ∀ ℓ ∈ dlogLargeBasePrimes m, ∃ i, ¬ ((ℓ : ℤ) ∣ rec.cprime i)

def dlogSmallPinningHypothesis (m : ℕ) {t : ℕ} (rec : DlogSampleRecord m t) : Prop :=
  ∀ ℓ ∈ dlogSmallBasePrimes m, ∃ i, ¬ ((ℓ : ℤ) ∣ rec.cprime i)

def dlogThirdRegisterValue (p : ℕ) (g x : ZMod p) (a b : ℕ) : ZMod p :=
  g ^ a * x ^ (p - 1 - b)

def dlogModexpFactors (p : ℕ) (g x : ZMod p) (a b : ℕ) : ZMod p × ZMod p :=
  (g ^ a, x ^ (p - 1 - b))

def dlogModMulRemainder (w : ℕ) (a b : Reg w) (mReg : Reg (2 * w)) : Reg (2 * (2 * w)) :=
  booleanWordDivRemainder (2 * w) (booleanWordMulResult w a b) mReg

def dlogModMulGateCount (w : ℕ) : ℕ := 2730 * w ^ 2 + 398 * w + 60

def dlogModMulSpaceCount (w : ℕ) : ℕ := 91 * w ^ 2 + 27 * w + 2

def dlogModexpValue (base m : ℕ) (e : ℕ) : ℕ :=
  if h : e = 0 then 1 % m
  else (dlogModexpValue base m (e / 2) ^ 2 * (if e % 2 = 1 then base else 1)) % m
termination_by e
decreasing_by
  omega

def dlogModexpMulCount (e : ℕ) : ℕ := 2 * (Nat.log2 e + 1)

def dlogModexpGateCount (w e : ℕ) : ℕ :=
  dlogModexpMulCount e * dlogModMulGateCount w

structure DlogResidueRead where

  cprime : ℤ

  residue : ℤ

def DlogReadRelation (m q : ℕ) (i : Fin q) (rd : DlogResidueRead) : Prop :=
  (m : ℤ) * (i : ℤ) = (q : ℤ) * rd.cprime + rd.residue

def DlogGoodRead (q : ℕ) (rd : DlogResidueRead) : Prop :=
  rd.residue.natAbs ≤ q / 12

def dlogReadFiberDivisor (m q w : ℕ) : ℕ := Nat.gcd (m / w) q

def dlogTotalGateCount (p x q : ℕ) (enc : DlogGroupEncoding p x q) : ℕ :=
  2 * ((enc.pBits + 1) ^ 2 + (enc.pBits + 1)) + 6400 * (Nat.log2 p + 1) ^ 3

def dlogTotalSpaceCount (p x q : ℕ) (enc : DlogGroupEncoding p x q) : ℕ :=
  3 * (enc.pBits + 1) + (91 * (Nat.log2 p + 1) ^ 2 + 27 * (Nat.log2 p + 1) + 2)

def dlogResidueIndexVal (K : ℕ) (k : ℤ) : ℕ := (k + (K : ℤ)).toNat

def dlogResidueIndex (K : ℕ) (k : ℤ)
    (hk : -((K : ℤ)) ≤ k ∧ k ≤ (K : ℤ)) : Fin (2 * K + 1) :=
  ⟨dlogResidueIndexVal K k, by
    simp only [dlogResidueIndexVal]
    have h0 : 0 ≤ k + (K : ℤ) := by omega
    have h1 : k + (K : ℤ) ≤ 2 * (K : ℤ) := by omega
    have h3 : ((k + (K : ℤ)).toNat : ℤ) = k + (K : ℤ) := by
      rw [Int.toNat_of_nonneg h0]
    have h4 : ((k + (K : ℤ)).toNat : ℤ) ≤ 2 * (K : ℤ) := by omega
    have h5 : (k + (K : ℤ)).toNat ≤ 2 * K := by exact_mod_cast h4
    omega⟩

def dlogDivisibleReadBudget (m q w : ℕ) : ℕ :=
  (2 * ((q / 12) / (w * dlogReadFiberDivisor m q w)) + 1) * dlogReadFiberDivisor m q w

def dlogMarginal {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (π : X → Y) (y : Y) : ℝ :=
  ∑ x, if π x = y then law.prob x else 0

def dlogJointMass {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y) (y : Y) : ℝ :=
  ∑ x, if π x = y ∧ E x then law.prob x else 0

noncomputable def dlogUniformGoodIndexLaw {Y : Type} [Fintype Y] [DecidableEq Y]
    (G : Y → Prop) [DecidablePred G] (hG : 0 < dlogGoodIndexCard G) : FinDist Y where
  prob y := if G y then (dlogGoodIndexCard G : ℝ)⁻¹ else 0
  nonneg _ := by positivity
  sum_one := by
    classical
    have hcard : ((dlogGoodIndexCard G : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hG)
    show (∑ y, (if G y then (dlogGoodIndexCard G : ℝ)⁻¹ else 0)) = 1
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard

def dlogGoodnessWeight {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (E : X → Prop) [DecidablePred E] (π : X → Y) (y : Y) : ℝ :=
  dlogJointMass law E π y / dlogMarginal law π y

def dlogUniformMarginal {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (law : FinDist X) (π : X → Y) : Prop :=
  ∀ y, dlogMarginal law π y = (Fintype.card Y : ℝ)⁻¹

end Qatlib.Concepts.PeriodSampling.DiscreteLog
