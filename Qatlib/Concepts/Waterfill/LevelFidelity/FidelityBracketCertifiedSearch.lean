/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
import Qatlib.Concepts.Waterfill.LevelSearch.WaterFillingOptimization

/-!
# Certified rational fidelity search

This module implements rational fidelity bisection with a ledger of divisions, coordinate reads,
and comparisons, and produces explicit endpoint certificates. It proves bracket and mass bounds,
a conditional fidelity-error estimate, and scaling identities for water-filling profiles used in
quantum rejection sampling [OzolsRoettelerRoland2013].

## Main statements

* `certifiedFidelitySearch_eq`: identify the returned bracket and exact search ledger.
* `certifiedFidelity_error`: bound the upper-endpoint fidelity error under margin and depth
  conditions.
* `frontier1`: combine bracket, mass, error, and operation-count guarantees.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch

open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open scoped BigOperators

/-- A record of division counts, mass-coordinate reads, dot-product-coordinate reads, and
comparisons in certified fidelity search. -/
structure CertifiedSearchLedger where
  divisions : ℕ
  massReads : ℕ
  dotReads : ℕ
  comparisons : ℕ
  deriving DecidableEq, Repr

/-- Add two certified-search ledgers componentwise. -/
def ledgerAdd (a b : CertifiedSearchLedger) : CertifiedSearchLedger :=
  ⟨a.divisions + b.divisions, a.massReads + b.massReads,
    a.dotReads + b.dotReads, a.comparisons + b.comparisons⟩

instance : Add CertifiedSearchLedger where
  add := ledgerAdd

/-- The rational mass and target-overlap readings at both endpoints of a fidelity bracket. -/
structure FidelityBracketReading where
  loMass : ℚ
  loDot : ℚ
  hiMass : ℚ
  hiDot : ℚ
  deriving DecidableEq, Repr

/-- A record of endpoint readings, Boolean fidelity-test results, and the work ledger for
producing them. -/
structure FidelityBracketCertificate where
  reading : FidelityBracketReading
  loReaches : Bool
  hiReaches : Bool
  ledger : CertifiedSearchLedger
  deriving DecidableEq, Repr

/-- Bisect the rational water-level interval using the squared-overlap fidelity test, returning
the bracket together with its accumulated operation ledger. -/
def certifiedFidelitySearch {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) :
    ℕ → (ℚ × ℚ) × CertifiedSearchLedger
  | 0 => ((0, computedWaterHigh π σ), ⟨m, 0, 0, 0⟩)
  | k + 1 =>
      let r := certifiedFidelitySearch π σ p k
      let b := r.1
      let led := r.2
      let mid := (b.1 + b.2) / 2
      let mass := computedMass π σ mid
      let dot := computedDot π σ mid
      let br := if dot ^ 2 ≥ p * mass then (mid, b.2) else (b.1, mid)
      (br, ⟨led.divisions + 1, led.massReads + m, led.dotReads + m, led.comparisons + 1⟩)

/-- Evaluate mass and target overlap at both bracket endpoints, record the Boolean fidelity
tests, and attach their evaluation ledger. -/
def certifiedFidelityCertificate {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (b : ℚ × ℚ) :
    FidelityBracketCertificate :=
  let massLo := computedMass π σ b.1
  let dotLo := computedDot π σ b.1
  let massHi := computedMass π σ b.2
  let dotHi := computedDot π σ b.2
  { reading := ⟨massLo, dotLo, massHi, dotHi⟩
    loReaches := decide (dotLo ^ 2 ≥ p * massLo)
    hiReaches := decide (dotHi ^ 2 ≥ p * massHi)
    ledger := ⟨0, 2 * m, 2 * m, 2⟩ }

/-- Combine the work ledger of certified bisection with the ledger for its final endpoint
certificate. -/
def certifiedFidelityWork {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) :
    CertifiedSearchLedger :=
  let s := (certifiedFidelitySearch π σ p k).2
  let c := (certifiedFidelityCertificate π σ p (certifiedFidelitySearch π σ p k).1).ledger
  ⟨s.divisions + c.divisions, s.massReads + c.massReads, s.dotReads + c.dotReads,
    s.comparisons + c.comparisons⟩

/-- The computed target overlap is nonnegative for nonnegative profiles and water level. -/
theorem computedDot_nonneg {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) {γ : ℚ} (hγ : 0 ≤ γ) :
    0 ≤ computedDot π σ γ := by
  unfold computedDot
  refine Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (hσ j) (le_min (hπ j) (mul_nonneg hγ (hσ j)))

/-- For a nonnegative target profile, the computed target overlap is monotone in the water
level. -/
theorem computedDot_mono {m : ℕ} (π σ : Fin m → ℚ)
    (hσ : ∀ j, 0 ≤ σ j) {a b : ℚ} (hab : a ≤ b) :
    computedDot π σ a ≤ computedDot π σ b := by
  unfold computedDot
  refine Finset.sum_le_sum fun j _ => ?_
  have hle : waterFill π σ a j ≤ waterFill π σ b j :=
    min_le_min (le_refl _) (mul_le_mul_of_nonneg_right hab (hσ j))
  exact mul_le_mul_of_nonneg_left hle (hσ j)

/-- The computed squared mass is nonnegative at every rational water level. -/
theorem computedMass_nonneg {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    0 ≤ computedMass π σ γ := by
  unfold computedMass computedWaterEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For a nonnegative source and strictly positive target, the computed upper water level
saturates every coordinate at its source amplitude. -/
theorem waterFill_at_high {m : ℕ} (π σ : Fin m → ℚ)
    (h : ∀ j, 0 ≤ π j ∧ 0 < σ j) (j : Fin m) :
    waterFill π σ (computedWaterHigh π σ) j = π j := by
  have hn (i : Fin m) : 0 ≤ π i / σ i := div_nonneg (h i).1 (h i).2.le
  have hj : π j / σ j ≤ ∑ i, π i / σ i :=
    Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ j)
  have hb : π j ≤ computedWaterHigh π σ * σ j :=
    (div_le_iff₀ (h j).2).mp (by unfold computedWaterHigh; linarith)
  rw [waterFill, min_eq_left hb]

/-- For nonnegative profiles and ordered nonnegative levels, prove the cross-multiplied
inequality expressing decrease of squared overlap relative to mass. -/
theorem computedFidelity_anti {m : ℕ} (π σ : Fin m → ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) :
    computedDot π σ b ^ 2 * computedMass π σ a ≤
      computedDot π σ a ^ 2 * computedMass π σ b := by
  have h := realFidelity_anti (m := m) (fun i => (π i : ℝ)) (fun i => (σ i : ℝ))
    (fun i => Rat.cast_nonneg.mpr (hπ i)) (fun i => Rat.cast_nonneg.mpr (hσ i))
    (Rat.cast_nonneg.mpr ha) (Rat.cast_le.mpr hab)
  rw [realDot_cast, realMass_cast, realDot_cast, realMass_cast] at h
  exact_mod_cast h

/-- For nonnegative profiles, passing the fidelity test at a level implies passing it at every
smaller nonnegative level. -/
theorem fidelityReaches_mono {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hreaches : fidelityReaches π σ p b) :
    fidelityReaches π σ p a := by
  have hna : 0 ≤ computedMass π σ a := computedMass_nonneg π σ a
  have hnb : 0 ≤ computedMass π σ b := computedMass_nonneg π σ b
  unfold fidelityReaches at hreaches ⊢
  by_cases hm : computedMass π σ b = 0
  · have hmono := computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ j⟩) ha hab
    have hmE : computedWaterEnergy π σ b = 0 := hm
    rw [hmE] at hmono
    have hma : computedMass π σ a = 0 := le_antisymm hmono hna
    rw [hma, mul_zero]
    exact sq_nonneg _
  · have hanti := computedFidelity_anti π σ hπ hσ ha hab
    have hposb : 0 < computedMass π σ b := lt_of_le_of_ne hnb (Ne.symm hm)
    have hstep2 : p * computedMass π σ b * computedMass π σ a ≤
        computedDot π σ b ^ 2 * computedMass π σ a := by nlinarith [hna]
    have hstep3 : computedDot π σ b ^ 2 * computedMass π σ a ≤
        computedDot π σ a ^ 2 * computedMass π σ b := hanti
    nlinarith [hposb, hna]

/-- Certified bisection returns `fidelityBracket` and the exact ledger `⟨m + k, m * k, m * k,
k⟩`. -/
theorem certifiedFidelitySearch_eq {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) :
    (certifiedFidelitySearch π σ p k).1 = fidelityBracket π σ p k ∧
    (certifiedFidelitySearch π σ p k).2 = ⟨m + k, m * k, m * k, k⟩ := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      have hbr : (certifiedFidelitySearch π σ p k).1 = fidelityBracket π σ p k := ih.1
      have hled : (certifiedFidelitySearch π σ p k).2 = ⟨m + k, m * k, m * k, k⟩ := ih.2
      constructor
      · simp only [certifiedFidelitySearch, fidelityBracket]
        rw [hbr]
      · simp only [certifiedFidelitySearch]
        rw [hled]
        simp only [CertifiedSearchLedger.mk.injEq]
        exact ⟨by omega, by rw [Nat.mul_succ], by rw [Nat.mul_succ], by simp⟩

/-- Express the certified-search ledger using `searchWork`, with `k` additional divisions and
separate mass and dot-product read counts. -/
theorem certifiedFidelitySearch_refines_frozen_work {m : ℕ} (π σ : Fin m → ℚ)
    (p : ℚ) (k : ℕ) :
    (certifiedFidelitySearch π σ p k).2 =
      ⟨(searchWork m k).divisions + k, (searchWork m k).energyEvaluations,
        (searchWork m k).energyEvaluations, (searchWork m k).comparisons⟩ := by
  have h := certifiedFidelitySearch_eq π σ p k
  rw [h.2]
  rfl

/-- For nonnegative source, positive target, and a threshold exceeding the source's
overlap-to-mass ratio, every bracket has the stated dyadic width and passes the fidelity
test only at its lower endpoint. -/
theorem certifiedFidelityBracket_props {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2)) :
    ∀ k : ℕ,
      let b := fidelityBracket π σ p k
      0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ computedWaterHigh π σ ∧
        b.2 - b.1 = computedWaterHigh π σ / (2 : ℚ) ^ k ∧
        fidelityReaches π σ p b.1 ∧ ¬ fidelityReaches π σ p b.2 := by
  intro k
  induction k with
  | zero =>
      have hh := computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)
      have hz := computedMass_dot_zero π σ hπ
      have hmassH : computedMass π σ (computedWaterHigh π σ) = ∑ j, (π j) ^ 2 := by
        simpa [computedMass] using! hh.2
      have hdotH : computedDot π σ (computedWaterHigh π σ) = ∑ j, π j * σ j := by
        unfold computedDot
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [waterFill_at_high π σ (fun i => ⟨hπ i, hσ i⟩) j]
        ring
      dsimp only [fidelityBracket]
      refine ⟨?_, ?_, le_rfl, ?_, ?_, ?_⟩
      · norm_num
      · have hsum : (0 : ℚ) ≤ ∑ j, π j / σ j :=
          Finset.sum_nonneg fun j _ => div_nonneg (hπ j) (hσ j).le
        unfold computedWaterHigh
        linarith
      · rw [pow_zero, div_one, sub_zero]
      · unfold fidelityReaches
        rw [hz.2, hz.1, mul_zero]
        exact sq_nonneg _
      · unfold fidelityReaches
        rw [hdotH, hmassH]
        exact not_le.mpr hrange
  | succ k ih =>
      (try dsimp only at ih)
      obtain ⟨hl, hll, hlu, hw, hrl, hru⟩ := ih
      dsimp only [fidelityBracket]
      split_ifs with hm
      · refine ⟨?_, ?_, hlu, ?_, ?_, hru⟩
        · nlinarith [hll, hl]
        · nlinarith [hll]
        · calc
            (fidelityBracket π σ p k).2 -
                ((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2
                = ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1) / 2 := by ring
            _ = (computedWaterHigh π σ / (2 : ℚ) ^ k) / 2 := by rw [hw]
            _ = computedWaterHigh π σ / (2 : ℚ) ^ (k + 1) := by
              rw [pow_succ, div_mul_eq_div_div]
        · exact hm
      · refine ⟨hl, ?_, ?_, ?_, hrl, ?_⟩
        · nlinarith [hll]
        · nlinarith [hll, hlu]
        · calc
            ((fidelityBracket π σ p k).1 + (fidelityBracket π σ p k).2) / 2 -
                (fidelityBracket π σ p k).1
                = ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1) / 2 := by ring
            _ = (computedWaterHigh π σ / (2 : ℚ) ^ k) / 2 := by rw [hw]
            _ = computedWaterHigh π σ / (2 : ℚ) ^ (k + 1) := by
              rw [pow_succ, div_mul_eq_div_div]
        · exact hm

/-- Under the stated profile and threshold hypotheses, bracket endpoint masses are ordered
between zero and the source squared norm, with their difference bounded by the bracket width
times twice the source-target dot product. -/
theorem certifiedFidelity_energy {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2)) :
    0 ≤ computedMass π σ (fidelityBracket π σ p k).1 ∧
    computedMass π σ (fidelityBracket π σ p k).1 ≤ computedMass π σ (fidelityBracket π σ p k).2 ∧
    computedMass π σ (fidelityBracket π σ p k).2 ≤ (∑ j, (π j) ^ 2) ∧
    computedMass π σ (fidelityBracket π σ p k).2 - computedMass π σ (fidelityBracket π σ p k).1 ≤
      2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  have hlo : 0 ≤ (fidelityBracket π σ p k).1 := hbr.1
  have hle : (fidelityBracket π σ p k).1 ≤ (fidelityBracket π σ p k).2 := hbr.2.1
  have hhi : (fidelityBracket π σ p k).2 ≤ computedWaterHigh π σ := hbr.2.2.1
  have hwidth : (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1 =
      computedWaterHigh π σ / (2 : ℚ) ^ k := hbr.2.2.2.1
  have hsat := computedWaterHigh_saturates π σ (fun j => ⟨hπ j, hσ j⟩)
  refine ⟨computedMass_nonneg π σ _, ?_, ?_, ?_⟩
  · exact computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hlo hle
  · have hlo2 : 0 ≤ (fidelityBracket π σ p k).2 := hlo.trans hle
    have hmono := computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hlo2 hhi
    simpa [computedMass] using! le_trans hmono hsat.2.le
  · have hinc := computedWaterEnergy_increment π σ (fun j => ⟨hπ j, hσ' j⟩) hlo hle
    calc
      computedMass π σ (fidelityBracket π σ p k).2 -
          computedMass π σ (fidelityBracket π σ p k).1
          = computedWaterEnergy π σ (fidelityBracket π σ p k).2 -
            computedWaterEnergy π σ (fidelityBracket π σ p k).1 := rfl
      _ ≤ 2 * (∑ j, π j * σ j) * ((fidelityBracket π σ p k).2 -
            (fidelityBracket π σ p k).1) := hinc
      _ = 2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) := by
        rw [hwidth]

/-- Under the positivity, threshold-range, coordinate-margin, and depth hypotheses, the upper
bracket endpoint has computed fidelity within `ε` of `p`. -/
theorem certifiedFidelity_error {m : ℕ} (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k) :
    |computedFidelity π σ (fidelityBracket π σ p k).2 - p| ≤ ε := by
  have hσ' : ∀ j, 0 ≤ σ j := fun j => (hσ j).le
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  have ha0 : 0 ≤ (fidelityBracket π σ p k).1 := hbr.1
  have hab : (fidelityBracket π σ p k).1 ≤ (fidelityBracket π σ p k).2 := hbr.2.1
  have hb0 : 0 ≤ (fidelityBracket π σ p k).2 := hbr.1.trans hbr.2.1
  have hwidth : (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1 =
      computedWaterHigh π σ / (2 : ℚ) ^ k := hbr.2.2.2.1
  have hreach : computedDot π σ (fidelityBracket π σ p k).1 ^ 2 ≥
      p * computedMass π σ (fidelityBracket π σ p k).1 := hbr.2.2.2.2.1
  have hnotreach : ¬ (computedDot π σ (fidelityBracket π σ p k).2 ^ 2 ≥
      p * computedMass π σ (fidelityBracket π σ p k).2) := hbr.2.2.2.2.2

  have hgc : 0 < π i / σ i := div_pos hpi (hσ i)
  have hgc_lt : π i / σ i < (fidelityBracket π σ p k).2 := by
    by_contra hcon
    have hle : (fidelityBracket π σ p k).2 ≤ π i / σ i := le_of_not_gt hcon
    exact hnotreach (fidelityReaches_mono π σ p hπ hσ' hb0 hle hmargin)

  have hmass_gc : (π i) ^ 2 ≤ computedMass π σ (π i / σ i) := by
    unfold computedMass
    have hfill : waterFill π σ (π i / σ i) i = π i := by
      rw [waterFill]
      have hne : σ i ≠ 0 := (hσ i).ne'
      have heq : (π i / σ i) * σ i = π i := by field_simp
      rw [heq, min_eq_left (le_refl _)]
    have hle : (waterFill π σ (π i / σ i) i) ^ 2 ≤
        ∑ j, (waterFill π σ (π i / σ i) j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rwa [hfill] at hle
  have hmass_mono : computedMass π σ (π i / σ i) ≤ computedMass π σ (fidelityBracket π σ p k).2 :=
    computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) hgc.le hgc_lt.le
  have hmass_b : (π i) ^ 2 ≤ computedMass π σ (fidelityBracket π σ p k).2 :=
    le_trans hmass_gc hmass_mono
  have hmass_pos : 0 < computedMass π σ (fidelityBracket π σ p k).2 :=
    lt_of_lt_of_le (sq_pos_of_pos hpi) hmass_b

  have hdot_mono : computedDot π σ (fidelityBracket π σ p k).1 ≤
      computedDot π σ (fidelityBracket π σ p k).2 :=
    computedDot_mono π σ hσ' hab
  have hdot_hi : 0 ≤ computedDot π σ (fidelityBracket π σ p k).2 :=
    computedDot_nonneg π σ hπ hσ' hb0
  have hdot_lo : 0 ≤ computedDot π σ (fidelityBracket π σ p k).1 :=
    computedDot_nonneg π σ hπ hσ' ha0

  have hmass_inc : computedMass π σ (fidelityBracket π σ p k).2 -
      computedMass π σ (fidelityBracket π σ p k).1 ≤
      2 * (∑ j, π j * σ j) *
        ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1) :=
    computedWaterEnergy_increment π σ (fun j => ⟨hπ j, hσ' j⟩) ha0 hab
  have hmass_diff : 0 ≤ computedMass π σ (fidelityBracket π σ p k).2 -
      computedMass π σ (fidelityBracket π σ p k).1 :=
    sub_nonneg.mpr (computedWaterEnergy_mono π σ (fun j => ⟨hπ j, hσ' j⟩) ha0 hab)

  have hgap : p * computedMass π σ (fidelityBracket π σ p k).2 -
      computedDot π σ (fidelityBracket π σ p k).2 ^ 2 ≤
      p * (2 * (∑ j, π j * σ j) *
        ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1)) := by
    have hsq : computedDot π σ (fidelityBracket π σ p k).1 ^ 2 ≤
        computedDot π σ (fidelityBracket π σ p k).2 ^ 2 := by
      nlinarith [sq_nonneg (computedDot π σ (fidelityBracket π σ p k).1),
        sq_nonneg (computedDot π σ (fidelityBracket π σ p k).2), hdot_mono, hdot_hi]
    have hp0 : 0 ≤ p := hp.le
    nlinarith [hsq, hreach, hmass_inc, hmass_diff]

  have hwin : 2 * (∑ j, π j * σ j) * p *
      ((fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1) ≤ ε * (π i) ^ 2 := by
    have hpos2 : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
    rw [hwidth]
    have heq : 2 * (∑ j, π j * σ j) * p * (computedWaterHigh π σ / (2 : ℚ) ^ k) =
        (2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ) / (2 : ℚ) ^ k := by
      field_simp
    rw [heq]
    exact (div_le_iff₀ hpos2).2 hsteps

  have hfidelity : computedFidelity π σ (fidelityBracket π σ p k).2 =
      computedDot π σ (fidelityBracket π σ p k).2 ^ 2 /
        computedMass π σ (fidelityBracket π σ p k).2 := by
    unfold computedFidelity
    rw [if_neg (ne_of_gt hmass_pos)]
  have hsub : computedDot π σ (fidelityBracket π σ p k).2 ^ 2 /
        computedMass π σ (fidelityBracket π σ p k).2 - p =
      (computedDot π σ (fidelityBracket π σ p k).2 ^ 2 -
        p * computedMass π σ (fidelityBracket π σ p k).2) /
        computedMass π σ (fidelityBracket π σ p k).2 := by
      field_simp
  rw [hfidelity, hsub, abs_div, abs_of_nonneg (le_of_lt hmass_pos)]
  refine (div_le_iff₀ hmass_pos).2 ?_
  have hneg : computedDot π σ (fidelityBracket π σ p k).2 ^ 2 -
      p * computedMass π σ (fidelityBracket π σ p k).2 < 0 := sub_neg.mpr (lt_of_not_ge hnotreach)
  rw [abs_of_neg hneg]
  have hp0 : 0 ≤ p := hp.le
  have hS2 : 0 ≤ (∑ j, (σ j) ^ 2) := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hD : 0 ≤ (∑ j, π j * σ j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ' j)
  have hΔ : 0 ≤ (fidelityBracket π σ p k).2 - (fidelityBracket π σ p k).1 :=
    sub_nonneg.mpr hab
  nlinarith [hgap, hwin, hmass_b, hε.le]

/-- Under the stated profile and threshold hypotheses, the bracket certificate records the exact
endpoint readings, a passing lower test, and a failing upper test. -/
theorem certifiedFidelityCertificate_agrees {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2)) :
    let c := certifiedFidelityCertificate π σ p (fidelityBracket π σ p k)
    c.reading.loMass = computedMass π σ (fidelityBracket π σ p k).1 ∧
    c.reading.loDot = computedDot π σ (fidelityBracket π σ p k).1 ∧
    c.reading.hiMass = computedMass π σ (fidelityBracket π σ p k).2 ∧
    c.reading.hiDot = computedDot π σ (fidelityBracket π σ p k).2 ∧
    c.loReaches = true ∧ c.hiReaches = false := by
  have hbr := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hbr)
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [certifiedFidelityCertificate]
    exact decide_eq_true hbr.2.2.2.2.1
  · simp only [certifiedFidelityCertificate]
    exact decide_eq_false hbr.2.2.2.2.2

/-- The combined search and endpoint-certificate ledger is exactly `⟨m + k, m * k + 2 * m, m * k
+ 2 * m, k + 2⟩`. -/
theorem certifiedFidelity_work {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) :
    certifiedFidelityWork π σ p k = ⟨m + k, m * k + 2 * m, m * k + 2 * m, k + 2⟩ := by
  have h := certifiedFidelitySearch_eq π σ p k
  simp only [certifiedFidelityWork]
  rw [h.2]
  rfl

/-- Under the stated positivity, range, margin, and depth conditions, combine bracket
invariants, endpoint mass bounds, the fidelity-error estimate, and exact search and
certificate work counts. -/
theorem frontier1
    (m k : ℕ) (π σ : Fin m → ℚ) (p ε : ℚ) (i : Fin m)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j)
    (hp : 0 < p) (hε : 0 < ε) (hpi : 0 < π i)
    (hrange : (∑ j, π j * σ j) ^ 2 < p * (∑ j, (π j) ^ 2))
    (hmargin : computedDot π σ (π i / σ i) ^ 2 ≥ p * computedMass π σ (π i / σ i))
    (hsteps : 2 * (∑ j, π j * σ j) * p * computedWaterHigh π σ
              ≤ ε * (π i) ^ 2 * (2 : ℚ) ^ k) :
    let b := fidelityBracket π σ p k

    0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ computedWaterHigh π σ ∧
      b.2 - b.1 = computedWaterHigh π σ / (2 : ℚ) ^ k ∧
      fidelityReaches π σ p b.1 ∧ ¬ fidelityReaches π σ p b.2 ∧

    0 ≤ computedMass π σ b.1 ∧ computedMass π σ b.1 ≤ computedMass π σ b.2 ∧
      computedMass π σ b.2 ≤ (∑ j, (π j) ^ 2) ∧
      computedMass π σ b.2 - computedMass π σ b.1 ≤
        2 * (∑ j, π j * σ j) * (computedWaterHigh π σ / (2 : ℚ) ^ k) ∧

    |computedFidelity π σ b.2 - p| ≤ ε ∧

    (certifiedFidelitySearch π σ p k).1 = fidelityBracket π σ p k ∧
    (certifiedFidelitySearch π σ p k).2 = ⟨m + k, m * k, m * k, k⟩ ∧

    certifiedFidelityWork π σ p k = ⟨m + k, m * k + 2 * m, m * k + 2 * m, k + 2⟩ := by
  (try dsimp only)
  have hb := certifiedFidelityBracket_props π σ p hπ hσ hrange k
  (try dsimp only at hb)
  have he := certifiedFidelity_energy π σ p k hπ hσ hrange
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact he.1
  · exact he.2.1
  · exact he.2.2.1
  · exact he.2.2.2
  · exact certifiedFidelity_error π σ p ε i k hπ hσ hp hε hpi hrange hmargin hsteps
  · exact (certifiedFidelitySearch_eq π σ p k).1
  · exact (certifiedFidelitySearch_eq π σ p k).2
  · exact certifiedFidelity_work π σ p k

/-- Multiply every rational source amplitude by `lam`. -/
def scaledSource {m : ℕ} (π : Fin m → ℚ) (lam : ℚ) : Fin m → ℚ :=
  fun i => lam * π i

/-- Scaling the source and water level by a nonnegative factor scales every filled amplitude by
that factor. -/
theorem waterFill_scaled {m : ℕ} (π σ : Fin m → ℚ) {lam γ : ℚ} (hlam : 0 ≤ lam) (j : Fin m) :
    waterFill (scaledSource π lam) σ (lam * γ) j = lam * waterFill π σ γ j := by
  have hmin : min (lam * π j) (lam * (γ * σ j)) = lam * min (π j) (γ * σ j) := by
    by_cases h : π j ≤ γ * σ j
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hlam)]
    · have h' : γ * σ j ≤ π j := le_of_not_ge h
      rw [min_eq_right h', min_eq_right (mul_le_mul_of_nonneg_left h' hlam)]
  unfold waterFill scaledSource
  rw [mul_assoc, hmin]

/-- Scaling the source and water level by a nonnegative factor scales the computed mass by the
square of that factor. -/
theorem computedMass_scaled {m : ℕ} (π σ : Fin m → ℚ) {lam γ : ℚ} (hlam : 0 ≤ lam) :
    computedMass (scaledSource π lam) σ (lam * γ) = lam ^ 2 * computedMass π σ γ := by
  unfold computedMass computedWaterEnergy
  calc
    (∑ i, (waterFill (scaledSource π lam) σ (lam * γ) i) ^ 2)
        = ∑ i, (lam * waterFill π σ γ i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [waterFill_scaled π σ hlam i]
    _ = ∑ i, lam ^ 2 * (waterFill π σ γ i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    _ = lam ^ 2 * ∑ i, (waterFill π σ γ i) ^ 2 := by
          rw [Finset.mul_sum]

/-- Scaling the source and water level by a nonnegative factor scales the computed target
overlap by that factor. -/
theorem computedDot_scaled {m : ℕ} (π σ : Fin m → ℚ) {lam γ : ℚ} (hlam : 0 ≤ lam) :
    computedDot (scaledSource π lam) σ (lam * γ) = lam * computedDot π σ γ := by
  unfold computedDot
  calc
    (∑ i, σ i * waterFill (scaledSource π lam) σ (lam * γ) i)
        = ∑ i, σ i * (lam * waterFill π σ γ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [waterFill_scaled π σ hlam i]
    _ = ∑ i, lam * (σ i * waterFill π σ γ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    _ = lam * ∑ i, σ i * waterFill π σ γ i := by
          rw [Finset.mul_sum]

/-- Scaling the source and water level by a positive factor preserves the fidelity-test
predicate. -/
theorem fidelityReaches_scaled {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) {lam γ : ℚ} (hlam : 0 < lam) :
    fidelityReaches (scaledSource π lam) σ p (lam * γ) ↔ fidelityReaches π σ p γ := by
  unfold fidelityReaches
  rw [computedDot_scaled π σ hlam.le, computedMass_scaled π σ hlam.le]
  have hlam2 : 0 < lam ^ 2 := sq_pos_of_pos hlam
  constructor
  · intro h
    have h1 : lam ^ 2 * computedDot π σ γ ^ 2 ≥ lam ^ 2 * (p * computedMass π σ γ) := by
      calc
        lam ^ 2 * computedDot π σ γ ^ 2 = (lam * computedDot π σ γ) ^ 2 := by ring
        _ ≥ p * (lam ^ 2 * computedMass π σ γ) := h
        _ = lam ^ 2 * (p * computedMass π σ γ) := by ring
    exact le_of_mul_le_mul_left h1 hlam2
  · intro h
    have h1 : lam ^ 2 * (p * computedMass π σ γ) ≤ lam ^ 2 * computedDot π σ γ ^ 2 :=
      mul_le_mul_of_nonneg_left h hlam2.le
    calc
      p * (lam ^ 2 * computedMass π σ γ) = lam ^ 2 * (p * computedMass π σ γ) := by ring
      _ ≤ lam ^ 2 * computedDot π σ γ ^ 2 := h1
      _ = (lam * computedDot π σ γ) ^ 2 := by ring

/-- Scaling the source and water level by a positive factor leaves the computed fidelity
unchanged. -/
theorem computedFidelity_scaled {m : ℕ} (π σ : Fin m → ℚ) {lam γ : ℚ} (hlam : 0 < lam) :
    computedFidelity (scaledSource π lam) σ (lam * γ) = computedFidelity π σ γ := by
  have hmass : computedMass (scaledSource π lam) σ (lam * γ) = lam ^ 2 * computedMass π σ γ :=
    computedMass_scaled π σ hlam.le
  have hdot : computedDot (scaledSource π lam) σ (lam * γ) = lam * computedDot π σ γ :=
    computedDot_scaled π σ hlam.le
  unfold computedFidelity
  rw [hmass, hdot]
  by_cases hz : computedMass π σ γ = 0
  · simp [hz]
  · have hlam2 : 0 < lam ^ 2 := sq_pos_of_pos hlam
    have hlam2ne : lam ^ 2 ≠ 0 := ne_of_gt hlam2
    have hne : lam ^ 2 * computedMass π σ γ ≠ 0 := mul_ne_zero hlam2ne hz
    rw [if_neg hne, if_neg hz]
    have heq : (lam * computedDot π σ γ) ^ 2 = lam ^ 2 * computedDot π σ γ ^ 2 := by ring
    rw [heq]
    field_simp

/-- A positive water level and a coordinate with positive source and target amplitudes imply
positive computed mass. -/
theorem computedMass_pos_of {m : ℕ} (π σ : Fin m → ℚ) {γ : ℚ} (j : Fin m)
    (hγ : 0 < γ) (hπ : 0 < π j) (hσ : 0 < σ j) :
    0 < computedMass π σ γ := by
  have hfill : 0 < waterFill π σ γ j := by
    unfold waterFill
    exact lt_min hπ (mul_pos hγ hσ)
  unfold computedMass computedWaterEnergy
  show 0 < ∑ i, (waterFill π σ γ i) ^ 2
  exact Finset.sum_pos' (f := fun i => (waterFill π σ γ i) ^ 2)
    (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, sq_pos_of_pos hfill⟩

/-- For nonnegative profiles, every rational fidelity bracket has a nonnegative lower endpoint
and a strictly positive upper endpoint. -/
theorem fidelityBracket_bounds {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) :
    0 ≤ (fidelityBracket π σ p k).1 ∧ 0 < (fidelityBracket π σ p k).2 := by
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · rfl
      · have h := computedWaterHigh_pos π σ hπ hσ
        simp only [fidelityBracket]
        linarith
  | succ k ih =>
      obtain ⟨hl, hh⟩ := ih
      dsimp only [fidelityBracket]
      split_ifs with hm
      · exact ⟨by linarith, hh⟩
      · exact ⟨hl, by linarith⟩

/-- For a nonnegative source with a positive coordinate and a strictly positive target, the
upper fidelity-bracket endpoint has positive computed mass. -/
theorem certifiedFidelity_mass_pos {m : ℕ} (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) (i : Fin m)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 < σ j) (hpi : 0 < π i) :
    0 < computedMass π σ (fidelityBracket π σ p k).2 := by
  have hhi := fidelityBracket_bounds π σ p k hπ (fun j => (hσ j).le)
  exact computedMass_pos_of π σ i hhi.2 hpi (hσ i)

/-- Scaling the source and water level by a nonnegative factor scales the selected amplitude
`selectedBeta` by that factor. -/
theorem selectedBeta_scaled {m : ℕ} (π σ : Fin m → ℚ) {lam γ : ℚ} (hlam : 0 ≤ lam) :
    selectedBeta (scaledSource π lam) σ (lam * γ) = lam * selectedBeta π σ γ := by
  unfold selectedBeta
  have hcast : (lam : ℝ) ^ 2 * ((computedMass π σ γ : ℚ) : ℝ)
      = ((lam ^ 2 * computedMass π σ γ : ℚ) : ℝ) := by
    push_cast
    ring
  have hlamR : (0 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
  rw [computedMass_scaled π σ hlam, ← hcast, Real.sqrt_mul (by positivity),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hlamR]

end Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch
