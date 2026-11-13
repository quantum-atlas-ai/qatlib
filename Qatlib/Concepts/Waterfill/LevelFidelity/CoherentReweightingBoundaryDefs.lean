/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweighting
import Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
import Qatlib.Concepts.NativeNumerics.WaterFilling
import Qatlib.Concepts.Waterfill.LevelSearch.WaterFillingOptimization
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Boundary conditions and error bounds for coherent reweighting

`ExtendedBracket` records tight water-level bounds with nonnegative profiles and compatible
supports. The module evaluates `realFill`, `realMass`, and `realDot` at boundary levels, proves
continuity and quantitative variation bounds, and defines query-bound predicates for the quantum
rejection-sampling setting of [OzolsRoettelerRoland2013].

## Main statements

* `realMass_bracketLow`: express the low-level mass using `realPmax`.
* `realMass_abs_le`: bound mass variation between nonnegative water levels.
* `CertifiedBracket`: record the endpoint tests and width of a rational search bracket.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.Waterfill.LevelFidelity

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped BigOperators ComplexOrder ENNReal

variable {m : ℕ}

/-- A nonnegative ordered bracket with nonnegative source and target profiles, compatible
supports, and tight lower and upper water-level conditions. -/
def ExtendedBracket (π σ : Fin m → ℝ) (γlo γhi : ℝ) : Prop :=
  0 ≤ γlo ∧ γlo ≤ γhi ∧
    (∀ i, 0 ≤ π i) ∧ (∀ i, 0 ≤ σ i) ∧
    (∀ i, σ i = 0 → π i = 0) ∧
    BracketLow π σ γlo ∧ BracketHigh π σ γhi ∧
    BracketLowTight π σ γlo ∧ BracketHighTight π σ γhi

/-- The filled profile has positive squared mass and squared target overlap equal to `p` times
that mass. -/
def RealizesFidelity (π σ : Fin m → ℝ) (p γ : ℝ) : Prop :=
  0 < realMass π σ γ ∧ realDot π σ γ ^ 2 = p * realMass π σ γ

/-- A zero target coordinate has zero filled amplitude when the source profile is nonnegative. -/
theorem realFill_zeroSigma {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) {γ : ℝ} (i : Fin m)
    (h : σ i = 0) : realFill π σ γ i = 0 := by
  rw [realFill, h, mul_zero, min_eq_right (hπ i)]

/-- A zero source coordinate has zero filled amplitude for a nonnegative target profile and
water level. -/
theorem realFill_sourceZero {π σ : Fin m → ℝ} (hσ : ∀ i, 0 ≤ σ i) {γ : ℝ} (hγ : 0 ≤ γ)
    (i : Fin m) (h : π i = 0) : realFill π σ γ i = 0 := by
  rw [realFill, h, min_eq_left (mul_nonneg hγ (hσ i))]

/-- A coordinate with zero target amplitude can be removed from the filled squared-mass sum when
the source profile is nonnegative. -/
theorem realMass_zeroSigma {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) {γ : ℝ} (i : Fin m)
    (h : σ i = 0) :
    realMass π σ γ = ∑ j ∈ Finset.univ.erase i, (realFill π σ γ j) ^ 2 := by
  have hfill : realFill π σ γ i = 0 := realFill_zeroSigma hπ i h
  have hsum := Finset.sum_erase_add Finset.univ (fun j : Fin m => (realFill π σ γ j) ^ 2)
    (Finset.mem_univ i)
  rw [realMass, ← hsum]
  have hfi : (fun j : Fin m => (realFill π σ γ j) ^ 2) i = 0 := by simp [hfill]
  simp [hfill]

/-- A coordinate with zero target amplitude can be removed from the target-overlap sum when the
source profile is nonnegative. -/
theorem realDot_zeroSigma {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) {γ : ℝ} (i : Fin m)
    (h : σ i = 0) :
    realDot π σ γ = ∑ j ∈ Finset.univ.erase i, σ j * realFill π σ γ j := by
  have hfill : realFill π σ γ i = 0 := realFill_zeroSigma hπ i h
  have hsum := Finset.sum_erase_add Finset.univ (fun j : Fin m => σ j * realFill π σ γ j)
    (Finset.mem_univ i)
  rw [realDot, ← hsum]
  have hfi : (fun j : Fin m => σ j * realFill π σ γ j) i = 0 := by simp [hfill]
  simp [hfill]

/-- At a lower bracket level, each positive source coordinate has filled amplitude `γ * σ i`. -/
theorem realFill_bracketLow {π σ : Fin m → ℝ} (_hπ : ∀ i, 0 ≤ π i) {γ : ℝ}
    (h : BracketLow π σ γ) (i : Fin m) (hi : 0 < π i) : realFill π σ γ i = γ * σ i := by
  rw [realFill, min_eq_right (h i hi)]

/-- At an upper bracket level, each positive target coordinate is saturated at the source
amplitude `π i`. -/
theorem realFill_bracketHigh {π σ : Fin m → ℝ} (_hπ : ∀ i, 0 ≤ π i) {γ : ℝ}
    (h : BracketHigh π σ γ) (i : Fin m) (hi : 0 < σ i) : realFill π σ γ i = π i := by
  rw [realFill, min_eq_left (h i hi)]

/-- At an upper bracket level, every coordinate equals its source amplitude for nonnegative
profiles with compatible supports. -/
theorem realFill_bracketHigh_all {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    (hs : ∀ i, σ i = 0 → π i = 0) {γ : ℝ} (h : BracketHigh π σ γ) (i : Fin m) :
    realFill π σ γ i = π i := by
  by_cases hsi : 0 < σ i
  · exact realFill_bracketHigh hπ h i hsi
  · have hz : σ i = 0 := le_antisymm (not_lt.mp hsi) (hσ i)
    have hpi : π i = 0 := hs i hz
    rw [realFill, hpi, hz, mul_zero, min_eq_right (le_refl 0)]

/-- Sum `g` over a finite type, replacing each term whose index fails `p` by zero. -/
private def condSum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (g : α → ℝ) : ℝ := ∑ i, (if p i then g i else 0 : ℝ)

/-- Conditional sums agree when their summands agree at every index satisfying the condition. -/
private theorem sum_congr_ite {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f g : α → ℝ) (h : ∀ i, p i → f i = g i) : condSum p f = condSum p g := by
  unfold condSum
  apply Finset.sum_congr rfl; intro i _
  by_cases hi : p i
  · rw [if_pos hi, if_pos hi, h i hi]
  · rw [if_neg hi, if_neg hi]

/-- Factor a constant left multiplier out of a finite real sum. -/
private theorem sum_mul_const {α : Type*} [Fintype α] (c : ℝ) (g : α → ℝ) :
    ∑ i, c * g i = c * ∑ i, g i :=
  (Finset.mul_sum Finset.univ g c).symm

/-- Factor a constant left multiplier out of a conditional finite real sum. -/
private theorem sum_if_mul_const {α : Type*} [Fintype α] (c : ℝ) (p : α → Prop)
    [DecidablePred p] (g : α → ℝ) :
    condSum p (fun i => c * g i) = c * condSum p g := by
  unfold condSum
  calc (∑ i, (if p i then c * g i else 0 : ℝ))
      = ∑ i, ((if p i then g i else 0 : ℝ) * c) := by
        apply Finset.sum_congr rfl; intro i _
        by_cases hi : p i
        · rw [if_pos hi, if_pos hi]; ring
        · rw [if_neg hi, if_neg hi]; ring
    _ = (∑ i, (if p i then g i else 0 : ℝ)) * c := (Finset.sum_mul Finset.univ _ c).symm
    _ = c * (∑ i, (if p i then g i else 0 : ℝ)) := mul_comm _ _

/-- For nonnegative profiles and a nonnegative lower bracket level, the filled mass equals `γ ^
2 * realPmax π σ`. -/
theorem realMass_bracketLow {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) (h : BracketLow π σ γ) :
    realMass π σ γ = γ ^ 2 * realPmax π σ := by
  have hpoint : ∀ i, 0 < π i → (realFill π σ γ i) ^ 2 = (γ * σ i) ^ 2 := by
    intro i hi
    rw [realFill_bracketLow hπ h i hi]
  have hzero : ∀ i, ¬ (0 < π i) → (realFill π σ γ i) ^ 2 = 0 := by
    intro i hi
    rw [realFill_sourceZero hσ hγ i (le_antisymm (not_lt.mp hi) (hπ i))]
    ring
  have hsum : (∑ i, (realFill π σ γ i) ^ 2)
      = condSum (fun i : Fin m => 0 < π i) (fun i => (realFill π σ γ i) ^ 2) := by
    unfold condSum
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : 0 < π i
    · rw [if_pos hi]
    · rw [if_neg hi, hzero i hi]
  have hstep : condSum (fun i : Fin m => 0 < π i) (fun i => (realFill π σ γ i) ^ 2)
      = condSum (fun i : Fin m => 0 < π i) (fun i => (γ * σ i) ^ 2) :=
    sum_congr_ite (fun i : Fin m => 0 < π i) (fun i => (realFill π σ γ i) ^ 2)
      (fun i => (γ * σ i) ^ 2) hpoint
  have hstep2 : condSum (fun i : Fin m => 0 < π i) (fun i => (γ * σ i) ^ 2)
      = condSum (fun i : Fin m => 0 < π i) (fun i => γ ^ 2 * (σ i ^ 2)) :=
    sum_congr_ite (fun i : Fin m => 0 < π i)
      (fun i => (γ * σ i) ^ 2) (fun i => γ ^ 2 * (σ i ^ 2)) (fun _ _ => by ring)
  have hstep3 : condSum (fun i : Fin m => 0 < π i) (fun i => γ ^ 2 * (σ i ^ 2))
      = γ ^ 2 * condSum (fun i : Fin m => 0 < π i) (fun i => σ i ^ 2) :=
    sum_if_mul_const (γ ^ 2) (fun i : Fin m => 0 < π i) (fun i => σ i ^ 2)
  rw [realMass, hsum, hstep, hstep2, hstep3]
  rfl

/-- For nonnegative profiles and a nonnegative lower bracket level, the target overlap equals `γ
* realPmax π σ`. -/
theorem realDot_bracketLow {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) (h : BracketLow π σ γ) :
    realDot π σ γ = γ * realPmax π σ := by
  have hpoint : ∀ i, 0 < π i → σ i * realFill π σ γ i = γ * (σ i ^ 2) := by
    intro i hi
    rw [realFill_bracketLow hπ h i hi]
    ring
  have hzero : ∀ i, ¬ (0 < π i) → σ i * realFill π σ γ i = 0 := by
    intro i hi
    rw [realFill_sourceZero hσ hγ i (le_antisymm (not_lt.mp hi) (hπ i))]
    ring
  have hsum : (∑ i, σ i * realFill π σ γ i)
      = condSum (fun i : Fin m => 0 < π i) (fun i => σ i * realFill π σ γ i) := by
    unfold condSum
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : 0 < π i
    · rw [if_pos hi]
    · rw [if_neg hi, hzero i hi]
  have hstep : condSum (fun i : Fin m => 0 < π i) (fun i => σ i * realFill π σ γ i)
      = condSum (fun i : Fin m => 0 < π i) (fun i => γ * (σ i ^ 2)) :=
    sum_congr_ite (fun i : Fin m => 0 < π i) (fun i => σ i * realFill π σ γ i)
      (fun i => γ * (σ i ^ 2)) hpoint
  have hstep2 : condSum (fun i : Fin m => 0 < π i) (fun i => γ * (σ i ^ 2))
      = γ * condSum (fun i : Fin m => 0 < π i) (fun i => σ i ^ 2) :=
    sum_if_mul_const γ (fun i : Fin m => 0 < π i) (fun i => σ i ^ 2)
  rw [realDot, hsum, hstep, hstep2]
  rfl

/-- The filled mass at an upper bracket level is one for a normalized nonnegative source and a
nonnegative target with compatible support. -/
theorem realMass_bracketHigh {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    (hs : ∀ i, σ i = 0 → π i = 0) {γ : ℝ} (h : BracketHigh π σ γ)
    (hπn : (∑ i, π i ^ 2) = 1) :
    realMass π σ γ = 1 := by
  have hstep : (∑ i, (realFill π σ γ i) ^ 2) = ∑ i, π i ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    rw [realFill_bracketHigh_all hπ hσ hs h i]
  rw [realMass, hstep, hπn]

/-- For nonnegative profiles with compatible supports, the target overlap at an upper bracket
level equals the source-target dot product. -/
theorem realDot_bracketHigh {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    (hs : ∀ i, σ i = 0 → π i = 0) {γ : ℝ} (h : BracketHigh π σ γ) :
    realDot π σ γ = ∑ i, π i * σ i := by
  have hstep : (∑ i, σ i * realFill π σ γ i) = ∑ i, π i * σ i := by
    apply Finset.sum_congr rfl; intro i _
    rw [realFill_bracketHigh_all hπ hσ hs h i]; ring
  rw [realDot, hstep]

/-- The rational search bracket is ordered inside the initial interval, has width
`computedWaterHigh π σ / 2 ^ k`, and passes the fidelity test only at its lower endpoint. -/
def CertifiedBracket (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ) : Prop :=
  let b := fidelityBracket π σ p k
  0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ computedWaterHigh π σ ∧
    b.2 - b.1 = computedWaterHigh π σ / 2 ^ k ∧
    fidelityReaches π σ p b.1 ∧ ¬ fidelityReaches π σ p b.2

/-- The squared target overlap of the real filled profile is at least `p` times its squared
mass. -/
def RealReaches (π σ : Fin m → ℝ) (p γ : ℝ) : Prop :=
  realDot π σ γ ^ 2 ≥ p * realMass π σ γ

/-- A record of real quantities named `targetNormSq` and `mixedMass` for water-level error
estimates. -/
structure LevelErrorConstants (π σ : Fin m → ℝ) where

  targetNormSq : ℝ

  mixedMass : ℝ

/-- Store the target squared norm and the source-target dot product as the water-level error
constants. -/
def levelErrorConstants (π σ : Fin m → ℝ) : LevelErrorConstants π σ :=
  { targetNormSq := ∑ i, σ i ^ 2, mixedMass := ∑ i, σ i * π i }

/-- Truncation from above by a fixed real number does not increase absolute differences. -/
private theorem min_abs_sub_le_abs (a x y : ℝ) : |min a x - min a y| ≤ |x - y| := by
  by_cases hx : a ≤ x
  · by_cases hy : a ≤ y
    · have hx1 : min a x = a := min_eq_left hx
      have hy1 : min a y = a := min_eq_left hy
      calc |min a x - min a y| = |a - a| := by rw [hx1, hy1]
        _ = 0 := by
          rw [abs_of_nonneg (show (0:ℝ) ≤ a - a by linarith), sub_self]
        _ ≤ |x - y| := abs_nonneg _
    · have hx1 : min a x = a := min_eq_left hx
      have hy1 : min a y = y := min_eq_right (le_of_not_ge hy)
      calc |min a x - min a y| = |a - y| := by rw [hx1, hy1]
        _ = a - y := by rw [abs_of_nonneg (show (0:ℝ) ≤ a - y by linarith)]
        _ ≤ x - y := by linarith
        _ = |x - y| := by rw [abs_of_nonneg (show (0:ℝ) ≤ x - y by linarith)]
  · by_cases hy : a ≤ y
    · have hx1 : min a x = x := min_eq_right (le_of_not_ge hx)
      have hy1 : min a y = a := min_eq_left hy
      calc |min a x - min a y| = |x - a| := by rw [hx1, hy1]
        _ = a - x := by
          rw [abs_of_nonpos (show (x - a:ℝ) ≤ 0 by linarith)]
          ring
        _ ≤ y - x := by linarith
        _ = |x - y| := by
          rw [abs_of_nonpos (show (x - y:ℝ) ≤ 0 by linarith)]
          ring
    · have hx1 : min a x = x := min_eq_right (le_of_not_ge hx)
      have hy1 : min a y = y := min_eq_right (le_of_not_ge hy)
      have heq : |min a x - min a y| = |x - y| := by rw [hx1, hy1]
      exact heq.le

/-- For a nonnegative target profile, changing the water level changes coordinate `i` by at most
`|a - b| * σ i`. -/
theorem realFill_abs_le {m : ℕ} (π σ : Fin m → ℝ) (hσ : ∀ i, 0 ≤ σ i) (a b : ℝ) (i : Fin m) :
    |realFill π σ a i - realFill π σ b i| ≤ |a - b| * σ i := by
  calc |realFill π σ a i - realFill π σ b i|
      = |min (π i) (a * σ i) - min (π i) (b * σ i)| := by rw [realFill, realFill]
    _ ≤ |a * σ i - b * σ i| := min_abs_sub_le_abs _ _ _
    _ = |a - b| * σ i := by
      rw [show a * σ i - b * σ i = (a - b) * σ i by ring, abs_mul, abs_of_nonneg (hσ i)]

/-- For a nonnegative target profile, the change in target overlap is bounded by the level
difference times the target squared norm. -/
theorem realDot_abs_le {π σ : Fin m → ℝ} (hσ : ∀ i, 0 ≤ σ i) {a b : ℝ} :
    |realDot π σ a - realDot π σ b| ≤ |a - b| * ∑ i, σ i ^ 2 := by
  have hterm : ∀ i, |σ i * realFill π σ a i - σ i * realFill π σ b i|
      ≤ |a - b| * σ i ^ 2 := by
    intro i
    have h := realFill_abs_le π σ hσ a b i
    calc |σ i * realFill π σ a i - σ i * realFill π σ b i|
        = σ i * |realFill π σ a i - realFill π σ b i| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (hσ i)]
      _ ≤ σ i * (|a - b| * σ i) := mul_le_mul_of_nonneg_left h (hσ i)
      _ = |a - b| * σ i ^ 2 := by ring
  rw [realDot, realDot, ← Finset.sum_sub_distrib]
  calc |∑ i, (σ i * realFill π σ a i - σ i * realFill π σ b i)|
      ≤ ∑ i, |σ i * realFill π σ a i - σ i * realFill π σ b i| := by
        exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ i, (|a - b| * σ i ^ 2) := by
        exact Finset.sum_le_sum fun i _ => hterm i
    _ = |a - b| * ∑ i, σ i ^ 2 := by rw [sum_mul_const]

/-- For nonnegative profiles and levels, the mass difference is at most twice the level
difference times the source-target dot product. -/
theorem realMass_abs_le {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |realMass π σ a - realMass π σ b| ≤ 2 * |a - b| * ∑ i, σ i * π i := by
  have hterm : ∀ i, |(realFill π σ a i) ^ 2 - (realFill π σ b i) ^ 2|
      ≤ 2 * |a - b| * σ i * π i := by
    intro i
    have hfill : 0 ≤ realFill π σ a i ∧ realFill π σ a i ≤ π i :=
      ⟨realFill_nonneg π σ hπ hσ ha i, min_le_left _ _⟩
    have hfillb : 0 ≤ realFill π σ b i ∧ realFill π σ b i ≤ π i :=
      ⟨realFill_nonneg π σ hπ hσ hb i, min_le_left _ _⟩
    have h := realFill_abs_le π σ hσ a b i
    have hsum : realFill π σ a i + realFill π σ b i ≤ 2 * π i := by linarith
    have hnonneg : 0 ≤ realFill π σ a i + realFill π σ b i := by linarith
    rw [show (realFill π σ a i) ^ 2 - (realFill π σ b i) ^ 2
        = (realFill π σ a i - realFill π σ b i) * (realFill π σ a i + realFill π σ b i) by
          ring, abs_mul, abs_of_nonneg hnonneg]
    calc |realFill π σ a i - realFill π σ b i| * (realFill π σ a i + realFill π σ b i)
        ≤ (|a - b| * σ i) * (realFill π σ a i + realFill π σ b i) :=
          mul_le_mul_of_nonneg_right h hnonneg
      _ ≤ (|a - b| * σ i) * (2 * π i) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (abs_nonneg _) (hσ i))
      _ = 2 * |a - b| * σ i * π i := by ring
  rw [realMass, realMass, ← Finset.sum_sub_distrib]
  calc |∑ i, ((realFill π σ a i) ^ 2 - (realFill π σ b i) ^ 2)|
      ≤ ∑ i, |(realFill π σ a i) ^ 2 - (realFill π σ b i) ^ 2| := by
        exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ i, (2 * |a - b| * σ i * π i) := by
        exact Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * |a - b| * ∑ i, σ i * π i := by
        rw [← sum_mul_const]
        apply Finset.sum_congr rfl; intro i _; ring

/-- Each coordinate of the real filled profile is continuous as a function of the water level. -/
theorem continuous_realFill {π σ : Fin m → ℝ} (i : Fin m) :
    Continuous (fun γ : ℝ => realFill π σ γ i) := by
  unfold realFill
  exact continuous_const.min (continuous_id.mul continuous_const)

/-- The squared mass of the real filled profile is continuous as a function of the water level. -/
theorem continuous_realMass {π σ : Fin m → ℝ} :
    Continuous (fun γ : ℝ => realMass π σ γ) := by
  have hsq : ∀ i, Continuous (fun γ : ℝ => (realFill π σ γ i) ^ 2) := by
    intro i
    exact (continuous_realFill (π := π) (σ := σ) i).pow 2
  unfold realMass
  exact continuous_finsetSum Finset.univ (fun i _ => hsq i)

/-- The target overlap of the real filled profile is continuous as a function of the water
level. -/
theorem continuous_realDot {π σ : Fin m → ℝ} :
    Continuous (fun γ : ℝ => realDot π σ γ) := by
  have hfill : ∀ i, Continuous (fun γ : ℝ => realFill π σ γ i) := by
    intro i
    exact continuous_realFill (π := π) (σ := σ) i
  have hmul : ∀ i, Continuous (fun γ : ℝ => σ i * realFill π σ γ i) := by
    intro i
    exact (continuous_const.mul (continuous_realFill (π := π) (σ := σ) i))
  unfold realDot
  exact continuous_finsetSum Finset.univ (fun i _ => hmul i)

/-- The upper real fidelity threshold `realPmax` is nonnegative. -/
theorem realPmax_nonneg {π σ : Fin m → ℝ} : 0 ≤ realPmax π σ := by
  unfold realPmax
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The lower real fidelity threshold `realPmin` is nonnegative. -/
theorem realPmin_nonneg {π σ : Fin m → ℝ} : 0 ≤ realPmin π σ := by
  unfold realPmin
  positivity

/-- For nonnegative profiles and water level, the filled squared mass is bounded by the source
squared norm. -/
theorem realMass_le_source {π σ : Fin m → ℝ} (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) : realMass π σ γ ≤ ∑ i, π i ^ 2 := by
  have hterm : ∀ i, (realFill π σ γ i) ^ 2 ≤ π i ^ 2 := by
    intro i
    have h1 : 0 ≤ realFill π σ γ i := realFill_nonneg π σ hπ hσ hγ i
    have h2 : realFill π σ γ i ≤ π i := min_le_left _ _
    nlinarith
  unfold realMass
  exact Finset.sum_le_sum fun i _ => hterm i

variable {D : ℕ}

/-- The hidden-state dimension `D` is at least two. -/
def HardFamily (D : ℕ) : Prop := 2 ≤ D

/-- Both dimensions are one and both rational profiles are constantly one. -/
def ZeroQueryInstance (m D : ℕ) (π σ : Fin m → ℚ) : Prop :=
  m = 1 ∧ D = 1 ∧ π = (fun _ => (1 : ℚ)) ∧ σ = (fun _ => (1 : ℚ))

/-- A positive constant `c` lower-bounds the prepared input-query count of every successful
reweighting word by `c / (2 * Real.sqrt (levelMass π σ γ))`. -/
def SourceQueryBound (π σ : Fin m → ℚ) (γ : ℝ) (p c : ℝ) : Prop :=
  0 < c ∧
    ∀ (j₀ : Fin m × Fin D) (W : List (PreparedStep ((Fin m × Fin D) × Bool))),
      ReweightingSuccess j₀ π σ γ p W →
      c / (2 * Real.sqrt (levelMass π σ γ)) ≤ (preparedInputQueries W : ℝ)

/-- The constant unit source profile on a single coordinate. -/
def easyPi : Fin 1 → ℚ := fun _ => 1

/-- The constant unit target profile on a single coordinate. -/
def easySig : Fin 1 → ℚ := fun _ => 1

end Qatlib.Concepts.Waterfill.LevelFidelity
