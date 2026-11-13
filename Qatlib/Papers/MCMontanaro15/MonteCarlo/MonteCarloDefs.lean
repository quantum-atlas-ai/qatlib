/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityStat

/-!
# Finite payoff sources and Monte Carlo parameters

This module defines finite payoff sources, draw records, centered payoff bands, and resource
records for the Monte Carlo analysis of [Montanaro2015]. The identity
`algorithm3_reconstruction` reconstructs the scaled expectation from the two centered bands.

It also provides a second-moment bound on `tailAbove`, a two-level probability law, pilot
variance bounds and certified group sizes, and exponential bounds comparing a partition function
with its zero-energy limit.

## Main statements

* `algorithm3_reconstruction`: Reconstruction of the scaled expectation from centered bands.
* `tailAbove_le_secondMoment_div`: A second-moment bound for the upper tail contribution.
* `partitionFn_sub_partitionFnLimit_le`: An exponential bound on the partition-function tail.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

set_option autoImplicit false

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo
namespace StageBMONTECARLO

open Qatlib
open scoped BigOperators

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A finite probability distribution together with a real-valued payoff on its sample space. -/
structure PayoffSource where

  law : FinDist X

  payoff : X → ℝ

/-- A record of n draws from `X`, represented by a function from `Fin n`. -/
abbrev DrawRecord (n : ℕ) (X : Type) := Fin n → X

/-- The empirical average of the payoff over a finite draw record. -/
noncomputable def recordMean {X : Type} [Fintype X] {n : ℕ} (f : X → ℝ) (ω : DrawRecord n X) : ℝ :=
  FinDist.avg f ω

/-- The payoff obtained by dividing each value of `f` by σ. -/
noncomputable def scaledPayoff (f : X → ℝ) (σ : ℝ) : X → ℝ := fun x => f x / σ

/-- The scaled payoff f/σ shifted by the real value m. -/
noncomputable def centeredPayoff (f : X → ℝ) (σ m : ℝ) : X → ℝ := fun x => f x / σ - m

/-- The negative part of a real value, retained with its original sign and set to zero
otherwise. -/
noncomputable def bandBelowZero (v : ℝ) : ℝ := if v < 0 then v else 0

/-- The nonnegative part of a real value, set to zero on negative inputs. -/
noncomputable def bandAtLeastZero (v : ℝ) : ℝ := if 0 ≤ v then v else 0

omit [DecidableEq X] in

/-- Expectation under a finite distribution is additive on real payoffs. -/
theorem expect_add (p : FinDist X) (f g : X → ℝ) :
    p.expect (f + g) = p.expect f + p.expect g := by
  simp only [FinDist.expect, Pi.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]

omit [DecidableEq X] in

/-- The expectation of a negated payoff is the negative of its expectation. -/
theorem expect_neg (p : FinDist X) (f : X → ℝ) :
    p.expect (fun x => -f x) = -p.expect f := by
  have e : ∀ x, p.prob x * (-f x) = -(p.prob x * f x) := fun x => by ring
  have hmain : (∑ x, p.prob x * (-f x)) = -(∑ x, p.prob x * f x) := by
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_neg_distrib]
  unfold FinDist.expect
  exact hmain

omit [DecidableEq X] in

/-- Subtracting a constant from a payoff subtracts the same constant from its expectation. -/
theorem expect_sub_const (p : FinDist X) (f : X → ℝ) (c : ℝ) :
    p.expect (fun x => f x - c) = p.expect f - c := by
  have h : (∑ x, p.prob x * c) = c := by
    rw [← Finset.sum_mul, p.sum_one, one_mul]
  have e : ∀ x, p.prob x * (f x - c) = p.prob x * f x - p.prob x * c := fun x => by ring
  have hmain : (∑ x, p.prob x * (f x - c)) = (∑ x, p.prob x * f x) - c := by
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib, h]
  unfold FinDist.expect
  exact hmain

omit [DecidableEq X] in

/-- Dividing a payoff by a real constant divides its expectation by that constant. -/
theorem expect_div_const (p : FinDist X) (f : X → ℝ) (c : ℝ) :
    p.expect (fun x => f x / c) = p.expect f / c := by
  have e : ∀ x, p.prob x * (f x / c) = (p.prob x * f x) / c := fun x => by ring
  have hmain : (∑ x, p.prob x * (f x / c)) = (∑ x, p.prob x * f x) / c := by
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div]
  unfold FinDist.expect
  exact hmain

/-- The negative and nonnegative bands sum to the original real value. -/
theorem bandBelowZero_add_bandAtLeastZero (v : ℝ) :
    bandBelowZero v + bandAtLeastZero v = v := by
  by_cases h : v < 0
  · have hnot : ¬ (0 ≤ v) := fun h2 => (not_lt_of_ge h2) h
    simp [bandBelowZero, bandAtLeastZero, h, hnot]
  · have hpos : 0 ≤ v := le_of_not_gt h
    simp [bandBelowZero, bandAtLeastZero, h, hpos]

/-- The center minus the expected negated negative band plus the expected nonnegative band
equals the scaled payoff expectation. -/
theorem algorithm3_reconstruction (p : FinDist X) (f : X → ℝ) (σ m : ℝ) :
    m - p.expect (fun i => -(bandBelowZero (centeredPayoff f σ m i)))
        + p.expect (fun i => bandAtLeastZero (centeredPayoff f σ m i))
      = p.expect (fun i => f i / σ) := by
  have hsum : p.expect (fun i => bandBelowZero (centeredPayoff f σ m i)
          + bandAtLeastZero (centeredPayoff f σ m i))
      = p.expect (fun i => bandBelowZero (centeredPayoff f σ m i))
        + p.expect (fun i => bandAtLeastZero (centeredPayoff f σ m i)) :=
    expect_add p _ _
  have hband : p.expect (fun i => bandBelowZero (centeredPayoff f σ m i)
      + bandAtLeastZero (centeredPayoff f σ m i))
      = p.expect (fun i => centeredPayoff f σ m i) := by
    congr 1
    funext i
    exact bandBelowZero_add_bandAtLeastZero (centeredPayoff f σ m i)
  have hneg : p.expect (fun i => -(bandBelowZero (centeredPayoff f σ m i)))
      = -p.expect (fun i => bandBelowZero (centeredPayoff f σ m i)) :=
    expect_neg p _
  have hcenter : p.expect (fun i => centeredPayoff f σ m i)
      = p.expect (fun i => f i / σ) - m := expect_sub_const p _ _
  linarith

omit [DecidableEq X] in

/-- The empirical mean of a one-draw record equals the payoff of its single entry. -/
theorem recordMean_one (f : X → ℝ) (ω : DrawRecord 1 X) : recordMean f ω = f (ω 0) := by
  unfold recordMean FinDist.avg
  rw [Fin.sum_univ_one]
  norm_num

/-- If a payoff has variance at most one, a single draw differs from its expectation by more
than three with probability at most 1/9. -/
theorem pilot_chebyshev_one (p : FinDist X) (g : X → ℝ) (hg : p.variance g ≤ 1) :
    p.probEvent (L := 1) (fun ω : DrawRecord 1 X => 3 < |g (ω 0) - p.expect g|) ≤ 1 / 9 := by
  have h := p.chebyshev_avg g (by norm_num : (0 : ℕ) < 1) 3 (by norm_num)
  have havg : ∀ ω : DrawRecord 1 X, FinDist.avg g ω = g (ω 0) := by
    intro ω
    exact recordMean_one g ω
  simp only [havg] at h
  calc
    p.probEvent (L := 1) (fun ω : DrawRecord 1 X => 3 < |g (ω 0) - p.expect g|)
        ≤ p.variance g / ((1 : ℕ) * 3 ^ 2) := h
    _ ≤ 1 / 9 := by
      have hone : ((1 : ℕ) : ℝ) * 3 ^ 2 = 9 := by norm_num
      rw [hone]
      exact div_le_div_of_nonneg_right hg (by norm_num)

/-- The expected payoff retained only on outcomes where f(x) ≥ m. -/
noncomputable def tailAbove (p : FinDist X) (f : X → ℝ) (m : ℝ) : ℝ :=
  p.expect (fun x => if m ≤ f x then f x else 0)

/-- For a nonnegative payoff and positive threshold m, its retained upper-tail expectation is at
most its second moment divided by m. -/
theorem tailAbove_le_secondMoment_div (p : FinDist X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (m : ℝ) (hm : 0 < m) :
    tailAbove p f m ≤ p.expect (fun x => f x ^ 2) / m := by
  have hpoint : ∀ x, (if m ≤ f x then f x else 0) ≤ f x ^ 2 / m := by
    intro x
    by_cases h : m ≤ f x
    · have hsq : f x * m ≤ f x ^ 2 := by
        have hmul' := mul_le_mul_of_nonneg_right h (hf x)
        simpa [mul_comm, pow_two] using hmul'
      have hcancel : f x * m / m = f x := by field_simp
      rw [ite_eq_left h]
      calc f x = f x * m / m := hcancel.symm
        _ ≤ f x ^ 2 / m := div_le_div_of_nonneg_right hsq hm.le
    · rw [ite_eq_right h]
      exact div_nonneg (sq_nonneg _) hm.le
  unfold tailAbove
  calc
    p.expect (fun x => if m ≤ f x then f x else 0)
        = ∑ x, p.prob x * (if m ≤ f x then f x else 0) := rfl
    _ ≤ ∑ x, p.prob x * (f x ^ 2 / m) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (p.nonneg x)
    _ = p.expect (fun x => f x ^ 2) / m := by
        rw [FinDist.expect]
        exact expect_div_const p (fun x => f x ^ 2) m

/-- The layer count, work per layer, accuracy, and failure parameters for a layered estimate. -/
structure LayerParameters where

  layers : ℕ

  perLayer : ℕ

  accuracy : ℝ

  failure : ℝ

/-- The scale, accuracy, failure parameter, and layer parameters associated with Algorithm 3. -/
structure Algorithm3Parameters where

  sigma : ℝ

  epsilon : ℝ

  failure : ℝ

  layers : LayerParameters

/-- Natural-number counts for copies, reflections, median operations, and classical bits. -/
structure CostLedger where

  copies : ℕ

  reflections : ℕ

  medians : ℕ

  classicalBits : ℕ

/-- The cost ledger obtained by multiplying every count by the number of repetitions. -/
def CostLedger.replicate (c : CostLedger) (n : ℕ) : CostLedger :=
  { copies := c.copies * n
    reflections := c.reflections * n
    medians := c.medians * n
    classicalBits := c.classicalBits * n }

/-- A fixed draw count and a real-valued output function of that many natural-number
observations. -/
structure OpaqueSampler where

  draws : ℕ

  run : (Fin draws → ℕ) → ℝ

/-- The distinguished value N + 1 in `Fin (N + 2)`. -/
def twoLevelLarge (N : ℕ) : Fin (N + 2) := ⟨N + 1, by omega⟩

/-- The finite probability law assigning mass 1 − p to zero and mass p to N + 1, for 0 ≤ p ≤ 1. -/
noncomputable def twoLevelLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    FinDist (Fin (N + 2)) where
  prob x := (if x = 0 then 1 - p else 0) + (if x = twoLevelLarge N then p else 0)
  nonneg x := by
    by_cases h0 : x = 0
    · by_cases h1 : x = twoLevelLarge N
      · rw [ite_eq_left h0, ite_eq_left h1]
        linarith
      · rw [ite_eq_left h0, ite_eq_right h1]
        linarith
    · by_cases h1 : x = twoLevelLarge N
      · rw [ite_eq_right h0, ite_eq_left h1]
        linarith
      · rw [ite_eq_right h0, ite_eq_right h1]
        norm_num
  sum_one := by
    have h1 : (∑ x : Fin (N + 2), (if x = 0 then 1 - p else 0)) = 1 - p :=
      Fintype.sum_ite_eq' (0 : Fin (N + 2)) (fun _ => 1 - p)
    have h2 : (∑ x : Fin (N + 2), (if x = twoLevelLarge N then p else 0)) = p :=
      Fintype.sum_ite_eq' (twoLevelLarge N) (fun _ => p)
    rw [Finset.sum_add_distrib, h1, h2]
    ring

/-- The empirical average of the squared payoff over a pilot draw record. -/
noncomputable def pilotSecondMoment {n : ℕ} (f : X → ℝ) (ω : DrawRecord n X) : ℝ :=
  FinDist.avg (fun x => f x ^ 2) ω

/-- The empirical pilot second moment plus the tolerance t. -/
noncomputable def pilotVarianceBound {n : ℕ} (f : X → ℝ) (t : ℝ)
    (ω : DrawRecord n X) : ℝ :=
  pilotSecondMoment f ω + t

/-- The natural ceiling of four times the pilot variance bound divided by ε². -/
noncomputable def certifiedSamplesPerGroup {n : ℕ} (f : X → ℝ) (t ε : ℝ)
    (ω : DrawRecord n X) : ℕ :=
  Nat.ceil (4 * pilotVarianceBound f t ω / ε ^ 2)

/-- The number of zero-energy configurations, expressed as a real finite sum. -/
noncomputable def partitionFnLimit {Ω : Type} [Fintype Ω] (H : Ω → ℕ) : ℝ :=
  ∑ x : Ω, if H x = 0 then 1 else 0

/-- The zero-energy partition limit is at most the partition function at every real
inverse-temperature parameter. -/
theorem partitionFnLimit_le_partitionFn {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β : ℝ) :
    partitionFnLimit H ≤ partitionFn H β := by
  have hpoint : ∀ x : Ω, (if H x = 0 then 1 else 0) ≤ Real.exp (-(β * (H x : ℝ))) := by
    intro x
    by_cases h : H x = 0
    · rw [ite_eq_left h]
      have hz : (H x : ℝ) = 0 := by exact_mod_cast h
      rw [hz, mul_zero, neg_zero, Real.exp_zero]
    · rw [ite_eq_right h]
      exact (Real.exp_pos _).le
  unfold partitionFnLimit partitionFn
  exact Finset.sum_le_sum fun x _ => hpoint x

/-- For β ≥ 0, the partition function minus its zero-energy limit lies between zero and the
number of configurations times exp(−β). -/
theorem partitionFn_sub_partitionFnLimit_le {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β : ℝ)
    (hβ : 0 ≤ β) :
    0 ≤ partitionFn H β - partitionFnLimit H ∧
      partitionFn H β - partitionFnLimit H ≤ (Fintype.card Ω : ℝ) * Real.exp (-β) := by
  have hpoint : ∀ x : Ω,
      0 ≤ Real.exp (-(β * (H x : ℝ))) - (if H x = 0 then 1 else 0) ∧
      Real.exp (-(β * (H x : ℝ))) - (if H x = 0 then 1 else 0) ≤ Real.exp (-β) := by
    intro x
    by_cases h : H x = 0
    · rw [ite_eq_left h]
      have hz : (H x : ℝ) = 0 := by exact_mod_cast h
      rw [hz, mul_zero, neg_zero, Real.exp_zero]
      constructor
      · linarith
      · have : 0 < Real.exp (-β) := Real.exp_pos (-β)
        linarith
    · have hpos : 1 ≤ (H x : ℝ) := by
        have hn : (0 : ℕ) < H x := by omega
        exact_mod_cast hn
      rw [ite_eq_right h]
      constructor
      · have : 0 < Real.exp (-(β * (H x : ℝ))) := Real.exp_pos _
        linarith
      · have hkey : -(β * (H x : ℝ)) ≤ -β := by
          have hmul := mul_le_mul_of_nonneg_left hpos hβ
          linarith
        have hexp := (Real.exp_le_exp).2 hkey
        linarith
  have hsub : (∑ x : Ω, (Real.exp (-(β * (H x : ℝ))) - (if H x = 0 then 1 else 0)))
      = (∑ x : Ω, Real.exp (-(β * (H x : ℝ))))
        - (∑ x : Ω, (if H x = 0 then 1 else 0)) := by
          rw [Finset.sum_sub_distrib]
  have hlow : 0 ≤ ∑ x : Ω, (Real.exp (-(β * (H x : ℝ))) - (if H x = 0 then 1 else 0)) :=
    Finset.sum_nonneg fun x _ => (hpoint x).1
  have hupp : (∑ x : Ω, (Real.exp (-(β * (H x : ℝ))) - (if H x = 0 then 1 else 0)))
      ≤ ∑ _x : Ω, Real.exp (-β) :=
    Finset.sum_le_sum fun x _ => (hpoint x).2
  have hcard : (∑ _x : Ω, Real.exp (-β)) = (Fintype.card Ω : ℝ) * Real.exp (-β) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  constructor
  · unfold partitionFn partitionFnLimit
    rw [← hsub]
    exact hlow
  · unfold partitionFn partitionFnLimit
    rw [← hsub]
    linarith

end StageBMONTECARLO
end Qatlib.Papers.MCMontanaro15.MonteCarlo
