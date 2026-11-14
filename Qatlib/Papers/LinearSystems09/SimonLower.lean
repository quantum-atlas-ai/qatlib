/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Max
public import Mathlib.Order.Nat
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Simon collision bounds for linear-system reductions

This module analyzes the Simon-reduction runtime and the collision counting underlying the
lower-bound argument in [HarrowHassidimLloyd2009]. The set `hitPeriods` records periods
exhibited by distinct queried points, and its cardinality bounds imply a square-root query
threshold and conditional constraints on runtime exponents.

## Main statements

* `simon_birthday_sqrt`: Extracts a square-root lower bound from the collision inequality.
* `source_theorem5_simon_lower_bound_const`: Derives an exponent constraint from an eventual
  birthday bound with a positive constant.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.SimonLower

open Filter
open scoped Real Topology

/-- The Simon-reduction instance-size model `36 * n * 2^(3 * n)`. -/
noncomputable def simonInstanceSize (n : ℕ) : ℝ := 36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ))

/-- The Simon-reduction condition-number parameter `4 * n`. -/
noncomputable def simonConditionNumber (n : ℕ) : ℝ := 4 * (n : ℝ)

/-- The Simon-reduction runtime model `simonInstanceSize n ^ α * 2 ^ (β * simonConditionNumber
n)`. -/
noncomputable def simonReductionRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n)

/-- For positive `n`, the logarithm of the Simon runtime is `α * log (36 * n) + (3 * α + 4 * β)
* n * log 2` [HarrowHassidimLloyd2009]. -/
theorem clause11_simon_runtime_exponent (α β : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.log (simonReductionRuntime α β n)
      = α * Real.log (36 * (n : ℝ)) + (3 * α + 4 * β) * (n : ℝ) * Real.log 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne36 : 36 * (n : ℝ) ≠ 0 := by positivity
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hinst : (0 : ℝ) < simonInstanceSize n := by
    unfold simonInstanceSize
    positivity
  have hlogsize : Real.log (simonInstanceSize n)
      = Real.log (36 * (n : ℝ)) + 3 * (n : ℝ) * Real.log 2 := by
    have h1 : Real.log (36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ)))
        = Real.log (36 * (n : ℝ)) + Real.log ((2 : ℝ) ^ (3 * (n : ℝ))) :=
      Real.log_mul hne36 (by positivity)
    have h2 : Real.log ((2 : ℝ) ^ (3 * (n : ℝ))) = 3 * (n : ℝ) * Real.log 2 :=
      Real.log_rpow h2pos _
    show Real.log (36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ)))
      = Real.log (36 * (n : ℝ)) + 3 * (n : ℝ) * Real.log 2
    rw [h1, h2]
  have hlogpow : Real.log (simonInstanceSize n ^ α) = α * Real.log (simonInstanceSize n) :=
    Real.log_rpow hinst α
  have hlogtwo : Real.log ((2 : ℝ) ^ (β * simonConditionNumber n))
      = β * simonConditionNumber n * Real.log 2 := Real.log_rpow h2pos _
  have hmul : Real.log (simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n))
      = Real.log (simonInstanceSize n ^ α)
        + Real.log ((2 : ℝ) ^ (β * simonConditionNumber n)) :=
    Real.log_mul (by positivity) (by positivity)
  calc
    Real.log (simonReductionRuntime α β n)
      = Real.log (simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n)) := rfl
    _ = Real.log (simonInstanceSize n ^ α)
        + Real.log ((2 : ℝ) ^ (β * simonConditionNumber n)) := hmul
    _ = (α * Real.log (simonInstanceSize n))
        + (β * simonConditionNumber n * Real.log 2) := by rw [hlogpow, hlogtwo]
    _ = α * Real.log (36 * (n : ℝ)) + (3 * α + 4 * β) * (n : ℝ) * Real.log 2 := by
      rw [hlogsize]
      simp only [simonConditionNumber]
      ring

/-- An eventual lower bound `2^(n / 2)` on the Simon-reduction runtime implies `3 * α + 4 * β ≥
1 / 2`, as in Theorem 5 of [HarrowHassidimLloyd2009]. -/
theorem source_theorem5_simon_lower_bound (α β : ℝ)
    (hbirthday : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ ((n : ℝ) / 2) ≤ simonReductionRuntime α β n) :
    3 * α + 4 * β ≥ 1 / 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

  have hlog : ∀ n : ℕ, 0 < n →
      Real.log (simonReductionRuntime α β n)
        = α * Real.log (36 * (n : ℝ)) + (3 * α + 4 * β) * (n : ℝ) * Real.log 2 :=
    fun n hn => clause11_simon_runtime_exponent α β n hn

  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      1 / 2 - α * (Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2)) ≤
        3 * α + 4 * β := by
    filter_upwards [hbirthday, Filter.eventually_gt_atTop 0] with n hb hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlogineq : (n : ℝ) / 2 * Real.log 2 ≤ Real.log (simonReductionRuntime α β n) := by
      have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos h2pos _
      calc
        (n : ℝ) / 2 * Real.log 2 = Real.log ((2 : ℝ) ^ ((n : ℝ) / 2)) := by
          rw [Real.log_rpow h2pos]
        _ ≤ Real.log (simonReductionRuntime α β n) := Real.log_le_log hpowpos hb
    have hlg := hlog n hn
    have hDpos : 0 < (n : ℝ) * Real.log 2 := by positivity
    have key : (1 / 2 - α * (Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2))) *
          ((n : ℝ) * Real.log 2)
        = (n : ℝ) / 2 * Real.log 2 - α * Real.log (36 * (n : ℝ)) := by
      field_simp
    have hle : (n : ℝ) / 2 * Real.log 2 - α * Real.log (36 * (n : ℝ))
        ≤ (3 * α + 4 * β) * ((n : ℝ) * Real.log 2) := by
      nlinarith [hlogineq, hlg]
    exact le_of_mul_le_mul_right (by rw [key]; exact hle) hDpos

  have hlogn : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).tendsto_div_nhds_zero
    simpa using! h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst : Filter.Tendsto (fun n : ℕ => Real.log 36 / (n : ℝ))
      Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 36)
  have hlog36n : Filter.Tendsto (fun n : ℕ => Real.log (36 * (n : ℝ)) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have hsum : Filter.Tendsto
        (fun n : ℕ => Real.log 36 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 (0 + 0)) := hconst.add hlogn
    have hcongr : (fun n : ℕ => Real.log 36 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ))
        =ᶠ[Filter.atTop] (fun n : ℕ => Real.log (36 * (n : ℝ)) / (n : ℝ)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h36 : (36 : ℝ) ≠ 0 := by norm_num
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      rw [Real.log_mul h36 hne]
      ring
    have := hsum.congr' hcongr
    simpa using this
  have hdiv : Filter.Tendsto
      (fun n : ℕ => Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2))
      Filter.atTop (𝓝 0) := by
    have h := hlog36n.div_const (Real.log 2)
    have hcongr : (fun n : ℕ => Real.log (36 * (n : ℝ)) / (n : ℝ) / Real.log 2)
        =ᶠ[Filter.atTop]
          (fun n : ℕ => Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
      field_simp
    have h0 := h.congr' hcongr
    simpa using h0
  have hlim : Filter.Tendsto
      (fun n : ℕ => 1 / 2 - α * (Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2)))
      Filter.atTop (𝓝 (1 / 2 - α * 0)) :=
    tendsto_const_nhds.sub (hdiv.const_mul α)
  have := le_of_tendsto hlim hev
  simpa using this

/-- The positive-definite runtime model with the square root of the condition-number parameter
in the exponential factor. -/
noncomputable def simonPositiveDefiniteRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α *
    (2 : ℝ) ^ (β * Real.sqrt (simonConditionNumber n))

/-- For positive `n`, the positive-definite runtime has logarithm `α * log (36 * n) + 3 * α * n
* log 2 + 2 * β * sqrt n * log 2` [HarrowHassidimLloyd2009]. -/
theorem source_theorem5_positive_definite_exponent (α β : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.log (simonPositiveDefiniteRuntime α β n)
      = α * Real.log (36 * (n : ℝ)) + 3 * α * (n : ℝ) * Real.log 2 +
        2 * β * Real.sqrt (n : ℝ) * Real.log 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne36 : 36 * (n : ℝ) ≠ 0 := by positivity
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hinst : (0 : ℝ) < simonInstanceSize n := by
    unfold simonInstanceSize
    positivity
  have hsqrt : Real.sqrt (simonConditionNumber n) = 2 * Real.sqrt (n : ℝ) := by
    unfold simonConditionNumber
    have h4 : Real.sqrt (4 * (n : ℝ)) = Real.sqrt 4 * Real.sqrt (n : ℝ) :=
      Real.sqrt_mul (by norm_num) _
    have h2 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4, h2]
  have hlogsize : Real.log (simonInstanceSize n)
      = Real.log (36 * (n : ℝ)) + 3 * (n : ℝ) * Real.log 2 := by
    have h1 : Real.log (36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ)))
        = Real.log (36 * (n : ℝ)) + Real.log ((2 : ℝ) ^ (3 * (n : ℝ))) :=
      Real.log_mul hne36 (by positivity)
    have h2 : Real.log ((2 : ℝ) ^ (3 * (n : ℝ))) = 3 * (n : ℝ) * Real.log 2 :=
      Real.log_rpow h2pos _
    show Real.log (36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ)))
      = Real.log (36 * (n : ℝ)) + 3 * (n : ℝ) * Real.log 2
    rw [h1, h2]
  have hlogpow : Real.log (simonInstanceSize n ^ α) = α * Real.log (simonInstanceSize n) :=
    Real.log_rpow hinst α
  have hlogtwo : Real.log ((2 : ℝ) ^ (β * Real.sqrt (simonConditionNumber n)))
      = β * Real.sqrt (simonConditionNumber n) * Real.log 2 := Real.log_rpow h2pos _
  have hmul : Real.log (simonPositiveDefiniteRuntime α β n)
      = Real.log (simonInstanceSize n ^ α)
        + Real.log ((2 : ℝ) ^ (β * Real.sqrt (simonConditionNumber n))) := by
    unfold simonPositiveDefiniteRuntime
    exact Real.log_mul (by positivity) (by positivity)
  calc
    Real.log (simonPositiveDefiniteRuntime α β n)
      = α * Real.log (simonInstanceSize n)
          + β * Real.sqrt (simonConditionNumber n) * Real.log 2 := by
        rw [hmul, hlogpow, hlogtwo]
    _ = α * Real.log (36 * (n : ℝ)) + 3 * α * (n : ℝ) * Real.log 2 +
        2 * β * Real.sqrt (n : ℝ) * Real.log 2 := by
      rw [hlogsize, hsqrt]
      ring

/-- The finite set of binary periods obtained as sums of distinct points in `S`
[HarrowHassidimLloyd2009]. -/
def hitPeriods {n : ℕ} (S : Finset (Fin n → ZMod 2)) : Finset (Fin n → ZMod 2) :=
  S.offDiag.image (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) => p.1 + p.2)

/-- A period belongs to `hitPeriods S` exactly when it is the sum of a pair in `S.offDiag`. -/
theorem exhibits_iff_mem {n : ℕ} (S : Finset (Fin n → ZMod 2)) (s : Fin n → ZMod 2) :
    (∃ p ∈ S.offDiag, p.1 + p.2 = s) ↔ s ∈ hitPeriods S := by
  simp [hitPeriods]

/-- The number of exhibited periods is at most the number `S.card * S.card - S.card` of ordered
distinct pairs. -/
theorem card_hitPeriods_le_offDiag {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    (hitPeriods S).card ≤ S.card * S.card - S.card := by
  calc (hitPeriods S).card
      = (S.offDiag.image
          (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) => p.1 + p.2)).card := rfl
    _ ≤ S.offDiag.card := Finset.card_image_le
    _ = S.card * S.card - S.card := Finset.offDiag_card S

/-- The number of exhibited periods is at most `S.card * (S.card - 1)`
[HarrowHassidimLloyd2009]. -/
theorem card_hitPeriods_le {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    (hitPeriods S).card ≤ S.card * (S.card - 1) := by
  have h : S.card * (S.card - 1) = S.card * S.card - S.card := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [h]
  exact card_hitPeriods_le_offDiag S

/-- The zero binary vector is not exhibited by any pair of distinct points
[HarrowHassidimLloyd2009]. -/
theorem zero_not_mem_hitPeriods {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    (0 : Fin n → ZMod 2) ∉ hitPeriods S := by
  intro h
  simp only [hitPeriods, Finset.mem_image, Finset.mem_offDiag] at h
  obtain ⟨p, ⟨-, -, hpne⟩, hsum⟩ := h
  apply hpne
  have hneg : p.1 = -p.2 := add_eq_zero_iff_eq_neg.mp hsum
  have hneg2 : -p.2 = p.2 := by
    funext i
    exact CharTwo.neg_eq (p.2 i)
  rw [hneg, hneg2]

/-- There are `2^n - 1` nonzero binary vectors of length `n`. -/
theorem card_nonzero_periods (n : ℕ) :
    (Finset.univ.erase (0 : Fin n → ZMod 2)).card = 2 ^ n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [ ZMod.card]

/-- The number of periods exhibited by `S` is at most `2^n - 1` [HarrowHassidimLloyd2009]. -/
theorem card_hitPeriods_le_nonzero {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    (hitPeriods S).card ≤ 2 ^ n - 1 := by
  have hsub : hitPeriods S ⊆ Finset.univ.erase (0 : Fin n → ZMod 2) := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h0
    exact zero_not_mem_hitPeriods S (h0 ▸ hx)
  calc (hitPeriods S).card ≤ (Finset.univ.erase (0 : Fin n → ZMod 2)).card :=
        Finset.card_le_card hsub
    _ = 2 ^ n - 1 := card_nonzero_periods n

/-- If three times the ordered-pair count is at most the number of nonzero periods, then the
exhibited fraction is at most one third [HarrowHassidimLloyd2009]. -/
theorem simon_birthday_fraction {n : ℕ} (hn : 1 ≤ n) (S : Finset (Fin n → ZMod 2))
    (hsmall : 3 * ((S.card : ℝ) * ((S.card : ℝ) - 1)) ≤ (2 : ℝ) ^ n - 1) :
    ((hitPeriods S).card : ℝ) / ((2 : ℝ) ^ n - 1) ≤ 1 / 3 := by
  have hRn : (1 : ℝ) < (2 : ℝ) ^ n := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
      _ < (2 : ℝ) ^ n := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hden : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by linarith
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have hSe : S = ∅ := Finset.card_eq_zero.mp h0
    have hempty : hitPeriods S = ∅ := by simp [hitPeriods, hSe]
    simp [hempty]
  · have hcardN : ((hitPeriods S).card : ℝ) ≤ (S.card : ℝ) * ((S.card : ℝ) - 1) := by
      have h := card_hitPeriods_le S
      have hcast : ((S.card * (S.card - 1) : ℕ) : ℝ) =
          (S.card : ℝ) * ((S.card : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]
      calc ((hitPeriods S).card : ℝ) ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) := by
              exact_mod_cast h
        _ = (S.card : ℝ) * ((S.card : ℝ) - 1) := hcast
    have h3 : ((hitPeriods S).card : ℝ) * 3 ≤ (2 : ℝ) ^ n - 1 := by
      nlinarith [hcardN, hsmall]
    rw [div_le_iff₀ hden]
    nlinarith

/-- If `S` contains at most `q` points and the stated birthday inequality holds for `q`, the
fraction of exhibited nonzero periods is at most one third [HarrowHassidimLloyd2009]. -/
theorem simon_birthday_query_bound {n : ℕ} (hn : 1 ≤ n) {q : ℕ} (hq : 1 ≤ q)
    (hsmall : 3 * ((q : ℝ) * ((q : ℝ) - 1)) ≤ (2 : ℝ) ^ n - 1)
    (S : Finset (Fin n → ZMod 2)) (hS : S.card ≤ q) :
    ((hitPeriods S).card : ℝ) / ((2 : ℝ) ^ n - 1) ≤ 1 / 3 := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have hSe : S = ∅ := Finset.card_eq_zero.mp h0
    have hempty : hitPeriods S = ∅ := by simp [hitPeriods, hSe]
    simp [hempty]
  · have hcq : (S.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast hS
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hc1 : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hpos
    have hmono : (S.card : ℝ) * ((S.card : ℝ) - 1) ≤ (q : ℝ) * ((q : ℝ) - 1) :=
      mul_le_mul hcq (by linarith) (by linarith) (by linarith)
    exact simon_birthday_fraction hn S (by linarith)

/-- Exhibiting more than one third of nonzero periods using at most `q` queried points forces
`2^n - 1 < 3 * q * (q - 1)` [HarrowHassidimLloyd2009]. -/
theorem simon_birthday_query_lower {n : ℕ} (hn : 1 ≤ n) {q : ℕ} (hq : 1 ≤ q)
    (S : Finset (Fin n → ZMod 2)) (hS : S.card ≤ q)
    (hfrac : 1 / 3 < ((hitPeriods S).card : ℝ) / ((2 : ℝ) ^ n - 1)) :
    (2 : ℝ) ^ n - 1 < 3 * ((q : ℝ) * ((q : ℝ) - 1)) := by
  by_contra hle
  push Not at hle
  exact absurd (simon_birthday_query_bound hn hq hle S hS) (not_le.mpr hfrac)

/-- The strict birthday inequality forces `q > 2^(n / 2) / 3` for `n ≥ 1`
[HarrowHassidimLloyd2009]. -/
theorem simon_birthday_sqrt {n : ℕ} (hn : 1 ≤ n) {q : ℕ}
    (h : (2 : ℝ) ^ n - 1 < 3 * ((q : ℝ) * ((q : ℝ) - 1))) :
    (1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2) < (q : ℝ) := by
  have h2n : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hhalf : (2 : ℝ) ^ n / 2 ≤ (2 : ℝ) ^ n - 1 := by nlinarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    rcases Nat.eq_zero_or_pos q with hq0 | hqp
    · exfalso
      have hq0' : (q : ℝ) = 0 := by exact_mod_cast hq0
      rw [hq0'] at h
      nlinarith [hhalf, h]
    · exact_mod_cast hqp
  have hsq : (q : ℝ) * ((q : ℝ) - 1) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hq2big : (2 : ℝ) ^ n / 6 < (q : ℝ) ^ 2 := by nlinarith
  have ha2 : ((1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ n / 9 := by
    have hsqr : ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ n := by
      rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast]
      congr 1

      ring
    rw [mul_pow, hsqr]
    ring
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hlt : ((1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 < (q : ℝ) ^ 2 := by
    rw [ha2]
    nlinarith [hq2big, hpowpos]
  have hapos : (0 : ℝ) < (1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2) := by positivity
  have hqa : (0 : ℝ) < (q : ℝ) + (1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2) := by nlinarith
  have hprod : (0 : ℝ) <
      ((q : ℝ) - (1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2)) *
        ((q : ℝ) + (1 / 3) * (2 : ℝ) ^ ((n : ℝ) / 2)) := by
    nlinarith
  exact sub_pos.mp (pos_of_mul_pos_left hprod (le_of_lt hqa))

/-- An eventual lower bound `c * 2^(n / 2)` with positive `c` on the Simon runtime implies `3 *
α + 4 * β ≥ 1 / 2`, as used in Theorem 5 of [HarrowHassidimLloyd2009]. -/
theorem source_theorem5_simon_lower_bound_const (α β : ℝ) (c : ℝ) (hc : 0 < c)
    (hbirthday : ∀ᶠ n : ℕ in Filter.atTop,
      c * (2 : ℝ) ^ ((n : ℝ) / 2) ≤ simonReductionRuntime α β n) :
    3 * α + 4 * β ≥ 1 / 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      1 / 2 - α * (Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2))
        + Real.log c / ((n : ℝ) * Real.log 2) ≤ 3 * α + 4 * β := by
    filter_upwards [hbirthday, Filter.eventually_gt_atTop 0] with n hb hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlogineq : Real.log (c * (2 : ℝ) ^ ((n : ℝ) / 2)) ≤
        Real.log (simonReductionRuntime α β n) := by
      apply Real.log_le_log
      · positivity
      · exact hb
    have hsplit : Real.log (c * (2 : ℝ) ^ ((n : ℝ) / 2))
        = Real.log c + (n : ℝ) / 2 * Real.log 2 := by
      rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    have hlg := clause11_simon_runtime_exponent α β n hn
    have hDpos : 0 < (n : ℝ) * Real.log 2 := by positivity
    have key : (1 / 2 - α * (Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2))
          + Real.log c / ((n : ℝ) * Real.log 2)) * ((n : ℝ) * Real.log 2)
        = (n : ℝ) / 2 * Real.log 2 + Real.log c - α * Real.log (36 * (n : ℝ)) := by
      field_simp
      ring
    have hle : (n : ℝ) / 2 * Real.log 2 + Real.log c - α * Real.log (36 * (n : ℝ))
        ≤ (3 * α + 4 * β) * ((n : ℝ) * Real.log 2) := by
      nlinarith [hlogineq, hsplit, hlg]
    exact le_of_mul_le_mul_right (by rw [key]; exact hle) hDpos
  have hlogn : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).tendsto_div_nhds_zero
    simpa using! h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst : Filter.Tendsto (fun n : ℕ => Real.log 36 / (n : ℝ))
      Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 36)
  have hlog36n : Filter.Tendsto (fun n : ℕ => Real.log (36 * (n : ℝ)) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have hsum : Filter.Tendsto
        (fun n : ℕ => Real.log 36 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 (0 + 0)) := hconst.add hlogn
    have hcongr : (fun n : ℕ => Real.log 36 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ))
        =ᶠ[Filter.atTop] (fun n : ℕ => Real.log (36 * (n : ℝ)) / (n : ℝ)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h36 : (36 : ℝ) ≠ 0 := by norm_num
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      rw [Real.log_mul h36 hne]
      ring
    have := hsum.congr' hcongr
    simpa using this
  have hdiv : Filter.Tendsto
      (fun n : ℕ => Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2))
      Filter.atTop (𝓝 0) := by
    have h := hlog36n.div_const (Real.log 2)
    have hcongr : (fun n : ℕ => Real.log (36 * (n : ℝ)) / (n : ℝ) / Real.log 2)
        =ᶠ[Filter.atTop]
          (fun n : ℕ => Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
      field_simp
    have h0 := h.congr' hcongr
    simpa using h0
  have hdivc : Filter.Tendsto
      (fun n : ℕ => Real.log c / ((n : ℝ) * Real.log 2))
      Filter.atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (Real.log c / Real.log 2)
    have hcongr : (fun n : ℕ => Real.log c / Real.log 2 / (n : ℝ))
        =ᶠ[Filter.atTop] (fun n : ℕ => Real.log c / ((n : ℝ) * Real.log 2)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
      field_simp
    have h0 := h.congr' hcongr
    simpa using h0
  have hlim : Filter.Tendsto
      (fun n : ℕ => 1 / 2 - α * (Real.log (36 * (n : ℝ)) / ((n : ℝ) * Real.log 2))
        + Real.log c / ((n : ℝ) * Real.log 2))
      Filter.atTop (𝓝 (1 / 2 - α * 0 + 0)) :=
    tendsto_const_nhds.sub (hdiv.const_mul α) |>.add hdivc
  have := le_of_tendsto hlim hev
  simpa using this

/-- An eventual unit-constant birthday lower bound on the Simon runtime implies `3 * α + 4 * β ≥
1 / 2`. -/
theorem simon_lower_bound_from_const (α β : ℝ)
    (hbirthday : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ ((n : ℝ) / 2) ≤ simonReductionRuntime α β n) :
    3 * α + 4 * β ≥ 1 / 2 :=
  source_theorem5_simon_lower_bound_const α β 1 one_pos (by simpa using hbirthday)

end Qatlib.Papers.LinearSystems09.SimonLower
