/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Max
import Mathlib.Order.Nat
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.SimonLower

open Filter
open scoped Real Topology

noncomputable def simonInstanceSize (n : ℕ) : ℝ := 36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ))

noncomputable def simonConditionNumber (n : ℕ) : ℝ := 4 * (n : ℝ)

noncomputable def simonReductionRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n)

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

noncomputable def simonPositiveDefiniteRuntime (α β : ℝ) (n : ℕ) : ℝ :=
  simonInstanceSize n ^ α *
    (2 : ℝ) ^ (β * Real.sqrt (simonConditionNumber n))

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

def hitPeriods {n : ℕ} (S : Finset (Fin n → ZMod 2)) : Finset (Fin n → ZMod 2) :=
  S.offDiag.image (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) => p.1 + p.2)

theorem exhibits_iff_mem {n : ℕ} (S : Finset (Fin n → ZMod 2)) (s : Fin n → ZMod 2) :
    (∃ p ∈ S.offDiag, p.1 + p.2 = s) ↔ s ∈ hitPeriods S := by
  simp [hitPeriods]

theorem card_hitPeriods_le_offDiag {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    (hitPeriods S).card ≤ S.card * S.card - S.card := by
  calc (hitPeriods S).card
      = (S.offDiag.image
          (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) => p.1 + p.2)).card := rfl
    _ ≤ S.offDiag.card := Finset.card_image_le
    _ = S.card * S.card - S.card := Finset.offDiag_card S

theorem card_hitPeriods_le {n : ℕ} (S : Finset (Fin n → ZMod 2)) :
    (hitPeriods S).card ≤ S.card * (S.card - 1) := by
  have h : S.card * (S.card - 1) = S.card * S.card - S.card := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [h]
  exact card_hitPeriods_le_offDiag S

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

theorem card_nonzero_periods (n : ℕ) :
    (Finset.univ.erase (0 : Fin n → ZMod 2)).card = 2 ^ n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_fun, ZMod.card]

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

theorem simon_birthday_query_lower {n : ℕ} (hn : 1 ≤ n) {q : ℕ} (hq : 1 ≤ q)
    (S : Finset (Fin n → ZMod 2)) (hS : S.card ≤ q)
    (hfrac : 1 / 3 < ((hitPeriods S).card : ℝ) / ((2 : ℝ) ^ n - 1)) :
    (2 : ℝ) ^ n - 1 < 3 * ((q : ℝ) * ((q : ℝ) - 1)) := by
  by_contra hle
  push_neg at hle
  exact absurd (simon_birthday_query_bound hn hq hle S hS) (not_le.mpr hfrac)

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
      push_cast
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

theorem simon_lower_bound_from_const (α β : ℝ)
    (hbirthday : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ^ ((n : ℝ) / 2) ≤ simonReductionRuntime α β n) :
    3 * α + 4 * β ≥ 1 / 2 :=
  source_theorem5_simon_lower_bound_const α β 1 one_pos (by simpa using hbirthday)

end Qatlib.Papers.LinearSystems09.SimonLower
