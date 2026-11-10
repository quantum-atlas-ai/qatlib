/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.ContinuedFractionOrderConsumers
import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.OrderRecovery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib
open scoped Classical

inductive ShorPreResult where

  | factor (d : ℕ)

  | residue

def shorPerfectPowerDivisor (N : ℕ) : Option ℕ :=
  ((Finset.range N).filter fun m =>
      2 ≤ m ∧ ∃ e ∈ Finset.Icc 2 N, m ^ e = N).toList.head?

def shorPreprocess (N : ℕ) : ShorPreResult :=
  if 4 ≤ N ∧ 2 ∣ N then ShorPreResult.factor 2
  else
    match shorPerfectPowerDivisor N with
    | some m => ShorPreResult.factor m
    | none => ShorPreResult.residue

def decodeUnit (N k : ℕ) [NeZero N] (b : Reg k) : Option (ZMod N)ˣ :=
  (decodeBoundedBits k (Fintype.card (ZMod N)ˣ) b).map
    fun i => (Fintype.equivFin (ZMod N)ˣ).symm i

noncomputable def attemptFactor (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (yz : Fin M × Fin M) : Option ℕ :=
  (cfPairLCMOrderDecode N M a yz).1.bind (orderFactor N a)

def attemptSuccess (N M k : ℕ) [NeZero N]
    (t : Reg k ⊕ (ZMod N)ˣ × Fin M × Fin M) : Prop :=
  match t with
  | Sum.inl _ => False
  | Sum.inr (a, y, z) => (attemptFactor N M a (y, z)).isSome

instance instDecidableAttemptSuccess (N M k : ℕ) [NeZero N] :
    DecidablePred (attemptSuccess N M k) := fun t => by
  unfold attemptSuccess
  split
  · exact isFalse (by rintro ⟨⟩)
  · rename_i a y z
    exact inferInstanceAs (Decidable ((attemptFactor N M a (y, z)).isSome))

def attemptRepSuccess (N M k R : ℕ) [NeZero N]
    (ω : Fin R → Reg k ⊕ (ZMod N)ˣ × Fin M × Fin M) : Prop :=
  ∃ j : Fin R, attemptSuccess N M k (ω j)

instance instDecidableAttemptRepSuccess (N M k R : ℕ) [NeZero N] :
    DecidablePred (attemptRepSuccess N M k R) := fun ω =>
  Fintype.decidableExistsFintype (α := Fin R)
    (p := fun j => attemptSuccess N M k (ω j))

noncomputable def attemptMass (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (t : Reg k ⊕ (ZMod N)ˣ × Fin M × Fin M) : ℝ :=
  ((2 ^ k : ℝ))⁻¹ *
    match t with
    | Sum.inl b => if decodeUnit N k b = none then 1 else 0
    | Sum.inr (a, y, z) =>
        (modularOrderLaw N M a hM).prob y * (modularOrderLaw N M a hM).prob z

noncomputable def attemptLaw (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k) :
    FinDist (Reg k ⊕ (ZMod N)ˣ × Fin M × Fin M) where
  prob := attemptMass N M k hM
  nonneg := by
    intro t
    rcases t with b | ⟨a, y, z⟩
    · unfold attemptMass
      show ((2 ^ k : ℝ))⁻¹ * (if decodeUnit N k b = none then 1 else 0) ≥ 0
      by_cases hb : decodeUnit N k b = none
      · simp only [if_pos hb]
        exact mul_nonneg (inv_nonneg.2 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)) zero_le_one
      · simp only [if_neg hb]
        exact mul_nonneg (inv_nonneg.2 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)) (by norm_num)
    · unfold attemptMass
      exact mul_nonneg (inv_nonneg.2 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k))
        (mul_nonneg ((modularOrderLaw N M a hM).nonneg y)
          ((modularOrderLaw N M a hM).nonneg z))
  sum_one := by
    classical
    have hle : Fintype.card (ZMod N)ˣ ≤ 2 ^ k := hk
    have hfib := bounded_bit_decoder_fibers k (Fintype.card (ZMod N)ˣ) hle
    have hcard : (Finset.univ.filter (fun b : Reg k => decodeUnit N k b = none)).card
        = (Finset.univ.filter
            (fun b : Reg k => decodeBoundedBits k (Fintype.card (ZMod N)ˣ) b = none)).card := by
      rw [Finset.filter_congr
        (p := fun b : Reg k => decodeUnit N k b = none)
        (q := fun b : Reg k => decodeBoundedBits k (Fintype.card (ZMod N)ˣ) b = none)
        (fun b _ => by unfold decodeUnit; exact Option.map_eq_none_iff)]
    have hleft : ∑ b : Reg k, attemptMass N M k hM (Sum.inl b)
        = ((2 ^ k - Fintype.card (ZMod N)ˣ : ℕ) : ℝ) / 2 ^ k := by
      unfold attemptMass
      rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) =>
        show ((2 ^ k : ℝ))⁻¹ * (if decodeUnit N k b = none then 1 else 0)
            = (if decodeUnit N k b = none then 1 else 0) / 2 ^ k from
          by by_cases hb : decodeUnit N k b = none <;> simp [hb]]
      rw [← Finset.sum_div, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one, hcard, hfib.2, Nat.cast_sub hle]
    have hpair : ∀ (a : (ZMod N)ˣ) (y z : Fin M),
        attemptMass N M k hM (Sum.inr (a, (y, z)))
          = ((modularOrderLaw N M a hM).prob y *
              (modularOrderLaw N M a hM).prob z) / 2 ^ k := by
      intro a y z
      unfold attemptMass
      show ((2 ^ k : ℝ))⁻¹ * ((modularOrderLaw N M a hM).prob y *
          (modularOrderLaw N M a hM).prob z)
        = ((modularOrderLaw N M a hM).prob y *
            (modularOrderLaw N M a hM).prob z) / 2 ^ k
      ring
    have hrow : ∀ (a : (ZMod N)ˣ) (y : Fin M),
        ∑ z : Fin M, attemptMass N M k hM (Sum.inr (a, (y, z)))
          = (modularOrderLaw N M a hM).prob y * ((2 ^ k : ℝ))⁻¹ := by
      intro a y
      rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) =>
        show attemptMass N M k hM (Sum.inr (a, (y, z)))
            = (modularOrderLaw N M a hM).prob y *
                ((modularOrderLaw N M a hM).prob z * ((2 ^ k : ℝ))⁻¹) from
          by rw [hpair a y z]; ring,
        ← Finset.mul_sum, ← Finset.sum_mul,
        (modularOrderLaw N M a hM).sum_one]
      ring
    have hinner : ∀ a : (ZMod N)ˣ,
        ∑ bc : Fin M × Fin M, attemptMass N M k hM (Sum.inr (a, bc)) = ((2 ^ k : ℝ))⁻¹ := by
      intro a
      rw [Fintype.sum_prod_type,
        Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hrow a y,
        ← Finset.sum_mul, (modularOrderLaw N M a hM).sum_one]
      ring
    have hright : ∑ q : (ZMod N)ˣ × Fin M × Fin M,
        attemptMass N M k hM (Sum.inr q)
        = (Fintype.card (ZMod N)ˣ : ℝ) / 2 ^ k := by
      rw [Fintype.sum_prod_type,
        Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
          show ∑ bc : Fin M × Fin M, attemptMass N M k hM (Sum.inr (a, bc))
            = ((2 ^ k : ℝ))⁻¹ from hinner a,
        Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_univ]
      field_simp
    rw [Fintype.sum_sum_type, hleft, hright]
    have hkey : (((2 ^ k - Fintype.card (ZMod N)ˣ : ℕ) : ℝ)
        + (Fintype.card (ZMod N)ˣ : ℝ)) = (2 ^ k : ℝ) :=
      by exact_mod_cast Nat.sub_add_cancel hle
    field_simp
    linarith [hkey]

noncomputable def shorAttemptBound (N k : ℕ) [NeZero N] : ℝ :=
  ((Fintype.card (ZMod N)ˣ : ℝ) / 2 ^ k) *
    (1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ))) *
    ((8 / Real.pi ^ 2) ^ 2 / 4)

noncomputable def shorProgramSuccessProb (N R k M : ℕ) [NeZero N] (hM : 0 < M)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k) : ℝ :=
  match shorPreprocess N with
  | ShorPreResult.factor _ => 1
  | ShorPreResult.residue =>
      (attemptLaw N M k hM hk).probEvent (attemptRepSuccess N M k R)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
