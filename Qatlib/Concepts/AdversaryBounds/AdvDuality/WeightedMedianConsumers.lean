/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable def heterogeneousCoinProb (b x : Bool) : ℝ :=
  match b, x with
  | false, true => 1/4
  | false, false => 3/4
  | true, true => 3/4
  | true, false => 1/4

theorem heterogeneousCoinProb_nonneg (b x : Bool) : 0 ≤ heterogeneousCoinProb b x := by
  unfold heterogeneousCoinProb
  split <;> norm_num

theorem heterogeneousCoinProb_sum_one (b : Bool) :
    ∑ x : Bool, heterogeneousCoinProb b x = 1 := by
  rw [Fintype.sum_bool]
  cases b <;> norm_num [heterogeneousCoinProb]

noncomputable def heterogeneousCoinLaw (b : Bool) : FinDist Bool where
  prob := heterogeneousCoinProb b
  nonneg := heterogeneousCoinProb_nonneg b
  sum_one := heterogeneousCoinProb_sum_one b

noncomputable def heterogeneousCoinValue (b x : Bool) : ℝ :=
  match b, x with
  | false, true => 4
  | true, true => 4/3
  | _, false => 0

theorem heterogeneous_nonidentical_coin_consumer :
    (heterogeneousCoinLaw false).prob true = 1/4 ∧
      (heterogeneousCoinLaw true).prob true = 3/4 ∧
      heterogeneousCoinValue false true = 4 ∧ heterogeneousCoinValue true true = 4/3 ∧
      (∀ b, heterogeneousCoinValue b false = 0) ∧
      (∀ b, (heterogeneousCoinLaw b).expect (heterogeneousCoinValue b) = 1) ∧
      ((heterogeneousCoinLaw false).expect (fun x => (heterogeneousCoinValue false x-1)^2) = 3) ∧
      ((heterogeneousCoinLaw true).expect (fun x => (heterogeneousCoinValue true x-1)^2) = 1/3) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro b; cases b <;> rfl
  · intro b
    show ∑ x : Bool, heterogeneousCoinProb b x * heterogeneousCoinValue b x = 1
    cases b <;> rw [Fintype.sum_bool] <;>
      norm_num [heterogeneousCoinProb, heterogeneousCoinValue]
  · show ∑ x : Bool, heterogeneousCoinProb false x *
        (heterogeneousCoinValue false x - 1)^2 = 3
    rw [Fintype.sum_bool]
    norm_num [heterogeneousCoinProb, heterogeneousCoinValue]
  · show ∑ x : Bool, heterogeneousCoinProb true x *
        (heterogeneousCoinValue true x - 1)^2 = 1/3
    rw [Fintype.sum_bool]
    norm_num [heterogeneousCoinProb, heterogeneousCoinValue]

theorem sum_fin_two_mul_of_parity {A B : ℝ} : ∀ m : ℕ,
    ∑ b : Fin (2*m), (if b.val % 2 = 0 then A else B) = m * (A + B) := by
  intro m
  induction m with
  | zero => norm_num
  | succ k ih =>
      have hsplit : ∑ b : Fin (2*(k+1)), (if b.val % 2 = 0 then A else B)
          = (∑ b : Fin (2*k), (if b.val % 2 = 0 then A else B)) + A + B := by
        have h1 : ∑ b : Fin (2*(k+1)), (if b.val % 2 = 0 then A else B)
            = ∑ b : Fin (2*k), (if (Fin.castAdd 2 b).val % 2 = 0 then A else B)
              + ∑ j : Fin 2, (if (Fin.natAdd (2*k) j).val % 2 = 0 then A else B) :=
          Fin.sum_univ_add (a := 2*k) (b := 2) (fun b => if b.val % 2 = 0 then A else B)
        have h2 : (∑ b : Fin (2*k), (if (Fin.castAdd 2 b).val % 2 = 0 then A else B))
            = ∑ b : Fin (2*k), (if b.val % 2 = 0 then A else B) :=
          Finset.sum_congr rfl fun b _ => rfl
        have h3 : (∑ j : Fin 2, (if (Fin.natAdd (2*k) j).val % 2 = 0 then A else B))
            = A + B := by
          rw [Fin.sum_univ_two (fun j => if (Fin.natAdd (2*k) j).val % 2 = 0 then A else B)]
          have e0 : (Fin.natAdd (2*k) (0 : Fin 2)).val % 2 = 0 := by
            show ((2*k : ℕ) + 0) % 2 = 0
            omega
          have e1 : ¬ (Fin.natAdd (2*k) (1 : Fin 2)).val % 2 = 0 := by
            show ((2*k : ℕ) + 1) % 2 = 0 → False
            omega
          rw [if_pos e0, if_neg e1]
        rw [h1, h2, h3, add_assoc]
      rw [hsplit, ih]
      push_cast
      ring

theorem heterogeneous_counted_nonuniform_median_consumer : ∀ (r : ℕ),
      let p : Fin (2*r+1) → Fin 64 → FinDist Bool :=
          fun _ b => heterogeneousCoinLaw (b.val % 2 == 1)
      let w : Fin (2*r+1) → Fin 64 → ℝ := fun _ b => if b.val % 2 = 0 then 1/96 else 2/96
      let f : Fin (2*r+1) → Fin 64 → Bool → ℝ := fun _ b => heterogeneousCoinValue (b.val % 2 == 1)
      (∑ ω ∈ Finset.univ.filter (fun ω => 1/2 < |sortedBlockMedian r (weightedBlock r 64 w f ω)-1|),
        (blockRecordLaw r 64 p).prob ω) ≤ (2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) ∧
      (∀ ω, (countedBlockMedian r 64 w f ω).2.1 = (2*r+1)*64) := by
  intro r
  have hcoin := heterogeneous_nonidentical_coin_consumer
  have hcenter : ∀ b : Fin 64,
      (heterogeneousCoinLaw (b.val % 2 == 1)).expect
        (heterogeneousCoinValue (b.val % 2 == 1)) = 1 :=
    fun b => hcoin.2.2.2.2.2.1 _
  have hmean : ∀ j : Fin (2*r+1),
      ∑ b : Fin 64, (if b.val % 2 = 0 then (1:ℝ)/96 else 2/96) *
        (heterogeneousCoinLaw (b.val % 2 == 1)).expect
          (heterogeneousCoinValue (b.val % 2 == 1)) = 1 := by
    intro j
    calc ∑ b : Fin 64, (if b.val % 2 = 0 then (1:ℝ)/96 else 2/96) *
          (heterogeneousCoinLaw (b.val % 2 == 1)).expect
            (heterogeneousCoinValue (b.val % 2 == 1))
        = ∑ b : Fin 64, (if b.val % 2 = 0 then (1:ℝ)/96 else 2/96) :=
          Finset.sum_congr rfl fun b _ => by rw [hcenter b, mul_one]
      _ = 32 * ((1:ℝ)/96 + 2/96) := sum_fin_two_mul_of_parity (m := 32)
      _ = 1 := by norm_num
  have hvar : ∀ j : Fin (2*r+1),
      ∑ b : Fin 64, ((if b.val % 2 = 0 then (1:ℝ)/96 else 2/96))^2 *
        (heterogeneousCoinLaw (b.val % 2 == 1)).expect (fun x =>
          (heterogeneousCoinValue (b.val % 2 == 1) x -
            (heterogeneousCoinLaw (b.val % 2 == 1)).expect
              (heterogeneousCoinValue (b.val % 2 == 1)))^2)
      ≤ (1/2)^2/16 := by
    intro j
    have hterm : ∀ b : Fin 64,
        ((if b.val % 2 = 0 then (1:ℝ)/96 else 2/96))^2 *
          (heterogeneousCoinLaw (b.val % 2 == 1)).expect (fun x =>
            (heterogeneousCoinValue (b.val % 2 == 1) x -
              (heterogeneousCoinLaw (b.val % 2 == 1)).expect
                (heterogeneousCoinValue (b.val % 2 == 1)))^2)
          = if b.val % 2 = 0 then ((1:ℝ)/96)^2*3 else ((2:ℝ)/96)^2*(1/3) := by
      intro b
      rw [hcenter b]
      rcases Nat.mod_two_eq_zero_or_one (b.val) with hmod | hmod
      · rw [hmod]
        show ((1:ℝ)/96)^2 * (heterogeneousCoinLaw ((0:Nat) == 1)).expect
            (fun x => (heterogeneousCoinValue ((0:Nat) == 1) x - 1)^2)
          = ((1:ℝ)/96)^2*3
        have hb : ((0:Nat) == 1) = false := rfl
        rw [hb, hcoin.2.2.2.2.2.2.1]
      · rw [hmod]
        show ((2:ℝ)/96)^2 * (heterogeneousCoinLaw ((1:Nat) == 1)).expect
            (fun x => (heterogeneousCoinValue ((1:Nat) == 1) x - 1)^2)
          = ((2:ℝ)/96)^2*(1/3)
        have hb : ((1:Nat) == 1) = true := rfl
        rw [hb, hcoin.2.2.2.2.2.2.2]
    calc ∑ b : Fin 64, ((if b.val % 2 = 0 then (1:ℝ)/96 else 2/96))^2 *
          (heterogeneousCoinLaw (b.val % 2 == 1)).expect (fun x =>
            (heterogeneousCoinValue (b.val % 2 == 1) x -
              (heterogeneousCoinLaw (b.val % 2 == 1)).expect
                (heterogeneousCoinValue (b.val % 2 == 1)))^2)
        = ∑ b : Fin 64,
            (if b.val % 2 = 0 then ((1:ℝ)/96)^2*3 else ((2:ℝ)/96)^2*(1/3)) :=
          Finset.sum_congr rfl fun b _ => hterm b
      _ = 32 * (((1:ℝ)/96)^2*3 + ((2:ℝ)/96)^2*(1/3)) := sum_fin_two_mul_of_parity (m := 32)
      _ ≤ (1/2)^2/16 := by norm_num
  refine ⟨?_, fun ω => (heterogeneous_counted_estimator_reads_and_comparisons r 64
    (fun _ b => if b.val % 2 = 0 then 1/96 else 2/96)
    (fun _ b => heterogeneousCoinValue (b.val % 2 == 1)) ω).2.1⟩
  exact heterogeneous_weighted_median_concentration (X := Bool) r 64
    (fun _ b => heterogeneousCoinLaw (b.val % 2 == 1))
    (fun _ b => if b.val % 2 = 0 then 1/96 else 2/96)
    (fun _ b => heterogeneousCoinValue (b.val % 2 == 1)) 1 (1/2) (by norm_num) hmean hvar

end Qatlib.Concepts.AdversaryBounds.AdvDuality
