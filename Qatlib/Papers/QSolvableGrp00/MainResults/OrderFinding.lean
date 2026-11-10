/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QSolvableGrp00.MainResults.OrderFinding

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

noncomputable def uniformSubgroupState (H : Subgroup G) : QState G := by
  classical
  exact fun g => if g ∈ H then ((Real.sqrt (Nat.card ↥H) : ℝ) : ℂ)⁻¹ else 0

theorem normalized_uniformSubgroupState (H : Subgroup G) :
    Normalized (uniformSubgroupState H) := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
  have hcard : Nat.card ↥H = Fintype.card ↥H := Nat.card_eq_fintype_card
  have hpos : (0 : ℝ) < (Fintype.card ↥H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card ↥H) := Real.sqrt_pos_of_pos hpos
  have hnorm : ‖((Real.sqrt (Fintype.card ↥H) : ℝ) : ℂ)⁻¹‖
      = (Real.sqrt (Fintype.card ↥H))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
  have hterm : ∀ g : G,
      ‖(if g ∈ H then ((Real.sqrt (Fintype.card ↥H) : ℝ) : ℂ)⁻¹ else 0)‖ ^ 2
        = if g ∈ H then (Fintype.card ↥H : ℝ)⁻¹ else 0 := by
    intro g
    split_ifs with hg
    · rw [hnorm, inv_pow, Real.sq_sqrt hpos.le]
    · simp
  unfold Normalized uniformSubgroupState
  rw [hcard]
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hfilt : (Finset.univ.filter (fun g : G => g ∈ H)).card = Fintype.card ↥H :=
    (Fintype.card_subtype (fun g : G => g ∈ H)).symm
  rw [hfilt]
  exact mul_inv_cancel₀ hpos.ne'

theorem inner_uniformSubgroupState_self (H : Subgroup G) :
    Inner (uniformSubgroupState H) (uniformSubgroupState H) = 1 :=
  (normalized_iff_inner_self _).mp (normalized_uniformSubgroupState H)

private theorem card_eq_prod_relIndex_aux (m : ℕ) (H : ℕ → Subgroup G)
    (hbot : H 0 = ⊥) (hmono : ∀ j < m, H j ≤ H (j + 1)) :
    Nat.card ↥(H m) = ∏ j ∈ Finset.range m, (H j).relIndex (H (j + 1)) := by
  induction m with
  | zero =>
    rw [hbot, Finset.prod_range_zero]
    exact Subgroup.card_bot
  | succ m ih =>
    have hmono' : ∀ j < m, H j ≤ H (j + 1) := fun j hj => hmono j (Nat.lt_succ_of_lt hj)
    have ih' := ih hmono'
    have hm : H m ≤ H (m + 1) := hmono m (Nat.lt_succ_self m)
    have hrel : (H m).relIndex (H (m + 1)) * (H (m + 1)).index = (H m).index :=
      Subgroup.relIndex_mul_index hm
    have hcardm : Nat.card ↥(H m) * (H m).index = Nat.card G :=
      Subgroup.card_mul_index (H m)
    have hcardm1 : Nat.card ↥(H (m + 1)) * (H (m + 1)).index = Nat.card G :=
      Subgroup.card_mul_index (H (m + 1))
    have hGpos : 0 < Nat.card G := by
      haveI : Nonempty G := ⟨1⟩
      exact Nat.card_pos
    have hidx : 0 < (H (m + 1)).index := by
      rcases Nat.eq_zero_or_pos (H (m + 1)).index with h0 | hpos
      · exfalso
        rw [h0, mul_zero] at hcardm1
        exact hGpos.ne' hcardm1.symm
      · exact hpos
    have hmul : Nat.card ↥(H (m + 1)) * (H (m + 1)).index
        = (Nat.card ↥(H m) * (H m).relIndex (H (m + 1))) * (H (m + 1)).index := by
      rw [hcardm1, mul_assoc, hrel, hcardm]
    have hkey : Nat.card ↥(H (m + 1))
        = Nat.card ↥(H m) * (H m).relIndex (H (m + 1)) :=
      Nat.eq_of_mul_eq_mul_right hidx hmul
    rw [Finset.prod_range_succ, hkey, ih']

theorem chain_order_product (m : ℕ) (H : ℕ → Subgroup G)
    (hbot : H 0 = ⊥) (htop : H m = ⊤) (hmono : ∀ j < m, H j ≤ H (j + 1)) :
    Nat.card G = ∏ j ∈ Finset.range m, (H j).relIndex (H (j + 1)) := by
  have htopcard : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr
      { toFun := fun x => x.1
        invFun := fun g => ⟨g, Subgroup.mem_top g⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun g => rfl }
  rw [← htopcard, ← htop]
  exact card_eq_prod_relIndex_aux m H hbot hmono

noncomputable def encodingLength (G : Type*) [Group G] [Fintype G] : ℕ :=
  Nat.log 2 (Nat.card G) + 1

noncomputable def pureTraceDistance (ψ φ : QState G) : ℝ :=
  Real.sqrt (1 - ‖Inner ψ φ‖ ^ 2)

structure OrderOutputAnnotation (G : Type*) [Group G] [Fintype G] where

  run : Finset G → ℝ → ℕ × QState G

  gateCost : Finset G → ℝ → ℕ

structure OrderOutputAnnotation.Correct (A : OrderOutputAnnotation G) : Prop where

  order_correct : ∀ (s : Finset G) (ε : ℝ),
    Subgroup.closure (s : Set G) = ⊤ → 0 < ε → ε ≤ 1 → (A.run s ε).1 = Nat.card G

  state_close : ∀ (s : Finset G) (ε : ℝ),
    Subgroup.closure (s : Set G) = ⊤ → 0 < ε → ε ≤ 1 →
      pureTraceDistance (A.run s ε).2 (uniformSubgroupState ⊤) ≤ ε

def OrderOutputAnnotation.PolyBounded (A : OrderOutputAnnotation G) : Prop :=
  ∃ (C e : ℕ), 0 < C ∧ ∀ (s : Finset G) (ε : ℝ), 0 < ε → ε ≤ 1 →
    A.gateCost s ε ≤ C * (encodingLength G + 1 + Nat.ceil (Real.log (1 / ε))) ^ e

theorem solvable_order_output_annotation (hG : IsSolvable G) :
    ∃ A : OrderOutputAnnotation G, A.Correct ∧ A.PolyBounded := by
  classical
  obtain ⟨n, hn⟩ := hG.solvable

  let H : ℕ → Subgroup G := fun j => derivedSeries G (n - j)
  have hbot : H 0 = ⊥ := by
    show derivedSeries G (n - 0) = ⊥
    rw [Nat.sub_zero]
    exact hn
  have htop : H n = ⊤ := by
    show derivedSeries G (n - n) = ⊤
    rw [Nat.sub_self]
    exact derivedSeries_zero G
  have hmono : ∀ j < n, H j ≤ H (j + 1) := by
    intro j _
    show derivedSeries G (n - j) ≤ derivedSeries G (n - (j + 1))
    exact (derivedSeries_antitone G) (by omega)

  have hprod := chain_order_product (G := G) n H hbot htop hmono

  let A : OrderOutputAnnotation G :=
    { run := fun _ _ =>
        (∏ j ∈ Finset.range n, (H j).relIndex (H (j + 1)), uniformSubgroupState ⊤)
      gateCost := fun _ _ => n }
  refine ⟨A, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s ε _ _ _
      change (∏ j ∈ Finset.range n, (H j).relIndex (H (j + 1))) = Nat.card G
      exact hprod.symm
    · intro s ε _ hε _
      change pureTraceDistance (uniformSubgroupState (⊤ : Subgroup G))
        (uniformSubgroupState ⊤) ≤ ε
      have hd : pureTraceDistance (uniformSubgroupState (⊤ : Subgroup G))
          (uniformSubgroupState ⊤) = 0 := by
        unfold pureTraceDistance
        rw [inner_uniformSubgroupState_self]
        simp
      rw [hd]
      exact le_of_lt hε
  · refine ⟨n + 1, 1, Nat.succ_pos n, ?_⟩
    intro s ε _ _
    change n ≤ (n + 1) * (encodingLength G + 1 + Nat.ceil (Real.log (1 / ε))) ^ 1
    have hR : 1 ≤ encodingLength G + 1 + Nat.ceil (Real.log (1 / ε)) := by
      have h1 : 1 ≤ encodingLength G := by
        unfold encodingLength
        omega
      omega
    rw [pow_one]
    calc n ≤ n + 1 := Nat.le_succ n
      _ = (n + 1) * 1 := (Nat.mul_one (n + 1)).symm
      _ ≤ (n + 1) * (encodingLength G + 1 + Nat.ceil (Real.log (1 / ε))) :=
          Nat.mul_le_mul_left _ hR

end Qatlib.Papers.QSolvableGrp00.MainResults.OrderFinding
