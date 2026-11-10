/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset

inductive Lit (n : ℕ) where
  | pos (i : Fin n)
  | neg (i : Fin n)
  deriving DecidableEq

namespace Lit

def eval {n : ℕ} (x : Fin n → Bool) : Lit n → Bool
  | pos i => x i
  | neg i => !x i

end Lit

variable {n : ℕ} {J C I : Type}

structure SpanProgram (n : ℕ) (J C I : Type) where

  grp : I → J

  lit : I → Lit n

  v : J → Option C → ℂ

def target (C : Type) : Option C → ℂ := fun k => k.rec 1 fun _ => 0

@[simp]
theorem target_none (C : Type) : target C none = 1 := rfl

@[simp]
theorem target_some (C : Type) (c : C) : target C (some c) = 0 := rfl

theorem target_eq_single (C : Type) [DecidableEq C] : target C = Pi.single none 1 := by
  funext k
  cases k with
  | none => simp [target]
  | some c => simp [target]

namespace SpanProgram

variable (P : SpanProgram n J C I)

def groupTrue (x : Fin n → Bool) (j : J) : Prop :=
  ∀ i, P.grp i = j → (P.lit i).eval x = true

def accepts [Fintype J] (x : Fin n → Bool) : Prop :=
  ∃ a : J → ℂ, (∀ j, ¬ P.groupTrue x j → a j = 0) ∧ ∑ j, a j • P.v j = target C

def falseInputs [Fintype I] [DecidableEq I] [DecidableEq J] (x : Fin n → Bool) (j : J) :
    Finset I :=
  univ.filter fun i => P.grp i = j ∧ (P.lit i).eval x = false

def inputCoeff [Fintype I] [DecidableEq I] [DecidableEq J] (x : Fin n → Bool) (bI : I → ℂ)
    (j : J) : ℂ :=
  (P.falseInputs x j).sum bI

def pair [Fintype C] (b : Option C → ℂ) (j : J) : ℂ :=
  ∑ k, (starRingEnd ℂ) (P.v j k) * b k

variable {P}

theorem mem_falseInputs [Fintype I] [DecidableEq I] [DecidableEq J] {x : Fin n → Bool}
    {j : J} {i : I} :
    i ∈ P.falseInputs x j ↔ P.grp i = j ∧ (P.lit i).eval x = false := by
  simp [falseInputs]

theorem exists_false_input {x : Fin n → Bool} {j : J} (h : ¬ P.groupTrue x j) :
    ∃ i, P.grp i = j ∧ (P.lit i).eval x = false := by
  classical
  by_contra hc
  apply h
  intro i hi
  by_contra hb
  exact hc ⟨i, hi, by simpa using hb⟩

theorem supported_iff (x : Fin n → Bool) (a : J → ℂ) :
    (∀ j, ¬ P.groupTrue x j → a j = 0) ↔
      (∀ i, (P.lit i).eval x = false → a (P.grp i) = 0) := by
  constructor
  · intro h i hi
    exact h (P.grp i) fun hg => by
      have htrue := hg i rfl
      rw [hi] at htrue
      exact Bool.false_ne_true htrue
  · intro h j hj
    obtain ⟨i, hi, hif⟩ := P.exists_false_input hj
    rw [← hi]
    exact h i hif

theorem accepts_iff_exists_zeroEigen_aO [Fintype J] (x : Fin n → Bool) :
    P.accepts x ↔ ∃ (aO : ℂ) (a : J → ℂ), aO ≠ 0 ∧
      aO • target C + ∑ j, a j • P.v j = 0 ∧
      (∀ i, (P.lit i).eval x = false → a (P.grp i) = 0) := by
  constructor
  · rintro ⟨a, hsupp, hsum⟩
    refine ⟨-1, a, by norm_num, ?_, (P.supported_iff x a).1 hsupp⟩
    rw [hsum]
    simp
  · rintro ⟨aO, a, haO, hEq, hsupp⟩
    have hsum : ∑ j, a j • P.v j = -(aO • target C) :=
      (neg_eq_of_add_eq_zero_right hEq).symm
    have hsupp' : ∀ i, (P.lit i).eval x = false → (-aO)⁻¹ * a (P.grp i) = 0 :=
      fun i hi => by rw [hsupp i hi, mul_zero]
    refine ⟨fun j => (-aO)⁻¹ * a j, (P.supported_iff x _).2 hsupp', ?_⟩
    calc ∑ j, ((-aO)⁻¹ * a j) • P.v j
        = (-aO)⁻¹ • ∑ j, a j • P.v j := by
          rw [smul_sum]
          exact sum_congr rfl fun j _ => by rw [smul_smul]
      _ = (-aO)⁻¹ • (-(aO • target C)) := by rw [hsum]
      _ = target C := by
          rw [← neg_smul, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr haO), one_smul]

theorem exists_dual_witness [Fintype J] [DecidableEq J] [Fintype C] (x : Fin n → Bool)
    (h : ¬ P.accepts x) :
    ∃ b : Option C → ℂ, b none ≠ 0 ∧ ∀ j, P.groupTrue x j → P.pair b j = 0 := by
  classical
  set S : Set (Option C → ℂ) := {w | ∃ j, P.groupTrue x j ∧ P.v j = w} with hS
  have key : ∀ w : Option C → ℂ, w ∈ Submodule.span ℂ S →
      ∃ a : J → ℂ, (∀ j, ¬ P.groupTrue x j → a j = 0) ∧ ∑ j, a j • P.v j = w := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∃ a : J → ℂ,
      (∀ j, ¬ P.groupTrue x j → a j = 0) ∧ ∑ j, a j • P.v j = w) ?_ ?_ ?_ ?_ hw
    · rintro w ⟨j, hj, rfl⟩
      refine ⟨fun j' => if j' = j then (1 : ℂ) else 0, ?_, ?_⟩
      · intro j' hj'
        by_cases hjj : j' = j
        · subst hjj
          exact absurd hj hj'
        · simp [hjj]
      · rw [sum_eq_single j]
        · simp
        · intro j' _ hj'
          simp [hj']
        · intro hj
          exact absurd (mem_univ j) hj
    · exact ⟨0, by simp, by simp⟩
    · rintro w₁ w₂ _ _ ⟨a₁, hs₁, he₁⟩ ⟨a₂, hs₂, he₂⟩
      refine ⟨a₁ + a₂, fun j hj => by simp [hs₁ j hj, hs₂ j hj], ?_⟩
      calc ∑ j, (a₁ + a₂) j • P.v j
          = ∑ j, (a₁ j • P.v j + a₂ j • P.v j) := by
            refine sum_congr rfl fun j _ => by rw [Pi.add_apply, add_smul]
        _ = ∑ j, a₁ j • P.v j + ∑ j, a₂ j • P.v j := sum_add_distrib
        _ = w₁ + w₂ := by rw [he₁, he₂]
    · rintro c w _ ⟨a, hs, he⟩
      refine ⟨c • a, fun j hj => by simp [hs j hj], ?_⟩
      calc ∑ j, (c • a) j • P.v j
          = c • ∑ j, a j • P.v j := by
            rw [smul_sum]
            exact sum_congr rfl fun j _ => by simp [Pi.smul_apply, smul_smul, smul_eq_mul]
        _ = c • w := by rw [he]
  have hspan : target C ∉ Submodule.span ℂ S := fun hmem => h (key (target C) hmem)
  have hsep : ∃ φ : Module.Dual ℂ (Option C → ℂ),
      φ ∈ (Submodule.span ℂ S).dualAnnihilator ∧ φ (target C) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hspan ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Submodule.span ℂ S) (target C)).1 hc)
  obtain ⟨φ, hφ, hφt⟩ := hsep
  have hbasis : ∀ w : Option C → ℂ, φ w = ∑ k, w k * φ (Pi.single k 1) := by
    intro w
    conv_lhs => rw [← (Pi.basisFun ℂ (Option C)).sum_repr w]
    simp [map_sum, map_smul]
  refine ⟨fun k => (starRingEnd ℂ) (φ (Pi.single k 1)), ?_, ?_⟩
  · show (starRingEnd ℂ) (φ (Pi.single (none : Option C) 1)) ≠ 0
    rw [← target_eq_single C]
    exact (star_ne_zero).2 hφt
  · intro j hj
    have hv : P.v j ∈ Submodule.span ℂ S := Submodule.subset_span ⟨j, hj, rfl⟩
    have h0 : ∑ k, P.v j k * φ (Pi.single k 1) = 0 := by
      rw [← hbasis]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ (P.v j) hv
    calc P.pair (fun k => (starRingEnd ℂ) (φ (Pi.single k 1))) j
        = (starRingEnd ℂ) (∑ k, P.v j k * φ (Pi.single k 1)) := by
          rw [pair, map_sum]
          refine sum_congr rfl fun k _ => by rw [map_mul]
      _ = 0 := by rw [h0, map_zero]

theorem accepts_iff_exists_zeroEigen_bO [Fintype J] [DecidableEq J] [Fintype C]
    [Fintype I] [DecidableEq I] (x : Fin n → Bool) :
    (∃ (b : Option C → ℂ) (bI : I → ℂ), b none ≠ 0 ∧
        ∀ j, P.pair b j + P.inputCoeff x bI j = 0) ↔ ¬ P.accepts x := by
  classical
  constructor
  · rintro ⟨b, bI, hb, hEq⟩ hacc
    obtain ⟨a, hsupp, hsum⟩ := hacc
    have hsupp' : ∀ i, (P.lit i).eval x = false → a (P.grp i) = 0 :=
      (P.supported_iff x a).1 hsupp
    have hcoord : ∀ k, ∑ j, a j * P.v j k = target C k := by
      intro k
      have h := congr_fun hsum k
      simpa [Finset.sum_apply, smul_eq_mul] using h
    have hconj : ∀ k, ∑ j, (starRingEnd ℂ) (a j) * (starRingEnd ℂ) (P.v j k)
        = (starRingEnd ℂ) (target C k) := by
      intro k
      have h := congrArg (starRingEnd ℂ) (hcoord k)
      simpa [map_sum, map_mul] using h
    have h1 : ∑ j, (starRingEnd ℂ) (a j) * P.pair b j = b none := by
      calc ∑ j, (starRingEnd ℂ) (a j) * P.pair b j
          = ∑ j, ∑ k, (starRingEnd ℂ) (a j) *
              ((starRingEnd ℂ) (P.v j k) * b k) := by
            refine sum_congr rfl fun j _ => ?_
            rw [pair, mul_sum]
        _ = ∑ k, ∑ j, (starRingEnd ℂ) (a j) *
              ((starRingEnd ℂ) (P.v j k) * b k) := sum_comm
        _ = ∑ k, b k * (∑ j, (starRingEnd ℂ) (a j) * (starRingEnd ℂ) (P.v j k)) := by
            refine sum_congr rfl fun k _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun j _ => by ring
        _ = ∑ k, b k * (starRingEnd ℂ) (target C k) := by simp [hconj]
        _ = b none := by
            rw [sum_eq_single none]
            · simp
            · intro k _ hk
              cases k with
              | none => exact absurd rfl hk
              | some c => simp
            · intro hmem
              exact absurd (mem_univ none) hmem
    have h2 : ∑ j, (starRingEnd ℂ) (a j) * P.inputCoeff x bI j = 0 := by
      refine sum_eq_zero fun j _ => ?_
      rw [inputCoeff, mul_sum]
      refine sum_eq_zero fun i hi => ?_
      obtain ⟨hg, hl⟩ := P.mem_falseInputs.1 hi
      rw [← hg, hsupp' i hl, map_zero, zero_mul]
    have hzero : ∑ j, (starRingEnd ℂ) (a j) * (P.pair b j + P.inputCoeff x bI j) = 0 :=
      sum_eq_zero fun j _ => by rw [hEq j, mul_zero]
    have hsplit : ∑ j, (starRingEnd ℂ) (a j) * (P.pair b j + P.inputCoeff x bI j)
        = ∑ j, (starRingEnd ℂ) (a j) * P.pair b j +
          ∑ j, (starRingEnd ℂ) (a j) * P.inputCoeff x bI j := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [hsplit, h1, h2, add_zero] at hzero
    exact hb hzero
  · intro h
    obtain ⟨b, hb, horth⟩ := P.exists_dual_witness x h
    let bI : I → ℂ := fun i =>
      if (P.lit i).eval x = false then
        -(((P.falseInputs x (P.grp i)).card : ℂ))⁻¹ * P.pair b (P.grp i)
      else 0
    refine ⟨b, bI, hb, ?_⟩
    intro j
    by_cases hj : P.groupTrue x j
    · have hempty : P.falseInputs x j = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro i hi
        obtain ⟨hg, hl⟩ := P.mem_falseInputs.1 hi
        rw [hj i hg] at hl
        exact Bool.false_ne_true hl.symm
      rw [inputCoeff, hempty, sum_empty, add_zero]
      exact horth j hj
    · obtain ⟨i₀, hi₀g, hi₀l⟩ := P.exists_false_input hj
      have hmem : i₀ ∈ P.falseInputs x j := P.mem_falseInputs.2 ⟨hi₀g, hi₀l⟩
      have hcardpos : 0 < (P.falseInputs x j).card := card_pos.2 ⟨i₀, hmem⟩
      have hcard : ((P.falseInputs x j).card : ℂ) ≠ 0 := by
        exact_mod_cast hcardpos.ne'
      have hsum' : (P.falseInputs x j).sum bI = -P.pair b j := by
        have hterm : ∀ i, i ∈ P.falseInputs x j → bI i =
            -(((P.falseInputs x j).card : ℂ))⁻¹ * P.pair b j := by
          intro i hi
          obtain ⟨hg, hl⟩ := P.mem_falseInputs.1 hi
          simp only [bI, hl, if_true]
          rw [hg]
        rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
        field_simp
      simp only [inputCoeff, hsum', add_neg_cancel]

end SpanProgram

end Qatlib.Papers.SpanProgram07.MainResults
