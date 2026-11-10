/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgram07.MainResults.SpanProgram
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset
open scoped BigOperators

variable {n : ℕ} {J C I : Type}

namespace SpanProgram

def wt [Fintype J] (z : J → ℝ) (w : J → ℂ) : ℝ := ∑ j, z j * ‖w j‖ ^ 2

theorem wt_nonneg [Fintype J] {z : J → ℝ} (hz : ∀ j, 0 ≤ z j) (w : J → ℂ) :
    0 ≤ wt z w := by
  refine sum_nonneg fun j _ => ?_
  exact mul_nonneg (hz j) (sq_nonneg _)

theorem wt_smul [Fintype J] (t : ℝ) (z : J → ℝ) (w : J → ℂ) :
    wt (fun j => t * z j) w = t * wt z w := by
  rw [wt, wt, Finset.mul_sum]
  exact sum_congr rfl fun j _ => by ring

variable (P : SpanProgram n J C I)

def WsizeTrueAt [Fintype J] (z : J → ℝ) (S : Finset J) (c : ℝ) : Prop :=
  (∀ w : J → ℂ, (∀ j, j ∉ S → w j = 0) →
      (∑ j ∈ S, w j • P.v j = target C) → c ≤ wt z w) ∧
    ∃ w : J → ℂ, (∀ j, j ∉ S → w j = 0) ∧
      (∑ j ∈ S, w j • P.v j = target C) ∧ wt z w = c

def WsizeFalseAt [Fintype J] [Fintype C] (z : J → ℝ) (S : Finset J) (c : ℝ) : Prop :=
  (∀ b : Option C → ℂ, b none = 1 → (∀ j ∈ S, P.pair b j = 0) →
      c ≤ ∑ j, z j * ‖P.pair b j‖ ^ 2) ∧
    ∃ b : Option C → ℂ, b none = 1 ∧ (∀ j ∈ S, P.pair b j = 0) ∧
      ∑ j, z j * ‖P.pair b j‖ ^ 2 = c

variable {P}

theorem WsizeTrueAt.le_wt [Fintype J] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (h : P.WsizeTrueAt z S c) {w : J → ℂ} (hsupp : ∀ j, j ∉ S → w j = 0)
    (hsum : ∑ j ∈ S, w j • P.v j = target C) : c ≤ wt z w :=
  h.1 w hsupp hsum

theorem WsizeFalseAt.le [Fintype J] [Fintype C] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (h : P.WsizeFalseAt z S c) {b : Option C → ℂ} (hb : b none = 1)
    (horth : ∀ j ∈ S, P.pair b j = 0) :
    c ≤ ∑ j, z j * ‖P.pair b j‖ ^ 2 :=
  h.1 b hb horth

theorem WsizeTrueAt.smul [Fintype J] {z : J → ℝ} {S : Finset J} {c : ℝ} (t : ℝ) (ht : 0 ≤ t)
    (h : P.WsizeTrueAt z S c) : P.WsizeTrueAt (fun j => t * z j) S (t * c) := by
  constructor
  · intro w hsupp hsum
    have hle : c ≤ wt z w := h.1 w hsupp hsum
    rw [wt_smul]
    exact mul_le_mul_of_nonneg_left hle ht
  · obtain ⟨w, hsupp, hsum, hwt⟩ := h.2
    exact ⟨w, hsupp, hsum, by rw [wt_smul, hwt]⟩

theorem WsizeFalseAt.smul [Fintype J] [Fintype C] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (t : ℝ) (ht : 0 ≤ t) (h : P.WsizeFalseAt z S c) :
    P.WsizeFalseAt (fun j => t * z j) S (t * c) := by
  constructor
  · intro b hb horth
    have hle : c ≤ ∑ j, z j * ‖P.pair b j‖ ^ 2 := h.1 b hb horth
    have hsum : ∑ j, (t * z j) * ‖P.pair b j‖ ^ 2
        = t * ∑ j, z j * ‖P.pair b j‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hle ht
  · obtain ⟨b, hb, horth, hval⟩ := h.2
    refine ⟨b, hb, horth, ?_⟩
    have hsum : ∑ j, (t * z j) * ‖P.pair b j‖ ^ 2
        = t * ∑ j, z j * ‖P.pair b j‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [hsum, hval]

theorem WsizeTrueAt.mono [Fintype J] {z z' : J → ℝ} {S : Finset J} {c c' : ℝ}
    (hz : ∀ j, z j ≤ z' j)
    (h : P.WsizeTrueAt z S c) (h' : P.WsizeTrueAt z' S c') : c ≤ c' := by
  obtain ⟨w', hsupp, hsum, hval⟩ := h'.2
  have hle : c ≤ wt z w' := h.1 w' hsupp hsum
  have hmono : wt z w' ≤ wt z' w' := by
    refine sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right (hz j) (sq_nonneg _)
  calc c ≤ wt z w' := hle
    _ ≤ wt z' w' := hmono
    _ = c' := hval

def WsizeTrueLE [Fintype J] (z : J → ℝ) (S : Finset J) (c : ℝ) : Prop :=
  ∃ w : J → ℂ, (∀ j, j ∉ S → w j = 0) ∧
    (∑ j ∈ S, w j • P.v j = target C) ∧ wt z w ≤ c

def WsizeFalseLE [Fintype J] [Fintype C] (z : J → ℝ) (S : Finset J) (c : ℝ) : Prop :=
  ∃ b : Option C → ℂ, b none = 1 ∧ (∀ j ∈ S, P.pair b j = 0) ∧
    ∑ j, z j * ‖P.pair b j‖ ^ 2 ≤ c

theorem WsizeTrueAt.toLE [Fintype J] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (h : P.WsizeTrueAt z S c) : P.WsizeTrueLE z S c :=
  ⟨h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.1, le_of_eq h.2.choose_spec.2.2⟩

theorem WsizeFalseAt.toLE [Fintype J] [Fintype C] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (h : P.WsizeFalseAt z S c) : P.WsizeFalseLE z S c :=
  ⟨h.2.choose, h.2.choose_spec.1, h.2.choose_spec.2.1, le_of_eq h.2.choose_spec.2.2⟩

theorem WsizeTrueAt.ofLE [Fintype J] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (hle : P.WsizeTrueLE z S c)
    (hge : ∀ w : J → ℂ, (∀ j, j ∉ S → w j = 0) →
      (∑ j ∈ S, w j • P.v j = target C) → c ≤ wt z w) :
    P.WsizeTrueAt z S c :=
  ⟨hge, hle.choose, hle.choose_spec.1, hle.choose_spec.2.1, le_antisymm hle.choose_spec.2.2
    (hge _ hle.choose_spec.1 hle.choose_spec.2.1)⟩

theorem WsizeFalseAt.ofLE [Fintype J] [Fintype C] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (hle : P.WsizeFalseLE z S c)
    (hge : ∀ b : Option C → ℂ, b none = 1 → (∀ j ∈ S, P.pair b j = 0) →
      c ≤ ∑ j, z j * ‖P.pair b j‖ ^ 2) :
    P.WsizeFalseAt z S c :=
  ⟨hge, hle.choose, hle.choose_spec.1, hle.choose_spec.2.1, le_antisymm
    hle.choose_spec.2.2 (hge _ hle.choose_spec.1 hle.choose_spec.2.1)⟩

theorem wt_le_of_pointwise_le [Fintype J] {z z' : J → ℝ} (hz : ∀ j, z j ≤ z' j)
    (w : J → ℂ) : wt z w ≤ wt z' w := by
  refine sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_right (hz j) (sq_nonneg _)

theorem WsizeTrueLE.smul [Fintype J] {z : J → ℝ} {S : Finset J} {c : ℝ} (t : ℝ) (ht : 0 ≤ t)
    (h : P.WsizeTrueLE z S c) : P.WsizeTrueLE (fun j => t * z j) S (t * c) := by
  obtain ⟨w, hsupp, hsum, hwt⟩ := h
  refine ⟨w, hsupp, hsum, ?_⟩
  rw [wt_smul]
  exact mul_le_mul_of_nonneg_left hwt ht

theorem WsizeFalseLE.smul [Fintype J] [Fintype C] {z : J → ℝ} {S : Finset J} {c : ℝ}
    (t : ℝ) (ht : 0 ≤ t) (h : P.WsizeFalseLE z S c) :
    P.WsizeFalseLE (fun j => t * z j) S (t * c) := by
  obtain ⟨b, hb, horth, hval⟩ := h
  refine ⟨b, hb, horth, ?_⟩
  have hsum : ∑ j, (t * z j) * ‖P.pair b j‖ ^ 2 = t * ∑ j, z j * ‖P.pair b j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hsum]
  exact mul_le_mul_of_nonneg_left hval ht

end SpanProgram

end Qatlib.Papers.SpanProgram07.MainResults
