/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction

namespace Qatlib.Papers.QMatchingFlow05.QueryBounds

open Qatlib.Papers.QMatchingFlow05.SearchTools

def middleWeight {N : ℕ} (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j = true).card

theorem middleWeight_eq_majorityCount {N : ℕ} (x : Fin N → Bool) :
    middleWeight x = MajorityCount x := rfl

def layeredMaxFlow {N : ℕ} (x : Fin N → Bool) : ℕ := middleWeight x

def layeredVertexCount (p : ℕ) : ℕ := 2 * p + 2

def layeredCapacity (p : ℕ) : ℕ := layeredVertexCount p

theorem layeredThreshold_eq_majority {N : ℕ} :
    (fun x : Fin N → Bool => decide (N / 2 < layeredMaxFlow x)) = @MajorityBit N := by
  funext x
  rfl

theorem theorem7_exact_queryLower (k : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (P : Program (k + k + 1) W)
    (h : Exact P (fun x => decide ((k + k + 1) / 2 < layeredMaxFlow x))) :
    k + 1 ≤ QueryCount P.circuit :=
  majority_exact_lower k P h

def MajorityBoundedLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
      (P : Program N W),
    Bounded P (@MajorityBit N) →
    c * (N : ℝ) ≤ (QueryCount P.circuit : ℝ)

theorem exact_implies_majorityBound (k : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (P : Program (k + k + 1) W) (h : Exact P MajorityBit) :
    k + 1 ≤ QueryCount P.circuit :=
  majority_exact_lower k P h

theorem theorem7_flow_queryLower (hmaj : MajorityBoundedLower)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ (W : Type) [Fintype W] [DecidableEq W],
      ∃ c : ℝ, 0 < c ∧ ∀ (P : Program (p * p) W),
        Bounded P (fun x => decide ((p * p) / 2 < layeredMaxFlow x)) →
        c * ((2 * (p : ℝ) + 2) ^ 2) ≤ (QueryCount P.circuit : ℝ) := by
  intro W _ _
  obtain ⟨c, hc, hbound⟩ := hmaj
  refine ⟨c / 32, by linarith, ?_⟩
  intro P hP
  have hb : c * ((p * p : ℕ) : ℝ) ≤ (QueryCount P.circuit : ℝ) :=
    hbound (p * p) W P hP
  have hpq : ((p * p : ℕ) : ℝ) = (p : ℝ) * (p : ℝ) := by push_cast; ring
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hcast : (2 * (p : ℝ) + 2) ^ 2 ≤ 32 * ((p : ℝ) * (p : ℝ)) := by
    nlinarith [hp1, sq_nonneg ((p : ℝ) - 1), sq_nonneg ((p : ℝ) - 2)]
  calc (c / 32) * ((2 * (p : ℝ) + 2) ^ 2)
      ≤ (c / 32) * (32 * ((p : ℝ) * (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = c * ((p : ℝ) * (p : ℝ)) := by ring
    _ = c * ((p * p : ℕ) : ℝ) := by rw [hpq]
    _ ≤ (QueryCount P.circuit : ℝ) := hb

end Qatlib.Papers.QMatchingFlow05.QueryBounds

end
