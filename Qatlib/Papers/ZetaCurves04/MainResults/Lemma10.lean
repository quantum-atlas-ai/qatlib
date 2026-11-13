/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs
import Qatlib.Papers.ZetaCurves04.MainResults.Model.CoinDefs

/-!
# Finite-group generation and failure budgets

Proper additive subgroups of finite groups have at most half the ambient cardinality, so their
complements have at least half. Together with elementary failure-budget and closure facts, this
module proves finite-group cardinality and closure facts. It does not construct
the paper's group generator algorithm.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `proper_addSubgroup_card_le_half`: A proper additive subgroup of a finite group has
  cardinality at most half the group cardinality.
* `lemma10_generating_algorithm_statement`: **Statement only — not proved in Qatlib.**

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Lemma10

open Qatlib.Papers.ZetaCurves04.MainResults.Model

/-- The three failure allowances `1 / 16`, `1 / 16`, and `1 / 8` sum to `1 / 4`. See
[Kedlaya2006]. -/
theorem lemma10_failure_budget : (1 / 16 : ℝ) + 1 / 16 + 1 / 8 = 1 / 4 := by
  norm_num

/-- Three repetitions with failure factor one half give the expression `1 - 1 / 8`. -/
theorem lemma7_prob_three : (1 : ℝ) - (1 / 2 : ℝ) ^ 3 = 1 - 1 / 8 := by
  norm_num

/-- The finite set of elements belonging to the additive subgroup `H`. -/
noncomputable def subgroupElems {G : Type*} [AddGroup G] [Fintype G]
    (H : AddSubgroup G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => x ∈ H)

/-- The finite set of elements outside the additive subgroup `H`. -/
noncomputable def subgroupCompl {G : Type*} [AddGroup G] [Fintype G]
    (H : AddSubgroup G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => x ∉ H)

/-- A proper additive subgroup of a finite group has cardinality at most half the group
cardinality. See [Kedlaya2006]. -/
theorem proper_addSubgroup_card_le_half {G : Type*} [AddGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) (hH : H ≠ ⊤) :
    2 * (subgroupElems H).card ≤ Fintype.card G := by
  classical
  have hex : ∃ h : G, h ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hH (le_antisymm le_top (fun x _ => hcon x))
  obtain ⟨h, hh⟩ := hex
  have hmap : ∀ x ∈ subgroupElems H, h + x ∈ subgroupCompl H := by
    intro x hx
    unfold subgroupElems at hx
    unfold subgroupCompl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro hmem
    have heq : h = (h + x) + (-x) := by rw [add_assoc, add_neg_cancel, add_zero]
    have hmem' : h ∈ H := by
      rw [heq]
      exact H.add_mem hmem (H.neg_mem hx)
    exact hh hmem'
  have hcard : (subgroupElems H).card ≤ (subgroupCompl H).card := by
    refine Finset.card_le_card_of_injOn (fun x => h + x) ?_ ?_
    · intro x hx
      exact hmap x (by simpa using hx)
    · intro x hx y hy hxy
      exact add_left_cancel hxy
  have hpart : (subgroupElems H).card + (subgroupCompl H).card = Fintype.card G := by
    unfold subgroupElems subgroupCompl
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x => x ∈ H)
    have hu : (Finset.univ : Finset G).card = Fintype.card G := Finset.card_univ
    rw [hu] at h
    exact h
  omega

/-- At least half the elements of a finite group lie outside a proper additive subgroup. See
[Kedlaya2006]. -/
theorem more_than_half_outside {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (hH : H ≠ ⊤) :
    Fintype.card G ≤ 2 * (subgroupCompl H).card := by
  classical
  have h := proper_addSubgroup_card_le_half H hH
  have hpart : (subgroupElems H).card + (subgroupCompl H).card = Fintype.card G := by
    unfold subgroupElems subgroupCompl
    have h' := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (p := fun x => x ∈ H)
    have hu : (Finset.univ : Finset G).card = Fintype.card G := Finset.card_univ
    rw [hu] at h'
    exact h'
  omega

/-- A finite superset of a generating set also generates the whole additive group. -/
theorem addSubgroup_closure_mono {G : Type*} [AddCommGroup G]
    {S T : Finset G} (hsub : S ⊆ T)
    (hgen : AddSubgroup.closure (S : Set G) = ⊤) :
    AddSubgroup.closure (T : Set G) = ⊤ := by
  have hle : AddSubgroup.closure (S : Set G) ≤ AddSubgroup.closure (T : Set G) :=
    AddSubgroup.closure_mono (by
      intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      exact hsub hx)
  rw [hgen] at hle
  exact top_le_iff.mp hle

/-- The set of all elements generates the whole finite additive group. -/
theorem addSubgroup_closure_univ {G : Type*} [AddCommGroup G] [Fintype G] :
    AddSubgroup.closure ((Finset.univ : Finset G) : Set G) = ⊤ := by
  rw [Finset.coe_univ, AddSubgroup.closure_univ]

/-- **Statement only — not proved in Qatlib.** Generating-set sampling with a
uniform step bound, relative to supplied primitive semantics and a family of
finite groups. The relation of those groups to curve class groups is external.
Initialization/decoding costs follow the supplied machine convention. -/
def lemma10_generating_algorithm_statement
    (G : CurveData → Type) [∀ C, AddCommGroup (G C)] [∀ C, Fintype (G C)]
    (M : ∀ C, PrimitiveMachine Unit (Finset (G C))) (logq : CurveData → ℕ) : Prop :=
  ∃ (program : ∀ C, List (M C).Step) (c k : ℕ), ∀ C,
    16 * (C.g : ℝ) < halfPower C.q 1 →
    ((M C).algorithm () (program C)).IsMC
      (fun T => AddSubgroup.closure (T : Set (G C)) = ⊤) ∧
    ((M C).algorithm () (program C)).cost ≤ c * (C.g + logq C + 1) ^ k

end Qatlib.Papers.ZetaCurves04.MainResults.Lemma10
