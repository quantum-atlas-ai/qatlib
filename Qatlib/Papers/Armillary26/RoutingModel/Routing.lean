/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.PermBlocks.Rank
public import Qatlib.Concepts.CodeCert.PermBlocks.Algebra

@[expose] public section

/-!
# Routing: role transport and the additive visit law

Generic routing pieces shared by the Armillary construction: transporting a
bijection through two relabelings, the additive visit law on a round of `M`
groups (each step bijective, complementary steps mutually inverse), and the
entrywise bridge from a routing array to the assembled permutation blocks.

The paper-specific consumer is [Zhang et al., 2026][ZhangArmillary2026],
the frozen unpublished author manuscript identified in the root bibliography.
-/

namespace Qatlib.Papers.Armillary26.RoutingModel

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodeCert.PermBlocks

/-- Transport a bijection through source and target relabelings. -/
def roleMap {α β γ δ : Type*} (f : α ≃ β) (ra : γ ≃ α) (rb : δ ≃ β) : γ ≃ δ :=
  (ra.trans f).trans rb.symm

/-- The transported role map acts by relabel, map, relabel back. -/
theorem roleMap_apply {α β γ δ : Type*} (f : α ≃ β) (ra : γ ≃ α) (rb : δ ≃ β)
    (x : γ) : roleMap f ra rb x = rb.symm (f (ra x)) := rfl

/-- The partner of group `a` at round step `t` under the additive law. -/
def visitAt (M t : ℕ) (a : Fin M) : Fin M :=
  ⟨((a : ℕ) + t) % M, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le (a : ℕ)) a.isLt)⟩

/-- Complementary steps are mutually inverse on groups. -/
theorem visit_comp (M s t : ℕ) (_hM : 0 < M) (hs : s < M) (hst : s + t = M)
    (a : Fin M) :
    visitAt M t (visitAt M s a) = a ∧ visitAt M s (visitAt M t a) = a := by
  have hcase : ∀ x : Fin M, visitAt M t (visitAt M s x) = x := by
    intro x
    by_cases hx : (x : ℕ) + s < M
    · have hinner : ((x : ℕ) + s) % M = (x : ℕ) + s := Nat.mod_eq_of_lt hx
      apply Fin.ext
      simp only [visitAt, Fin.val_mk]
      rw [hinner]
      have hsum : (x : ℕ) + s + t = (x : ℕ) + M := by omega
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt x.isLt
    · have hxM : M ≤ (x : ℕ) + s := by omega
      have hxlt : (x : ℕ) + s < 2 * M := by
        have := x.isLt
        omega
      have hinner : ((x : ℕ) + s) % M = (x : ℕ) + s - M := by
        have h1 : M ≤ (x : ℕ) + s := by omega
        have h2 : (x : ℕ) + s - M < M := by omega
        rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2]
      apply Fin.ext
      simp only [visitAt, Fin.val_mk]
      rw [hinner]
      have hsum : (x : ℕ) + s - M + t = (x : ℕ) := by omega
      rw [hsum]
      exact Nat.mod_eq_of_lt x.isLt
  constructor
  · exact hcase a
  · have hage : (a : ℕ) + t < 2 * M := by
      have := a.isLt
      omega
    rcases Nat.lt_or_ge ((a : ℕ) + t) M with hlt | hge
    · have hinner : ((a : ℕ) + t) % M = (a : ℕ) + t := Nat.mod_eq_of_lt hlt
      apply Fin.ext
      simp only [visitAt, Fin.val_mk]
      rw [hinner]
      have hsum : (a : ℕ) + t + s = (a : ℕ) + M := by omega
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt a.isLt
    · have hinner : ((a : ℕ) + t) % M = (a : ℕ) + t - M := by
        have h1 : M ≤ (a : ℕ) + t := by omega
        have h2 : (a : ℕ) + t - M < M := by omega
        rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2]
      apply Fin.ext
      simp only [visitAt, Fin.val_mk]
      rw [hinner]
      have hsum : (a : ℕ) + t - M + s = (a : ℕ) := by omega
      rw [hsum]
      exact Nat.mod_eq_of_lt a.isLt

/-- Every round step is a bijection on the groups. -/
theorem visit_bij (M t : ℕ) (hM : 0 < M) (ht : t < M) :
    Function.Bijective (visitAt M t) := by
  by_cases ht0 : t = 0
  · subst ht0
    have hid : visitAt M 0 = id := by
      funext a
      apply Fin.ext
      show ((a : ℕ) + 0) % M = (a : ℕ)
      rw [Nat.add_zero]
      exact Nat.mod_eq_of_lt a.isLt
    rw [hid]
    exact Function.bijective_id
  · have hst : t + (M - t) = M := by omega
    have hMt : M - t < M := by omega
    have hcomp := fun x => visit_comp M t (M - t) hM ht hst x
    have hcomp2 := fun x => visit_comp M (M - t) t hM hMt (by omega) x
    refine ⟨fun a b hab => ?_, fun b => ⟨visitAt M (M - t) b, ?_⟩⟩
    · rw [← (hcomp2 a).2, ← (hcomp2 b).2, hab]
    · exact (hcomp2 b).1

/-- Assembled blocks carry the routing permutations entrywise. -/
theorem permBlocks_entry {K ι α β : Type*} [DecidableEq ι] [Field K]
    (σ : α → β → Equiv.Perm ι) (a : α) (b : β) (p q : ι) :
    (permBlocks σ : Matrix (α × ι) (β × ι) K) (a, p) (b, q) = permMat (σ a b) p q := rfl

end Qatlib.Papers.Armillary26.RoutingModel
