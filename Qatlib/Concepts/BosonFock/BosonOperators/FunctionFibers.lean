/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section


/-! # Actual assignment functions with collision-free initial-mode fibers

Demand: LinearOptics10 Lemma 21. A function on n photon positions has one
preimage in each initial mode and none elsewhere exactly when it is a
permutation followed by the inclusion Fin n into Fin m.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.BosonFock.BosonOperators.FunctionFibers

/-- The genuine fiber counts of the first n distinct occupied modes. -/
def SingleFibers {m n : ℕ} (f : Fin n → Fin m) : Prop :=
  ∀ i, (Finset.univ.filter (fun k => f k = i)).card = if i.val < n then 1 else 0

/-- Every value with a nonempty required fiber lies among the first n modes. -/
theorem smallRange {m n : ℕ} {f : Fin n → Fin m} (hf : SingleFibers f) (k : Fin n) :
    (f k).val < n := by
  by_contra h
  have hz := hf (f k)
  rw [ite_eq_right h] at hz
  have hp : 0 < (Finset.univ.filter (fun t => f t = f k)).card :=
    Finset.card_pos.mpr ⟨k, by simp⟩
  omega

/-- One preimage per occupied mode makes the actual assignment injective. -/
theorem fiberInjective {m n : ℕ} {f : Fin n → Fin m} (hf : SingleFibers f) :
    Function.Injective f := by
  intro a b hab
  have hc : (Finset.univ.filter (fun t => f t = f a)).card ≤ 1 := by
    rw [hf (f a), ite_eq_left (smallRange hf a)]
  exact (Finset.card_le_one.mp hc) a (by simp) b (by simp [hab])

/-- The actual permutation obtained by restricting a collision-free assignment to its range. -/
def asPerm {m n : ℕ} (f : Fin n → Fin m) (hf : SingleFibers f) : Equiv.Perm (Fin n) :=
  let g : Fin n → Fin n := fun k => ⟨(f k).val, smallRange hf k⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply fiberInjective hf
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) hab
  Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,rfl⟩)

/-- Lifting the constructed true permutation recovers every original assignment value. -/
theorem liftPerm {m n : ℕ} (h : n ≤ m) (f : Fin n → Fin m) (hf : SingleFibers f)
    (k : Fin n) : Fin.castLE h (asPerm f hf k) = f k := by
  apply Fin.ext
  rfl

/-- Every actual lifted permutation has exactly the required collision-free mode fibers. -/
theorem permFibers {m n : ℕ} (h : n ≤ m) (sigma : Equiv.Perm (Fin n)) :
    SingleFibers (fun k => Fin.castLE h (sigma k)) := by
  intro i
  by_cases hi : i.val < n
  · let q : Fin n := ⟨i.val,hi⟩
    have he : (Finset.univ.filter (fun k => Fin.castLE h (sigma k) = i)) =
        {sigma.symm q} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        apply sigma.injective
        rw [sigma.apply_symm_apply]
        apply Fin.ext
        exact congrArg (fun x : Fin m => x.val) hk
      · rintro rfl
        apply Fin.ext
        simp [q]
    rw [he, Finset.card_singleton, ite_eq_left hi]
  · have he : (Finset.univ.filter (fun k => Fin.castLE h (sigma k) = i)) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hk
      apply hi
      have hv := congrArg Fin.val hk
      exact hv ▸ (sigma k).isLt
    rw [he, Finset.card_empty, ite_eq_right hi]

/-- Lifted permutations and actual admissible photon assignments are equivalent finite types. -/
def fiberEquiv {m n : ℕ} (h : n ≤ m) :
    Equiv.Perm (Fin n) ≃ {f : Fin n → Fin m // SingleFibers f} where
  toFun sigma := ⟨fun k => Fin.castLE h (sigma k), permFibers h sigma⟩
  invFun f := asPerm f.val f.property
  left_inv sigma := by
    apply Equiv.ext
    intro k
    apply Fin.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    funext k
    exact liftPerm h f.val f.property k

/-- Summing any actual complex assignment weight over the required fibers is an actual permutation sum. -/
theorem weightedSum {m n : ℕ} (h : n ≤ m) (w : (Fin n → Fin m) → ℂ) :
    (∑ sigma : Equiv.Perm (Fin n), w (fun k => Fin.castLE h (sigma k))) =
      ∑ f : Fin n → Fin m, if SingleFibers f then w f else 0 := by
  classical
  calc
    _ = ∑ f : {f : Fin n → Fin m // SingleFibers f}, w f.val := by
      exact Fintype.sum_equiv (fiberEquiv h) _ _ (fun _ => rfl)
    _ = ∑ f ∈ Finset.univ.filter SingleFibers, w f := by
      exact (Finset.sum_subtype _ (fun f => by simp) w).symm
    _ = _ := by rw [Finset.sum_filter]

end Qatlib.Concepts.BosonFock.BosonOperators.FunctionFibers
