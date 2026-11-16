/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
public import Mathlib.Data.Finset.Powerset

@[expose] public section


/-! # Actual collision-free occupations and fixed-size mode subsets

The occupation type and collision predicate are unchanged. The maps record
the modes occupied once and reconstruct their actual zero-one counts.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.BosonFock.BosonOperators.FockFree
open Qatlib.Concepts.BosonFock.BosonOperators

/-- A genuinely collision-free occupation has every mode count at most one. -/
theorem freeBound {m n : ℕ} (S : ↥(collisionFreeFock m n)) (i : Fin m) :
    (S.1.1 i : ℕ) ≤ 1 := (Finset.mem_filter.mp S.2).2 i

/-- The modes occupied once form a subset with exactly the actual particle number. -/
def freeSet {m n : ℕ} (S : ↥(collisionFreeFock m n)) :
    {t : Finset (Fin m) // t.card = n} :=
  ⟨Finset.univ.filter (fun i => (S.1.1 i : ℕ) = 1), by
    have he : (∑ i : Fin m, if (S.1.1 i : ℕ) = 1 then (1 : ℕ) else 0) = n := by
      calc
        _ = ∑ i : Fin m, (S.1.1 i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          have hi := freeBound S i
          split_ifs <;> omega
        _ = n := S.1.2
    simpa using he⟩

/-- A size-n mode subset defines an actual zero-one occupation, including the empty sector. -/
def setOcc {m n : ℕ} (t : {t : Finset (Fin m) // t.card = n}) : FockOccupation m n :=
  ⟨fun i => ⟨if i ∈ t.1 then 1 else 0, by
    split_ifs with hi
    · have hp := Finset.card_pos.mpr ⟨i, hi⟩
      rw [t.2] at hp
      omega
    · omega⟩, by
      simpa using t.2⟩

/-- The occupation reconstructed from a subset satisfies the genuine collision-free predicate. -/
theorem setFree {m n : ℕ} (t : {t : Finset (Fin m) // t.card = n}) :
    setOcc t ∈ collisionFreeFock m n := by
  simp only [collisionFreeFock, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  change (if i ∈ t.1 then 1 else 0 : ℕ) ≤ 1
  split_ifs <;> omega

/-- Reading the occupied modes and reconstructing their counts recovers the entire occupation. -/
theorem setOfFree {m n : ℕ} (S : ↥(collisionFreeFock m n)) : setOcc (freeSet S) = S.1 := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (if i ∈ (freeSet S).1 then 1 else 0 : ℕ) = (S.1.1 i : ℕ)
  simp only [freeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi := freeBound S i
  split_ifs <;> omega

/-- Reading occupied modes from a reconstructed subset recovers exactly that subset. -/
theorem freeOfSet {m n : ℕ} (t : {t : Finset (Fin m) // t.card = n}) :
    freeSet ⟨setOcc t, setFree t⟩ = t := by
  apply Subtype.ext
  ext i
  simp [freeSet, setOcc]

/-- Genuine collision-free occupations are equivalent to subsets of modes of the same size. -/
def freeEquiv (m n : ℕ) : ↥(collisionFreeFock m n) ≃ {t : Finset (Fin m) // t.card = n} where
  toFun := freeSet
  invFun := fun t => ⟨setOcc t, setFree t⟩
  left_inv := fun S => Subtype.ext (setOfFree S)
  right_inv := freeOfSet

/-- Size-n mode subsets are exactly the actual n-element powerset of all modes. -/
def sizeEquiv (m n : ℕ) : {t : Finset (Fin m) // t.card = n} ≃
    ↥(Finset.univ.powersetCard n : Finset (Finset (Fin m))) where
  toFun := fun t => ⟨t.1, by simp [t.2]⟩
  invFun := fun t => ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The actual number of collision-free occupations is the binomial coefficient of the mode count. -/
theorem freeCard (m n : ℕ) : (collisionFreeFock m n).card = m.choose n := by
  have he := Fintype.card_congr ((freeEquiv m n).trans (sizeEquiv m n))
  simpa only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using he

end Qatlib.Concepts.BosonFock.BosonOperators.FockFree
