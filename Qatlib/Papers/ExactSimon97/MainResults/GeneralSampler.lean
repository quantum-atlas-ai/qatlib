/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Uniform Fourier sampling on finite abelian annihilators

The coordinate character pairing identifies a product of finite cyclic groups with its additive
character group. Under this identification, Fourier measurement of a normalized coset state is
uniform on `annihilatorGen H`. The development follows [BrassardHoyer1997].

## Main statements

* `charPairEquiv`: identifies group elements with all additive characters.
* `card_annihilatorGen_mul`: relates annihilator, subgroup, and ambient cardinalities.
* `bornProb_genCosetState_uniform`: computes the uniform annihilator distribution.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Classical
open Finset

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ExactSimon97.MainResults

variable {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]

/-- The additive character obtained by fixing the first argument of `charPair`. -/
def charPairChar (g : AbGroup n m) : AddChar (AbGroup n m) ℂ where
  toFun := fun h => charPair (m := m) g h
  map_zero_eq_one' := by simp [charPair]
  map_add_eq_mul' := by
    intro h h'
    exact charPair_add_right (m := m) g h h'

/-- Evaluating `charPairChar g` at `h` gives `charPair g h`. -/
@[simp] theorem charPairChar_apply (g h : AbGroup n m) :
    charPairChar (m := m) g h = charPair (m := m) g h := rfl

/-- Pairing with the vector supported at coordinate `i` with value one extracts the standard
additive character of `g i`. -/
theorem charPair_single (g : AbGroup n m) (i : Fin n) :
    charPair (m := m) g (Pi.single i (1 : ZMod (m i))) = ZMod.stdAddChar (g i) := by
  simp only [charPair]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Distinct group elements define distinct additive characters through `charPairChar`. -/
theorem charPairChar_injective : Function.Injective (fun g : AbGroup n m => charPairChar (m := m) g) := by
  intro g g' h
  funext i
  have hh := DFunLike.congr_fun h (Pi.single i (1 : ZMod (m i)))
  simp only [charPairChar_apply, charPair_single] at hh
  exact ZMod.injective_stdAddChar hh

/-- The additive character group has the same finite cardinality as the product of cyclic
groups. -/
theorem character_card :
    Fintype.card (AddChar (AbGroup n m) ℂ) = Fintype.card (AbGroup n m) := by
  have h := card_characterAnnihilator (⊥ : AddSubgroup (AbGroup n m))
  have hbot : Fintype.card (⊥ : AddSubgroup (AbGroup n m)) = 1 := by simp
  have h' : Fintype.card (characterAnnihilator (⊥ : AddSubgroup (AbGroup n m))) =
      Fintype.card (AbGroup n m) := by
    simpa [hbot] using h
  have hall : characterAnnihilator (⊥ : AddSubgroup (AbGroup n m)) = ⊤ := by
    ext χ
    rw [mem_characterAnnihilator]
    simp
  rw [hall] at h'
  simpa using h'

/-- The equivalence identifying each element of the product of cyclic groups with its character
under `charPair`. See [BrassardHoyer1997]. -/
noncomputable def charPairEquiv : AbGroup n m ≃ AddChar (AbGroup n m) ℂ :=
  Equiv.ofBijective (fun g => charPairChar (m := m) g)
    ((Fintype.bijective_iff_injective_and_card (fun g => charPairChar (m := m) g)).mpr
      ⟨charPairChar_injective, (character_card).symm⟩)

/-- The character equivalence sends `g` to `charPairChar g`. -/
@[simp] theorem charPairEquiv_apply (g : AbGroup n m) :
    charPairEquiv (m := m) g = charPairChar (m := m) g := rfl

/-- The subgroup of labels whose associated characters are trivial on `H`. -/
def annihilatorGen (H : AddSubgroup (AbGroup n m)) : AddSubgroup (AbGroup n m) where
  carrier := {g | charPairChar (m := m) g ∈ characterAnnihilator H}
  zero_mem' := by
    rw [Set.mem_setOf_eq, mem_characterAnnihilator]
    intro h
    simp [charPair]
  add_mem' := by
    intro g g' hg hg'
    rw [Set.mem_setOf_eq, mem_characterAnnihilator] at hg hg' ⊢
    intro h
    change charPair (m := m) (g + g') h = 1
    rw [charPair_add_left]
    have h1 : charPair (m := m) g ↑h = 1 := hg h
    have h2 : charPair (m := m) g' ↑h = 1 := hg' h
    rw [h1, h2, one_mul]
  neg_mem' := by
    intro g hg
    rw [Set.mem_setOf_eq, mem_characterAnnihilator] at hg ⊢
    intro h
    change charPair (m := m) (-g) h = 1
    have hneg : charPair (m := m) (-g) h = (charPair (m := m) g h)⁻¹ := by
      simp only [charPair, Pi.neg_apply, neg_mul, AddChar.map_neg_eq_inv,
        Finset.prod_inv_distrib]
    have h1 : charPair (m := m) g ↑h = 1 := hg h
    rw [hneg, h1, inv_one]

/-- A label lies in `annihilatorGen H` exactly when its associated character lies in the
character annihilator of `H`. -/
theorem mem_annihilatorGen {H : AddSubgroup (AbGroup n m)} {g : AbGroup n m} :
    g ∈ annihilatorGen H ↔ charPairChar (m := m) g ∈ characterAnnihilator H := Iff.rfl

/-- The equivalence between annihilator labels and the character annihilator of `H`. -/
noncomputable def annihilatorEquiv (H : AddSubgroup (AbGroup n m)) :
    annihilatorGen H ≃ characterAnnihilator H :=
  Equiv.subtypeEquiv (charPairEquiv (m := m)) (fun _ => Iff.rfl)

/-- The subgroup of annihilator labels has the same cardinality as the character annihilator. -/
theorem card_annihilatorGen (H : AddSubgroup (AbGroup n m)) :
    Fintype.card (annihilatorGen H) = Fintype.card (characterAnnihilator H) :=
  Fintype.card_congr (annihilatorEquiv H)

/-- The cardinality of the annihilator-label subgroup times `|H|` equals the ambient group
cardinality. See [BrassardHoyer1997]. -/
theorem card_annihilatorGen_mul (H : AddSubgroup (AbGroup n m)) :
    Fintype.card (annihilatorGen H) * Fintype.card H = Fintype.card (AbGroup n m) := by
  rw [card_annihilatorGen]
  exact card_characterAnnihilator H

/-- The coordinate Fourier transform agrees with `abelianQFT` evaluated at the associated
character. See [BrassardHoyer1997]. -/
theorem FG_eq_abelianQFT (f : AbGroup n m → ℂ) (g : AbGroup n m) :
    FG (m := m) f g = abelianQFT f (charPairChar (m := m) g) := by
  simp only [FG, abelianQFT, abelianQFTMatrix, Matrix.mulVec, dotProduct,
    charPairChar_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Fourier measurement of a coset state has probability `|H| / |G|` on annihilator labels and
zero elsewhere. See [BrassardHoyer1997]. -/
theorem bornProb_genCosetState (H : AddSubgroup (AbGroup n m)) (s : AbGroup n m)
    (g : AbGroup n m) :
    BornProb (FG (m := m) (abelianCosetState H s)) g =
      if g ∈ annihilatorGen H then
        (Fintype.card H : ℝ) / (Fintype.card (AbGroup n m) : ℝ) else 0 := by
  have hψ : FG (m := m) (abelianCosetState H s) =
      fun g => abelianQFT (abelianCosetState H s) (charPairChar (m := m) g) := by
    funext x
    exact FG_eq_abelianQFT _ _
  rw [hψ]
  rw [show BornProb (fun g => abelianQFT (abelianCosetState H s) (charPairChar (m := m) g)) g =
      BornProb (abelianQFT (abelianCosetState H s)) (charPairChar (m := m) g) from rfl]
  rw [bornProb_abelianQFT_cosetState]
  rfl

/-- The ratio `|H| / |G|` equals the reciprocal cardinality of the annihilator-label subgroup. -/
theorem uniform_annihilator (H : AddSubgroup (AbGroup n m)) :
    (Fintype.card H : ℝ) / (Fintype.card (AbGroup n m) : ℝ) =
      1 / (Fintype.card (annihilatorGen H) : ℝ) := by
  have h := card_annihilatorGen_mul H
  have hHpos : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hGpos : (0 : ℝ) < Fintype.card (AbGroup n m) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (AbGroup n m) : ℝ) =
      (Fintype.card (annihilatorGen H) : ℝ) * (Fintype.card H : ℝ) := by
    exact_mod_cast h.symm
  rw [hcard]
  field_simp [ne_of_gt hHpos]

/-- Fourier measurement of a normalized coset state is uniform on the annihilator-label subgroup
and vanishes outside it. See [BrassardHoyer1997]. -/
theorem bornProb_genCosetState_uniform (H : AddSubgroup (AbGroup n m)) (s : AbGroup n m)
    (g : AbGroup n m) :
    BornProb (FG (m := m) (abelianCosetState H s)) g =
      if g ∈ annihilatorGen H then
        1 / (Fintype.card (annihilatorGen H) : ℝ) else 0 := by
  rw [bornProb_genCosetState, uniform_annihilator]

end Qatlib.Papers.ExactSimon97.MainResults
