/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram

/-!
# Collision laws for uniform linear hashes

This module computes collision probabilities for uniformly sampled linear-response matrices. It
proves the prime-alphabet law `pair_collision` and the general image-cardinality formula
`pair_collision_general`, with a binary upper bound valid for distinct databases; these provide
precise sampling laws for the random-code construction of [TerhalSmolin1998].

## Main statements

* `pair_collision_general`: The collision probability equals the reciprocal of the `m`th power
  of the response-image cardinality, giving the general-alphabet linear-hash law relevant to
  [TerhalSmolin1998].
* `pair_collision_le_binary`: For distinct databases, the collision probability under a uniform
  generator matrix is at most `1 / 2^m`.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.RandomHashLaw

open LinearCodeProgram

/-- For a surjective homomorphism of finite abelian groups, a uniformly sampled input maps to
zero with probability equal to the reciprocal of the target cardinality. -/
theorem uniform_zero_fiber {G H : Type} [Fintype G] [Fintype H]
    [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype' G).toOuterMeasure {g | f g = 0} = (1:ENNReal) / Fintype.card H := by
  classical
  let e : G ≃ H × f.ker := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fun h => AddMonoidHom.fiberEquivKerOfSurjective hf h)).trans
      (Equiv.sigmaEquivProd H f.ker))
  have hc : Fintype.card G = Fintype.card H * Fintype.card f.ker := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  rw [PMF.toOuterMeasure_uniformOfFintype'_apply]
  have hk : Fintype.card {g : G | f g = 0} = Fintype.card f.ker :=
    Fintype.card_congr (Equiv.refl _)
  rw [hk]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_one]
  rw [hc]
  push_cast
  have hH : (Fintype.card H:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK : (Fintype.card f.ker:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

variable {A m n : ℕ} [NeZero A]

/-- The additive homomorphism sending a generator matrix to its response vector on `d`. -/
def responseHom (d : Fin n → ZMod A) :
    (Fin m → Fin n → ZMod A) →+ (Fin m → ZMod A) where
  toFun g := response g d
  map_zero' := by ext i; simp [response, answer]
  map_add' g h := by ext i; simp [response, answer, add_mul, Finset.sum_add_distrib]

omit [NeZero A] in

/-- Over a prime alphabet, every response vector can be realized by a generator matrix when `d`
is nonzero. -/
theorem responseHom_surjective [Fact (Nat.Prime A)] (d : Fin n → ZMod A) (hd : d ≠ 0) :
    Function.Surjective (responseHom (m:=m) d) := by
  classical
  have hex : ∃ j, d j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hd (funext h)
  obtain ⟨j,hj⟩ := hex
  intro z
  refine ⟨fun i => Pi.single j (z i / d j), ?_⟩
  ext i
  simp [responseHom, response, answer, Pi.single_apply, ite_mul, hj]

omit [NeZero A] in

/-- Two databases have equal responses exactly when the response homomorphism of their
difference vanishes on the generator matrix. -/
theorem responses_equal_iff (g : Fin m → Fin n → ZMod A) (y y' : Fin n → ZMod A) :
    response g y = response g y' ↔ responseHom (y-y') g = 0 := by
  have he : responseHom (y-y') g = response g y - response g y' := by
    ext i
    simp [responseHom, response, answer, mul_sub, Finset.sum_sub_distrib]
  rw [he, sub_eq_zero]

/-- The uniform distribution on generator matrices over `ZMod A`. -/
noncomputable def matrixLaw (A m n : ℕ) [NeZero A] : PMF (Fin m → Fin n → ZMod A) :=
  PMF.uniformOfFintype' _

/-- For distinct databases over a prime alphabet, a uniform generator matrix produces equal
responses with probability `1 / A^m`. -/
theorem pair_collision [Fact (Nat.Prime A)] (y y' : Fin n → ZMod A) (hne : y ≠ y') :
    (matrixLaw A m n).toOuterMeasure {g | response g y = response g y'} =
      (1:ENNReal) / A^m := by
  have he : {g : Fin m → Fin n → ZMod A | response g y = response g y'} =
      {g | responseHom (y-y') g = 0} := by
    ext g
    exact responses_equal_iff g y y'
  rw [he, matrixLaw, uniform_zero_fiber _
    (responseHom_surjective (y-y') (sub_ne_zero.mpr hne))]
  simp

/-- The additive subgroup consisting of all dot-product responses against `d`. -/
abbrev ResponseImage (d : Fin n → ZMod A) := (FourierReadout.dotHom d).range

/-- The additive homomorphism sending each generator row to its dot product with `d`, regarded
as an element of `ResponseImage d`. -/
def imageResponseHom (d : Fin n → ZMod A) :
    (Fin m → Fin n → ZMod A) →+ (Fin m → ResponseImage d) where
  toFun g i := ⟨FourierReadout.dotHom d (g i), ⟨g i,rfl⟩⟩
  map_zero' := by ext i; simp
  map_add' g h := by ext i; simp

/-- Every vector of values in `ResponseImage d` is realized by some generator matrix. -/
theorem imageResponseHom_surjective (d : Fin n → ZMod A) :
    Function.Surjective (imageResponseHom (m:=m) d) := by
  classical
  intro z
  refine ⟨fun i => Classical.choose (z i).property, ?_⟩
  ext i
  exact Classical.choose_spec (z i).property

/-- The dot-product response image of a nonzero vector has at least two elements. -/
theorem image_card_ge_two (d : Fin n → ZMod A) (hd : d ≠ 0) :
    2 ≤ Fintype.card (ResponseImage d) := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hd (funext h)
  let a : ResponseImage d := ⟨d j, ⟨Pi.single j 1, by
    simp [FourierReadout.dotHom, Pi.single_apply, ite_mul]⟩⟩
  have ha : a ≠ 0 := by
    intro h
    exact hj (congrArg Subtype.val h)
  letI : Nontrivial (ResponseImage d) := ⟨⟨a,0,ha⟩⟩
  exact Fintype.one_lt_card

/-- Two databases have equal responses exactly when their difference has zero image-valued
response. -/
theorem equal_iff_image_zero (g : Fin m → Fin n → ZMod A) (y y' : Fin n → ZMod A) :
    response g y = response g y' ↔ imageResponseHom (y-y') g = 0 := by
  rw [responses_equal_iff]
  constructor
  · intro h
    ext i
    exact congrFun h i
  · intro h
    funext i
    exact congrArg Subtype.val (congrFun h i)

/-- The collision probability equals the reciprocal of the `m`th power of the response-image
cardinality, giving the general-alphabet linear-hash law relevant to [TerhalSmolin1998]. -/
theorem pair_collision_general (y y' : Fin n → ZMod A) :
    (matrixLaw A m n).toOuterMeasure {g | response g y = response g y'} =
      (1:ENNReal) / (Fintype.card (ResponseImage (y-y')))^m := by
  have he : {g : Fin m → Fin n → ZMod A | response g y = response g y'} =
      {g | imageResponseHom (y-y') g = 0} := by
    ext g
    exact equal_iff_image_zero g y y'
  rw [he, matrixLaw, uniform_zero_fiber _ (imageResponseHom_surjective (y-y'))]
  simp

/-- For distinct databases, the collision probability under a uniform generator matrix is at
most `1 / 2^m`. -/
theorem pair_collision_le_binary (y y' : Fin n → ZMod A) (hne : y ≠ y') :
    (matrixLaw A m n).toOuterMeasure {g | response g y = response g y'} ≤
      (1:ENNReal)/2^m := by
  rw [pair_collision_general]
  apply ENNReal.div_le_div_left
  exact pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast image_card_ge_two (y-y') (sub_ne_zero.mpr hne)) m

end Qatlib.Papers.SingleQuery97.MainResults.RandomHashLaw
