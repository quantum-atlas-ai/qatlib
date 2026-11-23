/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.GaussAlgorithm.GaussKickback
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.GaussSum

@[expose] public section

/-!
# Character orthogonality for actual multiplicative Gauss periods

This is the finite harmonic-analysis step in the McEliece weight formula.
The annihilator contains exactly the actual multiplicative characters that
are trivial on the supplied field subgroup. Their sum derives its indicator;
no weight formula or desired final output is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The actual character subgroup dual to the field's multiplicative subgroup. -/
def gaussAnn (subgroup : Subgroup Fˣ) : Subgroup (MulChar F ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ subgroup).ofDual

noncomputable instance annFintype (subgroup : Subgroup Fˣ) : Fintype (gaussAnn subgroup) :=
  Fintype.ofFinite _

/-- Characters in the actual annihilator separate every point outside the subgroup. -/
theorem ann_separates (subgroup : Subgroup Fˣ) (u : Fˣ) :
    (∀ character : gaussAnn subgroup, (character : MulChar F ℂ) u = 1) ↔ u ∈ subgroup := by
  have h := MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff
    (M := F) (R := ℂ) (X := gaussAnn subgroup) (m := u)
  simpa only [gaussAnn, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply,
    Subtype.forall] using h.symm

/-- Summing the actual annihilator characters gives its derived subgroup indicator. -/
theorem ann_sum (subgroup : Subgroup Fˣ) (u : Fˣ) :
    (∑ character : gaussAnn subgroup, (character : MulChar F ℂ) u) =
      if u ∈ subgroup then (Fintype.card (gaussAnn subgroup) : ℂ) else 0 := by
  classical
  let evaluate : gaussAnn subgroup →* ℂ :=
    { toFun := fun character => (character : MulChar F ℂ) u
      map_one' := by simp
      map_mul' := by intro a b; simp }
  have he : evaluate = 1 ↔ u ∈ subgroup := by
    rw [← ann_separates subgroup u]
    constructor
    · intro h character
      exact congrArg (fun map : gaussAnn subgroup →* ℂ => map character) h
    · intro h
      ext character
      exact h character
  change (∑ character : gaussAnn subgroup, evaluate character) = _
  rw [sum_hom_units, he]
  simp only [Nat.cast_ite, Nat.cast_zero]

/-- The number of actual annihilator characters is the actual multiplicative subgroup index. -/
theorem ann_card (subgroup : Subgroup Fˣ) :
    Fintype.card (gaussAnn subgroup) = Nat.card (Fˣ ⧸ subgroup) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

/-- Field elements are exactly zero or an actual multiplicative unit. -/
def fieldUnits : Option Fˣ ≃ F where
  toFun
    | none => 0
    | some u => u
  invFun x := if hx : x = 0 then none else some (Units.mk0 x hx)
  left_inv record := by
    cases record with
    | none => simp
    | some u => simp [Units.ne_zero]
  right_inv x := by
    by_cases hx : x = 0 <;> simp [hx]

/-- A finite field sum whose zero term vanishes is exactly the sum over actual units. -/
theorem field_unit_sum (value : F → ℂ) (hz : value 0 = 0) :
    (∑ x : F, value x) = ∑ u : Fˣ, value u := by
  have h := Equiv.sum_comp (fieldUnits (F := F)) value
  rw [Fintype.sum_option] at h
  change value 0 + (∑ u : Fˣ, value u) = ∑ x : F, value x at h
  rw [hz, zero_add] at h
  exact h.symm

/-- The actual subgroup additive period equals the derived sum of actual Gauss sums. -/
theorem period_gauss (subgroup : Subgroup Fˣ) (additive : AddChar F ℂ) (parameter : F) :
    (Fintype.card (gaussAnn subgroup) : ℂ) *
        (∑ u : subgroup, additive (parameter * (u : Fˣ))) =
      ∑ character : gaussAnn subgroup,
        Qatlib.Papers.PottsPartEval07.GaussAlgorithm.gaussSum character.val additive parameter := by
  symm
  unfold Qatlib.Papers.PottsPartEval07.GaussAlgorithm.gaussSum
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [field_unit_sum _ (by simp only [MulChar.map_zero, Finset.sum_const_zero, zero_mul])]
  simp_rw [ann_sum]
  have hind : ∀ u : Fˣ,
      (if u ∈ subgroup then (Fintype.card (gaussAnn subgroup) : ℂ) else 0) *
        additive (parameter * u) =
      (Fintype.card (gaussAnn subgroup) : ℂ) *
        (if u ∈ subgroup then additive (parameter * u) else 0) := by
    intro u
    split_ifs <;> simp
  simp_rw [hind]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The nontrivial Gauss queries are the actual nonidentity annihilator characters. -/
def annActive (subgroup : Subgroup Fˣ) := {character : gaussAnn subgroup // character ≠ 1}

noncomputable instance activeFintype (subgroup : Subgroup Fˣ) : Fintype (annActive subgroup) := by
  unfold annActive
  infer_instance

/-- Removing the known trivial Gauss sum leaves only actual nontrivial query terms. -/
theorem period_spectrum (subgroup : Subgroup Fˣ) (additive : AddChar F ℂ)
    (ha : additive ≠ 1) (parameter : F) (hp : parameter ≠ 0) :
    (Fintype.card (gaussAnn subgroup) : ℂ) *
        (∑ u : subgroup, additive (parameter * (u : Fˣ))) =
      -1 + ∑ character : annActive subgroup,
        (character.val.val parameter)⁻¹ *
          Qatlib.Papers.PottsPartEval07.GaussAlgorithm.gaussSum character.val.val additive 1 := by
  rw [period_gauss]
  let value : gaussAnn subgroup → ℂ := fun character =>
    Qatlib.Papers.PottsPartEval07.GaussAlgorithm.gaussSum character.val additive parameter
  have hsplit : (∑ character : gaussAnn subgroup, value character) =
      value 1 + ∑ character : annActive subgroup, value character.val := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : gaussAnn subgroup)), add_comm]
    congr 1
    exact Finset.sum_subtype _ (by simp) _
  change (∑ character : gaussAnn subgroup, value character) = _
  rw [hsplit]
  have htrivial : value 1 = -1 := by
    change _root_.gaussSum (1 : MulChar F ℂ) (additive.mulShift parameter) = -1
    exact gaussSum_one_left ((AddChar.IsPrimitive.of_ne_one ha) hp)
  rw [htrivial]
  congr 1
  apply Finset.sum_congr rfl
  intro character _
  simpa only [one_mul] using
    Qatlib.Papers.PottsPartEval07.GaussAlgorithm.gaussSum_mul_right
      character.val.val additive 1 parameter hp

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
