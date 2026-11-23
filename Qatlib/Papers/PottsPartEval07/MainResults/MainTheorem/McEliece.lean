/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.ScalarPeriod

@[expose] public section

/-!
# Derived McEliece identity for actual subgroup trace coordinates

The formula is proved from trace orthogonality, the scalar-coordinate
multiplication homomorphism and annihilator duality. The Gauss sums and
coefficients are actual field characters; the weight formula is a conclusion.
The annihilator's actual index replaces an unproved numerical parameter.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped Classical BigOperators
open Qatlib.Papers.PottsPartEval07.CodeStructure
open Qatlib.Papers.PottsPartEval07.ExactRecovery

variable {F : Type*} [Field F] [Fintype F]
  [Algebra (ZMod (ringChar F)) F] [Fact (ringChar F).Prime]

/-- Nondegeneracy constructs an actual preimage for every prime-field trace value. -/
theorem trace_surjective : Function.Surjective (Algebra.trace (ZMod (ringChar F)) F) := by
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F (a := 1) one_ne_zero
  simp only [one_mul] at hb
  intro value
  refine ⟨(value / Algebra.trace (ZMod (ringChar F)) F b) • b, ?_⟩
  rw [map_smul]
  change (value / Algebra.trace (ZMod (ringChar F)) F b) *
    Algebra.trace (ZMod (ringChar F)) F b = value
  exact div_mul_cancel₀ value hb

/-- A primitive prime-field character gives a nontrivial actual trace character. -/
theorem trace_char_ne (additive : AddChar (ZMod (ringChar F)) ℂ)
    (ha : additive.IsPrimitive) : traceAddChar additive ≠ 1 := by
  have hbase : additive ≠ 1 := by
    have h := ha (a := 1) one_ne_zero
    simpa only [AddChar.mulShift_one] using h
  obtain ⟨value, hv⟩ := AddChar.ne_one_iff.mp hbase
  obtain ⟨x, hx⟩ := trace_surjective (F := F) value
  apply AddChar.ne_one_iff.mpr
  refine ⟨x, ?_⟩
  change additive (Algebra.trace (ZMod (ringChar F)) F x) ≠ 1
  rwa [hx]

/-- Scalar-coordinate products contain the actual coordinate subgroup. -/
theorem scalar_contains (subgroup : Subgroup Fˣ) : subgroup ≤ scalarGroup subgroup := by
  intro u hu
  refine ⟨(1, ⟨u, hu⟩), ?_⟩
  simp [scalarOrbit]

/-- The actual Gauss-character count is bounded by the actual coordinate subgroup index. -/
theorem gauss_index_le (subgroup : Subgroup Fˣ) :
    Nat.card (gaussAnn (scalarGroup subgroup)) ≤ subgroup.index := by
  rw [Nat.card_eq_fintype_card, ann_card, ← Subgroup.index_eq_card]
  exact Subgroup.index_antitone (scalar_contains subgroup)

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- The actual trace-word Hamming weight equals the derived nontrivial Gauss spectrum. -/
theorem mceliece_identity (subgroup : Subgroup Fˣ) (coordinate : E ≃ subgroup)
    (additive : AddChar (ZMod (ringChar F)) ℂ) (ha : additive.IsPrimitive)
    (parameter : F) (hp : parameter ≠ 0) :
    (ringChar F : ℂ) * (Nat.card (gaussAnn (scalarGroup subgroup)) : ℂ) *
        (hammingWeight (traceWord (fun e => ((coordinate e : Fˣ) : F)) parameter) : ℂ) =
      (Nat.card (scalarOrbit subgroup).ker : ℂ) *
        ((Fintype.card F : ℂ) - ∑ character : annActive (scalarGroup subgroup),
          (character.val.val parameter)⁻¹ *
            Qatlib.Papers.PottsPartEval07.GaussAlgorithm.gaussSum character.val.val
              (traceAddChar additive) 1) := by
  let group := scalarGroup subgroup
  let d := Nat.card (gaussAnn group)
  let fiber := Nat.card (scalarOrbit subgroup).ker
  have hdindex : d = group.index := by
    rw [show d = Nat.card (gaussAnn group) from rfl, Nat.card_eq_fintype_card,
      ann_card, Subgroup.index_eq_card]
  have hdcard : d * Nat.card group = Fintype.card F - 1 := by
    calc
      _ = group.index * Nat.card group := congrArg (fun n => n * Nat.card group) hdindex
      _ = Nat.card Fˣ := group.index_mul_card
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hfcard : fiber * Nat.card group = (ringChar F - 1) * Fintype.card E := by
    rw [show fiber = Nat.card (scalarOrbit subgroup).ker from rfl, scalar_card,
      Nat.card_congr coordinate.symm, Nat.card_eq_fintype_card]
  have hmul : d * ((ringChar F - 1) * Fintype.card E) = fiber * (Fintype.card F - 1) := by
    calc
      _ = d * (fiber * Nat.card group) := by rw [hfcard]
      _ = fiber * (d * Nat.card group) := by ring
      _ = _ := by rw [hdcard]
  have hq : 1 ≤ ringChar F := (Fact.out : (ringChar F).Prime).one_le
  have hQ : 1 ≤ Fintype.card F := Fintype.card_pos
  have hmulC := congrArg (fun n : ℕ => (n : ℂ)) hmul
  simp only [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_sub hQ, Nat.cast_one] at hmulC
  have hw := trace_orbit_sum subgroup coordinate additive ha parameter
  have hperiod := period_spectrum group (traceAddChar additive) (trace_char_ne additive ha)
    parameter hp
  rw [← Nat.card_eq_fintype_card] at hperiod
  change (ringChar F : ℂ) * (d : ℂ) *
      (hammingWeight (traceWord (fun e => ((coordinate e : Fˣ) : F)) parameter) : ℂ) = _
  linear_combination (d : ℂ) * hw - (fiber : ℂ) * hperiod + hmulC

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
