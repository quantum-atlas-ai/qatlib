/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLog
import Mathlib.Data.Nat.Choose.Sum
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLie

open scoped BigOperators MonoidAlgebra
open BCHDynkin BCHWordLog

section Exponential
variable {A : Type} [Ring A] [Algebra ℚ A]

def generatorSeries (X : A) : PowerSeries A :=
  PowerSeries.mk (fun n => (n.factorial : ℚ)⁻¹ • X ^ n)

theorem generatorSeries_constant (X : A) : (generatorSeries X).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [generatorSeries, PowerSeries.coeff_mk, Nat.factorial_zero, Nat.cast_one,
    inv_one, pow_zero, one_smul]

theorem generatorSeries_map {B : Type} [Ring B] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) (X : A) :
    PowerSeries.map φ.toRingHom (generatorSeries X) = generatorSeries (φ X) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, generatorSeries, PowerSeries.coeff_mk,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul, map_pow]

theorem factorial_choose (n i j : ℕ) (h : i + j = n) :
    (n.factorial : ℚ)⁻¹ * n.choose i = (i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹ := by
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (n.choose i : ℚ) * i.factorial * j.factorial = n.factorial := by
    have hni : n - i = j := by omega
    exact_mod_cast (by simpa only [hni] using
      (Nat.choose_mul_factorial_mul_factorial (show i ≤ n by omega)))
  field_simp
  nlinarith [he]

theorem generatorSeries_add (X Y : A) (hXY : Commute X Y) :
    generatorSeries (X + Y) = generatorSeries X * generatorSeries Y := by
  apply PowerSeries.ext
  intro n
  simp only [generatorSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [hXY.add_pow', Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    factorial_choose n p.1 p.2 (Finset.mem_antidiagonal.mp hp)]

def wordSeries (xs : List A) : PowerSeries A := (xs.map generatorSeries).prod

theorem wordSeries_map {B : Type} [Ring B] [Algebra ℚ B] (φ : A →ₐ[ℚ] B) (xs : List A) :
    PowerSeries.map φ.toRingHom (wordSeries xs) = wordSeries (xs.map φ) := by
  induction xs with
  | nil => simp only [wordSeries, List.map_nil, List.prod_nil, map_one]
  | cons X xs ih =>
    simpa only [wordSeries, List.map_cons, List.prod_cons, map_mul,
      generatorSeries_map] using congrArg (fun s => generatorSeries (φ X) * s) ih

theorem wordSeries_constant (xs : List A) : (wordSeries xs).constantCoeff = 1 := by
  induction xs with
  | nil => simp [wordSeries]
  | cons X xs ih =>
    simpa only [wordSeries, List.map_cons, List.prod_cons, map_mul,
      generatorSeries_constant, one_mul] using ih

end Exponential

section Coproduct
variable {α : Type}

theorem commute_series (f g : PowerSeries (WordAlg α)) :
    Commute (PowerSeries.map leftEmbedding.toRingHom f) (PowerSeries.map rightEmbedding.toRingHom g) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro p _
  simp only [PowerSeries.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact (commute_embeddings _ _).eq

def IsGroupLike (f : PowerSeries (WordAlg α)) : Prop :=
  PowerSeries.map coproduct.toRingHom f =
    PowerSeries.map leftEmbedding.toRingHom f * PowerSeries.map rightEmbedding.toRingHom f

theorem generatorSeries_groupLike (p : WordAlg α) (hp : IsPrimitive p) :
    IsGroupLike (generatorSeries p) := by
  rw [IsGroupLike, generatorSeries_map, generatorSeries_map, generatorSeries_map, hp]
  exact generatorSeries_add _ _ (commute_embeddings p p)

theorem groupLike_one : IsGroupLike (1 : PowerSeries (WordAlg α)) := by
  simp [IsGroupLike]

theorem IsGroupLike.mul {f g : PowerSeries (WordAlg α)}
    (hf : IsGroupLike f) (hg : IsGroupLike g) : IsGroupLike (f * g) := by
  dsimp only [IsGroupLike] at *
  simp only [map_mul, hf, hg]
  rw [mul_assoc, ← mul_assoc (PowerSeries.map rightEmbedding.toRingHom f),
    (commute_series g f).symm.eq]
  simp only [mul_assoc]

theorem logCoefficient_primitive (f : PowerSeries (WordAlg α))
    (hf : f.constantCoeff = 1) (hgroup : IsGroupLike f) (n : ℕ) :
    IsPrimitive (logCoefficient f n) := by
  have h := congrArg (fun s => logCoefficient s n) hgroup
  change logCoefficient (PowerSeries.map coproduct.toRingHom f) n =
    logCoefficient (PowerSeries.map leftEmbedding.toRingHom f *
      PowerSeries.map rightEmbedding.toRingHom f) n at h
  have hc (φ : WordAlg α →ₐ[ℚ] PairAlg α) :
      (PowerSeries.map φ.toRingHom f).constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hf, map_one]
  rw [logCoefficient_map, logCoefficient_mul _ _ (hc leftEmbedding) (hc rightEmbedding)
    (commute_series f f), logCoefficient_map, logCoefficient_map] at h
  exact h

end Coproduct

section Grading
variable {α : Type}

def IsGraded (f : PowerSeries (WordAlg α)) : Prop :=
  ∀ n : ℕ, grading (PowerSeries.coeff n f) = n • PowerSeries.coeff n f

theorem graded_one : IsGraded (1 : PowerSeries (WordAlg α)) := by
  intro n
  cases n <;> simp [PowerSeries.coeff_one, grading_one]

theorem IsGraded.sub {f g : PowerSeries (WordAlg α)} (hf : IsGraded f) (hg : IsGraded g) :
    IsGraded (f - g) := by
  intro n
  rw [map_sub, map_sub, hf, hg, smul_sub]

theorem IsGraded.mul {f g : PowerSeries (WordAlg α)} (hf : IsGraded f) (hg : IsGraded g) :
    IsGraded (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [grading_mul, hf, hg, smul_mul_assoc, mul_smul_comm, ← add_nsmul,
    Finset.mem_antidiagonal.mp hp]

theorem IsGraded.pow {f : PowerSeries (WordAlg α)} (hf : IsGraded f) (k : ℕ) :
    IsGraded (f ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using graded_one
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem generatorSeries_graded (p : WordAlg α) (hp : grading p = p) :
    IsGraded (generatorSeries p) := by
  intro n
  simp only [generatorSeries, PowerSeries.coeff_mk, map_smul,
    grading_pow_of_degree_one p hp n]
  exact smul_comm _ _ _

theorem logCoefficient_graded (f : PowerSeries (WordAlg α)) (hf : IsGraded f) (n : ℕ) :
    grading (logCoefficient f n) = n • logCoefficient f n := by
  rw [logCoefficient_finite, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, ((hf.sub graded_one).pow (k + 1)) n]
  exact smul_comm _ _ _

end Grading

section ActualWord
variable {α : Type}

def letterWord (xs : List (ℚ × α)) : PowerSeries (WordAlg α) :=
  wordSeries (xs.map (fun p => p.1 • letter p.2))

theorem letterWord_constant (xs : List (ℚ × α)) : (letterWord xs).constantCoeff = 1 :=
  wordSeries_constant _

theorem letterWord_groupLike (xs : List (ℚ × α)) : IsGroupLike (letterWord xs) := by
  induction xs with
  | nil => exact groupLike_one
  | cons p xs ih =>
    exact (generatorSeries_groupLike _ ((primitive_letter p.2).smul p.1)).mul ih

theorem letterWord_graded (xs : List (ℚ × α)) : IsGraded (letterWord xs) := by
  induction xs with
  | nil => exact graded_one
  | cons p xs ih =>
    exact (generatorSeries_graded (p.1 • letter p.2) (by rw [map_smul, grading_letter])).mul ih

theorem letterWord_log_primitive (xs : List (ℚ × α)) (n : ℕ) :
    IsPrimitive (logCoefficient (letterWord xs) n) :=
  logCoefficient_primitive _ (letterWord_constant xs) (letterWord_groupLike xs) n

theorem letterWord_log_dynkin (xs : List (ℚ × α)) (n : ℕ) :
    dynkin (logCoefficient (letterWord xs) n) = n • logCoefficient (letterWord xs) n := by
  rw [dynkin_eq_grading (letterWord_log_primitive xs n)]
  exact logCoefficient_graded _ (letterWord_graded xs) n

theorem letterWord_log_support_length (xs : List (ℚ × α)) (n : ℕ) (w : FreeMonoid α)
    (hw : w ∈ (logCoefficient (letterWord xs) n).support) : w.toList.length = n :=
  support_length_of_grading _ n (logCoefficient_graded _ (letterWord_graded xs) n) w hw

theorem letterWord_log_eq_bracket_sum (xs : List (ℚ × α)) (n : ℕ) (hn : 0 < n) :
    logCoefficient (letterWord xs) n =
      ∑ w ∈ (logCoefficient (letterWord xs) n).support,
        ((logCoefficient (letterWord xs) n) w / (n : ℚ)) •
          rightBracket (w.toList.map letter) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : logCoefficient (letterWord xs) n = (n : ℚ)⁻¹ •
      dynkin (logCoefficient (letterWord xs) n) := by
    rw [letterWord_log_dynkin, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      inv_mul_cancel₀ hn0, one_smul]
  rw [dynkin_apply] at he
  change logCoefficient (letterWord xs) n = (n : ℚ)⁻¹ •
    (∑ w ∈ (logCoefficient (letterWord xs) n).support,
      (logCoefficient (letterWord xs) n) w • rightBracket (w.toList.map letter)) at he
  rw [Finset.smul_sum] at he
  simpa only [smul_smul, div_eq_mul_inv, mul_comm] using he

end ActualWord
end Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLie
