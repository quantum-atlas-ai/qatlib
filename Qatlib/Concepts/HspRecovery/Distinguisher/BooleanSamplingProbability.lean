/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanRecovery
import Qatlib.Concepts.HspRecovery.Distinguisher.HiddenSubgroupRepetition

/-!
# Boolean Fourier halfspace probabilities

Identifies the Boolean orthogonal complement of a subgroup with its character annihilator.
Restricting the Boolean dot product to a subgroup gives an additive homomorphism to `ZMod 2`,
whose kernel has half the subgroup's cardinality when the homomorphism is nonzero.

Uses this count to show that a hidden subgroup sample is orthogonal to a fixed vector outside
the hidden subgroup with probability one half, and that all `m` fresh samples are orthogonal
with probability `(1 / 2) ^ m`. This is the halfspace estimate used in Simon-type recovery
[Simon1997].

## Main statements

* `booleanOrthogonalCharacterEquiv`: identifies orthogonal vectors with annihilating characters.
* `booleanDotOnSubgroupHom_ker_card_mul_two`: counts the kernel of a nonzero dot-product map.
* `hiddenSubgroupFreshSamples_boolean_halfspace`: computes the fresh-sample halfspace
  probability.

## References

* [Simon, 1997][Simon1997]
-/

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.Distinguisher

open scoped Classical

/-- The additive equivalence between the Boolean orthogonal complement of `H` and its character
annihilator, induced by `booleanCharacterEquiv`. -/
noncomputable def booleanOrthogonalCharacterEquiv {n : ℕ}
    (H : AddSubgroup (BooleanVec n)) :
    booleanOrthogonal H ≃+ characterAnnihilator H where
  toFun a := ⟨booleanCharacterEquiv n a,
    (booleanCharacterEquiv_mem_characterAnnihilator_iff H a).2 a.property⟩
  invFun χ := ⟨(booleanCharacterEquiv n).symm χ, by
    apply (booleanCharacterEquiv_mem_characterAnnihilator_iff H _).1
    rw [(booleanCharacterEquiv n).apply_symm_apply]
    exact χ.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (booleanCharacterEquiv n).symm_apply_apply (a : BooleanVec n)
  right_inv χ := by
    apply Subtype.ext
    exact (booleanCharacterEquiv n).apply_symm_apply (χ : AddChar (BooleanVec n) ℂ)
  map_add' a b := by
    apply Subtype.ext
    change booleanCharacterEquiv n ((a : BooleanVec n) + (b : BooleanVec n)) =
      booleanCharacterEquiv n (a : BooleanVec n) + booleanCharacterEquiv n (b : BooleanVec n)
    exact map_add (booleanCharacterEquiv n) (a : BooleanVec n) (b : BooleanVec n)

/-- The orthogonal-complement equivalence sends a vector to its Boolean character. -/
@[simp] theorem booleanOrthogonalCharacterEquiv_apply {n : ℕ}
    (H : AddSubgroup (BooleanVec n)) (a : booleanOrthogonal H) :
    ((booleanOrthogonalCharacterEquiv H a : characterAnnihilator H) :
      AddChar (BooleanVec n) ℂ) = booleanCharacterEquiv n a := rfl

/-- The inverse orthogonal-complement equivalence sends an annihilating character to its Boolean
vector index. -/
@[simp] theorem booleanOrthogonalCharacterEquiv_symm_apply {n : ℕ}
    (H : AddSubgroup (BooleanVec n)) (χ : characterAnnihilator H) :
    (((booleanOrthogonalCharacterEquiv H).symm χ : booleanOrthogonal H) : BooleanVec n) =
      (booleanCharacterEquiv n).symm χ := rfl

/-- The additive homomorphism on `K` obtained by taking the Boolean dot product with `x`. -/
def booleanDotOnSubgroupHom {n : ℕ} (K : AddSubgroup (BooleanVec n)) (x : BooleanVec n) :
    K →+ ZMod 2 :=
  (booleanDotHom x).comp K.subtype

/-- The restricted dot-product homomorphism evaluates to `booleanDot x a`. -/
@[simp] theorem booleanDotOnSubgroupHom_apply {n : ℕ}
    (K : AddSubgroup (BooleanVec n)) (x : BooleanVec n) (a : K) :
    booleanDotOnSubgroupHom K x a = booleanDot x a := rfl

/-- Every element of `ZMod 2` equals zero or one. -/
private theorem zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hz : z.val ≤ 1 := Nat.le_of_lt_succ (by simpa using z.val_lt)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hz with hz | hz
  · exact Or.inl ((ZMod.val_eq_zero z).1 hz)
  · exact Or.inr ((ZMod.val_eq_one (by norm_num) z).1 hz)

/-- If `x` is outside the orthogonal complement of `K`, dot product with `x` maps `K`
surjectively onto `ZMod 2`. -/
theorem booleanDotOnSubgroupHom_surjective_of_not_mem_orthogonal {n : ℕ}
    (K : AddSubgroup (BooleanVec n)) (x : BooleanVec n)
    (hx : x ∉ booleanOrthogonal K) :
    Function.Surjective (booleanDotOnSubgroupHom K x) := by
  rw [mem_booleanOrthogonal] at hx
  push Not at hx
  obtain ⟨a, ha⟩ := hx
  have ha1 : booleanDot x a = 1 :=
    (zmod_two_eq_zero_or_one (booleanDot x a)).resolve_left ha
  intro z
  rcases zmod_two_eq_zero_or_one z with rfl | rfl
  · exact ⟨0, by simp [booleanDotOnSubgroupHom]⟩
  · exact ⟨a, by simpa [booleanDotOnSubgroupHom] using! ha1⟩

/-- If `x` is outside the orthogonal complement of `K`, twice the cardinality of the restricted
dot-product kernel equals the cardinality of `K`. -/
theorem booleanDotOnSubgroupHom_ker_card_mul_two {n : ℕ}
    (K : AddSubgroup (BooleanVec n)) (x : BooleanVec n)
    (hx : x ∉ booleanOrthogonal K) :
    Fintype.card (booleanDotOnSubgroupHom K x).ker * 2 = Fintype.card K := by
  let φ := booleanDotOnSubgroupHom K x
  have hsurj : Function.Surjective φ :=
    booleanDotOnSubgroupHom_surjective_of_not_mem_orthogonal K x hx
  have hcard := φ.ker.card_mul_index
  rw [AddSubgroup.index_ker, φ.range_eq_top_of_surjective hsurj] at hcard
  norm_num at hcard ⊢
  exact hcard

/-- For independent samples, the probability that every entry satisfies `P` is the one-sample
probability of `P` raised to the number of samples. -/
theorem FinDist.sum_probOf_forall_eq_pow {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (P : X → Prop) [DecidablePred P] (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → X => ∀ i, P (xs i)), p.probOf xs) =
      (∑ x ∈ Finset.univ.filter P, p.prob x) ^ m := by
  classical
  have hindicator : ∀ xs : Fin m → X,
      (if (∀ i, P (xs i)) then (1 : ℝ) else 0) =
        ∏ i, if P (xs i) then (1 : ℝ) else 0 := by
    intro xs
    by_cases h : ∀ i, P (xs i)
    · simp [h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (by
        intro hall
        exact hi (hall i))]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  rw [Finset.sum_filter]
  calc
    (∑ xs : Fin m → X, if (∀ i, P (xs i)) then p.probOf xs else 0) =
        ∑ xs : Fin m → X, p.probOf xs * ∏ i, if P (xs i) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro xs _
      rw [← hindicator xs]
      by_cases h : ∀ i, P (xs i) <;> simp [h]
    _ = ∏ i, (∑ x, p.prob x * (if P x then (1 : ℝ) else 0)) :=
      FinDist.expect_prod p (fun _ x => if P x then 1 else 0)
    _ = ∏ _i : Fin m, (∑ x ∈ Finset.univ.filter P, p.prob x) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x <;> simp [hx]
    _ = (∑ x ∈ Finset.univ.filter P, p.prob x) ^ m := by
      simp

variable {n : ℕ} {R : Type*}
  [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- For a function hiding `H` and `x ∉ H`, the probability that a decoded Fourier sample is
orthogonal to `x` is exactly one half. -/
theorem hiddenSubgroupSampleDist_boolean_halfspace
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    (x : BooleanVec n) (hx : x ∉ H) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar (BooleanVec n) ℂ =>
        booleanDot x ((booleanCharacterEquiv n).symm χ) = 0),
      (hiddenSubgroupSampleDist f e).prob χ) = (1 / 2 : ℝ) := by
  classical
  let K := booleanOrthogonal H
  let A := characterAnnihilator H
  let φ := booleanDotOnSubgroupHom K x
  have hxK : x ∉ booleanOrthogonal K := by
    simpa [K, booleanOrthogonal_booleanOrthogonal_eq H] using hx
  have hker : Fintype.card φ.ker * 2 = Fintype.card K := by
    simpa [φ] using booleanDotOnSubgroupHom_ker_card_mul_two K x hxK
  have hKA : Fintype.card K = Fintype.card A := by
    exact Fintype.card_congr (booleanOrthogonalCharacterEquiv H).toEquiv
  let P : AddChar (BooleanVec n) ℂ → Prop := fun χ =>
    booleanDot x ((booleanCharacterEquiv n).symm χ) = 0
  let S : Finset (AddChar (BooleanVec n) ℂ) := Finset.univ.filter P
  have hfilterCard :
      (S.filter (fun χ => χ ∈ A)).card = Fintype.card φ.ker := by
    let q : φ.ker ≃ {χ : AddChar (BooleanVec n) ℂ // P χ ∧ χ ∈ A} :=
      { toFun := fun a =>
          ⟨booleanOrthogonalCharacterEquiv H a.1, by
            constructor
            · change booleanDot x ((booleanCharacterEquiv n).symm
                (((booleanOrthogonalCharacterEquiv H a.1 : characterAnnihilator H) :
                  AddChar (BooleanVec n) ℂ))) = 0
              rw [booleanOrthogonalCharacterEquiv_apply,
                (booleanCharacterEquiv n).symm_apply_apply]
              have ha := a.property
              change booleanDotOnSubgroupHom K x a.1 = 0 at ha
              exact ha
            · exact (booleanOrthogonalCharacterEquiv H a.1).property⟩
        invFun := fun χ =>
          ⟨(booleanOrthogonalCharacterEquiv H).symm
              ⟨χ, by simpa [A] using χ.property.2⟩, by
            change booleanDot x
              (((booleanOrthogonalCharacterEquiv H).symm
                ⟨χ, by simpa [A] using χ.property.2⟩ : K) : BooleanVec n) = 0
            simpa [P] using χ.property.1⟩
        left_inv := by
          intro a
          apply Subtype.ext
          change (booleanOrthogonalCharacterEquiv H).symm
            (booleanOrthogonalCharacterEquiv H (a.1 : K)) = (a.1 : K)
          simp
        right_inv := by
          intro χ
          apply Subtype.ext
          simp }
    calc
      (S.filter (fun χ => χ ∈ A)).card =
          (Finset.univ.filter (fun χ => P χ ∧ χ ∈ A)).card := by
            apply congrArg Finset.card
            ext χ
            simp [S]
      _ = Fintype.card {χ : AddChar (BooleanVec n) ℂ // P χ ∧ χ ∈ A} := by
            exact (Fintype.card_subtype _).symm
      _ = Fintype.card φ.ker := (Fintype.card_congr q).symm
  have hsum :
      (∑ χ ∈ S, (hiddenSubgroupSampleDist f e).prob χ) =
        ∑ χ ∈ S.filter (fun χ => χ ∈ A),
          (1 / (Fintype.card A : ℝ)) := by
    calc
      (∑ χ ∈ S, (hiddenSubgroupSampleDist f e).prob χ) =
          ∑ χ ∈ S, if χ ∈ A then (1 / (Fintype.card A : ℝ)) else 0 := by
            apply Finset.sum_congr rfl
            intro χ hχ
            rw [hiddenSubgroupSampleDist_prob f H hf e]
      _ = ∑ χ ∈ S.filter (fun χ => χ ∈ A),
          (1 / (Fintype.card A : ℝ)) := by
            exact (Finset.sum_filter (s := S) (fun χ => χ ∈ A)
              (fun _ => (1 / (Fintype.card A : ℝ)))).symm
  have hker_pos : (0 : ℝ) < Fintype.card φ.ker := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
  have hreal : (Fintype.card A : ℝ) = 2 * Fintype.card φ.ker := by
    have hker' : (Fintype.card φ.ker : ℝ) * 2 = Fintype.card K := by
      exact_mod_cast hker
    have hKA' : (Fintype.card K : ℝ) = Fintype.card A := by
      exact_mod_cast hKA
    nlinarith
  change (∑ χ ∈ S, (hiddenSubgroupSampleDist f e).prob χ) = _
  rw [hsum, Finset.sum_const, nsmul_eq_mul, hfilterCard, hreal]
  field_simp [ne_of_gt hker_pos]

/-- For a function hiding `H` and `x ∉ H`, the probability that all `m` fresh decoded Fourier
samples are orthogonal to `x` is `ENNReal.ofReal ((1 / 2) ^ m)`. -/
theorem hiddenSubgroupFreshSamples_boolean_halfspace
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    (x : BooleanVec n) (hx : x ∉ H) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        ∀ i, booleanDot x ((booleanCharacterEquiv n).symm (xs i)) = 0),
      hiddenSubgroupFreshSamples f e m xs) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
  classical
  let P : AddChar (BooleanVec n) ℂ → Prop := fun χ =>
    booleanDot x ((booleanCharacterEquiv n).symm χ) = 0
  have hprob := FinDist.sum_probOf_forall_eq_pow (hiddenSubgroupSampleDist f e) P m
  rw [hiddenSubgroupSampleDist_boolean_halfspace f H hf e x hx] at hprob
  calc
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        ∀ i, booleanDot x ((booleanCharacterEquiv n).symm (xs i)) = 0),
      hiddenSubgroupFreshSamples f e m xs) =
        ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∀ i, P (xs i)), ENNReal.ofReal ((hiddenSubgroupSampleDist f e).probOf xs) := by
            apply Finset.sum_congr
            · ext xs
              simp [P]
            · intro xs hxs
              rw [hiddenSubgroupFreshSamples_apply]
    _ = ENNReal.ofReal
        (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∀ i, P (xs i)), (hiddenSubgroupSampleDist f e).probOf xs) := by
            exact (ENNReal.ofReal_sum_of_nonneg (fun xs _ =>
              Finset.prod_nonneg (fun i _ => (hiddenSubgroupSampleDist f e).nonneg (xs i)))).symm
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by rw [hprob]

end Qatlib.Concepts.HspRecovery.Distinguisher
