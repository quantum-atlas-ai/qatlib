/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Operator-norm error propagation for matrix products

Develops perturbation bounds in the matrix norm induced by the Euclidean norm. Products and
powers of contractions accumulate at most the sum of the factor errors.

The cubic map `X ↦ X * X.conjTranspose * X` is bounded in terms of perturbations of `X`,
including explicit estimates near a unitary matrix and for scaled linear-cubic combinations. See
[Bhatia1997] for related background.

## Main statements

* `l2_norm_list_prod_sub_prod_le`: For a list of pairs of contractions, the Euclidean
  operator-norm distance between the two ordered products is at most the sum of the distances
  between paired factors.
* `l2_norm_scaled_cubic_sub_unitary_le`: If `‖X - U‖ ≤ ε` for unitary `U`, then `‖a • X - b • (X
  * X.conjTranspose * X) - U‖ ≤ (‖a‖ + ‖b‖ * (3 + 3 * ε + ε²)) * ε + ‖a - b - 1‖` in Euclidean
  operator norm.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.OperatorErrors.OperatorError

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The identity matrix has Euclidean operator norm at most one, including when the index type
is empty. -/
theorem l2_norm_one_le : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (Matrix I I ℂ) with h | h
  · simp [Subsingleton.elim (1 : Matrix I I ℂ) 0]
  · exact CStarRing.norm_one.le

/-- Every unitary matrix has Euclidean operator norm at most one. -/
theorem l2_norm_unitary_le_one {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (Matrix I I ℂ) with h | h
  · simp [Subsingleton.elim U 0]
  · exact (CStarRing.norm_of_mem_unitary hU).le

omit [DecidableEq I] in

/-- For compatible rectangular matrices, `‖A * B - C * D‖ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖` in
the Euclidean operator norm. -/
theorem l2_norm_rect_mul_sub_mul_le {J K : Type*} [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] (A C : Matrix I J ℂ) (B D : Matrix J K ℂ) :
    ‖A * B - C * D‖ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  have h : A * B - C * D = (A - C) * B + C * (B - D) := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h]
  exact (norm_add_le _ _).trans
    (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))

/-- The Euclidean operator-norm difference of two square-matrix products is bounded by `‖A - C‖
* ‖B‖ + ‖C‖ * ‖B - D‖`. -/
theorem l2_norm_mul_sub_mul_le (A B C D : Matrix I I ℂ) :
    ‖A * B - C * D‖ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ :=
  l2_norm_rect_mul_sub_mul_le A C B D

/-- Multiplication on both sides by matrices of Euclidean operator norm at most one does not
increase the norm of the middle matrix. -/
theorem l2_norm_sandwich_le (X Y Z : Matrix I I ℂ)
    (hX : ‖X‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) : ‖X * Y * Z‖ ≤ ‖Y‖ := by
  calc
    _ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖Y‖ * 1 := by gcongr
    _ = _ := by ring

/-- A finite list product of matrices with Euclidean operator norm at most one also has norm at
most one. -/
theorem l2_norm_list_prod_le_one (A : List (Matrix I I ℂ))
    (hA : ∀ a ∈ A, ‖a‖ ≤ 1) : ‖A.prod‖ ≤ 1 := by
  induction A with
  | nil => exact l2_norm_one_le
  | cons a A ih =>
    rw [List.prod_cons]
    have ht := ih (fun b hb => hA b (List.mem_cons_of_mem a hb))
    exact (norm_mul_le _ _).trans
      (by simpa using mul_le_mul (hA a List.mem_cons_self) ht (norm_nonneg _) zero_le_one)

/-- For a list of pairs of contractions, the Euclidean operator-norm distance between the two
ordered products is at most the sum of the distances between paired factors. -/
theorem l2_norm_list_prod_sub_prod_le (pairs : List (Matrix I I ℂ × Matrix I I ℂ))
    (hp : ∀ p ∈ pairs, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1) :
    ‖(pairs.map Prod.fst).prod - (pairs.map Prod.snd).prod‖ ≤
      (pairs.map (fun p => ‖p.1 - p.2‖)).sum := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    have hh := hp p List.mem_cons_self
    have ht : ∀ q ∈ pairs, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1 :=
      fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hprod : ‖(pairs.map Prod.fst).prod‖ ≤ 1 :=
      l2_norm_list_prod_le_one _ (by
        intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        exact (ht q hq).1)
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine (l2_norm_mul_sub_mul_le _ _ _ _).trans ?_
    have hleft := mul_le_mul_of_nonneg_left hprod (norm_nonneg (p.1 - p.2))
    have hright := mul_le_mul_of_nonneg_right hh.2
      (norm_nonneg ((pairs.map Prod.fst).prod - (pairs.map Prod.snd).prod))
    nlinarith [ih ht]

/-- Every natural power of a matrix with Euclidean operator norm at most one has norm at most
one. -/
theorem l2_norm_pow_le_one (U : Matrix I I ℂ) (hU : ‖U‖ ≤ 1) (r : ℕ) :
    ‖U ^ r‖ ≤ 1 := by
  have h := l2_norm_list_prod_le_one (List.replicate r U) (by
    intro a ha
    obtain rfl := List.eq_of_mem_replicate ha
    exact hU)
  simpa only [List.prod_replicate] using h

/-- For contractions `U` and `V`, the Euclidean operator-norm distance between their `r`th
powers is at most `r * ‖U - V‖`. -/
theorem l2_norm_pow_sub_pow_le (U V : Matrix I I ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (r : ℕ) :
    ‖U ^ r - V ^ r‖ ≤ (r : ℝ) * ‖U - V‖ := by
  have h := l2_norm_list_prod_sub_prod_le (List.replicate r (U, V)) (by
    intro p hp
    obtain rfl := List.eq_of_mem_replicate hp
    exact ⟨hU, hV⟩)
  simpa only [List.map_replicate, List.prod_replicate, List.sum_replicate,
    nsmul_eq_mul] using h

/-- For two `Fin n`-indexed families of contractions, the distance between their ordered
products is at most the sum of their pointwise Euclidean operator-norm distances. -/
theorem l2_norm_prod_sub_prod_le {n : ℕ} (A B : Fin n → Matrix I I ℂ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ∀ i, ‖B i‖ ≤ 1) :
    ‖(List.ofFn A).prod - (List.ofFn B).prod‖ ≤ ∑ i, ‖A i - B i‖ := by
  have h := l2_norm_list_prod_sub_prod_le (List.ofFn (fun i => (A i, B i))) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨hA i, hB i⟩)
  simpa only [List.map_ofFn, Function.comp_def, List.sum_ofFn] using h

/-- For matrices assigned to a list of labels and contractive at each listed label, the distance
between the two ordered products is at most the sum of the listed factor distances. -/
theorem l2_norm_list_map_prod_sub_prod_le {α : Type*} (cs : List α)
    (A B : α → Matrix I I ℂ)
    (hA : ∀ c ∈ cs, ‖A c‖ ≤ 1) (hB : ∀ c ∈ cs, ‖B c‖ ≤ 1) :
    ‖(cs.map A).prod - (cs.map B).prod‖ ≤ (cs.map fun c => ‖A c - B c‖).sum := by
  have h := l2_norm_list_prod_sub_prod_le (cs.map fun c => (A c, B c)) (by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact ⟨hA c hc, hB c hc⟩)
  simpa only [List.map_map, Function.comp_def] using h

/-- For two contractive matrix families whose distance at each listed label is at most `ε`, the
distance between their ordered products is at most the list length times `ε`. -/
theorem l2_norm_list_map_prod_sub_prod_le_of_le {α : Type*} (cs : List α)
    (A B : α → Matrix I I ℂ) (ε : ℝ)
    (hA : ∀ c ∈ cs, ‖A c‖ ≤ 1) (hB : ∀ c ∈ cs, ‖B c‖ ≤ 1)
    (hε : ∀ c ∈ cs, ‖A c - B c‖ ≤ ε) :
    ‖(cs.map A).prod - (cs.map B).prod‖ ≤ (cs.length : ℝ) * ε := by
  refine (l2_norm_list_map_prod_sub_prod_le cs A B hA hB).trans ?_
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ht := ih (fun d hd => hA d (List.mem_cons_of_mem c hd))
      (fun d hd => hB d (List.mem_cons_of_mem c hd))
      (fun d hd => hε d (List.mem_cons_of_mem c hd))
    have hh := hε c List.mem_cons_self
    nlinarith

/-- The Euclidean operator-norm difference between `X * X.conjTranspose * X` and `Y *
Y.conjTranspose * Y` is at most `(‖X‖² + ‖X‖ * ‖Y‖ + ‖Y‖²) * ‖X - Y‖`. -/
theorem l2_norm_cubic_sub_cubic_le (X Y : Matrix I I ℂ) :
    ‖X * X.conjTranspose * X - Y * Y.conjTranspose * Y‖ ≤
      (‖X‖ ^ 2 + ‖X‖ * ‖Y‖ + ‖Y‖ ^ 2) * ‖X - Y‖ := by
  have h : X * X.conjTranspose * X - Y * Y.conjTranspose * Y =
      (X - Y) * X.conjTranspose * X + Y * (X.conjTranspose - Y.conjTranspose) * X +
        Y * Y.conjTranspose * (X - Y) := by noncomm_ring
  have hn3 (A B C : Matrix I I ℂ) : ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  rw [h]
  refine (norm_add_le _ _).trans
    ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  calc _ ≤ ‖X - Y‖ * ‖X.conjTranspose‖ * ‖X‖ +
      ‖Y‖ * ‖X.conjTranspose - Y.conjTranspose‖ * ‖X‖ +
      ‖Y‖ * ‖Y.conjTranspose‖ * ‖X - Y‖ :=
        add_le_add (add_le_add (hn3 _ _ _) (hn3 _ _ _)) (hn3 _ _ _)
    _ = _ := by
      rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose,
        Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
      ring

/-- For unitary `U`, the distance from `X * X.conjTranspose * X` to `U` is at most `(‖X‖² + ‖X‖
+ 1) * ‖X - U‖` in Euclidean operator norm. -/
theorem l2_norm_cubic_sub_unitary_le (X U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    ‖X * X.conjTranspose * X - U‖ ≤ (‖X‖ ^ 2 + ‖X‖ + 1) * ‖X - U‖ := by
  have hUU : U * U.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  have h := l2_norm_cubic_sub_cubic_le X U
  rw [hUU, Matrix.one_mul] at h
  have hu := l2_norm_unitary_le_one hU
  have hpoly : ‖X‖ ^ 2 + ‖X‖ * ‖U‖ + ‖U‖ ^ 2 ≤ ‖X‖ ^ 2 + ‖X‖ + 1 := by
    nlinarith [norm_nonneg X, norm_nonneg U,
      mul_self_le_mul_self (norm_nonneg U) hu,
      mul_le_mul_of_nonneg_left hu (norm_nonneg X)]
  exact h.trans (mul_le_mul_of_nonneg_right hpoly (norm_nonneg _))

/-- If `X` is within Euclidean operator-norm distance `ε` of a unitary matrix, then `‖X‖ ≤ 1 +
ε`. -/
theorem l2_norm_le_one_add_error {X U : Matrix I I ℂ} {ε : ℝ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hε : ‖X - U‖ ≤ ε) : ‖X‖ ≤ 1 + ε := by
  have h := norm_add_le (X - U) U
  rw [sub_add_cancel] at h
  linarith [l2_norm_unitary_le_one hU]

/-- If `X` is within Euclidean operator-norm distance `ε` of unitary `U`, its cubic expression
is within `(3 + 3 * ε + ε²) * ε` of `U`. -/
theorem l2_norm_cubic_sub_unitary_of_error {X U : Matrix I I ℂ} {ε : ℝ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hε : ‖X - U‖ ≤ ε) :
    ‖X * X.conjTranspose * X - U‖ ≤ (3 + 3 * ε + ε ^ 2) * ε := by
  have he0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hx := l2_norm_le_one_add_error hU hε
  have hpoly : ‖X‖ ^ 2 + ‖X‖ + 1 ≤ 3 + 3 * ε + ε ^ 2 := by
    nlinarith [norm_nonneg X, mul_self_le_mul_self (norm_nonneg X) hx]
  refine (l2_norm_cubic_sub_unitary_le X U hU).trans ?_
  exact mul_le_mul hpoly hε (norm_nonneg _) (by positivity)

/-- If `‖X - U‖ ≤ ε` for unitary `U`, then `‖a • X - b • (X * X.conjTranspose * X) - U‖ ≤ (‖a‖ +
‖b‖ * (3 + 3 * ε + ε²)) * ε + ‖a - b - 1‖` in Euclidean operator norm. -/
theorem l2_norm_scaled_cubic_sub_unitary_le {X U : Matrix I I ℂ} {ε : ℝ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hε : ‖X - U‖ ≤ ε) (a b : ℂ) :
    ‖a • X - b • (X * X.conjTranspose * X) - U‖ ≤
      (‖a‖ + ‖b‖ * (3 + 3 * ε + ε ^ 2)) * ε + ‖a - b - 1‖ := by
  have hid : a • X - b • (X * X.conjTranspose * X) - U =
      (a • (X - U) - b • (X * X.conjTranspose * X - U)) + (a - b - 1) • U := by
    module
  rw [hid]
  refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
  rw [norm_smul, norm_smul, norm_smul]
  have h1 := mul_le_mul_of_nonneg_left hε (norm_nonneg a)
  have h2 := mul_le_mul_of_nonneg_left (l2_norm_cubic_sub_unitary_of_error hU hε)
    (norm_nonneg b)
  have h3 := mul_le_mul_of_nonneg_left (l2_norm_unitary_le_one hU) (norm_nonneg (a - b - 1))
  nlinarith

end Qatlib.Foundations.OperatorErrors.OperatorError
