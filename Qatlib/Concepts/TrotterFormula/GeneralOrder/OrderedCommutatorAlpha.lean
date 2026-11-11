/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders

/-!
# Ordered composition commutator coefficients

This module indexes conjugation coefficients by `pfCompositions` and builds the associated
reverse-ordered repeated generator words. It introduces an initial composition coefficient, a
revised multinomially weighted coefficient, and real-linear adjoint budgets for the ordered
expansions used in product-formula analysis [ChildsEtAl2021Trotter].

The coefficient expansion `pfConjCoeff_ordered` and the recursive budget identities give a
conjugation remainder estimate in both general and skew-Hermitian modes. The revised coefficient
`pfCommAlphaOrderedV2` is related explicitly to the factorial-normalized adjoint budget.

## Main statements

* `pfConjCoeff_ordered`: ordered composition expansion of conjugation coefficients.
* `pfConjWord_ordered_remainder_norm_mode`: remainder estimate in terms of the ordered adjoint
  budget.
* `pfCommAlphaOrderedV2_eq_budget`: factorial relation between the revised coefficient and the
  budget.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The finite set of `s`-tuples of natural numbers whose entries sum to `p`. -/
def pfCompositions (s p : ℕ) : Finset (Fin s → ℕ) :=
  ((Finset.univ : Finset (Fin s → Fin (p + 1))).image
      fun f i => (f i).val).filter
    (fun q => ∑ i, q i = p)

/-- The generator word formed in reverse index order, repeating each generator according to its
multiplicity in `q`. -/
def pfOrderedCompositionWord (xs : List (Matrix I I ℂ)) (q : Fin xs.length → ℕ) :
    List (Matrix I I ℂ) :=
  (List.ofFn (fun i : Fin xs.length => (xs.get i, q i))).reverse.flatMap
    (fun kc => List.replicate kc.2 kc.1)

/-- The sum over compositions of `p!` divided by the product whose factors are the multiplicity
factorials multiplied by the nested commutator norm. -/
noncomputable def pfCommAlphaOrdered (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions xs.length p,
    (p.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ) *
      ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖

/-- Membership in `pfCompositions s n` is equivalent to having total sum `n`. -/
theorem pfCompositions_mem {s n : ℕ} (q : Fin s → ℕ) :
    q ∈ pfCompositions s n ↔ ∑ i, q i = n := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply Finset.mem_image.mpr
    refine ⟨fun i => ⟨q i, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hi : q i ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)
      omega
    · rfl

/-- Splits a sum over compositions with `s+1` entries according to the first entry and the
remaining composition. -/
theorem pfCompositions_sum_cons {E : Type*} [AddCommMonoid E] (s n : ℕ)
    (f : (Fin (s+1) → ℕ) → E) :
    ∑ q ∈ pfCompositions (s+1) n, f q =
      ∑ j : Fin (n+1), ∑ r ∈ pfCompositions s (n-j.val), f (Fin.cons j.val r) := by
  classical
  rw [Finset.sum_sigma' (Finset.univ : Finset (Fin (n+1)))
    (fun j => pfCompositions s (n-j.val)) (fun j r => f (Fin.cons j.val r))]
  symm
  apply Finset.sum_bij (fun z _ => Fin.cons z.1.val z.2)
  · rintro ⟨j,r⟩ hz
    have hr := (Finset.mem_sigma.mp hz).2
    rw [pfCompositions_mem] at hr ⊢
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hj := j.isLt
    (try dsimp only at hr)
    omega
  · rintro ⟨j,r⟩ hz ⟨k,u⟩ hw he
    have h0 := congrFun he 0
    have hj : j = k := Fin.ext (by simpa using! h0)
    subst k
    have hu : r = u := funext (fun i => by simpa using! congrFun he i.succ)
    subst u
    rfl
  · intro q hq
    have hsum := (pfCompositions_mem q).mp hq
    have h0 : q 0 ≤ n := by
      rw [Fin.sum_univ_succ] at hsum
      omega
    let j : Fin (n+1) := ⟨q 0, by omega⟩
    let r : Fin s → ℕ := fun i => q i.succ
    refine ⟨⟨j,r⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [pfCompositions_mem]
      rw [Fin.sum_univ_succ] at hsum
      dsimp [r,j]
      omega
    · exact Fin.cons_self_tail q
  · intro z _
    rfl

omit [DecidableEq I] in

/-- Appending `j` copies of `X` to a seeded commutator word applies `pfAdPower X` of order `j`
to its nested commutator. -/
theorem pfNestedCommList_append_replicate (B X : Matrix I I ℂ)
    (w : List (Matrix I I ℂ)) (j : ℕ) :
    pfNestedCommList (B :: (w ++ List.replicate j X)) =
      pfAdPower X (pfNestedCommList (B :: w)) j := by
  simp only [pfNestedCommList, List.foldl_append]
  generalize w.foldl (fun D Y => pfComm Y D) B = C
  induction j generalizing C with
  | zero => simp [pfAdPower]
  | succ j ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    exact (Function.iterate_succ_apply (fun D => pfComm X D) j C).symm

omit [Fintype I] [DecidableEq I] in

/-- The ordered composition word for `X :: xs` consists of the tail composition word followed by
the specified number of copies of `X`. -/
theorem pfOrderedCompositionWord_cons (X : Matrix I I ℂ)
    (xs : List (Matrix I I ℂ)) (q : Fin (xs.length+1) → ℕ) :
    pfOrderedCompositionWord (X::xs) q =
      pfOrderedCompositionWord xs (fun i => q i.succ) ++ List.replicate (q 0) X := by
  simp [pfOrderedCompositionWord, List.ofFn_succ, List.reverse_cons,
    List.flatMap_append]

omit [DecidableEq I] in

/-- Expands the degree-`n` conjugation coefficient as a sum of nested commutators over ordered
compositions, weighted by reciprocal factorial products. -/
theorem pfConjCoeff_ordered (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (n : ℕ) :
    pfConjCoeff xs B n =
      ∑ q ∈ pfCompositions xs.length n,
        (∏ i, ((q i).factorial : ℝ))⁻¹ •
          pfNestedCommList (B :: pfOrderedCompositionWord xs q) := by
  classical
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => simp [pfConjCoeff, pfCompositions, pfOrderedCompositionWord, pfNestedCommList]
    | succ n =>
      have he : pfCompositions 0 (n+1) = ∅ := by
        ext q
        simp [pfCompositions_mem]
      simp [pfConjCoeff, he]
  | cons X xs ih =>
    rw [pfConjCoeff]
    change _ = ∑ q ∈ pfCompositions (xs.length+1) n,
      (∏ i, ((q i).factorial : ℝ))⁻¹ •
        pfNestedCommList (B :: pfOrderedCompositionWord (X::xs) q)
    rw [pfCompositions_sum_cons]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]
    let L := pfAdPowerLinear X j.val
    change (j.val.factorial : ℝ)⁻¹ • L
      (∑ q ∈ pfCompositions xs.length (n-j.val),
        (∏ i, ((q i).factorial : ℝ))⁻¹ •
          pfNestedCommList (B :: pfOrderedCompositionWord xs q)) = _
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [map_smul, smul_smul, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, _root_.mul_inv_rev, mul_comm]
    rw [pfOrderedCompositionWord_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [pfNestedCommList_append_replicate]
    rfl

/-- The sum over degree-`n` compositions of the norms of their nested commutators after applying
`L`, weighted by reciprocal factorial products. -/
def pfOrderedAdBudget (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (n : ℕ) (L : Matrix I I ℂ →ₗ[ℝ] Matrix I I ℂ) : ℝ :=
  ∑ q ∈ pfCompositions xs.length n,
    (∏ i, ((q i).factorial : ℝ))⁻¹ *
      ‖L (pfNestedCommList (B :: pfOrderedCompositionWord xs q))‖

/-- The ordered adjoint budget is nonnegative. -/
theorem pfOrderedAdBudget_nonneg (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (n : ℕ) (L : Matrix I I ℂ →ₗ[ℝ] Matrix I I ℂ) :
    0 ≤ pfOrderedAdBudget xs B n L := by
  classical
  apply Finset.sum_nonneg
  intro q _
  positivity

/-- The norm of a real-linear image of a conjugation coefficient is bounded by the corresponding
ordered adjoint budget. -/
theorem pfConjCoeff_ordered_linear_norm_le (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (n : ℕ) (L : Matrix I I ℂ →ₗ[ℝ] Matrix I I ℂ) :
    ‖L (pfConjCoeff xs B n)‖ ≤ pfOrderedAdBudget xs B n L := by
  classical
  rw [pfConjCoeff_ordered, map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [map_smul, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- For an empty generator list at order zero, `pfCommAlphaOrdered` equals one. -/
theorem pfCommAlphaOrdered_nil_zero (B : Matrix I I ℂ) :
    pfCommAlphaOrdered [] B 0 = 1 := by
  simp [pfCommAlphaOrdered, pfCompositions]

/-- Splits the ordered adjoint budget for a nonempty generator list by the multiplicity of its
leading generator. -/
theorem pfOrderedAdBudget_cons (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (p : ℕ) (L : Matrix I I ℂ →ₗ[ℝ] Matrix I I ℂ) :
    pfOrderedAdBudget (X::xs) B p L =
      ∑ j : Fin (p+1), (j.val.factorial : ℝ)⁻¹ *
        pfOrderedAdBudget xs B (p-j.val) (L.comp (pfAdPowerLinear X j.val)) := by
  classical
  unfold pfOrderedAdBudget
  change (∑ q ∈ pfCompositions (xs.length+1) p,
    (∏ i, ((q i).factorial : ℝ))⁻¹ *
      ‖L (pfNestedCommList (B :: pfOrderedCompositionWord (X::xs) q))‖) = _
  rw [pfCompositions_sum_cons]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fin.prod_univ_succ, pfOrderedCompositionWord_cons]
  simp only [Fin.cons_zero, Fin.cons_succ, pfNestedCommList_append_replicate,
    LinearMap.comp_apply, pfAdPowerLinear, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.mul_inv_rev]
  ring

/-- Decomposes the identity-map adjoint budget into the tail budget and the positive
leading-generator multiplicity contributions. -/
theorem pfOrderedAdBudget_remainder_cons (X B : Matrix I I ℂ)
    (xs : List (Matrix I I ℂ)) (p : ℕ) :
    pfOrderedAdBudget (X::xs) B p LinearMap.id =
      pfOrderedAdBudget xs B p LinearMap.id +
      ∑ k : Fin p, ((p-k.val).factorial : ℝ)⁻¹ *
        pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val)) := by
  classical
  have hr : pfOrderedAdBudget (X::xs) B p LinearMap.id =
      ∑ k : Fin (p+1), ((p-k.val).factorial : ℝ)⁻¹ *
        pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val)) := by
    rw [pfOrderedAdBudget_cons]
    simp only [LinearMap.id_comp]
    rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (p+1)))]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.revPerm_apply, Fin.val_rev, Nat.add_sub_add_right]
    rw [Nat.sub_sub_self (Nat.le_of_lt_succ k.isLt)]
  rw [hr, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_mul]
  have hzero : pfAdPowerLinear X 0 = (LinearMap.id : Matrix I I ℂ →ₗ[ℝ] Matrix I I ℂ) := by
    ext C
    rfl
  rw [hzero, add_comm]

/-- Bounds the scaled conjugation remainder of a coefficient by an ordered adjoint budget and
the appropriate word inflation factor. -/
theorem pfConjCoeff_ordered_remainder_scaled_le (skew : Bool) (X B : Matrix I I ℂ)
    (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) (k : Fin p)
    (hX : skew=true → Xᴴ=-X) :
    ‖t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t -
      pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖ ≤
      (((p-k.val).factorial : ℝ)⁻¹ *
        pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val))) *
        |t|^p * pfWordInflation skew [X] t := by
  have hr := pfConjExp_remainder_mode skew X (pfConjCoeff xs B k.val) (p-k.val) t hX
  have hc := pfConjCoeff_ordered_linear_norm_le xs B k.val (pfAdPowerLinear X (p-k.val))
  change ‖pfAdPower X (pfConjCoeff xs B k.val) (p-k.val)‖ ≤ _ at hc
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ |t|^k.val * (‖pfAdPower X (pfConjCoeff xs B k.val) (p-k.val)‖ *
        |t|^(p-k.val) / ((p-k.val).factorial : ℝ) * pfWordInflation skew [X] t) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ |t|^k.val * (pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val)) *
        |t|^(p-k.val) / ((p-k.val).factorial : ℝ) * pfWordInflation skew [X] t) := by
      gcongr
      exact pfWordInflation_nonneg skew [X] t
    _ = (((p-k.val).factorial : ℝ)⁻¹ *
        pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val))) *
        (|t|^k.val * |t|^(p-k.val)) * pfWordInflation skew [X] t := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le k.isLt.le]

/-- Bounds the conjugation-word remainder by the ordered adjoint budget times `|t|^p` and the
word inflation factor. In skew mode the generators are required to be skew-Hermitian. -/
theorem pfConjWord_ordered_remainder_norm_mode (skew : Bool)
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (t : ℝ)
    (hxs : skew=true → ∀ X∈xs, Xᴴ=-X) :
    ‖pfConjWord xs B t - pfConjTrunc xs B p t‖ ≤
      pfOrderedAdBudget xs B p LinearMap.id * |t|^p * pfWordInflation skew xs t := by
  classical
  induction xs generalizing p with
  | nil =>
    cases p with
    | zero =>
      simp [pfConjWord, pfConjTrunc, pfOrderedAdBudget, pfCompositions,
        pfOrderedCompositionWord, pfNestedCommList, pfWordInflation, suzukiMass]
    | succ n =>
      have hp : pfConjTrunc [] B (n+1) t = B := by
        rw [pfConjTrunc, Fin.sum_univ_succ]
        simp [pfConjCoeff]
      rw [pfConjWord, hp, sub_self, norm_zero]
      exact mul_nonneg
        (mul_nonneg (pfOrderedAdBudget_nonneg [] B (n+1) LinearMap.id) (by positivity))
        (pfWordInflation_nonneg skew [] t)
  | cons X xs ih =>
    have hX : skew=true → Xᴴ=-X := fun h => hxs h X List.mem_cons_self
    have htail : skew=true → ∀ Y∈xs, Yᴴ=-Y :=
      fun h Y hY => hxs h Y (List.mem_cons_of_mem X hY)
    have hr := ih p htail
    have hh : ‖pfConjExp X (pfConjWord xs B t - pfConjTrunc xs B p t) t‖ ≤
        pfOrderedAdBudget xs B p LinearMap.id * |t|^p * pfWordInflation skew (X::xs) t := by
      apply ((pfConjExp_norm_mode skew X _ t hX).trans
        (mul_le_mul_of_nonneg_right hr (pfWordInflation_nonneg skew [X] t))).trans_eq
      rw [pfWordInflation_cons skew X xs t]
      ring
    have hs : ‖∑ k : Fin p, t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t -
        pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖ ≤
        (∑ k : Fin p, ((p-k.val).factorial : ℝ)⁻¹ *
          pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val))) *
          |t|^p * pfWordInflation skew (X::xs) t := by
      calc
        _ ≤ ∑ k : Fin p, ‖t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t -
            pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖ := norm_sum_le _ _
        _ ≤ ∑ k : Fin p, (((p-k.val).factorial : ℝ)⁻¹ *
            pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val))) *
            |t|^p * pfWordInflation skew (X::xs) t := by
          apply Finset.sum_le_sum
          intro k _
          apply (pfConjCoeff_ordered_remainder_scaled_le skew X B xs p t k hX).trans
          apply mul_le_mul_of_nonneg_left (pfWordInflation_head_le skew X xs t)
          exact mul_nonneg
            (mul_nonneg (by positivity) (pfOrderedAdBudget_nonneg xs B k.val _)) (by positivity)
        _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [pfConjWord_remainder_cons]
    calc
      _ ≤ ‖pfConjExp X (pfConjWord xs B t-pfConjTrunc xs B p t) t‖ +
          ‖∑ k : Fin p, t^k.val • (pfConjExp X (pfConjCoeff xs B k.val) t -
            pfTaylorBefore (pfConjExp X (pfConjCoeff xs B k.val)) (p-k.val) t)‖ := norm_add_le _ _
      _ ≤ pfOrderedAdBudget xs B p LinearMap.id * |t|^p * pfWordInflation skew (X::xs) t +
          (∑ k : Fin p, ((p-k.val).factorial : ℝ)⁻¹ *
            pfOrderedAdBudget xs B k.val (pfAdPowerLinear X (p-k.val))) *
            |t|^p * pfWordInflation skew (X::xs) t := add_le_add hh hs
      _ = _ := by rw [pfOrderedAdBudget_remainder_cons]; ring

/-- The multinomially weighted sum of seeded nested commutator norms over ordered compositions
of `p`. -/
def pfCommAlphaOrderedV2 (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) : ℝ :=
  ∑ q ∈ pfCompositions xs.length p,
    ((p.factorial : ℝ) / (∏ i, ((q i).factorial : ℝ))) *
      ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖

/-- The revised ordered commutator coefficient equals `p!` times the identity-map ordered
adjoint budget. -/
theorem pfCommAlphaOrderedV2_eq_budget (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) :
    pfCommAlphaOrderedV2 xs B p = (p.factorial : ℝ) * pfOrderedAdBudget xs B p LinearMap.id := by
  simp only [pfCommAlphaOrderedV2, pfOrderedAdBudget, LinearMap.id_apply,
    Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The revised ordered coefficient scaled by `|t|^p/p!` equals the ordered adjoint budget
scaled by `|t|^p`. -/
theorem pfCommAlphaOrderedV2_scaled (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    pfCommAlphaOrderedV2 xs B p * |t|^p / (p.factorial : ℝ) =
      pfOrderedAdBudget xs B p LinearMap.id * |t|^p := by
  rw [pfCommAlphaOrderedV2_eq_budget]
  have hp : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  field_simp

/-- For an empty generator list at order zero, the revised ordered commutator coefficient equals
the seed norm. -/
theorem pfCommAlphaOrderedV2_nil_zero (B : Matrix I I ℂ) :
    pfCommAlphaOrderedV2 [] B 0 = ‖B‖ := by
  simp [pfCommAlphaOrderedV2, pfCompositions, pfOrderedCompositionWord, pfNestedCommList]

end Qatlib.Concepts.TrotterFormula.GeneralOrder
