/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedCompositions
import Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedSegments

/-!
# Grouped integral remainders for ordered conjugations

This module identifies the grouped composition expansion of a conjugation remainder with its
recursive ordered form. It expands the outer remainder into explicit commutator integrals and
matches the last grouping level to that expansion, in the commutator-scaling setting of
[ChildsEtAl2021Trotter].

The theorem `frontier1` combines this identity with segmented error bounds, an explicit
tolerance-based segment choice, and label-visit counts.

## Main statements

* `outer_integrals_compositions`: expansion of the outer remainder over degrees and ordered
  compositions.
* `groupedIntegralRemainder_eq_orderedRemainder`: equality of the grouped and recursive
  remainders for positive order.
* `frontier1`: remainder identity, segmented estimates, selected accuracy, and tagged visit
  counts.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedRemainder
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I]

/-- Expresses `orderedOuterRemainder` as a finite sum of integrals of conjugated iterated
commutators, with the corresponding Taylor weights. -/
theorem outer_integrals (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) :
    orderedOuterRemainder X xs B p t =
      ∑ k : Fin p, ∫ u in 0..t,
        (t^k.val * ((t-u)^(p-k.val-1) / ((p-k.val-1).factorial:ℝ))) •
          pfConjExp X (pfAdPower X (pfConjCoeff xs B k.val) (p-k.val)) u := by
  unfold orderedOuterRemainder
  apply Finset.sum_congr rfl
  intro k _
  have hk : p-k.val-1+1 = p-k.val := by omega
  have h := pfConjExp_taylor_integral_remainder X (pfConjCoeff xs B k.val) (p-k.val-1) t
  rw [hk] at h
  rw [h, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro u _
  (try dsimp only)
  rw [smul_smul]

/-- Conjugation by a fixed matrix exponential commutes with the interval integral of a
continuous matrix-valued function. -/
theorem conjugation_integral (X : Matrix I I ℂ) (f : ℝ → Matrix I I ℂ)
    (hf : Continuous f) (s t : ℝ) :
    (∫ u in 0..t, pfConjExp X (f u) s) = pfConjExp X (∫ u in 0..t, f u) s := by
  let L : Matrix I I ℂ →L[ℝ] Matrix I I ℂ := (pfConjExpLinear X s).toContinuousLinearMap
  exact L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 t)

/-- Combines the finitely many terms of `orderedOuterRemainder` into a single interval integral. -/
theorem outer_integral_sum (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) :
    orderedOuterRemainder X xs B p t =
      ∫ u in 0..t, ∑ k : Fin p,
        (t^k.val * ((t-u)^(p-k.val-1) / ((p-k.val-1).factorial:ℝ))) •
          pfConjExp X (pfAdPower X (pfConjCoeff xs B k.val) (p-k.val)) u := by
  rw [outer_integrals]
  symm
  apply intervalIntegral.integral_finsetSum
  intro k _
  have hscalar : Continuous (fun u : ℝ =>
      t^k.val * ((t-u)^(p-k.val-1) / ((p-k.val-1).factorial:ℝ))) := by fun_prop
  exact (hscalar.smul (pfConjExp_contDiff X
    (pfAdPower X (pfConjCoeff xs B k.val) (p-k.val))).continuous).intervalIntegrable 0 t

/-- Prepending a generator leaves `srcGen` unchanged at indices at most the length of the
original list. -/
theorem srcGen_cons (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (j : ℕ) (hj' : j ≤ xs.length) :
    srcGen (X::xs) j = srcGen xs j := by
  simp only [srcGen,List.length_cons]
  have he : xs.length+1-j=(xs.length-j)+1 := by omega
  rw [he,List.getD_cons_succ]

/-- Prepending a generator leaves `groupedRepetition` unchanged when the composition length does
not exceed the original list length. -/
theorem groupedRepetition_cons (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (q : List ℕ) (hq : q.length ≤ xs.length) :
    groupedRepetition (X::xs) q = groupedRepetition xs q := by
  unfold groupedRepetition
  apply List.flatMap_congr
  intro i _
  rw [srcGen_cons X xs (i.val+1) (by have := i.isLt; omega)]

/-- A grouped integral term whose composition fits in the tail is conjugated by the new leading
exponential when a generator is prepended. -/
theorem groupedIntegralTerm_cons (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (p : ℕ) (q : List ℕ) (hq' : q.length ≤ xs.length) (t : ℝ) :
    groupedIntegralTerm (X::xs) B p q t =
      pfConjExp X (groupedIntegralTerm xs B p q t) t := by
  unfold groupedIntegralTerm
  (try dsimp only)
  rw [groupedRepetition_cons X xs q hq',srcGen_cons X xs q.length hq']
  have he : (X::xs).length-q.length=(xs.length-q.length)+1 := by
    simp only [List.length_cons]
    omega
  rw [he,List.take_succ_cons]
  simp only [pfConjWord]

/-- Splits the grouped remainder for a nonempty word into the conjugated tail remainder and the
sum over compositions at the final level. -/
theorem groupedIntegralRemainder_cons (X B : Matrix I I ℂ)
    (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) :
    groupedIntegralRemainder (X::xs) B p t =
      pfConjExp X (groupedIntegralRemainder xs B p t) t +
        ∑ q∈groupedCompositions p (xs.length+1),groupedIntegralTerm (X::xs) B p q t := by
  unfold groupedIntegralRemainder
  rw [List.length_cons,Finset.sum_Icc_succ_top (by omega : 1 ≤ xs.length+1)]
  congr 1
  change _ = (pfConjExpLinear X t) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hl := ((clause49_grouped_compositions_mem q).mp hq).1
  exact groupedIntegralTerm_cons X B xs p q
    (by have := (Finset.mem_Icc.mp hk).2; omega) t

/-- Lifting `sourceParts s r` with a final part `j` recovers `Fin.cons j r`. -/
theorem groupedLift_last (s j : ℕ) (r : Fin s → ℕ) :
    groupedLift (s+1) (s+1) (sourceParts s r++[j]) = Fin.cons j r := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [groupedLift,Fin.val_zero,Nat.sub_zero,le_refl,ite_true,Fin.cons_zero]
    rw [List.getD_append_right _ _ _ _ (by simp [sourceParts])]
    simp [sourceParts]
  · have ha : s+1-a.succ.val-1=s-1-a.val := by simp only [Fin.val_succ]; omega
    have hb : s+1-a.succ.val ≤ s+1 := by omega
    simp only [groupedLift,if_pos hb,ha,Fin.cons_succ]
    rw [List.getD_append _ _ _ _ (by simp only [sourceParts,List.length_ofFn]; omega),
      clause49_sourceParts_getD r _ (by omega)]
    congr 1
    apply Fin.ext
    change s-1-(s-1-a.val)=a.val
    omega

/-- The final-level grouped repetition is the ordered composition word for the tail followed by
`j` copies of the leading generator. -/
theorem groupedRepetition_last (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (j : ℕ) (r : Fin xs.length → ℕ) :
    groupedRepetition (X::xs) (sourceParts xs.length r++[j]) =
      pfOrderedCompositionWord xs r++List.replicate j X := by
  have hl : (sourceParts xs.length r++[j]).length=(X::xs).length := by simp [sourceParts]
  rw [← clause49_grouped_flat_word (X::xs) _ hl.le]
  simp only [hl,List.length_cons]
  rw [groupedLift_last,pfOrderedCompositionWord_cons]
  simp only [Fin.cons_zero,Fin.cons_succ]

/-- The product of factorials of the source parts equals the product of factorials of the
entries of `r`. -/
theorem sourceParts_factorial_prod (s : ℕ) (r : Fin s → ℕ) :
    (((sourceParts s r).map Nat.factorial).prod : ℝ) = ∏ i,((r i).factorial : ℝ) := by
  simp only [sourceParts,List.map_ofFn,List.prod_ofFn,Nat.cast_prod]
  calc
    _ = ∏ i : Fin s, ((r (Fin.revPerm i)).factorial : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      apply congrArg (fun k : Fin s => ((r k).factorial : ℝ))
      apply Fin.ext
      change s-1-i.val=s-(i.val+1)
      omega
    _ = _ := Equiv.prod_comp Fin.revPerm (fun i => ((r i).factorial : ℝ))

/-- Evaluates the final-level grouped scalar as a Taylor integral weight times the reciprocal
product of composition factorials. -/
theorem groupedScalar_last (s p : ℕ) (n : Fin p) (r : Fin s → ℕ) (t u : ℝ) :
    groupedScalar p (sourceParts s r++[p-n.val]) t u =
      (t^n.val * ((t-u)^(p-n.val-1) / ((p-n.val-1).factorial:ℝ))) *
        (∏ i,((r i).factorial:ℝ))⁻¹ := by
  unfold groupedScalar
  simp only [List.getLastD_concat,List.dropLast_concat]
  rw [show p-(p-n.val)=n.val by omega,sourceParts_factorial_prod]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Expands a final-level grouped integral term into an integral of conjugated iterated
commutators with explicit factorial weights. -/
theorem groupedIntegralTerm_last (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (p : ℕ) (n : Fin p) (r : Fin xs.length → ℕ) (t : ℝ) :
    groupedIntegralTerm (X::xs) B p (sourceParts xs.length r++[p-n.val]) t =
      ∫ u in 0..t,
        ((t^n.val * ((t-u)^(p-n.val-1) / ((p-n.val-1).factorial:ℝ))) *
          (∏ i,((r i).factorial:ℝ))⁻¹) •
          pfConjExp X (pfAdPower X
            (pfNestedCommList (B::pfOrderedCompositionWord xs r)) (p-n.val)) u := by
  unfold groupedIntegralTerm
  (try dsimp only)
  rw [groupedRepetition_last,pfNestedCommList_append_replicate]
  have hl : (sourceParts xs.length r++[p-n.val]).length=(X::xs).length := by simp [sourceParts]
  simp only [hl,Nat.sub_self,List.take_zero,pfConjWord]
  have hx : srcGen (X::xs) (X::xs).length=X := by simp [srcGen]
  rw [hx]
  simp only [groupedScalar_last]

/-- Expands a scaled conjugated commutator of `pfConjCoeff` into a sum over ordered
compositions. -/
theorem coeff_integrand (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (n d : ℕ) (a u : ℝ) :
    a • pfConjExp X (pfAdPower X (pfConjCoeff xs B n) d) u =
      ∑ r∈pfCompositions xs.length n,
        (a*(∏ i,((r i).factorial:ℝ))⁻¹) •
          pfConjExp X (pfAdPower X (pfNestedCommList (B::pfOrderedCompositionWord xs r)) d) u := by
  let L := (pfConjExpLinear X u).comp (pfAdPowerLinear X d)
  change a • L (pfConjCoeff xs B n) = _
  rw [pfConjCoeff_ordered,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul,smul_smul]
  rfl

/-- Expresses the outer remainder as a double sum over Taylor degrees and ordered compositions
of explicit commutator integrals. -/
theorem outer_integrals_compositions (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (p : ℕ) (t : ℝ) :
    orderedOuterRemainder X xs B p t =
      ∑ n : Fin p,∑ r∈pfCompositions xs.length n.val,
        ∫ u in 0..t,
          ((t^n.val * ((t-u)^(p-n.val-1) / ((p-n.val-1).factorial:ℝ))) *
            (∏ i,((r i).factorial:ℝ))⁻¹) •
            pfConjExp X (pfAdPower X
              (pfNestedCommList (B::pfOrderedCompositionWord xs r)) (p-n.val)) u := by
  rw [outer_integrals]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [coeff_integrand]
  apply intervalIntegral.integral_finsetSum
  intro r _
  have hc : Continuous (fun u : ℝ =>
      (t^n.val * ((t-u)^(p-n.val-1) / ((p-n.val-1).factorial:ℝ))) *
        (∏ i,((r i).factorial:ℝ))⁻¹) := by fun_prop
  exact (hc.smul (pfConjExp_contDiff X
    (pfAdPower X (pfNestedCommList (B::pfOrderedCompositionWord xs r)) (p-n.val))).continuous).intervalIntegrable 0 t

/-- The sum of grouped integral terms at the final level equals `orderedOuterRemainder`. -/
theorem grouped_last_level (X B : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (p : ℕ) (t : ℝ) :
    (∑ q∈groupedCompositions p (xs.length+1),groupedIntegralTerm (X::xs) B p q t) =
      orderedOuterRemainder X xs B p t := by
  rw [grouped_sum_last,outer_integrals_compositions]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro r _
  exact groupedIntegralTerm_last X B xs p n r t

/-- For positive order, the grouped integral remainder equals the recursively defined ordered
remainder. -/
theorem groupedIntegralRemainder_eq_orderedRemainder (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    groupedIntegralRemainder xs B p t = orderedRemainder xs B p t := by
  induction xs with
  | nil => rw [Qatlib.Concepts.TrotterFormula.GeneralOrder.groupedIntegralRemainder_nil,
      clause49_remainder_nil B p hp t]
  | cons X xs ih =>
    rw [groupedIntegralRemainder_cons,grouped_last_level,ih]
    exact (pfConjWord_remainder_cons X B xs p t).symm

/-- Identifies the grouped integral remainder with the ordered remainder for every positive
order. -/
theorem grouped_identity [DecidableEq I] (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    groupedIntegralRemainder xs B p t=orderedRemainder xs B p t := by
  cases Subsingleton.elim ‹DecidableEq I› (Classical.decEq I)
  exact groupedIntegralRemainder_eq_orderedRemainder xs B p hp t

/-- For a matched skew-Hermitian word of positive order, combines the grouped remainder identity
with ordered and raw commutator error bounds. The selected tagged word attains the requested
tolerance and has the stated number of visits to each label. -/
theorem frontier1 [DecidableEq I] {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (B H : Matrix I I ℂ) (p r : ℕ) (t ε : ℝ)
    (hp : 1 ≤ p) (hr : 0<r) (hε : 0<ε)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) (hH : H.conjTranspose = -H) :
    groupedIntegralRemainder xs B p t=orderedRemainder xs B p t ∧
      ‖(segmentWord xs t r).prod-NormedSpace.exp (t • H)‖ ≤
        prefixMultinomial xs p*|t|^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p) ∧
      ‖(segmentWord xs t r).prod-NormedSpace.exp (t • H)‖ ≤
        (p.factorial:ℝ)*pfCommAlphaSelf xs (p+1)*|t|^(p+1)/
          (((p+1).factorial:ℝ)*(r:ℝ)^p) ∧
      0<orderedSegments xs p t ε ∧
      ‖((taggedSegmentWord xs lab t (orderedSegments xs p t ε)).map Prod.snd).prod-
        NormedSpace.exp (t • H)‖ ≤ ε ∧
      ∀ j,(taggedSegmentWord xs lab t (orderedSegments xs p t ε)).countP (fun z => z.1=j) =
        orderedSegments xs p t ε*((List.finRange xs.length).filter (fun i => lab i=j)).length := by
  cases Subsingleton.elim ‹DecidableEq I› (Classical.decEq I)
  refine ⟨grouped_identity xs B p hp t,?_,?_,selected_tagged_error xs lab H p t ε hp hε hc hxs hH⟩
  · rw [segmentWord,pf_segment_word_prod]
    exact matched_segmented_ordered xs H p r t hp hr hc hxs hH
  · rw [segmentWord,pf_segment_word_prod]
    exact pf_matched_word_segmented_skew xs H p r t hp hr hc hxs hH

end Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedRemainder
