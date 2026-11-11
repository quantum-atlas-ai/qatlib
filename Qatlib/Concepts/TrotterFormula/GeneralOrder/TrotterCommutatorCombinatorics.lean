/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Grouped remainders and support-chain counting

This module proves Taylor integral identities for single-generator conjugation and relates them
to the grouped remainder definitions. It also develops finite-support counting estimates used to
organize local product-formula costs in commutator-scaling analyses [ChildsEtAl2021Trotter].

Double counting bounds packed support families, while successive overlap choices bound
`supportChainCount`. The result `finiteRangeLedger_witness` packages segment, depth, and routing
bounds into a resource record.

## Main statements

* `clause17_identity_singleton`: grouped remainder identity for a singleton generator.
* `packing_card_bound`: bound on the size of a packed family of nonempty supports.
* `supportChainCount_le`: factorial overlap-degree bound for support chains.
* `finiteRangeLedger_witness`: finite-range resource ledger with explicit bounds.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false
set_option maxHeartbeats 400000

open Matrix Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped ComplexOrder
open Set
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Expresses the error of exponential conjugation after truncation before degree `n+1` as the
weighted integral of the conjugated `(n+1)`st iterated commutator. -/
theorem pfConjExp_taylor_integral_remainder (X C : Matrix I I ℂ) (n : ℕ) (t : ℝ) :
    pfConjExp X C t - pfTaylorBefore (pfConjExp X C) (n + 1) t =
      ∫ τ in 0..t, (((t - τ) ^ n / (n.factorial : ℝ)) •
        pfConjExp X (pfAdPower X C (n + 1)) τ) := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [pfTaylorBefore_succ, taylorWithinEval_self, sub_self,
      intervalIntegral.integral_same]
  · have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_Icc (by grind)
    have hcd := pfConjExp_contDiff X C
    have hca (k : ℕ) (x : ℝ) : ContDiffAt ℝ ((k : ℕ) : ℕ∞) (pfConjExp X C) x :=
      (hcd.contDiffAt).of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
    have hrem := taylor_integral_remainder (f := pfConjExp X C) (x := t) (x₀ := 0)
      (n := n) ((hcd.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn
        (s := uIcc 0 t))
    have hpoly : taylorWithinEval (pfConjExp X C) n (uIcc 0 t) 0 t =
        taylorWithinEval (pfConjExp X C) n univ 0 t := by
      rw [taylor_within_apply, taylor_within_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hca j 0) (left_mem_uIcc),
        iteratedDerivWithin_univ]
    have hcongr : EqOn (fun τ => (((t - τ) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) (pfConjExp X C) (uIcc 0 t) τ))
        (fun τ => (((t - τ) ^ n / (n.factorial : ℝ)) •
        pfConjExp X (pfAdPower X C (n + 1)) τ)) (uIcc 0 t) := by
      intro τ hτ
      show (((t - τ) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) (pfConjExp X C) (uIcc 0 t) τ) = _
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hca (n + 1) τ) hτ,
        pfConjExp_iteratedDeriv]
    rw [pfTaylorBefore_succ, ← hpoly, hrem, intervalIntegral.integral_congr hcongr]
omit [DecidableEq I] in

/-- The grouped integral remainder of an empty generator list is zero. -/
theorem groupedIntegralRemainder_nil (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    groupedIntegralRemainder [] B p t = 0 := by
  simp [groupedIntegralRemainder]

/-- For positive `p`, the only grouped composition of length one is the singleton list
containing `p`. -/
theorem groupedCompositions_one {p : ℕ} (hp : 0 < p) :
    groupedCompositions p 1 = ({List.replicate 1 p} : Finset (List ℕ)) := by
  classical
  ext q
  simp only [groupedCompositions, Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨f, _, hq⟩, hs, _⟩
    have hof : List.ofFn (fun i : Fin 1 => (f i).val) = [(f 0).val] := by
      rw [List.ofFn_succ, List.ofFn_zero]
    rw [hof] at hq
    have hq' : q = [(f 0).val] := hq.symm
    subst hq'
    have hs' : ([(f 0).val] : List ℕ).sum = (f 0).val := by simp
    rw [hs'] at hs
    rw [hs]
    simp
  · rintro rfl
    refine ⟨⟨fun _ => ⟨p, Nat.lt_succ_self p⟩, Finset.mem_univ _, ?_⟩, by simp, by exact hp.ne'⟩
    rw [List.ofFn_succ, List.ofFn_zero]
    simp
open scoped ComplexOrder
open Set
variable {I : Type} [Fintype I] [DecidableEq I]
variable {I : Type} [Fintype I]

/-- For a singleton generator list, the grouped integral term is the Taylor-weighted integral of
the conjugated order-`p` commutator. -/
theorem groupedIntegralTerm_singleton (X B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    groupedIntegralTerm [X] B p (List.replicate 1 p) t =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        pfConjExp X (pfAdPower X B p) τ) := by
  have hlen : (List.replicate 1 p).length = 1 := List.length_replicate
  have hlast : (List.replicate 1 p).getLastD 0 = p := by simp
  have hdrop : ((List.replicate 1 p).dropLast.map Nat.factorial).prod = 1 := by simp
  have hscalar : ∀ τ : ℝ, groupedScalar p (List.replicate 1 p) t τ =
      ((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) := by
    intro τ
    show (((t - τ) ^ ((List.replicate 1 p).getLastD 0 - 1) *
        t ^ (p - (List.replicate 1 p).getLastD 0)) /
      ((((List.replicate 1 p).getLastD 0 - 1).factorial : ℝ) *
        (((List.replicate 1 p).dropLast.map Nat.factorial).prod : ℝ))) = _
    rw [hlast, hdrop, Nat.sub_self, pow_zero, mul_one, Nat.cast_one, mul_one]
  have hsrc : srcGen [X] (List.replicate 1 p).length = X := by
    rw [hlen]
    rfl
  have hrep : groupedRepetition [X] (List.replicate 1 p) = List.replicate p X := by
    have hfr : List.finRange 1 = [(0 : Fin 1)] := by
      rw [← List.ofFn_id, List.ofFn_succ, List.ofFn_zero]
      simp
    simp only [groupedRepetition]
    rw [hlen, hfr]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  have hnest : pfNestedCommList (B :: groupedRepetition [X] (List.replicate 1 p)) =
      pfAdPower X B p := by
    rw [hrep]
    simpa using! pfNestedCommList_append_replicate B X ([] : List (Matrix I I ℂ)) p
  have htake : ([X] : List (Matrix I I ℂ)).take (1 - (List.replicate 1 p).length) = [] := by
    rw [hlen]
    rfl
  have hbody : (∫ τ in 0..t, (groupedScalar p (List.replicate 1 p) t τ) •
        pfConjWord [srcGen [X] (List.replicate 1 p).length]
          (pfNestedCommList (B :: groupedRepetition [X] (List.replicate 1 p))) τ) =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        pfConjExp X (pfAdPower X B p) τ) := by
    refine intervalIntegral.integral_congr fun τ _ => ?_
    show (groupedScalar p (List.replicate 1 p) t τ) •
        pfConjWord [srcGen [X] (List.replicate 1 p).length]
          (pfNestedCommList (B :: groupedRepetition [X] (List.replicate 1 p))) τ = _
    rw [hscalar τ, hsrc, hnest]
    rfl
  show pfConjWord (([X] : List (Matrix I I ℂ)).take (1 - (List.replicate 1 p).length))
      (∫ τ in 0..t, (groupedScalar p (List.replicate 1 p) t τ) •
        pfConjWord [srcGen [X] (List.replicate 1 p).length]
          (pfNestedCommList (B :: groupedRepetition [X] (List.replicate 1 p))) τ) t = _
  rw [htake, hbody]
  rfl

/-- For a singleton generator list and positive order, the grouped remainder is the integral of
the conjugated order-`p` commutator with the Taylor remainder weight. -/
theorem groupedIntegralRemainder_singleton (X B : Matrix I I ℂ) (p : ℕ)
    (hp : 0 < p) (t : ℝ) :
    groupedIntegralRemainder [X] B p t =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        pfConjExp X (pfAdPower X B p) τ) := by
  classical
  show ∑ k ∈ Finset.Icc 1 1, ∑ q ∈ groupedCompositions p k,
    groupedIntegralTerm [X] B p q t = _
  rw [Finset.Icc_self, Finset.sum_singleton, groupedCompositions_one hp,
    Finset.sum_singleton]
  exact groupedIntegralTerm_singleton X B p t

/-- For a singleton generator and positive order, the difference between conjugation and its
truncation equals the grouped integral remainder. -/
theorem clause17_identity_singleton (X B : Matrix I I ℂ) (p : ℕ) (hp : 0 < p) (t : ℝ) :
    pfConjWord [X] B t - pfConjTrunc [X] B p t = groupedIntegralRemainder [X] B p t := by
  have hpp : p - 1 + 1 = p := by omega
  have hfun : pfConjWord [X] B = pfConjExp X B := rfl
  have htrunc : pfConjTrunc [X] B p t = pfTaylorBefore (pfConjExp X B) p t := by
    rw [← hfun]
    exact (pfConjWord_taylor_before [X] B p t).symm
  have w1 := pfConjExp_taylor_integral_remainder X B (p - 1) t
  rw [hpp] at w1
  rw [hfun, htrunc, groupedIntegralRemainder_singleton X B p hp t]
  exact w1

/-- The cardinality of a finite subset is the sum of its membership indicator over the ambient
finite type. -/
theorem card_eq_sum_ite {α : Type} [Fintype α] (t : Finset α) :
    t.card = ∑ a : α, (if a ∈ t then (1 : ℕ) else 0) := by
  have h : t = Finset.univ.filter (fun a => a ∈ t) := by
    ext a
    simp
  conv_lhs => rw [h]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The sum of support cardinalities equals the sum, over sites, of the number of supports
containing each site. -/
theorem sum_card_support_eq_sum_card_fiber {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) :
    (∑ i : ι, (supp i).card) =
      ∑ x : S, (Finset.univ.filter (fun i : ι => x ∈ supp i)).card := by
  classical
  calc
    (∑ i : ι, (supp i).card) = ∑ i : ι, ∑ x : S, (if x ∈ supp i then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact card_eq_sum_ite (supp i)
    _ = ∑ x : S, ∑ i : ι, (if x ∈ supp i then (1 : ℕ) else 0) :=
      Finset.sum_comm
    _ = ∑ x : S, (Finset.univ.filter (fun i : ι => x ∈ supp i)).card := by
      apply Finset.sum_congr rfl
      intro x _
      rw [card_eq_sum_ite (Finset.univ.filter (fun i : ι => x ∈ supp i))]
      simp

/-- A family of nonempty supports with at most `τ` terms per site has at most `τ * Fintype.card
S` terms. -/
theorem packing_card_bound {S : Type} [Fintype S] {m : ℕ} (supp : Fin m → Finset S)
    (τ : ℕ) (hτ : IsTermPacking supp τ) (hne : ∀ i : Fin m, (supp i).Nonempty) :
    m ≤ τ * Fintype.card S := by
  classical
  have hone : ∀ i : Fin m, 1 ≤ (supp i).card := fun i => Finset.card_pos.mpr (hne i)
  have hsum : (m : ℕ) ≤ ∑ i : Fin m, (supp i).card :=
    calc
      (m : ℕ) = ∑ i : Fin m, (1 : ℕ) := by simp
      _ ≤ ∑ i : Fin m, (supp i).card := Finset.sum_le_sum (fun i _ => hone i)
  have hdouble := sum_card_support_eq_sum_card_fiber supp
  have hsum' : (m : ℕ) ≤ ∑ x : S, (Finset.univ.filter (fun i : Fin m => x ∈ supp i)).card :=
    hsum.trans_eq hdouble
  have hpack : (∑ x : S, (Finset.univ.filter (fun i : Fin m => x ∈ supp i)).card) ≤
      ∑ x : S, τ := Finset.sum_le_sum (fun x _ => hτ x)
  have hconst : (∑ x : S, τ) = τ * Fintype.card S := by
    rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    ring
  linarith

/-- Constructs a finite-range resource ledger with the specified segment and gate counts, depth
bounded by the maximal overlap degree plus one, and routing swaps bounded by the sum of
support swap budgets. -/
theorem finiteRangeLedger_witness {S : Type} [Fintype S] {m : ℕ}
    (supp : Fin m → Finset S) (dist : S → S → ℝ) (τ : ℕ)
    (hτ : IsTermPacking supp τ) (hne : ∀ i : Fin m, (supp i).Nonempty)
    {D : ℕ} (xs : List (Operator D)) (lab : Fin xs.length → Fin m) (r : ℕ) :
    ∃ ledger : FiniteRangeLedger,
      ledger.segments = r ∧
      ledger.gatesPerStep = xs.length ∧
      ledger.depthPerStep ≤ maxOverlapDegree supp + 1 ∧
      ledger.routingSwapsPerStep ≤
        ((List.finRange xs.length).map (fun i =>
          supportSwapBudget dist (supp (lab i)))).sum ∧
      m ≤ τ * Fintype.card S ∧
      r * ledger.gatesPerStep = r * xs.length ∧
      r * (ledger.depthPerStep + ledger.routingSwapsPerStep) ≤
        r * (maxOverlapDegree supp + 1 +
          ((List.finRange xs.length).map (fun i =>
            supportSwapBudget dist (supp (lab i)))).sum) := by
  refine ⟨⟨r, xs.length, maxOverlapDegree supp + 1,
    ((List.finRange xs.length).map (fun i =>
      supportSwapBudget dist (supp (lab i)))).sum⟩, rfl, rfl, le_rfl, le_rfl,
      packing_card_bound supp τ hτ hne, rfl, le_rfl⟩
open scoped ComplexOrder
open Set
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]
variable {I : Type} [Fintype I]
variable {S ι : Type} [Fintype S] [Fintype ι]

/-- The value of `f` at any member of a list is bounded by the fold taking the maximum of all
values and zero. -/
theorem le_list_foldl_max {α : Type} (f : α → ℕ) (l : List α) (x : α) (hx : x ∈ l) :
    f x ≤ l.foldl (fun acc b => max acc (f b)) 0 := by
  have key : ∀ (z : ℕ) (l : List α), f x ≤ z ∨ x ∈ l →
      f x ≤ l.foldl (fun acc b => max acc (f b)) z := by
    intro z l
    induction l generalizing z with
    | nil =>
      intro h
      exact h.elim id (fun h' => nomatch h')
    | cons a l ih =>
      intro h
      rw [List.foldl_cons]
      refine ih _ ?_
      rcases h with h | h
      · exact Or.inl (le_trans h (le_max_left z (f a)))
      · rcases List.mem_cons.mp h with h | h
        · left
          rw [← h]
          exact le_max_right z (f x)
        · exact Or.inr h
  exact key 0 l (Or.inr hx)

/-- Each support overlap degree is bounded by the maximum overlap degree. -/
theorem overlapDegree_le_maxOverlapDegree (supp : ι → Finset S) (a : ι) :
    overlapDegree supp a ≤ maxOverlapDegree supp := by
  set f : Fin (Fintype.card ι) → ℕ :=
    fun i => overlapDegree supp ((Fintype.equivFin ι).symm i) with hf
  have ha : Fintype.equivFin ι a ∈ List.finRange (Fintype.card ι) := List.mem_finRange _
  have hfeq : f (Fintype.equivFin ι a) = overlapDegree supp a := by
    simp [hf, Equiv.symm_apply_apply]
  have h := le_list_foldl_max f (List.finRange (Fintype.card ι)) (Fintype.equivFin ι a) ha
  rw [hfeq] at h
  exact h

/-- The number of supports intersecting a given support, including itself when nonempty, is at
most the maximum overlap degree plus one. -/
theorem card_overlap_neighbors_le (supp : ι → Finset S) (a : ι) :
    (Finset.univ.filter (fun b : ι => (supp a ∩ supp b).Nonempty)).card ≤
      maxOverlapDegree supp + 1 := by
  classical
  have hsub : (Finset.univ.filter (fun b : ι => (supp a ∩ supp b).Nonempty)) ⊆
      insert a (Finset.univ.filter (fun b : ι => b ≠ a ∧ (supp a ∩ supp b).Nonempty)) := by
    intro b hb
    have hb' : (supp a ∩ supp b).Nonempty := by simpa using! hb
    by_cases hba : b = a
    · simp [hba]
    · exact Finset.mem_insert_of_mem (by simp [hba, hb'])
  have hdeq : (Finset.univ.filter (fun b : ι => b ≠ a ∧ (supp a ∩ supp b).Nonempty)).card =
      overlapDegree supp a := rfl
  have h1 : (Finset.univ.filter (fun b : ι => (supp a ∩ supp b).Nonempty)).card ≤
      (Finset.univ.filter (fun b : ι => b ≠ a ∧ (supp a ∩ supp b).Nonempty)).card + 1 :=
    calc
      (Finset.univ.filter (fun b : ι => (supp a ∩ supp b).Nonempty)).card ≤
          (insert a (Finset.univ.filter (fun b : ι =>
            b ≠ a ∧ (supp a ∩ supp b).Nonempty))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun b : ι => b ≠ a ∧ (supp a ∩ supp b).Nonempty)).card + 1 :=
        Finset.card_insert_le _ _
  rw [hdeq] at h1
  have hd := overlapDegree_le_maxOverlapDegree supp a
  omega
omit [Fintype S] in

/-- Removing the last entry from a support chain preserves the support-chain property. -/
theorem supportChain_snoc {ℓ : ℕ} (supp : ι → Finset S) (p : Fin ℓ → ι) (b : ι)
    (h : SupportChain supp (Fin.snoc p b)) : SupportChain supp p := by
  intro j
  have hj := h j.castSucc
  rw [Fin.val_castSucc] at hj
  rcases hj with h0 | hex
  · exact Or.inl h0
  · obtain ⟨i, hilt, hov⟩ := hex
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | hlast
    · refine Or.inr ⟨i', ?_, ?_⟩
      · simpa using! hilt
      · simpa [Fin.snoc_castSucc] using! hov
    · rw [hlast, Fin.val_last] at hilt
      have hj' := j.isLt
      omega
omit [Fintype S] in

/-- The last entry of a support chain with a nonempty prefix intersects the support of some
earlier entry. -/
theorem supportChain_snoc_last {ℓ : ℕ} (hℓ : 0 < ℓ) (supp : ι → Finset S)
    (p : Fin ℓ → ι) (b : ι) (h : SupportChain supp (Fin.snoc p b)) :
    ∃ i : Fin ℓ, ((supp (p i)) ∩ (supp b)).Nonempty := by
  have hj := h (Fin.last ℓ)
  rw [Fin.val_last] at hj
  rcases hj with h0 | hex
  · omega
  · obtain ⟨i, hilt, hov⟩ := hex
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | hlast
    · refine ⟨i', ?_⟩
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using! hov
    · rw [hlast, Fin.val_last] at hilt
      omega

/-- The number of support chains of length one equals the number of term labels. -/
theorem supportChainCount_one (m : ℕ) (supp : Fin m → Finset S) :
    supportChainCount supp 1 = m := by
  classical
  have hall : ∀ idx : Fin 1 → Fin m, SupportChain supp idx := by
    intro idx j
    left
    have hj := j.isLt
    omega
  have hcard : Fintype.card (Fin 1 → Fin m) = m := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]
  have hfilter : (Finset.univ.filter (fun idx : Fin 1 → Fin m => SupportChain supp idx)) =
      Finset.univ := by
    ext idx
    simp [hall]
  unfold supportChainCount
  rw [hfilter, Finset.card_univ]
  exact hcard

/-- For positive chain length `ℓ`, bounds the number of one-step extensions by the current chain
count times `ℓ * (maxOverlapDegree supp + 1)`. -/
theorem supportChainCount_succ_le (m : ℕ) (supp : Fin m → Finset S) {ℓ : ℕ}
    (hℓ : 0 < ℓ) :
    supportChainCount supp (ℓ + 1) ≤
      supportChainCount supp ℓ * (ℓ * (maxOverlapDegree supp + 1)) := by
  classical
  set Δ1 : ℕ := maxOverlapDegree supp + 1
  have hext : ∀ p : Fin ℓ → Fin m,
      (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card ≤
        ℓ * Δ1 := by
    intro p
    have hsub : (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))) ⊆
        Finset.univ.biUnion (fun i : Fin ℓ =>
          Finset.univ.filter (fun b : Fin m => ((supp (p i)) ∩ (supp b)).Nonempty)) := by
      intro b hb
      have hchain : SupportChain supp (Fin.snoc p b) := by simpa using! hb
      obtain ⟨i, hov⟩ := supportChain_snoc_last hℓ supp p b hchain
      refine Finset.mem_biUnion.mpr ⟨i, ?_⟩
      simpa using! hov
    have hcard : (Finset.univ.biUnion (fun i : Fin ℓ =>
        Finset.univ.filter (fun b : Fin m => ((supp (p i)) ∩ (supp b)).Nonempty))).card ≤
        ∑ i : Fin ℓ, Δ1 :=
      calc
        _ ≤ ∑ i : Fin ℓ,
            (Finset.univ.filter (fun b : Fin m => ((supp (p i)) ∩ (supp b)).Nonempty)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ i : Fin ℓ, Δ1 :=
          Finset.sum_le_sum (fun i _ => by
            dsimp [Δ1]
            exact card_overlap_neighbors_le supp (p i))
    calc
      (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card ≤
          (Finset.univ.biUnion (fun i : Fin ℓ =>
            Finset.univ.filter (fun b : Fin m => ((supp (p i)) ∩ (supp b)).Nonempty))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ i : Fin ℓ, Δ1 := hcard
      _ = ℓ * Δ1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  have hsum : supportChainCount supp (ℓ + 1) =
      ∑ p : Fin ℓ → Fin m,
        (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card := by
    unfold supportChainCount
    symm
    calc
      (∑ p : Fin ℓ → Fin m,
          (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card)
          = ∑ p : Fin ℓ → Fin m, ∑ b : Fin m,
            (if SupportChain supp (Fin.snoc p b) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [card_eq_sum_ite (Finset.univ.filter (fun b : Fin m =>
          SupportChain supp (Fin.snoc p b)))]
        simp
      _ = ∑ b : Fin m, ∑ p : Fin ℓ → Fin m,
            (if SupportChain supp (Fin.snoc p b) then 1 else 0) :=
        Finset.sum_comm
      _ = ∑ z : Fin m × (Fin ℓ → Fin m),
          (if SupportChain supp (Fin.snoc z.2 z.1) then 1 else 0) := by
        symm
        exact Fintype.sum_prod_type _
      _ = ∑ idx : Fin (ℓ + 1) → Fin m,
          (if SupportChain supp idx then 1 else 0) :=
        Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (ℓ + 1) => Fin m))
          (fun idx => if SupportChain supp idx then 1 else 0)
      _ = (Finset.univ.filter (fun idx : Fin (ℓ + 1) → Fin m =>
          SupportChain supp idx)).card := by
        rw [card_eq_sum_ite]
        simp
  rw [hsum]
  have hzero : ∀ p : Fin ℓ → Fin m,
      ¬SupportChain supp p →
        (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card = 0 := by
    intro p hp
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact hp (supportChain_snoc supp p b (by simpa using! hb))
  calc
    (∑ p : Fin ℓ → Fin m,
        (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card)
        = ∑ p : Fin ℓ → Fin m,
          (if SupportChain supp p then
            (Finset.univ.filter (fun b : Fin m => SupportChain supp (Fin.snoc p b))).card
          else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : SupportChain supp p
      · simp [hp]
      · simp [hp, hzero p hp]
    _ ≤ ∑ p : Fin ℓ → Fin m, (if SupportChain supp p then ℓ * Δ1 else 0) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : SupportChain supp p
      · simp [hp]
        exact hext p
      · simp [hp]
    _ = (ℓ * Δ1) * supportChainCount supp ℓ := by
      rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]
      unfold supportChainCount
      ring
    _ = supportChainCount supp ℓ * (ℓ * Δ1) := by ring

/-- The number of support chains of length `p+1` is at most `m * p! * (maxOverlapDegree supp +
1)^p`. -/
theorem supportChainCount_le (m : ℕ) (supp : Fin m → Finset S) (p : ℕ) :
    supportChainCount supp (p + 1) ≤
      m * p.factorial * (maxOverlapDegree supp + 1) ^ p := by
  classical
  induction p with
  | zero =>
    rw [supportChainCount_one]
    simp
  | succ p ih =>
    have hstep := supportChainCount_succ_le m supp (by omega : 0 < p + 1)
    calc
      supportChainCount supp (p + 1 + 1) ≤
          supportChainCount supp (p + 1) * ((p + 1) * (maxOverlapDegree supp + 1)) := hstep
      _ ≤ (m * p.factorial * (maxOverlapDegree supp + 1) ^ p) *
          ((p + 1) * (maxOverlapDegree supp + 1)) :=
        mul_le_mul_of_nonneg_right ih (Nat.zero_le _)
      _ = m * (p + 1).factorial * (maxOverlapDegree supp + 1) ^ (p + 1) := by
        rw [Nat.factorial_succ, Nat.pow_succ]
        ring
end Qatlib.Concepts.TrotterFormula.GeneralOrder
