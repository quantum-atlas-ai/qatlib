/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorRefinedDefs

/-!
# Refined ordered commutator expansions

This module proves the correspondence between grouped and flat compositions in ordered
conjugation expansions. It decomposes `orderedRemainder` by source level, identifies its Cauchy
integral form, and matches the words, weights, and budgets produced by `groupedLift`, in the
commutator-scaling setting of [ChildsEtAl2021Trotter].

It also establishes family scale and seed conversions, low-degree coefficient deviations,
support-growth estimates, and explicit first-fit parallel schedules. Further results track
long-range truncation, inverse stability, partition and synthesis errors, recursive Suzuki stage
counts, and gate and routing costs.

## Main statements

* `clause49_endpoint`: collects the ordered remainder and grouped-composition identities.
* `clause50_endpoint`: collects scale alignment, seed conversion, and budget normalization.
* `clause51_endpoint`: collects explicit two-generator coefficient deviations.
* `clause52_parallel_depth_endpoint`: gives the macro stage, depth, gate, and routing
  identities.
* `clause61_gate_count_endpoint`: relates the ferromagnetic ledger to executed word lengths.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSourceBoundsDefs
open Qatlib
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorExt
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The ordered remainder for an empty generator list vanishes at every positive order. -/
theorem clause49_remainder_nil (B : Matrix I I ℂ) (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    orderedRemainder [] B p t = 0 := by
  have hzero : ∀ b : Fin p, b.val ≠ 0 → pfConjCoeff [] B b.val = 0 := by
    intro b hb
    have hb1 : b.val = (b.val - 1) + 1 := by omega
    rw [hb1, pfConjCoeff.eq_2]
  have hsum : (∑ n : Fin p, t ^ n.val • pfConjCoeff [] B n.val) = B := by
    have h0 : (⟨0, hp⟩ : Fin p).val = 0 := rfl
    calc (∑ n : Fin p, t ^ n.val • pfConjCoeff [] B n.val)
        = t ^ (⟨0, hp⟩ : Fin p).val • pfConjCoeff [] B (⟨0, hp⟩ : Fin p).val := by
          refine Finset.sum_eq_single (f := fun n : Fin p =>
            t ^ n.val • pfConjCoeff [] B n.val) (⟨0, hp⟩ : Fin p) ?_ ?_
          · intro b _ hb
            show t ^ b.val • pfConjCoeff [] B b.val = 0
            rw [hzero b (fun hval => hb (Fin.ext hval)), smul_zero]
          · intro h
            exact (h (Finset.mem_univ _)).elim
      _ = B := by simp only [pfConjCoeff, pow_zero, one_smul]
  simp only [orderedRemainder, pfConjWord, pfConjTrunc, hsum, sub_self]

/-- The ordered remainder at positive order is the sum of its contributions over generator
levels. -/
theorem clause49_remainder_level_decomposition (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    orderedRemainder xs B p t =
      ∑ k ∈ Finset.range xs.length, orderedRemainderLevel xs B p k t := by
  have hshift : ∀ (n : ℕ) (g : ℕ → Matrix I I ℂ),
      (∑ k ∈ Finset.range (n + 1), g k) = g 0 + ∑ k ∈ Finset.range n, g (k + 1) := by
    intro n
    induction n with
    | zero => intro g; simp [Finset.sum_range_succ]
    | succ n ih =>
      intro g
      have h1 : (∑ k ∈ Finset.range (n + 1 + 1), g k) =
          (∑ k ∈ Finset.range (n + 1), g k) + g (n + 1) :=
        Finset.sum_range_succ (f := g) (n := n + 1)
      have h2 : (∑ k ∈ Finset.range (n + 1), g k) =
          g 0 + ∑ k ∈ Finset.range n, g (k + 1) := ih g
      have h3 : (∑ k ∈ Finset.range (n + 1), g (k + 1)) =
          (∑ k ∈ Finset.range n, g (k + 1)) + g (n + 1) :=
        Finset.sum_range_succ (f := fun k => g (k + 1)) (n := n)
      rw [h1, h2, h3]
      abel
  have hlin : ∀ (X : Matrix I I ℂ) (s : Finset ℕ) (f : ℕ → Matrix I I ℂ),
      (∑ k ∈ s, pfConjExp X (f k) t) = pfConjExp X (∑ k ∈ s, f k) t := by
    intro X s
    induction s using Finset.induction_on with
    | empty =>
      intro f
      simp [Finset.sum_empty, pfConjExp]
    | @insert a s ha ihf =>
      intro f
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ihf, ← pfConjExp_add]
  induction xs with
  | nil => exact clause49_remainder_nil B p hp t
  | cons X xs ih =>
    have hrec := pfConjWord_remainder_cons X B xs p t
    have hLHS : orderedRemainder (X :: xs) B p t =
        pfConjExp X (orderedRemainder xs B p t) t + orderedOuterRemainder X xs B p t := by
      simp only [orderedRemainder, orderedOuterRemainder]
      rw [hrec]
    have hlevel0 : orderedRemainderLevel (X :: xs) B p 0 t =
        orderedOuterRemainder X xs B p t := by
      show pfConjWord ((X :: xs).take 0)
          (orderedOuterRemainder ((X :: xs).getD 0 0) ((X :: xs).drop 1) B p t) t = _
      rw [List.take_zero, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
      rfl
    have hlevelSucc : ∀ k ∈ Finset.range xs.length,
        orderedRemainderLevel (X :: xs) B p (k + 1) t =
          pfConjExp X (orderedRemainderLevel xs B p k t) t := by
      intro k hk
      show pfConjWord ((X :: xs).take (k + 1))
          (orderedOuterRemainder ((X :: xs).getD (k + 1) 0) ((X :: xs).drop (k + 2)) B p t) t = _
      rw [List.take_succ_cons, List.drop_succ_cons, List.getD_cons_succ]
      show pfConjWord (X :: xs.take k)
          (orderedOuterRemainder (xs.getD k 0) (xs.drop (k + 1)) B p t) t = _
      rw [pfConjWord]
      show pfConjExp X (pfConjWord (xs.take k)
          (orderedOuterRemainder (xs.getD k 0) (xs.drop (k + 1)) B p t) t) t = _
      rw [orderedRemainderLevel]
    have hRHS : (∑ k ∈ Finset.range (X :: xs).length,
          orderedRemainderLevel (X :: xs) B p k t) =
        orderedOuterRemainder X xs B p t +
          ∑ k ∈ Finset.range xs.length,
            pfConjExp X (orderedRemainderLevel xs B p k t) t := by
      rw [show (X :: xs).length = xs.length + 1 by simp, hshift]
      rw [hlevel0]
      rw [Finset.sum_congr rfl (fun k hk => hlevelSucc k hk)]
    rw [hLHS, hRHS, hlin X (Finset.range xs.length), ih]
    abel

/-- The positive-order ordered remainder equals the Cauchy integral remainder of `pfConjWord`. -/
theorem clause49_remainder_eq_cauchy_integral (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (hp : 0 < p) (t : ℝ) :
    orderedRemainder xs B p t =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDeriv p (pfConjWord xs B) τ) := by
  exact pfConjWord_taylor_integral_remainder xs B p hp t

/-- Appending the source generator at level `k` extends the corresponding outer prefix by one
element. -/
theorem clause49_outer_inner_split (xs : List (Matrix I I ℂ)) (k : ℕ)
    (hk : 1 ≤ k) (hk' : k ≤ xs.length) :
    xs.take (xs.length - k) ++ [srcGen xs k] = xs.take (xs.length - k + 1) := by
  have hlt : xs.length - k < xs.length := by omega
  have hget : srcGen xs k = xs[xs.length - k] := by
    simp only [srcGen]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  have htake := List.take_succ_eq_append_getElem (l := xs) (i := xs.length - k)
    (by omega)
  rw [htake, hget]

/-- The grouped scalar equals the time-power weight divided by the last-part factorial and the
product of the preceding factorials. -/
theorem clause49_grouped_scalar_weight (p : ℕ) (q' : List ℕ) (t τ : ℝ) :
    groupedScalar p q' t τ =
      (t - τ) ^ (q'.getLastD 0 - 1) * t ^ (p - q'.getLastD 0) /
        (((q'.getLastD 0 - 1).factorial : ℝ) *
          ((q'.dropLast.map Nat.factorial).prod : ℝ)) := by
  simp only [groupedScalar]

/-- An index belongs to the support of `groupedLift` exactly when its reversed position lies
within `k` and the corresponding grouped part is nonzero. -/
theorem clause49_lift_support {s k : ℕ} (q' : List ℕ) (i : Fin s) :
    i ∈ compositionSupport (groupedLift s k q') ↔
      s - i.val ≤ k ∧ q'.getD (s - i.val - 1) 0 ≠ 0 := by
  simp [compositionSupport, groupedLift]

/-- A grouped lift has level `k` when `k` is positive, bounded by `s`, and its last active part
is nonzero. -/
theorem clause49_lift_level (s k : ℕ) (q' : List ℕ) (hk0 : 0 < k) (hks : k ≤ s)
    (hne : q'.getD (k - 1) 0 ≠ 0) :
    compositionLevel (groupedLift s k q') = k := by
  classical
  obtain ⟨sk, hsk⟩ : ∃ (i : Fin s), i.val = s - k := ⟨⟨s - k, by omega⟩, rfl⟩
  set S : Finset (Fin s) := compositionSupport (groupedLift s k q') with hSdef
  have hmemS : sk ∈ S := by
    refine hSdef ▸ ?_
    rw [clause49_lift_support]
    refine ⟨by omega, ?_⟩
    have hval : s - sk.val - 1 = k - 1 := by rw [hsk]; omega
    rw [hval]
    exact hne
  have hnonempty : S.Nonempty := ⟨sk, hmemS⟩
  have hmin : S.min' hnonempty = sk := by
    apply le_antisymm
    · exact Finset.min'_le S sk hmemS
    · have hle : ∀ b ∈ S, sk ≤ b := by
        intro b hb
        rw [hSdef, clause49_lift_support] at hb
        have hval : s - k ≤ b.val := by omega
        have hval' : sk.val ≤ b.val := by rw [hsk]; exact hval
        exact Fin.mk_le_mk.mpr hval'
      exact hle (S.min' hnonempty) (Finset.min'_mem S hnonempty)
  rw [compositionLevel, dif_pos (hSdef ▸ hnonempty), hmin, hsk]
  omega

omit [DecidableEq I] in

/-- Prepending a generator preserves source generators at levels belonging to the original list. -/
theorem clause49_srcGen_cons_lt (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (j : ℕ) (hj : j < xs.length) :
    srcGen (X :: xs) (j + 1) = srcGen xs (j + 1) := by
  simp only [srcGen]
  have hlen : (X :: xs).length = xs.length + 1 := rfl
  rw [hlen]
  have hsub : xs.length + 1 - (j + 1) = xs.length - j := by omega
  rw [hsub]
  have h2 : xs.length - j = (xs.length - j - 1) + 1 := by omega
  rw [h2, List.getD_cons_succ]
  congr 1

omit [DecidableEq I] in
omit [DecidableEq I] in

/-- The final source level of `X :: xs` selects `X`. -/
theorem clause49_srcGen_cons_last (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) :
    srcGen (X :: xs) (xs.length + 1) = X := by
  simp only [srcGen]
  have h : (X :: xs).length - (xs.length + 1) = 0 := by simp
  rw [h, List.getD_cons_zero]

omit [DecidableEq I] in

/-- The source block word of `X :: xs` appends `q 0` copies of `X` to the source block word of
the tail. -/
theorem clause49_source_block_word_cons (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ))
    (q : Fin (xs.length + 1) → ℕ) :
    sourceBlockWord (X :: xs) q =
      sourceBlockWord xs (fun j => q j.succ) ++ List.replicate (q 0) X := by
  show (List.finRange (xs.length + 1)).flatMap
      (fun i : Fin (xs.length + 1) =>
        List.replicate (q ⟨xs.length - i.val, by omega⟩) (srcGen (X :: xs) (i.val + 1))) = _
  show (List.finRange (xs.length + 1)).flatMap
      (fun i : Fin (xs.length + 1) =>
        List.replicate (q ⟨xs.length - i.val, by omega⟩) (srcGen (X :: xs) (i.val + 1))) =
      (List.finRange xs.length).flatMap
        (fun i : Fin xs.length =>
          List.replicate ((fun j : Fin xs.length => q j.succ) ⟨xs.length - 1 - i.val, by omega⟩)
            (srcGen xs (i.val + 1))) ++ List.replicate (q 0) X
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
    List.flatMap_singleton]
  simp only [Fin.val_last]
  rw [clause49_srcGen_cons_last X xs]
  have hcount : q ⟨xs.length - xs.length, by omega⟩ = q 0 := by
    apply congrArg q
    apply Fin.ext
    show (xs.length - xs.length) = 0
    omega
  rw [hcount]
  apply congrArg (fun l => l ++ List.replicate (q 0) X)
  apply List.flatMap_congr
  intro i hi
  have hgen : srcGen (X :: xs) ((i.castSucc : Fin (xs.length + 1)).val + 1) =
      srcGen xs (i.val + 1) := by
    have hcast : (i.castSucc : Fin (xs.length + 1)).val = i.val := rfl
    rw [hcast]
    exact clause49_srcGen_cons_lt X xs i.val i.isLt
  rw [hgen]
  have hcnt : q ⟨xs.length - (i.castSucc : Fin (xs.length + 1)).val, by omega⟩ =
      (fun j : Fin xs.length => q j.succ) ⟨xs.length - 1 - i.val, by omega⟩ := by
    apply congrArg q
    apply Fin.ext
    show (xs.length - (i.castSucc : Fin (xs.length + 1)).val) =
      (xs.length - 1 - i.val) + 1
    have hcast : (i.castSucc : Fin (xs.length + 1)).val = i.val := rfl
    rw [hcast]
    omega
  rw [hcnt]

omit [DecidableEq I] in

/-- The ordered composition word agrees with the source block word. -/
theorem clause49_source_block_word (xs : List (Matrix I I ℂ)) (q : Fin xs.length → ℕ) :
    pfOrderedCompositionWord xs q = sourceBlockWord xs q := by
  induction xs with
  | nil => simp [pfOrderedCompositionWord, sourceBlockWord]
  | cons X xs ih =>
    rw [pfOrderedCompositionWord_cons, clause49_source_block_word_cons]
    rw [ih (fun j => q j.succ)]

/-- A finite-range flat map may be truncated at `k` when all later blocks are empty. -/
theorem clause49_finRange_flatMap_trunc {α : Type} {n k : ℕ} (hk : k ≤ n)
    (g : Fin n → List α) (hg : ∀ i, k ≤ i.val → g i = []) :
    (List.finRange n).flatMap g =
      (List.finRange k).flatMap (fun i : Fin k => g (Fin.castLE hk i)) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      rfl
  | succ n ih =>
      by_cases hk0 : k = 0
      · subst hk0
        have hnil : (List.finRange (n + 1)).flatMap g = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro x hx
          exact hg x (Nat.zero_le _)
        rw [hnil, List.finRange_zero]
        rfl
      · by_cases hk2 : k = n + 1
        · subst hk2
          congr 1
        · have hkn : k ≤ n := by omega
          rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
            List.flatMap_singleton]
          have h2 : g (Fin.last n) = [] := hg (Fin.last n) hkn
          rw [h2]
          have hg' : ∀ i : Fin n, k ≤ i.val → g i.castSucc = [] := by
            intro i hi
            exact hg i.castSucc hi
          have hrec := ih hkn (fun i : Fin n => g i.castSucc) hg'
          rw [hrec, List.append_nil]
          apply List.flatMap_congr
          intro i hi
          apply congrArg g
          apply Fin.ext
          rfl

/-- At a reversed index, `groupedLift` returns the corresponding grouped part within the active
range and zero otherwise. -/
theorem clause49_lift_at (s k : ℕ) (q' : List ℕ) (i : Fin s) :
    groupedLift s k q' ⟨s - 1 - i.val, by omega⟩ =
      if i.val + 1 ≤ k then q'.getD i.val 0 else 0 := by
  simp only [groupedLift]
  have h1 : s - (s - 1 - i.val) = i.val + 1 := by omega
  have h2 : s - (s - 1 - i.val) - 1 = i.val := by omega
  show (if s - (s - 1 - i.val) ≤ k then q'.getD (s - (s - 1 - i.val) - 1) 0 else 0) =
    (if i.val + 1 ≤ k then q'.getD i.val 0 else 0)
  rw [h1]
  by_cases hc : i.val + 1 ≤ k
  · simp only [if_pos hc]
    congr 1
  · simp only [if_neg hc]

/-- Lifting a grouped list of admissible length produces its grouped repetition as the ordered
composition word. -/
theorem clause49_grouped_flat_word (xs : List (Matrix I I ℂ)) (q' : List ℕ)
    (h : q'.length ≤ xs.length) :
    pfOrderedCompositionWord xs (groupedLift xs.length q'.length q') =
      groupedRepetition xs q' := by
  rw [clause49_source_block_word]
  show (List.finRange xs.length).flatMap
      (fun i : Fin xs.length =>
        List.replicate
          (groupedLift xs.length q'.length q' ⟨xs.length - 1 - i.val, by omega⟩)
          (srcGen xs (i.val + 1))) = _
  show (List.finRange xs.length).flatMap
      (fun i : Fin xs.length =>
        List.replicate
          (groupedLift xs.length q'.length q' ⟨xs.length - 1 - i.val, by omega⟩)
          (srcGen xs (i.val + 1))) =
      (List.finRange q'.length).flatMap
        (fun i : Fin q'.length => List.replicate (q'.getD i.val 0) (srcGen xs (i.val + 1)))
  have htrunc := clause49_finRange_flatMap_trunc (α := Matrix I I ℂ) h
    (fun i : Fin xs.length =>
      List.replicate
        (if i.val + 1 ≤ q'.length then q'.getD i.val 0 else 0)
        (srcGen xs (i.val + 1)))
    (by
      intro i hi
      show List.replicate (if i.val + 1 ≤ q'.length then q'.getD i.val 0 else 0)
          (srcGen xs (i.val + 1)) = []
      have hcond : ¬(i.val + 1 ≤ q'.length) := by omega
      rw [if_neg hcond, List.replicate_zero])
  have hlift : (fun i : Fin xs.length =>
        List.replicate
          (groupedLift xs.length q'.length q' ⟨xs.length - 1 - i.val, by omega⟩)
          (srcGen xs (i.val + 1))) =
      (fun i : Fin xs.length =>
        List.replicate
          (if i.val + 1 ≤ q'.length then q'.getD i.val 0 else 0)
          (srcGen xs (i.val + 1))) := by
    funext i
    rw [clause49_lift_at]
  rw [hlift, htrunc]
  apply List.flatMap_congr
  intro i hi
  show List.replicate
      (if (Fin.castLE h i).val + 1 ≤ q'.length then q'.getD (Fin.castLE h i).val 0 else 0)
      (srcGen xs ((Fin.castLE h i).val + 1)) =
    List.replicate (q'.getD i.val 0) (srcGen xs (i.val + 1))
  have hv : (Fin.castLE h i).val = i.val := rfl
  rw [hv]
  have hi1 : i.val + 1 ≤ q'.length := by omega
  rw [if_pos hi1]

/-- The nested commutators formed from the lifted ordered word and the grouped repetition agree. -/
theorem clause49_grouped_flat_nested_comm (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (q' : List ℕ) (h : q'.length ≤ xs.length) :
    pfNestedCommList (B :: pfOrderedCompositionWord xs (groupedLift xs.length q'.length q')) =
      pfNestedCommList (B :: groupedRepetition xs q') := by
  rw [clause49_grouped_flat_word xs q' h]

/-- Taking a prefix preserves defaulted lookup at every index below the prefix bound. -/
theorem clause49_getD_take (l : List ℕ) (m j : ℕ) (hj : j < m) :
    (l.take m).getD j 0 = l.getD j 0 := by
  induction l generalizing m j with
  | nil => simp
  | cons a l ih =>
      cases j with
      | zero =>
          rw [List.take_cons (by omega : 0 < m)]
          simp only [List.getD_cons_zero]
      | succ j =>
          rw [List.take_cons (by omega : 0 < m), List.getD_cons_succ]
          exact ih (m - 1) j (by omega)

/-- The head of `groupedLift` is the last reversed part when active, and zero otherwise. -/
theorem clause49_lift_head (s k : ℕ) (q' : List ℕ) :
    groupedLift (s + 1) k q' 0 = if s + 1 ≤ k then q'.getD s 0 else 0 := by
  simp only [groupedLift]
  show (if s + 1 - 0 ≤ k then q'.getD (s + 1 - 0 - 1) 0 else 0) =
    (if s + 1 ≤ k then q'.getD s 0 else 0)
  have h2 : s + 1 - 0 - 1 = s := by omega
  have h1 : s + 1 - 0 = s + 1 := by omega
  rw [h2, h1]

/-- The tail of `groupedLift` is given by the corresponding reversed defaulted lookup within the
active range. -/
theorem clause49_lift_tail (s k : ℕ) (q' : List ℕ) (i : Fin s) :
    groupedLift (s + 1) k q' i.succ =
      if s - i.val ≤ k then q'.getD (s - i.val - 1) 0 else 0 := by
  simp only [groupedLift]
  show (if s + 1 - (i.val + 1) ≤ k then q'.getD (s + 1 - (i.val + 1) - 1) 0 else 0) =
    (if s - i.val ≤ k then q'.getD (s - i.val - 1) 0 else 0)
  have h1 : s + 1 - (i.val + 1) = s - i.val := by omega
  rw [h1]

/-- The factorial product of a grouped lift equals the reversed factorial product of its grouped
parts, padded with zeros. -/
theorem clause49_grouped_factorial_prod {s k : ℕ} (hk : k ≤ s) (q' : List ℕ) (hql : q'.length ≤ k) :
    (∏ i : Fin s, ((groupedLift s k q' i).factorial : ℝ)) =
      (∏ j : Fin k, ((q'.getD (k - 1 - j.val) 0).factorial : ℝ)) := by
  induction s generalizing k q' with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      have hq : q' = [] := by
        cases q' with
        | nil => rfl
        | cons a l => simp at hql
      subst hq
      rfl
  | succ s ih =>
      have hdecomp : (∏ i : Fin (s + 1), ((groupedLift (s + 1) k q' i).factorial : ℝ)) =
          ((groupedLift (s + 1) k q' 0).factorial) *
            (∏ i : Fin s, ((groupedLift (s + 1) k q' i.succ).factorial : ℝ)) :=
        Fin.prod_univ_succ _
      rw [hdecomp]
      by_cases hk1 : k = s + 1
      · subst hk1
        rw [clause49_lift_head, if_pos (by omega : s + 1 ≤ s + 1)]
        have hright : ∀ i : Fin s, groupedLift s s (q'.take s) i =
            (q'.take s).getD (s - i.val - 1) 0 := by
          intro i
          simp only [groupedLift]
          show (if s - i.val ≤ s then (q'.take s).getD (s - i.val - 1) 0 else 0) = _
          rw [if_pos (by omega)]
        have htail : (fun i : Fin s => ((groupedLift (s + 1) (s + 1) q' i.succ).factorial : ℝ)) =
            (fun i : Fin s => ((groupedLift s s (q'.take s) i).factorial : ℝ)) := by
          funext i
          rw [clause49_lift_tail, if_pos (by omega : s - i.val ≤ s + 1), hright i]
          have hget : q'.getD (s - i.val - 1) 0 = (q'.take s).getD (s - i.val - 1) 0 :=
            (clause49_getD_take q' s (s - i.val - 1) (by omega)).symm
          rw [hget]
        rw [htail]
        have htake : (q'.take s).length ≤ s := by simp
        rw [ih (by omega : s ≤ s) (q'.take s) htake]
        have hget (j : Fin s) :
            (q'.take s).getD (s - 1 - j.val) 0 = q'.getD (s - 1 - j.val) 0 :=
          clause49_getD_take q' s (s - 1 - j.val) (by omega)
        have hconv : (∏ j : Fin (s + 1), ((q'.getD (s + 1 - 1 - j.val) 0).factorial : ℝ)) =
            (∏ j : Fin (s + 1), ((q'.getD (s - j.val) 0).factorial : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hget2 : q'.getD (s + 1 - 1 - j.val) 0 = q'.getD (s - j.val) 0 := by
            congr 1 <;> omega
          rw [hget2]
        have hdecomp2 : (∏ j : Fin (s + 1), ((q'.getD (s - j.val) 0).factorial : ℝ)) =
            ((q'.getD s 0).factorial) *
              (∏ j : Fin s, ((q'.getD (s - 1 - j.val) 0).factorial : ℝ)) := by
          have h := Fin.prod_univ_succ
            (fun j : Fin (s + 1) => ((q'.getD (s - j.val) 0).factorial : ℝ))
          rw [h]
          have hhead : ((q'.getD (s - (0 : Fin (s + 1)).val) 0).factorial : ℝ) =
              ((q'.getD s 0).factorial : ℝ) := by
            show ((q'.getD s 0).factorial : ℝ) = ((q'.getD s 0).factorial : ℝ)
            rfl
          rw [hhead]
          congr 1
          show (∏ j ∈ (Finset.univ : Finset (Fin s)),
              ((q'.getD (s - (j.val + 1)) 0).factorial : ℝ)) =
            (∏ j ∈ (Finset.univ : Finset (Fin s)),
              ((q'.getD (s - 1 - j.val) 0).factorial : ℝ))
          apply Finset.prod_congr rfl
          intro j hj
          have hget2 : q'.getD (s - (j.val + 1)) 0 = q'.getD (s - 1 - j.val) 0 := by
            congr 1 <;> omega
          rw [hget2]
        rw [hconv, hdecomp2]
        apply congrArg (fun p => (↑(q'.getD s 0).factorial : ℝ) * p)
        show (∏ j ∈ (Finset.univ : Finset (Fin s)),
            (((q'.take s).getD (s - 1 - j.val) 0).factorial : ℝ)) =
          (∏ j ∈ (Finset.univ : Finset (Fin s)),
            ((q'.getD (s - 1 - j.val) 0).factorial : ℝ))
        apply Finset.prod_congr rfl
        intro j hj
        rw [hget j]
      · have hkn : k ≤ s := by omega
        rw [clause49_lift_head, if_neg (by omega : ¬(s + 1 ≤ k))]
        have hright : ∀ i : Fin s, groupedLift s k q' i =
            if s - i.val ≤ k then q'.getD (s - i.val - 1) 0 else 0 := by
          intro i
          simp only [groupedLift]
        have htail : (fun i : Fin s => ((groupedLift (s + 1) k q' i.succ).factorial : ℝ)) =
            (fun i : Fin s => ((groupedLift s k q' i).factorial : ℝ)) := by
          funext i
          rw [clause49_lift_tail, hright i]
        rw [htail]
        rw [ih hkn q' hql]
        have h1 : (0 : ℕ).factorial = 1 := rfl
        rw [h1]
        ring

/-- Reversing the finite index order preserves the factorial product of the defaulted grouped
parts. -/
theorem clause49_fin_prod_reverse {k : ℕ} (q' : List ℕ) :
    (∏ j : Fin k, ((q'.getD (k - 1 - j.val) 0).factorial : ℝ)) =
      (∏ j : Fin k, ((q'.getD j.val 0).factorial : ℝ)) := by
  refine Fintype.prod_bijective (fun j : Fin k => ⟨k - 1 - j.val, by omega⟩) ?_ _ _ (fun _ => rfl)
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    have h' : k - 1 - a.val = k - 1 - b.val := h
    omega
  · intro b
    refine ⟨⟨k - 1 - b.val, by omega⟩, ?_⟩
    apply Fin.ext
    show k - 1 - (k - 1 - b.val) = b.val
    omega

/-- A finite product of real ones equals one. -/
theorem clause49_fin_prod_ones (k : ℕ) : (∏ _j : Fin k, (1 : ℝ)) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Fin.prod_univ_succ, ih, mul_one]

/-- The factorial product over a padded finite range equals the factorial product over the
original list. -/
theorem clause49_fin_prod_eq_list_prod {k : ℕ} (q' : List ℕ) (hql : q'.length ≤ k) :
    (∏ j : Fin k, ((q'.getD j.val 0).factorial : ℝ)) =
      (q'.map (fun j => (j.factorial : ℝ))).prod := by
  induction k generalizing q' with
  | zero =>
      have hq : q' = [] := by
        cases q' with
        | nil => rfl
        | cons a l => simp at hql
      subst hq
      rfl
  | succ k ih =>
      cases q' with
      | nil =>
          have h1 : (0 : ℕ).factorial = 1 := rfl
          have hdecomp : (∏ j : Fin (k + 1), ((([] : List ℕ).getD j.val 0).factorial : ℝ)) =
              (([] : List ℕ).getD 0 0).factorial *
                (∏ j : Fin k, ((([] : List ℕ).getD (j.val + 1) 0).factorial : ℝ)) :=
            Fin.prod_univ_succ _
          rw [hdecomp]
          simp
      | cons a q'' =>
          have hql'' : q''.length ≤ k := by
            simp only [List.length_cons] at hql
            omega
          have hdecomp : (∏ j : Fin (k + 1), (((a :: q'').getD j.val 0).factorial : ℝ)) =
              ((a :: q'').getD 0 0).factorial *
                (∏ j : Fin k, (((a :: q'').getD (j.val + 1) 0).factorial : ℝ)) :=
            Fin.prod_univ_succ _
          rw [hdecomp]
          have h0 : (a :: q'').getD 0 0 = a := by simp [List.getD_cons_zero]
          rw [h0]
          have hconv : (∏ j : Fin k, (((a :: q'').getD (j.val + 1) 0).factorial : ℝ)) =
              (∏ j : Fin k, ((q''.getD j.val 0).factorial : ℝ)) := by
            show (∏ j ∈ (Finset.univ : Finset (Fin k)),
                (((a :: q'').getD (j.val + 1) 0).factorial : ℝ)) =
              (∏ j ∈ (Finset.univ : Finset (Fin k)),
                ((q''.getD j.val 0).factorial : ℝ))
            apply Finset.prod_congr rfl
            intro j hj
            have hsh : (a :: q'').getD (j.val + 1) 0 = q''.getD j.val 0 := by
              simp [List.getD_cons_succ]
            rw [hsh]
          rw [hconv]
          rw [ih q'' hql'']
          simp [List.prod_cons]

/-- The flat weight of a grouped lift equals the grouped weight when the grouped list has length
`k`. -/
theorem clause49_grouped_flat_weight {s k : ℕ} (hk : k ≤ s) (q' : List ℕ) (hql : q'.length = k) :
    flatWeight (groupedLift s k q') = groupedWeight q' := by
  unfold flatWeight groupedWeight
  have h1 := clause49_grouped_factorial_prod hk q' (by omega)
  have h2 := clause49_fin_prod_reverse (k := k) q'
  have h3 := clause49_fin_prod_eq_list_prod (k := k) q' (by omega)
  rw [h1, h2, h3]

/-- Every defaulted entry of a natural-number list is bounded by its sum. -/
theorem clause49_getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons a l ih =>
    cases i with
    | zero => simp [List.getD]
    | succ i =>
      rw [List.getD_cons_succ]
      have := ih i
      simp only [List.sum_cons] at this ⊢
      omega

/-- Grouped compositions are precisely lists of length `k` with sum `p` and nonzero final part. -/
theorem clause49_grouped_compositions_mem {p k : ℕ} (q' : List ℕ) :
    q' ∈ groupedCompositions p k ↔
      q'.length = k ∧ q'.sum = p ∧ q'.getLastD 0 ≠ 0 := by
  constructor
  · intro h
    rw [groupedCompositions, Finset.mem_filter] at h
    have himage := h.1
    rw [Finset.mem_image] at himage
    obtain ⟨f, hf, hq⟩ := himage
    refine ⟨?_, h.2.1, h.2.2⟩
    have hlen : (List.ofFn (fun i => (f i).val)).length = k := List.length_ofFn
    rw [← hq, hlen]
  · rintro ⟨hlen, hsum, hlast⟩
    rw [groupedCompositions, Finset.mem_filter]
    refine ⟨?_, hsum, hlast⟩
    have hle : ∀ i : Fin k, q'.getD i.val 0 ≤ p := by
      intro i
      have hgd := clause49_getD_le_sum q' i.val
      rw [hsum] at hgd
      exact hgd
    refine Finset.mem_image.mpr
      ⟨fun i : Fin k => ⟨q'.getD i.val 0, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩
    have hofn : List.ofFn (fun i : Fin k => q'.getD i.val 0) = q' := by
      apply List.ext_get
      · simp [List.length_ofFn, hlen]
      · intro n h1 h2
        rw [List.get_eq_getElem, List.getElem_ofFn h1]
        grind
    rw [hofn]

/-- Summing defaulted lookups over the exact length of a list recovers its sum. -/
theorem clause49_fin_getD_sum {k : ℕ} (l : List ℕ) (hl : l.length = k) :
    (∑ j : Fin k, l.getD j.val 0) = l.sum := by
  induction k generalizing l with
  | zero =>
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons a l' => simp at hl
      subst hnil
      exact Fintype.sum_empty _
  | succ k ih =>
      cases l with
      | nil => simp at hl
      | cons a l' =>
          have hl' : l'.length = k := by
            simp only [List.length_cons] at hl
            omega
          rw [Fin.sum_univ_succ]
          show (a :: l').getD 0 0 + ∑ i : Fin k, (a :: l').getD (i.val + 1) 0 = (a :: l').sum
          rw [show (a :: l').getD 0 0 = a from by simp [List.getD]]
          have hshift : ∀ i : Fin k, (a :: l').getD (i.val + 1) 0 = l'.getD i.val 0 := by
            intro i
            rw [List.getD_cons_succ]
          rw [Finset.sum_congr rfl (fun i _ => hshift i)]
          rw [ih l' hl']
          exact (List.sum_cons).symm

/-- The last element of a nonempty prefix is the defaulted lookup at the preceding index. -/
theorem clause49_take_getLastD {α : Type} (l : List α) (d : α) (k : ℕ)
    (hk : 1 ≤ k) (hl : k ≤ l.length) :
    (l.take k).getLastD d = l.getD (k - 1) d := by
  have hlt : k - 1 < l.length := by omega
  have htake : l.take k = l.take (k - 1) ++ [l[k - 1]] := by
    have h := List.take_succ_eq_append_getElem (α := α) hlt
    rwa [show (k - 1) + 1 = k by omega] at h
  rw [htake, List.getLastD_eq_getLast?, List.getLast?_append]
  have hgl : ([l[k - 1]] : List α).getLast? = some (l[k - 1]) := rfl
  rw [hgl]
  have hor : (some (l[k - 1])).or (l.take (k - 1)).getLast? = some (l[k - 1]) := rfl
  rw [hor, Option.getD_some]
  rw [List.getD_eq_getElem _ _ hlt]

/-- Defaulted lookup in `sourceParts` retrieves the corresponding reversed coordinate of the
composition. -/
theorem clause49_sourceParts_getD {s : ℕ} (q : Fin s → ℕ) (j : ℕ) (hj : j < s) :
    (sourceParts s q).getD j 0 = q ⟨s - 1 - j, by omega⟩ := by
  have hlen : (sourceParts s q).length = s := by
    simp only [sourceParts, List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [sourceParts, List.getElem_ofFn]

/-- The last element of a nonempty list equals its defaulted lookup at the last index. -/
theorem clause49_getLastD_eq_getD {α : Type} (l : List α) (d : α) (hl : 0 < l.length) :
    l.getLastD d = l.getD (l.length - 1) d := by
  have h := clause49_take_getLastD l d l.length (by omega) (by omega)
  rw [List.take_length] at h
  exact h

/-- Defaulted lookup at the last index of a nonempty list equals its last element. -/
theorem clause49_getD_lastD {α : Type} (l : List α) (d : α) (hl : 0 < l.length) :
    l.getD (l.length - 1) d = l.getLastD d := (clause49_getLastD_eq_getD l d hl).symm

/-- A composition of level `k` with nonempty support has minimum support index `s - k`. -/
theorem clause49_support_min_of_level {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hks : k ≤ s)
    (hne : (compositionSupport q).Nonempty) (hlevel : compositionLevel q = k) :
    ((compositionSupport q).min' hne).val = s - k := by
  rw [compositionLevel, dif_pos hne] at hlevel
  omega

/-- A composition of positive level has nonempty support. -/
theorem clause49_support_nonempty_of_level {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hlevel : compositionLevel q = k) : (compositionSupport q).Nonempty := by
  by_contra hne
  rw [compositionLevel, dif_neg hne] at hlevel
  omega

/-- Every coordinate below the minimum support index vanishes. -/
theorem clause49_eq_zero_below_level {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hks : k ≤ s)
    (hne : (compositionSupport q).Nonempty)
    (hmin : ((compositionSupport q).min' hne).val = s - k) (i : Fin s) (hi : i.val < s - k) :
    q i = 0 := by
  by_contra hne'
  have hmem : i ∈ compositionSupport q := by simp [compositionSupport, hne']
  have hle := Finset.min'_le (compositionSupport q) i hmem
  have hle' : ((compositionSupport q).min' hne).val ≤ i.val := (Fin.mk_le_mk).mp hle
  rw [hmin] at hle'
  omega

/-- The coordinate at the minimum support index is nonzero. -/
theorem clause49_hit_at_level {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hbound : s - k < s)
    (hne : (compositionSupport q).Nonempty)
    (hmin : ((compositionSupport q).min' hne).val = s - k) :
    q ⟨s - k, hbound⟩ ≠ 0 := by
  have hmin' : (compositionSupport q).min' hne = ⟨s - k, hbound⟩ := by
    apply Fin.ext
    exact hmin
  have hmem : (⟨s - k, hbound⟩ : Fin s) ∈ compositionSupport q := by
    rw [← hmin']
    exact Finset.min'_mem (compositionSupport q) hne
  simpa [compositionSupport] using! hmem

/-- The grouped representative of a composition of level `k` has length `k`. -/
theorem clause49_group_repr_length {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hks : k ≤ s)
    (hlevel : compositionLevel q = k) :
    (compositionGroup q).length = k := by
  have hlen : (sourceParts s q).length = s := by
    simp only [sourceParts, List.length_ofFn]
  rw [compositionGroup, hlevel, List.length_take, hlen, Nat.min_eq_left hks]

/-- The grouped representative of a composition of positive level has nonzero last part. -/
theorem clause49_group_repr_last_ne {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s)
    (hlevel : compositionLevel q = k) :
    (compositionGroup q).getLastD 0 ≠ 0 := by
  have hne := clause49_support_nonempty_of_level q k hk hlevel
  have hmin := clause49_support_min_of_level q k hks hne hlevel
  have hbound : s - k < s := Nat.sub_lt (n := s) (m := k) (by omega) (by omega)
  have hlen : (sourceParts s q).length = s := by
    simp only [sourceParts, List.length_ofFn]
  rw [compositionGroup, hlevel, clause49_take_getLastD _ 0 k hk (by omega)]
  rw [clause49_sourceParts_getD q (k - 1) (by omega)]
  have hnat : s - 1 - (k - 1) = s - k := by
    have h1 := Nat.sub_sub s 1 (k - 1)
    have h2 : 1 + (k - 1) = k := by omega
    omega
  have hfin : (⟨s - 1 - (k - 1), by omega⟩ : Fin s) = ⟨s - k, hbound⟩ := by
    apply Fin.ext
    show s - 1 - (k - 1) = s - k
    exact hnat
  have hq : q ⟨s - 1 - (k - 1), by omega⟩ = q ⟨s - k, hbound⟩ := by
    rw [hfin]
  rw [hq]
  exact clause49_hit_at_level q k hbound hne hmin

/-- Lifting the first `k` reversed source parts recovers a composition of level `k`. -/
theorem clause49_lift_take_repr {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s)
    (hlevel : compositionLevel q = k) :
    groupedLift s k ((sourceParts s q).take k) = q := by
  have hne := clause49_support_nonempty_of_level q k hk hlevel
  have hmin := clause49_support_min_of_level q k hks hne hlevel
  funext i
  by_cases hcond : s - i.val ≤ k
  · have hpos : 0 < s - i.val := by omega
    have hj : s - i.val - 1 < k := by omega
    have hjlt : s - i.val - 1 < s := by omega
    show (if s - i.val ≤ k then ((sourceParts s q).take k).getD (s - i.val - 1) 0 else 0) = q i
    rw [if_pos hcond]
    rw [clause49_getD_take _ k (s - i.val - 1) hj]
    rw [clause49_sourceParts_getD q (s - i.val - 1) hjlt]
    congr 1
    apply Fin.ext
    show s - 1 - (s - i.val - 1) = i.val
    omega
  · have hlt : i.val < s - k := by omega
    show (if s - i.val ≤ k then ((sourceParts s q).take k).getD (s - i.val - 1) 0 else 0) = q i
    rw [if_neg hcond]
    exact (clause49_eq_zero_below_level q k hks hne hmin i hlt).symm

/-- Lifting the grouped representative recovers a composition of positive level `k`. -/
theorem clause49_lift_group_repr {s : ℕ} (q : Fin s → ℕ) (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s)
    (hlevel : compositionLevel q = k) :
    groupedLift s k (compositionGroup q) = q := by
  rw [compositionGroup, hlevel]
  exact clause49_lift_take_repr q k hk hks hlevel

/-- The sum of the coordinates of a grouped lift equals the sum of its grouped list. -/
theorem clause49_sum_lift {s k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s) (q' : List ℕ) (hql : q'.length = k) :
    (∑ i : Fin s, groupedLift s k q' i) = q'.sum := by
  classical
  have hrev : (∑ i : Fin s, groupedLift s k q' i) =
      ∑ j : Fin s, (if j.val + 1 ≤ k then q'.getD j.val 0 else 0) := by
    refine Finset.sum_nbij (fun x : Fin s => ⟨s - 1 - x.val, by omega⟩) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_univ]
    · intro a₁ ha₁ a₂ ha₂ h
      apply Fin.eq_of_val_eq
      show a₁.val = a₂.val
      have hh := congrArg Fin.val h
      have hhb : s - 1 - a₁.val = s - 1 - a₂.val := hh
      omega
    · intro b hb
      refine ⟨⟨s - 1 - b.val, by omega⟩, ?_, ?_⟩
      · simp
      · apply Fin.eq_of_val_eq
        show s - 1 - (s - 1 - b.val) = b.val
        omega
    · intro a ha
      show groupedLift s k q' a =
        (if (⟨s - 1 - a.val, by omega⟩ : Fin s).val + 1 ≤ k
          then q'.getD (⟨s - 1 - a.val, by omega⟩ : Fin s).val 0 else 0)
      have h1 : (⟨s - 1 - a.val, by omega⟩ : Fin s).val = s - 1 - a.val := rfl
      rw [h1]
      have h2 : s - 1 - a.val + 1 = s - a.val := by omega
      rw [h2]
      simp only [groupedLift]
      have h3 : s - a.val - 1 = s - 1 - a.val := by omega
      rw [h3]
  rw [hrev]
  have hdrop : (∑ j : Fin s, (if j.val + 1 ≤ k then q'.getD j.val 0 else 0)) =
      (∑ j : Fin s, q'.getD j.val 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hc : j.val + 1 ≤ k
    · rw [if_pos hc]
    · rw [if_neg hc]
      have hle : q'.length ≤ j.val := by omega
      exact (List.getD_eq_default q' 0 hle).symm
  rw [hdrop]
  have hrestr : (∑ j : Fin s, q'.getD j.val 0) = ∑ j : Fin k, q'.getD j.val 0 := by
    have hlt : ∀ (j : Fin s) (_ : j ∈ (Finset.univ : Finset (Fin s)).filter
        (fun j : Fin s => j.val < k)), j.val < k := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hsub : (Finset.univ : Finset (Fin s)).filter (fun j : Fin s => j.val < k) ⊆
        (Finset.univ : Finset (Fin s)) := Finset.filter_subset _ _
    have hzero : ∀ j ∈ (Finset.univ : Finset (Fin s)),
        j ∉ (Finset.univ : Finset (Fin s)).filter (fun j : Fin s => j.val < k) →
        q'.getD j.val 0 = 0 := by
      intro j hj hj'
      have hlt' : ¬ (j.val < k) := by
        intro hcon
        apply hj'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcon
      have hle : q'.length ≤ j.val := by omega
      exact List.getD_eq_default q' 0 hle
    have h1 : (∑ j : Fin s, q'.getD j.val 0) =
        ∑ j ∈ (Finset.univ : Finset (Fin s)).filter (fun j : Fin s => j.val < k),
          q'.getD j.val 0 := by
      have h := Finset.sum_subset hsub hzero
      exact h.symm
    rw [h1]
    refine Finset.sum_bij (fun j (hj : j ∈ (Finset.univ : Finset (Fin s)).filter
        (fun j : Fin s => j.val < k)) => ⟨j.val, hlt j hj⟩) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_univ]
    · intro j₁ hj₁ j₂ hj₂ h
      apply Fin.eq_of_val_eq
      show j₁.val = j₂.val
      have hh := congrArg Fin.val h
      exact hh
    · intro b hb
      have hbv : b.val < k := b.isLt
      refine ⟨⟨b.val, lt_of_lt_of_le hbv hks⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hbv
      · apply Fin.eq_of_val_eq
        rfl
    · intro j hj
      rfl
  rw [hrestr]
  exact clause49_fin_getD_sum q' hql

/-- Two grouped lists of length `k` are equal if their lifts into `s` coordinates agree and `k ≤
s`. -/
theorem clause49_lift_injective {s k : ℕ} (hks : k ≤ s) (q'₁ q'₂ : List ℕ)
    (h₁ : q'₁.length = k) (h₂ : q'₂.length = k)
    (heq : groupedLift s k q'₁ = groupedLift s k q'₂) : q'₁ = q'₂ := by
  have hval : ∀ j : ℕ, j < k → q'₁.getD j 0 = q'₂.getD j 0 := by
    intro j hj
    have hjlt : j < s := by omega
    have hjk : j + 1 ≤ k := by omega
    have h1j : groupedLift s k q'₁ ⟨s - 1 - j, by omega⟩ = q'₁.getD j 0 := by
      rw [clause49_lift_at (i := ⟨j, hjlt⟩)]
      have hc : (⟨j, hjlt⟩ : Fin s).val + 1 ≤ k := by
        have hjv : (⟨j, hjlt⟩ : Fin s).val = j := rfl
        rw [hjv]
        exact hjk
      rw [if_pos hc]
    have h2j : groupedLift s k q'₂ ⟨s - 1 - j, by omega⟩ = q'₂.getD j 0 := by
      rw [clause49_lift_at (i := ⟨j, hjlt⟩)]
      have hc : (⟨j, hjlt⟩ : Fin s).val + 1 ≤ k := by
        have hjv : (⟨j, hjlt⟩ : Fin s).val = j := rfl
        rw [hjv]
        exact hjk
      rw [if_pos hc]
    have h3 : groupedLift s k q'₁ ⟨s - 1 - j, by omega⟩ =
        groupedLift s k q'₂ ⟨s - 1 - j, by omega⟩ := by
      rw [heq]
    calc q'₁.getD j 0 = groupedLift s k q'₁ ⟨s - 1 - j, by omega⟩ := h1j.symm
      _ = groupedLift s k q'₂ ⟨s - 1 - j, by omega⟩ := h3
      _ = q'₂.getD j 0 := h2j
  apply List.ext_get
  · omega
  · intro n hn hn'
    have hnk : n < k := by omega
    have h1' : q'₁.get ⟨n, hn⟩ = q'₁.getD n 0 := by
      have hgn := List.getD_eq_getElem q'₁ 0 hn
      rw [hgn]
      rfl
    have h2' : q'₂.get ⟨n, hn'⟩ = q'₂.getD n 0 := by
      have hgn := List.getD_eq_getElem q'₂ 0 hn'
      rw [hgn]
      rfl
    rw [h1', h2']
    exact hval n hnk

/-- Lifting grouped compositions of length `k` gives exactly the flat compositions of level `k`. -/
theorem clause49_lift_image_eq {s p k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s) :
    (groupedCompositions p k).image (groupedLift s k) =
      (pfCompositions s p).filter (fun q => compositionLevel q = k) := by
  classical
  ext q
  constructor
  · intro hq
    rw [Finset.mem_image] at hq
    obtain ⟨q', hq'mem, hq'eq⟩ := hq
    have hmem := clause49_grouped_compositions_mem (p := p) (k := k) q'
    have hlen : q'.length = k := (hmem.mp hq'mem).1
    have hsum : q'.sum = p := (hmem.mp hq'mem).2.1
    have hlast : q'.getLastD 0 ≠ 0 := (hmem.mp hq'mem).2.2
    rw [Finset.mem_filter]
    constructor
    · rw [pfCompositions_mem, ← hq'eq]
      rw [clause49_sum_lift hk hks q' hlen]
      exact hsum
    · rw [← hq'eq]
      have hget : q'.getD (k - 1) 0 ≠ 0 := by
        have h1 : q'.getD (q'.length - 1) 0 = q'.getLastD 0 := clause49_getD_lastD q' 0 (by omega)
        rw [hlen] at h1
        rw [h1]
        exact hlast
      exact clause49_lift_level s k q' (by omega) hks hget
  · intro hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqmem, hlevel⟩ := hq
    rw [pfCompositions_mem] at hqmem
    refine Finset.mem_image.mpr ⟨compositionGroup q, ?_, ?_⟩
    · have hne := clause49_support_nonempty_of_level q k hk hlevel
      have hmin := clause49_support_min_of_level q k hks hne hlevel
      rw [clause49_grouped_compositions_mem]
      refine ⟨clause49_group_repr_length q k hks hlevel, ?_,
        clause49_group_repr_last_ne q k hk hks hlevel⟩
      have htot : (∑ i : Fin s, groupedLift s k (compositionGroup q) i) =
          (compositionGroup q).sum :=
        clause49_sum_lift hk hks (compositionGroup q) (clause49_group_repr_length q k hks hlevel)
      have hlift : groupedLift s k (compositionGroup q) = q :=
        clause49_lift_group_repr q k hk hks hlevel
      rw [hlift] at htot
      rw [← htot]
      exact hqmem
    · exact clause49_lift_group_repr q k hk hks hlevel

/-- The grouped level cardinality equals the number of flat compositions of that level. -/
theorem clause49_level_card_eq {s p k : ℕ} (hk : 1 ≤ k) (hks : k ≤ s) :
    groupedLevelCard p k =
      ((pfCompositions s p).filter (fun q => compositionLevel q = k)).card := by
  classical
  have hinj : Set.InjOn (groupedLift s k) (groupedCompositions p k) := by
    intro a ha b hb hab
    have hlen : a.length = k := (clause49_grouped_compositions_mem (p := p) (k := k) a).mp ha |>.1
    have hlen' : b.length = k := (clause49_grouped_compositions_mem (p := p) (k := k) b).mp hb |>.1
    exact clause49_lift_injective hks a b hlen hlen' hab
  have hcard : ((groupedCompositions p k).image (groupedLift s k)).card =
      (groupedCompositions p k).card :=
    Finset.card_image_of_injOn hinj
  unfold groupedLevelCard
  rw [← hcard, clause49_lift_image_eq hk hks]

/-- The grouped and flat budgets agree at every admissible positive level. -/
theorem clause49_level_budget_eq (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p k : ℕ)
    (hk : 1 ≤ k) (hks : k ≤ xs.length) :
    groupedLevelBudget xs B p k = flatLevelBudget xs B p k := by
  classical
  have hmem : ∀ q' ∈ groupedCompositions p k,
      q'.length = k ∧ q'.sum = p ∧ q'.getLastD 0 ≠ 0 :=
    fun q' hq' => clause49_grouped_compositions_mem (p := p) (k := k) q' |>.mp hq'
  have hinj : Set.InjOn (groupedLift xs.length k) (groupedCompositions p k) := by
    intro a ha b hb hab
    exact clause49_lift_injective hks a b (hmem a ha).1 (hmem b hb).1 hab
  have hterm : ∀ q' ∈ groupedCompositions p k,
      groupedWeight q' * ‖pfNestedCommList (B :: groupedRepetition xs q')‖ =
        flatWeight (groupedLift xs.length k q') *
          ‖pfNestedCommList (B :: pfOrderedCompositionWord xs (groupedLift xs.length k q'))‖ := by
    intro q' hq'
    have hlen : q'.length = k := (hmem q' hq').1
    have hnc : pfNestedCommList (B :: pfOrderedCompositionWord xs (groupedLift xs.length k q')) =
        pfNestedCommList (B :: groupedRepetition xs q') := by
      have h := clause49_grouped_flat_nested_comm xs B q' (by omega)
      rwa [hlen] at h
    rw [clause49_grouped_flat_weight hks q' hlen, hnc]
  unfold groupedLevelBudget flatLevelBudget
  calc (∑ q' ∈ groupedCompositions p k,
        groupedWeight q' * ‖pfNestedCommList (B :: groupedRepetition xs q')‖)
      = ∑ q' ∈ groupedCompositions p k,
        flatWeight (groupedLift xs.length k q') *
          ‖pfNestedCommList (B :: pfOrderedCompositionWord xs (groupedLift xs.length k q'))‖ := by
        apply Finset.sum_congr rfl
        intro q' hq'
        exact hterm q' hq'
    _ = ∑ q ∈ (groupedCompositions p k).image (groupedLift xs.length k),
        flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖ :=
      (Finset.sum_image (f := fun q : Fin xs.length → ℕ =>
        flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖) hinj).symm
    _ = ∑ q ∈ (pfCompositions xs.length p).filter (fun q => compositionLevel q = k),
        flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖ := by
      rw [clause49_lift_image_eq hk hks]
    _ = ∑ q ∈ pfCompositions xs.length p,
        (if compositionLevel q = k then
          flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖ else 0) := by
      rw [Finset.sum_filter]
    _ = ∑ q ∈ pfCompositions xs.length p,
        (if compositionLevel q = k then
          flatWeight q * ‖pfNestedCommList (B :: pfOrderedCompositionWord xs q)‖ else 0) := rfl

/-- Summing grouped budgets over all positive source levels gives the sum of the flat budgets. -/
theorem clause49_all_levels_budget_eq (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 xs.length, groupedLevelBudget xs B p k) =
      (∑ k ∈ Finset.Icc 1 xs.length, flatLevelBudget xs B p k) := by
  apply Finset.sum_congr rfl
  intro k hk
  exact clause49_level_budget_eq xs B p k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

/-- The map `k ↦ s - k` sends the range below `s` onto the integers from one to `s`. -/
theorem clause49_frozen_level_reindex (s : ℕ) :
    (Finset.range s).image (fun k => s - k) = Finset.Icc 1 s := by
  ext ℓ
  constructor
  · intro hℓ
    rw [Finset.mem_image] at hℓ
    obtain ⟨k, hk, hkℓ⟩ := hℓ
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro hℓ
    rw [Finset.mem_Icc] at hℓ
    rw [Finset.mem_image]
    refine ⟨s - ℓ, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega

/-- The positive-order ordered remainder decomposes over source levels indexed from one to the
list length. -/
theorem clause49_remainder_source_level_sum (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (p : ℕ) (hp : 1 ≤ p) (t : ℝ) :
    orderedRemainder xs B p t =
      ∑ ℓ ∈ Finset.Icc 1 xs.length, orderedRemainderLevel xs B p (xs.length - ℓ) t := by
  rw [clause49_remainder_level_decomposition xs B p hp t]
  refine Finset.sum_bij (fun k _ => xs.length - k) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' : k < xs.length := Finset.mem_range.mp hk
    rw [Finset.mem_Icc]
    show 1 ≤ xs.length - k ∧ xs.length - k ≤ xs.length
    constructor <;> omega
  · intro a₁ ha₁ a₂ ha₂ h
    have h1 : a₁ < xs.length := Finset.mem_range.mp ha₁
    have h2 : a₂ < xs.length := Finset.mem_range.mp ha₂
    have h' : xs.length - a₁ = xs.length - a₂ := by simpa using! h
    omega
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    refine ⟨xs.length - b, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · show xs.length - (xs.length - b) = b
      omega
  · intro k hk
    have hk' : k < xs.length := Finset.mem_range.mp hk
    show orderedRemainderLevel xs B p k t
        = orderedRemainderLevel xs B p (xs.length - (xs.length - k)) t
    rw [show xs.length - (xs.length - k) = k by omega]

set_option linter.unusedSectionVars false in

/-- The source generator and outer-prefix length agree with the reversed source-level indexing. -/
theorem clause49_frozen_level_alignment (xs : List (Matrix I I ℂ)) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hℓs : ℓ ≤ xs.length) :
    srcGen xs ℓ = xs.getD (xs.length - ℓ) 0 ∧
    (xs.take (xs.length - ℓ)).length = xs.length - ℓ := by
  refine ⟨rfl, ?_⟩
  rw [List.length_take]
  omega

/-- For a singleton generator list, the ordered remainder equals conjugation minus its Taylor
truncation. -/
theorem clause49_ordered_singleton_expansion {J : Type} [Fintype J] [DecidableEq J]
    (X B : Matrix J J ℂ) (p : ℕ) (_hp : 0 < p) (t : ℝ) :
    orderedRemainder [X] B p t = pfConjWord [X] B t - pfConjTrunc [X] B p t := by
  rfl

/-- The source-level reindexing, remainder decomposition, generator alignment, and singleton
expansion hold together. -/
theorem clause49_frozen_bridge_statement :
    (∀ (s : ℕ),
        (Finset.range s).image (fun k => s - k) = Finset.Icc 1 s ∧
        (∀ (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (_hp : 1 ≤ p) (t : ℝ),
          orderedRemainder xs B p t =
            ∑ ℓ ∈ Finset.Icc 1 xs.length, orderedRemainderLevel xs B p (xs.length - ℓ) t) ∧
        (∀ (xs : List (Matrix I I ℂ)) (ℓ : ℕ) (_hℓ : 1 ≤ ℓ) (_hℓs : ℓ ≤ xs.length),
          srcGen xs ℓ = xs.getD (xs.length - ℓ) 0 ∧
          (xs.take (xs.length - ℓ)).length = xs.length - ℓ) ∧
        (∀ {J : Type} [Fintype J] [DecidableEq J] (X B : Matrix J J ℂ) (p : ℕ)
          (_hp : 0 < p) (t : ℝ),
          orderedRemainder [X] B p t = pfConjWord [X] B t - pfConjTrunc [X] B p t)) := by
  intro s
  refine ⟨clause49_frozen_level_reindex s, ?_, ?_, ?_⟩
  · intro xs B p hp t
    exact clause49_remainder_source_level_sum xs B p hp t
  · intro xs ℓ hℓ hℓs
    exact clause49_frozen_level_alignment xs ℓ hℓ hℓs
  · intro J _ _ X B p _hp t
    exact clause49_ordered_singleton_expansion X B p _hp t

/-- The refined ordered expansion combines the level decomposition, Cauchy remainder formula,
and grouped-composition identities. -/
theorem clause49_endpoint : ∀ (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (p : ℕ) (t : ℝ), 1 ≤ p →
    (orderedRemainder xs B p t =
      ∑ k ∈ Finset.range xs.length, orderedRemainderLevel xs B p k t) ∧
    (orderedRemainder xs B p t =
      ∫ τ in 0..t, (((t - τ) ^ (p - 1) / ((p - 1).factorial : ℝ)) •
        iteratedDeriv p (pfConjWord xs B) τ)) ∧
    (∀ k, 1 ≤ k → k ≤ xs.length →
      xs.take (xs.length - k) ++ [srcGen xs k] = xs.take (xs.length - k + 1)) ∧
    (∀ (s k : ℕ) (q' : List ℕ) (i : Fin s),
      i ∈ compositionSupport (groupedLift s k q') ↔
        s - i.val ≤ k ∧ q'.getD (s - i.val - 1) 0 ≠ 0) ∧
    (∀ (s k : ℕ) (q' : List ℕ), 0 < k → k ≤ s → q'.getD (k - 1) 0 ≠ 0 →
      compositionLevel (groupedLift s k q') = k) ∧
    (∀ (q' : List ℕ), q'.length ≤ xs.length →
      pfOrderedCompositionWord xs (groupedLift xs.length q'.length q') = groupedRepetition xs q') ∧
    (∀ (q' : List ℕ), q'.length ≤ xs.length →
      pfNestedCommList (B :: pfOrderedCompositionWord xs (groupedLift xs.length q'.length q')) =
        pfNestedCommList (B :: groupedRepetition xs q')) ∧
    (∀ (s k : ℕ) (q' : List ℕ), k ≤ s → q'.length = k →
      flatWeight (groupedLift s k q') = groupedWeight q') ∧
    (∀ (p k : ℕ) (q' : List ℕ),
      q' ∈ groupedCompositions p k ↔ q'.length = k ∧ q'.sum = p ∧ q'.getLastD 0 ≠ 0) ∧
    (∀ (p k : ℕ), 1 ≤ k → k ≤ xs.length →
      groupedLevelBudget xs B p k = flatLevelBudget xs B p k) ∧
    (∀ (p k : ℕ), 1 ≤ k → k ≤ xs.length →
      (groupedCompositions p k).image (groupedLift xs.length k) =
        (pfCompositions xs.length p).filter (fun q => compositionLevel q = k)) ∧
    (∀ (s : ℕ),
      (Finset.range s).image (fun k => s - k) = Finset.Icc 1 s ∧
      (∀ (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ) (_hp : 1 ≤ p) (t : ℝ),
        orderedRemainder xs B p t =
          ∑ ℓ ∈ Finset.Icc 1 xs.length, orderedRemainderLevel xs B p (xs.length - ℓ) t) ∧
      (∀ (xs : List (Matrix I I ℂ)) (ℓ : ℕ) (_hℓ : 1 ≤ ℓ) (_hℓs : ℓ ≤ xs.length),
        srcGen xs ℓ = xs.getD (xs.length - ℓ) 0 ∧
        (xs.take (xs.length - ℓ)).length = xs.length - ℓ) ∧
      (∀ {J : Type} [Fintype J] [DecidableEq J] (X B : Matrix J J ℂ) (p : ℕ)
        (_hp : 0 < p) (t : ℝ),
        orderedRemainder [X] B p t = pfConjWord [X] B t - pfConjTrunc [X] B p t)) := by
  intro xs B p t hp
  refine ⟨clause49_remainder_level_decomposition xs B p hp t, ?_,
    fun k hk1 hk2 => clause49_outer_inner_split xs k hk1 hk2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact clause49_remainder_eq_cauchy_integral xs B p (by omega) t
  · intro s k q' i
    exact clause49_lift_support q' i
  · intro s k q' hk0 hks hne
    exact clause49_lift_level s k q' hk0 hks hne
  · intro q' h
    exact clause49_grouped_flat_word xs q' h
  · intro q' h
    exact clause49_grouped_flat_nested_comm xs B q' h
  · intro s k q' hk hql
    exact clause49_grouped_flat_weight hk q' hql
  · intro p k q'
    exact clause49_grouped_compositions_mem q'
  · intro p k hk hks
    exact clause49_level_budget_eq xs B p k hk hks
  · intro p k hk hks
    exact clause49_lift_image_eq hk hks
  · exact clause49_frozen_bridge_statement

/-- Scaling every matrix in a nested commutator list by `a` scales the result by `a` to the list
length. -/
theorem clause50_nested_comm_scaling (l : List (Matrix I I ℂ)) (a : ℝ) :
    pfNestedCommList (l.map (fun Y => a • Y)) = a ^ l.length • pfNestedCommList l := by
  have hnest : ∀ (a c : ℝ) (X : Matrix I I ℂ), a • (c • X) = (a * c) • X := by
    intro a c X
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  have hnest' : ∀ (a c : ℝ) (X : Matrix I I ℂ), c • (a • X) = (a * c) • X := by
    intro a c X
    rw [hnest c a X, mul_comm]
  have hcomm : ∀ (Y D : Matrix I I ℂ) (a c : ℝ),
      pfComm (a • Y) (c • D) = (a * c) • pfComm Y D := by
    intro Y D a c
    calc pfComm (a • Y) (c • D) = (a • Y) * (c • D) - (c • D) * (a • Y) := rfl
      _ = a • (c • (Y * D)) - c • (a • (D * Y)) := by
          rw [show (a • Y) * (c • D) = a • (Y * (c • D)) by
                rw [smul_mul_assoc]]
          rw [show Y * (c • D) = c • (Y * D) by
                rw [mul_smul_comm]]
          rw [show (c • D) * (a • Y) = c • (D * (a • Y)) by
                rw [smul_mul_assoc]]
          rw [show D * (a • Y) = a • (D * Y) by
                rw [mul_smul_comm]]
      _ = (a * c) • (Y * D) - (a * c) • (D * Y) := by
          rw [hnest, hnest']
      _ = (a * c) • pfComm Y D := by rw [pfComm, smul_sub]
  have hfold : ∀ (l : List (Matrix I I ℂ)) (c : ℝ) (D : Matrix I I ℂ),
      (l.map (fun Y => a • Y)).foldl (fun D Y => pfComm Y D) (c • D) =
        (c * a ^ l.length) • (l.foldl (fun D Y => pfComm Y D) D) := by
    intro l
    induction l with
    | nil => intro c D; simp [List.map_nil, List.foldl_nil]
    | cons Y l ih =>
      intro c D
      rw [List.map_cons, List.foldl_cons]
      rw [hcomm Y D a c, ih (a * c) (pfComm Y D), List.foldl_cons, List.length_cons,
        pow_succ]
      congr 1
      ring
  induction l with
  | nil => simp [pfNestedCommList, List.map_nil]
  | cons Y l ih =>
    have h1 : (Y :: l).map (fun Y => a • Y) = (a • Y) :: l.map (fun Y => a • Y) := by
      simp [List.map_cons]
    rw [h1]
    simp only [pfNestedCommList]
    rw [hfold l a Y]
    simp only [pfNestedCommList, List.length_cons, pow_succ]
    congr 1
    ring

/-- The nested commutator is additive in its initial matrix. -/
theorem clause50_nested_comm_add (l : List (Matrix I I ℂ)) (X Y : Matrix I I ℂ) :
    pfNestedCommList ((X + Y) :: l) = pfNestedCommList (X :: l) + pfNestedCommList (Y :: l) := by
  have hcomm : ∀ (Z D E : Matrix I I ℂ), pfComm Z (D + E) = pfComm Z D + pfComm Z E := by
    intro Z D E
    simp only [pfComm, add_mul, mul_add, sub_eq_add_neg]
    abel
  have hfold : ∀ (l : List (Matrix I I ℂ)) (D E : Matrix I I ℂ),
      l.foldl (fun D Y => pfComm Y D) (D + E) =
        l.foldl (fun D Y => pfComm Y D) D + l.foldl (fun D Y => pfComm Y D) E := by
    intro l
    induction l with
    | nil => intro D E; simp [List.foldl_nil]
    | cons Z l ih =>
      intro D E
      rw [List.foldl_cons, hcomm, ih, List.foldl_cons, List.foldl_cons]
  simp only [pfNestedCommList]
  exact hfold l X Y

/-- The corrected ordered commutator statistic equals `p!` times the ordered adjoint budget. -/
theorem clause50_alpha_budget_factorial (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) :
    pfCommAlphaOrderedV2 xs B p = (p.factorial : ℝ) * pfOrderedAdBudget xs B p LinearMap.id := by
  exact pfCommAlphaOrderedV2_eq_budget xs B p

/-- Mapping the labels of repetition blocks commutes with flattening those blocks. -/
theorem clause50_flatten_map' {α : Type} {β : Type} (L : List (α × ℕ)) (f : α → β) :
    (L.map (fun kc => (f kc.1, kc.2))).flatMap (fun kc => List.replicate kc.2 kc.1)
      = L.flatMap (fun kc => List.replicate kc.2 (f kc.1)) := by
  induction L with
  | nil => rfl
  | cons kc L ih =>
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]

/-- The reversed repetition word can be expressed using `clause50PositionGroups`. -/
theorem clause50_positions_map {n : ℕ} {α : Type} (q : Fin n → ℕ) (f : Fin n → α) :
    (List.ofFn (fun i : Fin n => (f i, q i))).reverse.flatMap (fun kc => List.replicate kc.2 kc.1)
      = (clause50PositionGroups q).flatMap (fun kc => List.replicate kc.2 (f kc.1)) := by
  have hofn : List.ofFn (fun i : Fin n => (f i, q i))
      = (List.ofFn (fun i : Fin n => (i, q i))).map (fun kc => (f kc.1, kc.2)) := by
    apply List.ext_get
    · rw [List.length_ofFn, List.length_map, List.length_ofFn]
    · intro m hm hm'
      simp
  rw [hofn, ← List.map_reverse, clause50_flatten_map']
  rfl

/-- A nested commutator with initial matrix `B` equals the left fold of successive commutators
over the remaining list. -/
theorem clause50_nested_comm_eq_fold {I : Type} [Fintype I] (l : List (Matrix I I ℂ)) (B : Matrix I I ℂ) :
    pfNestedCommList (B :: l) = l.foldl (fun D Y => pfComm Y D) B := rfl

/-- Successive real scalar actions on a matrix combine by multiplication. -/
theorem clause50_smul_assoc {I : Type} [Fintype I] (a b : ℝ) (X : Matrix I I ℂ) :
    a • (b • X) = (a * b) • X := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

/-- A real scalar in the first commutator argument factors out. -/
theorem clause50_comm_scaling_arg {I : Type} [Fintype I] (Y D : Matrix I I ℂ) (a : ℝ) :
    pfComm (a • Y) D = a • pfComm Y D := by
  rw [pfComm, pfComm]
  calc (a • Y) * D - D * (a • Y) = a • (Y * D) - a • (D * Y) := by
        rw [smul_mul_assoc, mul_smul_comm]
    _ = a • (Y * D - D * Y) := by rw [smul_sub]

/-- A real scalar in the second commutator argument factors out. -/
theorem clause50_comm_scaling_acc {I : Type} [Fintype I] (Y D : Matrix I I ℂ) (a : ℝ) :
    pfComm Y (a • D) = a • pfComm Y D := by
  rw [pfComm, pfComm]
  calc Y * (a • D) - (a • D) * Y = a • (Y * D) - a • (D * Y) := by
        rw [mul_smul_comm, smul_mul_assoc]
    _ = a • (Y * D - D * Y) := by rw [smul_sub]

/-- A scalar power in the second commutator argument factors out. -/
theorem clause50_comm_scaling_acc_pow {I : Type} [Fintype I] (Y : Matrix I I ℂ) (a : ℝ) :
    ∀ (n : ℕ) (D : Matrix I I ℂ), pfComm Y (a ^ n • D) = a ^ n • pfComm Y D := by
  intro n D
  induction n generalizing D with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [← clause50_smul_assoc]
      rw [ih (a • D), clause50_comm_scaling_acc]

/-- A real scalar multiplying the initial accumulator factors out of a commutator fold. -/
theorem clause50_fold_seed_scale {I : Type} [Fintype I] (l : List (Matrix I I ℂ)) (a : ℝ)
    (D : Matrix I I ℂ) :
    l.foldl (fun D Y => pfComm Y D) (a • D) = a • (l.foldl (fun D Y => pfComm Y D) D) := by
  induction l generalizing D with
  | nil => simp
  | cons Y l ih =>
      rw [List.foldl_cons, List.foldl_cons, clause50_comm_scaling_acc, ih]

/-- Repeating a generator scaled by `a` for `n` commutators contributes the factor `a ^ n`. -/
theorem clause50_fold_replicate_scale {I : Type} [Fintype I] (Y : Matrix I I ℂ) (a : ℝ) (n : ℕ) (D0 : Matrix I I ℂ) :
    (List.replicate n (a • Y)).foldl (fun D Y' => pfComm Y' D) D0
      = a ^ n • ((List.replicate n Y).foldl (fun D Y' => pfComm Y' D) D0) := by
  induction n generalizing D0 with
  | zero => simp
  | succ n ih =>
      have h1 : List.replicate (n + 1) (a • Y) = (a • Y) :: List.replicate n (a • Y) := by
        rw [List.replicate_succ]
      have h2 : List.replicate (n + 1) Y = Y :: List.replicate n Y := by
        rw [List.replicate_succ]
      rw [h1, List.foldl_cons, h2, List.foldl_cons]
      rw [ih (D0 := pfComm (a • Y) D0)]
      rw [clause50_comm_scaling_arg]
      rw [clause50_fold_seed_scale]
      rw [clause50_smul_assoc, pow_succ]

/-- A scalar multiplying the initial matrix factors out of a repeated-generator commutator fold. -/
theorem clause50_fold_replicate_seed {I : Type} [Fintype I] (Y : Matrix I I ℂ) (n : ℕ) (a : ℝ) (D0 : Matrix I I ℂ) :
    (List.replicate n Y).foldl (fun D Y' => pfComm Y' D) (a • D0)
      = a • ((List.replicate n Y).foldl (fun D Y' => pfComm Y' D) D0) :=
  clause50_fold_seed_scale (List.replicate n Y) a D0

/-- A commutator fold over flattened blocks equals a fold of the individual block folds. -/
theorem clause50_fold_flatMap {I : Type} [Fintype I] {α : Type} (L : List (α × ℕ))
    (g : (α × ℕ) → List (Matrix I I ℂ)) (D0 : Matrix I I ℂ) :
    (L.flatMap g).foldl (fun D Y => pfComm Y D) D0
      = L.foldl (fun D kc => (g kc).foldl (fun D Y => pfComm Y D) D) D0 := by
  induction L generalizing D0 with
  | nil => rfl
  | cons a L ih =>
      rw [List.flatMap_cons, List.foldl_cons, List.foldl_append]
      rw [ih (List.foldl (fun D Y => pfComm Y D) D0 (g a))]

/-- A scalar multiplying the initial matrix factors out of a grouped commutator fold. -/
theorem clause50_fold_groups_seed {I : Type} [Fintype I] {n : ℕ} (L : List (Fin n × ℕ))
    (m : Fin n → Matrix I I ℂ) (a : ℝ) (X : Matrix I I ℂ) :
    L.foldl (fun D kc => (List.replicate kc.2 (m kc.1)).foldl (fun D Y => pfComm Y D) D) (a • X)
      = a • (L.foldl (fun D kc => (List.replicate kc.2 (m kc.1)).foldl (fun D Y => pfComm Y D) D) X) := by
  induction L generalizing X with
  | nil => simp
  | cons kc L ih =>
      rw [List.foldl_cons, List.foldl_cons, clause50_fold_seed_scale, ih]

/-- Scaling each generator in a grouped commutator fold contributes the product of its scale
raised to its repetition count. -/
theorem clause50_fold_groups_scale {I : Type} [Fintype I] {n : ℕ} (L : List (Fin n × ℕ)) (c : Fin n → ℝ)
    (m g : Fin n → Matrix I I ℂ) (hm : ∀ i, m i = c i • g i) :
    ∀ (X : Matrix I I ℂ),
      L.foldl (fun D kc => (List.replicate kc.2 (m kc.1)).foldl (fun D Y => pfComm Y D) D) X
        = (L.map (fun kc => c kc.1 ^ kc.2)).prod •
            (L.foldl (fun D kc => (List.replicate kc.2 (g kc.1)).foldl (fun D Y => pfComm Y D) D) X) := by
  intro X
  induction L generalizing X with
  | nil => simp
  | cons kc L ih =>
      rw [List.foldl_cons]
      have hgrp : (List.replicate kc.2 (m kc.1)).foldl (fun D Y => pfComm Y D) X
          = c kc.1 ^ kc.2 • ((List.replicate kc.2 (g kc.1)).foldl (fun D Y => pfComm Y D) X) := by
        rw [hm kc.1]
        exact clause50_fold_replicate_scale (g kc.1) (c kc.1) kc.2 X
      rw [hgrp]
      rw [clause50_fold_groups_seed L m (c kc.1 ^ kc.2)
        ((List.replicate kc.2 (g kc.1)).foldl (fun D Y => pfComm Y D) X)]
      rw [ih ((List.replicate kc.2 (g kc.1)).foldl (fun D Y => pfComm Y D) X)]
      rw [List.map_cons, List.prod_cons, List.foldl_cons, clause50_smul_assoc]

/-- The scale product over position groups equals the product over all composition coordinates. -/
theorem clause50_positions_scale_prod {n : ℕ} (q : Fin n → ℕ) (c : Fin n → ℝ) :
    ((clause50PositionGroups q).map (fun kc => c kc.1 ^ kc.2)).prod = ∏ i, c i ^ (q i) := by
  have hgrp : clause50PositionGroups q
      = List.map (fun i : Fin n => (i, q i)) (List.finRange n).reverse := by
    unfold clause50PositionGroups
    rw [List.ofFn_eq_map, ← List.map_reverse]
  rw [hgrp, List.map_map, List.map_reverse, List.prod_reverse]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  rfl

/-- For a family word, the nested commutator equals the family-labelled commutator multiplied by
`scaleProduct`. -/
theorem clause50_family_alignment {D m : ℕ} (H : Fin m → Operator D) (B : Operator D)
    (xs : List (Operator D)) (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ)
    (hfam : IsFamilyWord H xs lab c) (q : Fin xs.length → ℕ) :
    pfNestedCommList (B :: pfOrderedCompositionWord xs q) =
      scaleProduct c q • pfNestedCommList (B :: (familyCompositionWord lab q).map H) := by
  simp only [scaleProduct]
  have hword : pfOrderedCompositionWord xs q
      = (clause50PositionGroups q).flatMap (fun kc => List.replicate kc.2 (xs.get kc.1)) :=
    clause50_positions_map q (fun i => xs.get i)
  have hfamword : familyCompositionWord lab q
      = (clause50PositionGroups q).flatMap (fun kc => List.replicate kc.2 (lab kc.1)) :=
    clause50_positions_map q lab
  rw [clause50_nested_comm_eq_fold, hword]
  rw [clause50_fold_flatMap (g := fun kc => List.replicate kc.2 (xs.get kc.1))]
  rw [clause50_nested_comm_eq_fold, hfamword, List.map_flatMap]
  rw [clause50_fold_flatMap (g := fun kc => List.map H (List.replicate kc.2 (lab kc.1)))]
  simp only [List.map_replicate]
  rw [clause50_fold_groups_scale (L := clause50PositionGroups q) (c := c) (m := fun i => xs.get i)
    (g := fun i => H (lab i)) (fun i => hfam i)]
  rw [clause50_positions_scale_prod q c]

/-- The factorial-weighted ordered adjoint budget equals the composition sum of scaled family
commutator norms. -/
theorem clause50_family_ordered_budget_eq {D m : ℕ} (H : Fin m → Operator D) (B : Operator D)
    (L : Operator D →ₗ[ℝ] Operator D) (xs : List (Operator D)) (lab : Fin xs.length → Fin m)
    (c : Fin xs.length → ℝ) (hfam : IsFamilyWord H xs lab c) (p : ℕ) :
    (p.factorial : ℝ) * pfOrderedAdBudget xs B p L =
      ∑ q ∈ pfCompositions xs.length p,
        (p.factorial : ℝ) * (∏ i, ((q i).factorial : ℝ))⁻¹ *
          |scaleProduct c q| *
          ‖L (pfNestedCommList (B :: (familyCompositionWord lab q).map H))‖ := by
  simp only [scaleProduct]
  have hterm : ∀ q ∈ pfCompositions xs.length p,
      ‖L (pfNestedCommList (B :: pfOrderedCompositionWord xs q))‖ =
        |scaleProduct c q| *
          ‖L (pfNestedCommList (B :: (familyCompositionWord lab q).map H))‖ := by
    intro q hq
    have hal := clause50_family_alignment H B xs lab c hfam q
    have hmap : L (pfNestedCommList (B :: pfOrderedCompositionWord xs q)) =
        (∏ i, c i ^ (q i)) •
          L (pfNestedCommList (B :: (familyCompositionWord lab q).map H)) := by
      rw [hal]
      exact L.map_smul _ _
    rw [hmap, norm_smul]
    rfl
  unfold pfOrderedAdBudget
  calc (p.factorial : ℝ) *
        ∑ q ∈ pfCompositions xs.length p,
          (∏ i, ((q i).factorial : ℝ))⁻¹ *
            ‖L (pfNestedCommList (B :: pfOrderedCompositionWord xs q))‖
      = ∑ q ∈ pfCompositions xs.length p,
          (p.factorial : ℝ) * (∏ i, ((q i).factorial : ℝ))⁻¹ *
            |scaleProduct c q| *
            ‖L (pfNestedCommList (B :: (familyCompositionWord lab q).map H))‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hterm q hq, ← mul_assoc]
        ring
    _ = ∑ q ∈ pfCompositions xs.length p,
        (p.factorial : ℝ) * (∏ i, ((q i).factorial : ℝ))⁻¹ *
          |scaleProduct c q| *
          ‖L (pfNestedCommList (B :: (familyCompositionWord lab q).map H))‖ := rfl

/-- The head of flattened repetition blocks is the label of the first block with positive
repetition count. -/
theorem clause50_flatMap_replicate_head {α : Type} (L : List (α × ℕ)) :
    (L.flatMap (fun kc => List.replicate kc.2 kc.1)).head? =
      (clause50FirstPositive L).map Prod.fst := by
  induction L with
  | nil => simp [clause50FirstPositive]
  | cons kc L ih =>
    by_cases h : 0 < kc.2
    · rw [List.flatMap_cons]
      have hrep : (List.replicate kc.2 kc.1).head? = some kc.1 := by
        obtain ⟨m, hm⟩ : ∃ m, kc.2 = m + 1 := ⟨kc.2 - 1, by omega⟩
        rw [hm]
        simp [List.replicate_succ]
      rw [List.head?_append, hrep]
      simp [clause50FirstPositive, h]
    · have hz : kc.2 = 0 := by omega
      rw [List.flatMap_cons]
      simp only [hz, List.replicate_zero, List.nil_append]
      rw [ih]
      simp [clause50FirstPositive, h]

/-- The head of a family composition word is the label of the first positive block in reversed
position order. -/
theorem clause50_family_word_head {m n : ℕ} (lab : Fin n → Fin m) (q : Fin n → ℕ) :
    (familyCompositionWord lab q).head? =
      ((clause50FirstPositive (List.ofFn (fun i : Fin n => (lab i, q i))).reverse).map Prod.fst) := by
  change ((List.ofFn (fun i : Fin n => (lab i, q i))).reverse.flatMap
      (fun kc => List.replicate kc.2 kc.1)).head? = _
  exact clause50_flatMap_replicate_head _

/-- A list containing a positive repetition count has a first positive block. -/
theorem clause50_first_positive_some {α : Type} (L : List (α × ℕ)) :
    (∃ kc ∈ L, 0 < kc.2) → ∃ kc, clause50FirstPositive L = some kc := by
  induction L with
  | nil =>
      intro h
      simp at h
  | cons a t ih =>
      intro h
      by_cases ha : 0 < a.2
      · exact ⟨a, by simp [clause50FirstPositive, ha]⟩
      · have hrest : ∃ kc ∈ t, 0 < kc.2 := by
          obtain ⟨kc, hkc, hpos⟩ := h
          refine ⟨kc, ?_, hpos⟩
          rcases List.mem_cons.mp hkc with hhead | hkc'
          · exact absurd (hhead ▸ hpos) ha
          · exact hkc'
        obtain ⟨kc, hkc⟩ := ih hrest
        exact ⟨kc, by simp [clause50FirstPositive, ha, hkc]⟩

/-- A family composition with a positive coordinate has head `clause50FamilyHead`. -/
theorem clause50_family_head_some {m n : ℕ} (lab : Fin n → Fin m) (q : Fin n → ℕ)
    (hne : ∃ i, 0 < q i) :
    (familyCompositionWord lab q).head? = some (clause50FamilyHead lab q hne) := by
  rw [clause50_family_word_head]
  have hmem : ∃ kc ∈ (List.ofFn (fun i : Fin n => (lab i, q i))).reverse, 0 < kc.2 := by
    obtain ⟨i, hi⟩ := hne
    refine ⟨(lab i, q i), ?_, hi⟩
    exact List.mem_reverse.mpr ((List.mem_ofFn).2 ⟨i, rfl⟩)
  obtain ⟨kc, hkc⟩ := clause50_first_positive_some _ hmem
  have hmap : ((clause50FirstPositive (List.ofFn (fun i : Fin n => (lab i, q i))).reverse).map Prod.fst)
      = some kc.1 := by simp [hkc]
  rw [hmap]
  simp [clause50FamilyHead, hkc]

/-- A nonempty family composition word mapped through `H` splits into its selected head and
mapped tail. -/
theorem clause50_family_map_cons {D m n : ℕ} (H : Fin m → Operator D) (lab : Fin n → Fin m)
    (q : Fin n → ℕ) (hne : ∃ i, 0 < q i) :
    (familyCompositionWord lab q).map H =
      H (clause50FamilyHead lab q hne) :: ((familyCompositionWord lab q).tail).map H := by
  have hhead := clause50_family_head_some lab q hne
  rw [List.head?_eq_some_iff] at hhead
  obtain ⟨t, hwt⟩ := hhead
  rw [hwt]
  simp

/-- The first commutator step can be absorbed into the initial matrix of a nested commutator. -/
theorem clause50_nested_comm_seed_shift {I : Type} [Fintype I] (B X : Matrix I I ℂ)
    (l : List (Matrix I I ℂ)) :
    pfNestedCommList (B :: (X :: l)) = pfNestedCommList (pfComm X B :: l) := by
  rw [clause50_nested_comm_eq_fold, clause50_nested_comm_eq_fold]
  show (X :: l).foldl (fun D Y => pfComm Y D) B
      = l.foldl (fun D Y => pfComm Y D) (pfComm X B)
  rw [List.foldl_cons]

/-- A seeded family commutator can start from the commutator of its first family generator with
`B`. -/
theorem clause50_family_seed_conversion {D m n : ℕ} (H : Fin m → Operator D) (B : Operator D)
    (lab : Fin n → Fin m) (q : Fin n → ℕ) (hne : ∃ i, 0 < q i) :
    pfNestedCommList (B :: (familyCompositionWord lab q).map H) =
      pfNestedCommList (pfComm (H (clause50FamilyHead lab q hne)) B ::
        ((familyCompositionWord lab q).map H).tail) := by
  have hmap := clause50_family_map_cons H lab q hne
  rw [hmap]
  simp only [List.tail_cons]
  exact clause50_nested_comm_seed_shift B (H (clause50FamilyHead lab q hne)) _

/-- The unseeded family commutator equals the nested commutator seeded by its selected head
generator. -/
theorem clause50_family_unseeded_head_seeded {D m n : ℕ} (H : Fin m → Operator D)
    (lab : Fin n → Fin m) (q : Fin n → ℕ) (hne : ∃ i, 0 < q i) :
    familyNestedCommList H (familyCompositionWord lab q) =
      pfNestedCommList (H (clause50FamilyHead lab q hne) ::
        ((familyCompositionWord lab q).map H).tail) := by
  have hmap := clause50_family_map_cons H lab q hne
  rw [familyNestedCommList, hmap]
  simp only [List.tail_cons]

/-- Absorbing the first family generator into the seed preserves the nested commutator norm. -/
theorem clause50_family_seed_conversion_norm {D m n : ℕ} (H : Fin m → Operator D) (B : Operator D)
    (lab : Fin n → Fin m) (q : Fin n → ℕ) (hne : ∃ i, 0 < q i) :
    ‖pfNestedCommList (B :: (familyCompositionWord lab q).map H)‖
      = ‖pfNestedCommList (pfComm (H (clause50FamilyHead lab q hne)) B ::
          ((familyCompositionWord lab q).map H).tail)‖ := by
  rw [clause50_family_seed_conversion H B lab q hne]

/-- The total family-head selector agrees with the selector defined from a positive composition
coordinate. -/
theorem clause50_family_head_total_eq {m n : ℕ} (hn : 0 < n) (lab : Fin n → Fin m) (q : Fin n → ℕ)
    (hne : ∃ i, 0 < q i) :
    clause50FamilyHeadTotal hn lab q = clause50FamilyHead lab q hne := by
  have hmem : ∃ kc ∈ (List.ofFn (fun i : Fin n => (lab i, q i))).reverse, 0 < kc.2 := by
    obtain ⟨i, hi⟩ := hne
    refine ⟨(lab i, q i), ?_, hi⟩
    exact List.mem_reverse.mpr ((List.mem_ofFn).2 ⟨i, rfl⟩)
  obtain ⟨kc, hkc⟩ := clause50_first_positive_some _ hmem
  simp [clause50FamilyHeadTotal, clause50FamilyHead, hkc]

/-- A natural-valued composition of positive total degree has a positive coordinate. -/
theorem clause50_composition_ne {n p : ℕ} (q : Fin n → ℕ) (hp : 0 < p)
    (hsum : (∑ i, q i) = p) : ∃ i, 0 < q i := by
  by_contra hcon
  have hz : (∑ i, q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Nat.eq_zero_of_not_pos (fun hpos => hcon ⟨i, hpos⟩)
  omega

/-- The positive-order seeded family budget expands into multinomially weighted norms with the
first generator absorbed into the seed. -/
theorem clause50_family_budget_conversion {D m n : ℕ} (hn : 0 < n) (H : Fin m → Operator D)
    (B : Operator D) (lab : Fin n → Fin m) (c : Fin n → ℝ) (p : ℕ) (hp : 0 < p) :
    clause50SeededFamilyBudget H B lab c p =
      ∑ q ∈ pfCompositions n p,
        ((p.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ)) *
          |∏ i, (c i) ^ (q i)| *
          ‖pfNestedCommList (pfComm (H (clause50FamilyHeadTotal hn lab q)) B ::
            ((familyCompositionWord lab q).map H).tail)‖ := by
  unfold clause50SeededFamilyBudget
  apply Finset.sum_congr rfl
  intro q hq
  have hsum : (∑ i, q i) = p := (Finset.mem_filter.mp hq).2
  have hne : ∃ i, 0 < q i := clause50_composition_ne q hp hsum
  rw [clause50_family_head_total_eq hn lab q hne]
  rw [clause50_family_seed_conversion H B lab q hne]

/-- The positive-order unseeded family budget expands into multinomially weighted norms seeded
by the first family generator. -/
theorem clause50_family_budget_head_seeded {D m n : ℕ} (hn : 0 < n) (H : Fin m → Operator D)
    (lab : Fin n → Fin m) (c : Fin n → ℝ) (p : ℕ) (hp : 0 < p) :
    familyOrderedBudget H lab c p =
      ∑ q ∈ pfCompositions n p,
        ((p.factorial : ℝ) / ∏ i, ((q i).factorial : ℝ)) *
          |∏ i, (c i) ^ (q i)| *
          ‖pfNestedCommList (H (clause50FamilyHeadTotal hn lab q) ::
            ((familyCompositionWord lab q).map H).tail)‖ := by
  unfold familyOrderedBudget
  apply Finset.sum_congr rfl
  intro q hq
  have hsum : (∑ i, q i) = p := (Finset.mem_filter.mp hq).2
  have hne : ∃ i, 0 < q i := clause50_composition_ne q hp hsum
  rw [clause50_family_head_total_eq hn lab q hne]
  rw [clause50_family_unseeded_head_seeded H lab q hne]

/-- The ordered-budget normalization, nested-commutator linearity, family alignment, and seed
conversion hold together. -/
theorem clause50_endpoint : ∀ (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p : ℕ),
    (pfCommAlphaOrderedV2 xs B p = (p.factorial : ℝ) * pfOrderedAdBudget xs B p LinearMap.id) ∧
    (∀ (l : List (Matrix I I ℂ)) (a : ℝ),
      pfNestedCommList (l.map (fun Y => a • Y)) = a ^ l.length • pfNestedCommList l) ∧
    (∀ (l : List (Matrix I I ℂ)) (X Y : Matrix I I ℂ),
      pfNestedCommList ((X + Y) :: l) = pfNestedCommList (X :: l) + pfNestedCommList (Y :: l)) ∧
    clause50FamilyAlignmentStatement ∧
    clause50SeedConversionStatement := by
  intro xs B p
  refine ⟨clause50_alpha_budget_factorial xs B p, clause50_nested_comm_scaling,
    clause50_nested_comm_add, ?_, ?_⟩
  · exact fun {D m} Hfam Bfam Lfam xsfam labfam cfam pfam hfam =>
      ⟨clause50_family_alignment Hfam Bfam xsfam labfam cfam hfam,
        clause50_family_ordered_budget_eq Hfam Bfam Lfam xsfam labfam cfam hfam pfam⟩
  · exact fun {D m n} Hfam Bfam labfam qfam hnefam =>
      ⟨clause50_family_seed_conversion Hfam Bfam labfam qfam hnefam,
        clause50_family_unseeded_head_seeded Hfam labfam qfam hnefam⟩

/-- The cubic coefficient of the two-generator Suzuki series is the ordered sum of the four
degree-three monomials with factorial weights. -/
theorem clause51_series_cubic (X Y : Matrix I I ℂ) :
    suzukiSeries [X, Y] 3 = (1 / 6 : ℝ) • Y ^ 3 + X * ((1 / 2 : ℝ) • Y ^ 2) +
      ((1 / 2 : ℝ) • X ^ 2) * Y + (1 / 6 : ℝ) • X ^ 3 := by
  have e0 : suzukiSeries ([] : List (Matrix I I ℂ)) 0 = 1 := suzukiSeries_zero []
  have e1 : suzukiSeries ([] : List (Matrix I I ℂ)) 1 = 0 := suzukiSeries_nil_succ 0
  have e2 : suzukiSeries ([] : List (Matrix I I ℂ)) 2 = 0 := suzukiSeries_nil_succ 1
  have e3 : suzukiSeries ([] : List (Matrix I I ℂ)) 3 = 0 := suzukiSeries_nil_succ 2
  have hY3 : suzukiSeries [Y] 3 = (1 / 6 : ℝ) • Y ^ 3 := by
    rw [suzukiSeries_cons_three]
    simp only [suzukiSeries]
    simp
  have hY2 : suzukiSeries [Y] 2 = (1 / 2 : ℝ) • Y ^ 2 := by
    rw [suzukiSeries_cons_two]
    simp only [suzukiSeries]
    simp
  have hY1 : suzukiSeries [Y] 1 = Y := by
    rw [suzukiSeries_cons_one]
    simp only [suzukiSeries]
    simp
  rw [suzukiSeries_cons_three, hY3, hY2, hY1]

/-- The cubic Trotter deviation expands as the stated linear combination of six mixed ordered
monomials. -/
theorem clause51_cubic_deviation_word_form (X Y : Matrix I I ℂ) :
    trotterCubicDeviation X Y =
      (1 / 3 : ℝ) • (X ^ 2 * Y) + (1 / 3 : ℝ) • (X * Y ^ 2)
        - (1 / 6 : ℝ) • (X * Y * X) - (1 / 6 : ℝ) • (Y * X ^ 2)
        - (1 / 6 : ℝ) • (Y * X * Y) - (1 / 6 : ℝ) • (Y ^ 2 * X) := by
  have hexp : (X + Y) ^ 3 = X ^ 3 + X ^ 2 * Y + X * Y * X + Y * X ^ 2 + X * Y ^ 2
      + Y * X * Y + Y ^ 2 * X + Y ^ 3 := by
    noncomm_ring
  have hmul : X * ((1 / 2 : ℝ) • Y ^ 2) = (1 / 2 : ℝ) • (X * Y ^ 2) := by
    ext i j
    change (∑ k, X i k * ((1 / 2 : ℝ) • (Y ^ 2) k j)) = (1 / 2 : ℝ) • (∑ k, X i k * (Y ^ 2) k j)
    simp only [Complex.real_smul]
    rw [Finset.mul_sum]
    congr 1
    funext k
    ring
  have hmul2 : ((1 / 2 : ℝ) • X ^ 2) * Y = (1 / 2 : ℝ) • (X ^ 2 * Y) := by
    ext i j
    change (∑ k, ((1 / 2 : ℝ) • (X ^ 2) i k) * Y k j) = (1 / 2 : ℝ) • (∑ k, (X ^ 2) i k * Y k j)
    simp only [Complex.real_smul]
    rw [Finset.mul_sum]
    congr 1
    funext k
    ring
  have smul_entry : ∀ (a : ℝ) (M : Matrix I I ℂ) (i j : I), (a • M) i j = a • M i j := by
    intro a M i j; rfl
  have sub_entry : ∀ (A B : Matrix I I ℂ) (i j : I), (A - B) i j = A i j - B i j := by
    intro A B i j; rfl
  unfold trotterCubicDeviation
  rw [clause51_series_cubic, hmul, hmul2, hexp]
  ext i j
  simp only [sub_entry, Matrix.add_apply, smul_entry, Complex.real_smul]
  norm_num
  ring

/-- If `X` and `Y` commute, then `Y` commutes with `X ^ 2`. -/
theorem clause51_commute_pow (X Y : Matrix I I ℂ) (hxy : X * Y = Y * X) :
    Y * X ^ 2 = X ^ 2 * Y := by
  calc Y * X ^ 2 = (Y * X) * X := by rw [pow_two, mul_assoc]
    _ = (X * Y) * X := by rw [hxy]
    _ = X * (Y * X) := mul_assoc X Y X
    _ = X * (X * Y) := by rw [hxy]
    _ = X ^ 2 * Y := by rw [← mul_assoc, pow_two]

/-- The cubic Trotter deviation vanishes when the commutator vanishes. -/
theorem clause51_cubic_deviation_zero_of_commuting (X Y : Matrix I I ℂ) (h : pfComm X Y = 0) :
    trotterCubicDeviation X Y = 0 := by
  have hxy : X * Y = Y * X := by
    have hz : X * Y - Y * X = 0 := by
      simpa [pfComm] using! h
    exact sub_eq_zero.mp hz
  have h1 : X * Y * X = X ^ 2 * Y := by
    calc (X * Y) * X = (Y * X) * X := by rw [hxy]
      _ = Y * (X * X) := mul_assoc Y X X
      _ = Y * X ^ 2 := by rw [pow_two]
      _ = X ^ 2 * Y := clause51_commute_pow X Y hxy
  have h2 : Y * X ^ 2 = X ^ 2 * Y := clause51_commute_pow X Y hxy
  have h3 : Y * X * Y = X * Y ^ 2 := by
    calc (Y * X) * Y = (X * Y) * Y := by rw [hxy]
      _ = X * (Y * Y) := mul_assoc X Y Y
      _ = X * Y ^ 2 := by rw [pow_two]
  have h4 : Y ^ 2 * X = X * Y ^ 2 := by
    calc Y ^ 2 * X = Y * (Y * X) := by rw [pow_two, mul_assoc]
      _ = Y * (X * Y) := by rw [hxy]
      _ = (Y * X) * Y := (mul_assoc Y X Y).symm
      _ = (X * Y) * Y := by rw [hxy]
      _ = X * Y ^ 2 := by rw [mul_assoc, pow_two]
  rw [clause51_cubic_deviation_word_form, h1, h2, h3, h4]
  have smul_entry : ∀ (a : ℝ) (M : Matrix I I ℂ) (i j : I), (a • M) i j = a • M i j := by
    intro a M i j; rfl
  have sub_entry : ∀ (A B : Matrix I I ℂ) (i j : I), (A - B) i j = A i j - B i j := by
    intro A B i j; rfl
  ext i j
  simp only [sub_entry, Matrix.add_apply, smul_entry, Complex.real_smul]
  norm_num
  ring

/-- The cubic coefficient for a singleton generator is one sixth of its cube. -/
theorem clause51_cubic_coefficient_single (X : Matrix I I ℂ) :
    suzukiSeries [X] 3 = (1 / 6 : ℝ) • X ^ 3 := by
  rw [suzukiSeries_cons_three]
  simp only [suzukiSeries]
  simp

omit [DecidableEq I] in

/-- A real scalar multiplying the right matrix factor can be moved outside the product. -/
theorem clause51_mul_smul (a : ℝ) (A B : Matrix I I ℂ) :
    A * (a • B) = a • (A * B) := by
  ext i j
  change (∑ k, A i k * (a • B k j)) = a • (∑ k, A i k * B k j)
  simp only [Complex.real_smul]
  rw [Finset.mul_sum]
  congr 1
  funext k
  ring

omit [DecidableEq I] in

/-- A real scalar multiplying the left matrix factor can be moved outside the product. -/
theorem clause51_smul_mul (a : ℝ) (A B : Matrix I I ℂ) :
    (a • A) * B = a • (A * B) := by
  ext i j
  change (∑ k, (a • A i k) * B k j) = a • (∑ k, A i k * B k j)
  simp only [Complex.real_smul]
  rw [Finset.mul_sum]
  congr 1
  funext k
  ring

omit [DecidableEq I] in

/-- The product of two real-scaled matrices equals their matrix product scaled by the product of
the scalars. -/
theorem clause51_smul_mul_smul (a b : ℝ) (A B : Matrix I I ℂ) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [clause51_smul_mul, clause51_mul_smul, smul_smul]

/-- The Suzuki coefficient for a list with head `X` is the convolution of the exponential
coefficients of `X` with the coefficients of the tail. -/
theorem clause51_series_convolution (X : Matrix I I ℂ) (xs : List (Matrix I I ℂ)) (n : ℕ) :
    suzukiSeries (X :: xs) n =
      ∑ m ∈ Finset.range (n + 1), ((m.factorial : ℝ)⁻¹ • X ^ m) * suzukiSeries xs (n - m) := by
  simp only [suzukiSeries]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The two-generator Suzuki coefficient equals `twoGeneratorOrderedWords`. -/
theorem clause51_series_two_generators (X Y : Matrix I I ℂ) (n : ℕ) :
    suzukiSeries [X, Y] n = twoGeneratorOrderedWords n X Y := by
  rw [clause51_series_convolution]
  simp_rw [suzukiSeries_singleton]
  rfl

/-- The quartic two-generator Suzuki coefficient is the ordered sum of five degree-four
monomials with factorial weights. -/
theorem clause51_series_quartic (X Y : Matrix I I ℂ) :
    suzukiSeries [X, Y] 4 =
      (1 / 24 : ℝ) • Y ^ 4 + (1 / 6 : ℝ) • (X * Y ^ 3) + (1 / 4 : ℝ) • (X ^ 2 * Y ^ 2)
        + (1 / 6 : ℝ) • (X ^ 3 * Y) + (1 / 24 : ℝ) • X ^ 4 := by
  have hY4 : suzukiSeries [Y] 4 = (1 / 24 : ℝ) • Y ^ 4 := by
    rw [suzukiSeries_cons_four]
    simp only [suzukiSeries]
    simp
  have hY3 : suzukiSeries [Y] 3 = (1 / 6 : ℝ) • Y ^ 3 := by
    rw [suzukiSeries_cons_three]
    simp only [suzukiSeries]
    simp
  have hY2 : suzukiSeries [Y] 2 = (1 / 2 : ℝ) • Y ^ 2 := by
    rw [suzukiSeries_cons_two]
    simp only [suzukiSeries]
    simp
  have hY1 : suzukiSeries [Y] 1 = Y := by
    rw [suzukiSeries_cons_one]
    simp only [suzukiSeries]
    simp
  rw [suzukiSeries_cons_four, hY4, hY3, hY2, hY1]
  rw [clause51_mul_smul, clause51_smul_mul_smul, clause51_smul_mul]
  have hcoef : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by ring
  rw [hcoef]

/-- The quartic Trotter deviation expands as the stated linear combination of mixed degree-four
matrix words. -/
theorem clause51_quartic_deviation_word_form (X Y : Matrix I I ℂ) :
    trotterQuarticDeviation X Y =
      (1 / 8 : ℝ) • (X ^ 3 * Y) + (1 / 8 : ℝ) • (X * Y ^ 3) + (5 / 24 : ℝ) • (X ^ 2 * Y ^ 2)
        - (1 / 24 : ℝ) • ((X ^ 2 * Y) * X) - (1 / 24 : ℝ) • ((X * Y) * X ^ 2)
        - (1 / 24 : ℝ) • ((X * Y * X) * Y) - (1 / 24 : ℝ) • ((X * Y ^ 2) * X)
        - (1 / 24 : ℝ) • (Y * X ^ 3) - (1 / 24 : ℝ) • ((Y * X ^ 2) * Y)
        - (1 / 24 : ℝ) • ((Y * X * Y) * X) - (1 / 24 : ℝ) • ((Y * X) * Y ^ 2)
        - (1 / 24 : ℝ) • (Y ^ 2 * X ^ 2) - (1 / 24 : ℝ) • ((Y ^ 2 * X) * Y)
        - (1 / 24 : ℝ) • (Y ^ 3 * X) := by
  have hexp : (X + Y) ^ 4 =
      X ^ 4 + X ^ 3 * Y + (X ^ 2 * Y) * X + X ^ 2 * Y ^ 2 + (X * Y) * X ^ 2
        + (X * Y * X) * Y + (X * Y ^ 2) * X + X * Y ^ 3
        + Y * X ^ 3 + (Y * X ^ 2) * Y + (Y * X * Y) * X + (Y * X) * Y ^ 2
        + Y ^ 2 * X ^ 2 + (Y ^ 2 * X) * Y + Y ^ 3 * X + Y ^ 4 := by
    noncomm_ring
  unfold trotterQuarticDeviation
  rw [clause51_series_quartic, hexp]
  have smul_entry : ∀ (a : ℝ) (M : Matrix I I ℂ) (i j : I), (a • M) i j = a • M i j := by
    intro a M i j; rfl
  have sub_entry : ∀ (A B : Matrix I I ℂ) (i j : I), (A - B) i j = A i j - B i j := by
    intro A B i j; rfl
  ext i j
  simp only [sub_entry, Matrix.add_apply, smul_entry, Complex.real_smul]
  norm_num
  ring

/-- Right multiplication by the matrix natural-number cast equals real scalar multiplication. -/
theorem clause51_mul_natCast (c : ℕ) (M : Matrix I I ℂ) :
    M * (c : Matrix I I ℂ) = (c : ℝ) • M := by
  induction c with
  | zero => simp
  | succ c ih =>
      have h1 : ((c + 1 : ℕ) : ℝ) = (c : ℝ) + 1 := by push_cast; ring
      rw [h1, Nat.cast_succ, Matrix.mul_add, ih]
      simp [add_smul, one_smul]

/-- A binomial coefficient divided by `n!` equals the reciprocal factorial weights for the two
complementary degrees. -/
theorem clause51_choose_coeff {n m : ℕ} (hm : m ≤ n) :
    ((n.factorial : ℝ)⁻¹) * (n.choose m : ℝ)
      = (m.factorial : ℝ)⁻¹ * ((n - m).factorial : ℝ)⁻¹ := by
  have hneA : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero m)
  have hneB : ((n - m).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (n - m))
  have hneF : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  have hcast : (n.choose m : ℝ) * (m.factorial : ℝ) * ((n - m).factorial : ℝ)
      = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have h2 : (n.choose m : ℝ)
      = (n.factorial : ℝ) / ((m.factorial : ℝ) * ((n - m).factorial : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hneA hneB), ← mul_assoc]
    exact hcast
  rw [h2]
  calc
    ((n.factorial : ℝ)⁻¹) * ((n.factorial : ℝ) / ((m.factorial : ℝ) * ((n - m).factorial : ℝ)))
      = (((n.factorial : ℝ)⁻¹) * (n.factorial : ℝ))
          * ((m.factorial : ℝ) * ((n - m).factorial : ℝ))⁻¹ := by
            rw [div_eq_mul_inv, ← mul_assoc]
    _ = ((m.factorial : ℝ) * ((n - m).factorial : ℝ))⁻¹ := by
          rw [inv_mul_cancel₀ hneF, one_mul]
    _ = (m.factorial : ℝ)⁻¹ * ((n - m).factorial : ℝ)⁻¹ := by exact mul_inv _ _

/-- For commuting generators, every two-generator Suzuki coefficient equals the corresponding
coefficient of the exponential of their sum. -/
theorem clause51_series_commuting (X Y : Matrix I I ℂ) (hxy : X * Y = Y * X) (n : ℕ) :
    suzukiSeries [X, Y] n = ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n := by
  have hcomm : Commute X Y := hxy
  rw [clause51_series_two_generators, hcomm.add_pow n, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m ≤ n := by
    have hmem := Finset.mem_range.mp hm
    omega
  rw [clause51_smul_mul_smul, clause51_mul_natCast, smul_smul, clause51_choose_coeff hm']

/-- Every Trotter coefficient deviation vanishes for commuting generators. -/
theorem clause51_deviation_zero_of_commuting (X Y : Matrix I I ℂ) (hxy : X * Y = Y * X) (n : ℕ) :
    trotterDeviation n X Y = 0 := by
  rw [trotterDeviation, clause51_series_commuting X Y hxy n]
  simp

/-- The quartic Trotter deviation vanishes for commuting generators. -/
theorem clause51_quartic_deviation_zero_of_commuting (X Y : Matrix I I ℂ) (hxy : X * Y = Y * X) :
    trotterQuarticDeviation X Y = 0 := by
  rw [trotterQuarticDeviation, clause51_series_commuting X Y hxy 4]
  simp

/-- The quartic Trotter deviation vanishes when `pfComm X Y` is zero. -/
theorem clause51_quartic_deviation_zero_of_pfComm (X Y : Matrix I I ℂ) (h : pfComm X Y = 0) :
    trotterQuarticDeviation X Y = 0 := by
  have hxy : X * Y = Y * X := by
    have hz : X * Y - Y * X = 0 := by
      simpa [pfComm] using! h
    exact sub_eq_zero.mp hz
  exact clause51_quartic_deviation_zero_of_commuting X Y hxy

/-- The quadratic Trotter deviation vanishes exactly when the commutator vanishes. -/
theorem clause51_quadratic_deviation_zero_iff (X Y : Matrix I I ℂ) :
    trotterQuadraticDeviation X Y = 0 ↔ pfComm X Y = 0 := by
  unfold trotterQuadraticDeviation
  rw [clause51_second_order_deviates]
  constructor
  · intro h
    have h' : (1 / 2 : ℝ) • pfComm X Y = 0 := by simpa using! h
    rcases smul_eq_zero.mp h' with h1 | h2
    · norm_num at h1
    · exact h2
  · intro h
    simp [h]

/-- The norm of the quadratic Trotter deviation equals half the commutator norm. -/
theorem clause51_quadratic_deviation_norm (X Y : Matrix I I ℂ) :
    ‖trotterQuadraticDeviation X Y‖ = (1 / 2 : ℝ) * ‖pfComm X Y‖ := by
  rw [trotterQuadraticDeviation, clause51_second_order_deviates, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num)]

/-- The explicit low-degree coefficients, quadratic commutator criterion, and vanishing
deviations for commuting generators hold together. -/
theorem clause51_endpoint : ∀ (n : ℕ) (X Y : Matrix I I ℂ),
    (suzukiSeries [X, Y] 3 = (1 / 6 : ℝ) • Y ^ 3 + X * ((1 / 2 : ℝ) • Y ^ 2) +
      ((1 / 2 : ℝ) • X ^ 2) * Y + (1 / 6 : ℝ) • X ^ 3) ∧
    (suzukiSeries [X] 3 = (1 / 6 : ℝ) • X ^ 3) ∧
    (trotterQuadraticDeviation X Y = 0 ↔ pfComm X Y = 0) ∧
    (‖trotterQuadraticDeviation X Y‖ = (1 / 2 : ℝ) * ‖pfComm X Y‖) ∧
    (trotterCubicDeviation X Y =
      (1 / 3 : ℝ) • (X ^ 2 * Y) + (1 / 3 : ℝ) • (X * Y ^ 2)
        - (1 / 6 : ℝ) • (X * Y * X) - (1 / 6 : ℝ) • (Y * X ^ 2)
        - (1 / 6 : ℝ) • (Y * X * Y) - (1 / 6 : ℝ) • (Y ^ 2 * X)) ∧
    (pfComm X Y = 0 → trotterCubicDeviation X Y = 0) ∧
    (suzukiSeries [X, Y] n = twoGeneratorOrderedWords n X Y) ∧
    (suzukiSeries [X, Y] 4 =
      (1 / 24 : ℝ) • Y ^ 4 + (1 / 6 : ℝ) • (X * Y ^ 3) + (1 / 4 : ℝ) • (X ^ 2 * Y ^ 2)
        + (1 / 6 : ℝ) • (X ^ 3 * Y) + (1 / 24 : ℝ) • X ^ 4) ∧
    (trotterQuarticDeviation X Y =
      (1 / 8 : ℝ) • (X ^ 3 * Y) + (1 / 8 : ℝ) • (X * Y ^ 3) + (5 / 24 : ℝ) • (X ^ 2 * Y ^ 2)
        - (1 / 24 : ℝ) • ((X ^ 2 * Y) * X) - (1 / 24 : ℝ) • ((X * Y) * X ^ 2)
        - (1 / 24 : ℝ) • ((X * Y * X) * Y) - (1 / 24 : ℝ) • ((X * Y ^ 2) * X)
        - (1 / 24 : ℝ) • (Y * X ^ 3) - (1 / 24 : ℝ) • ((Y * X ^ 2) * Y)
        - (1 / 24 : ℝ) • ((Y * X * Y) * X) - (1 / 24 : ℝ) • ((Y * X) * Y ^ 2)
        - (1 / 24 : ℝ) • (Y ^ 2 * X ^ 2) - (1 / 24 : ℝ) • ((Y ^ 2 * X) * Y)
        - (1 / 24 : ℝ) • (Y ^ 3 * X)) ∧
    (X * Y = Y * X → trotterQuarticDeviation X Y = 0) ∧
    (X * Y = Y * X → trotterDeviation n X Y = 0) := by
  intro n X Y
  refine ⟨clause51_series_cubic X Y, clause51_cubic_coefficient_single X,
    clause51_quadratic_deviation_zero_iff X Y, clause51_quadratic_deviation_norm X Y,
    clause51_cubic_deviation_word_form X Y, clause51_cubic_deviation_zero_of_commuting X Y,
    clause51_series_two_generators X Y n, clause51_series_quartic X Y,
    clause51_quartic_deviation_word_form X Y, ?_, ?_⟩
  · intro hxy
    exact clause51_quartic_deviation_zero_of_commuting X Y hxy
  · intro hxy
    exact clause51_deviation_zero_of_commuting X Y hxy n

/-- One support-thickening step adds at most `S.card * occ * d` sites to a bounded finite-range
family. -/
theorem clause52_support_thickening_card_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (hF : FiniteRangeBounded F b d occ) (S : Finset (Fin Λ)) :
    (supportThickening F S).card ≤ S.card + S.card * occ * d := by
  classical
  set T : Finset (Fin Λ) :=
    Finset.univ.filter (fun i => ¬Disjoint (F i).support S) with hT
  have hTcard : T.card ≤ S.card * occ := by
    have hcover : T ⊆ S.biUnion
        (fun s : Fin Λ => Finset.univ.filter (fun i => s ∈ (F i).support)) := by
      intro i hi
      rw [hT, Finset.mem_filter] at hi
      have hne : (F i).support ∩ S ≠ ∅ := by
        intro hcon
        exact hi.2 (Finset.disjoint_iff_inter_eq_empty.mpr hcon)
      obtain ⟨s, hs⟩ := (Finset.nonempty_iff_ne_empty).mpr hne
      rcases Finset.mem_inter.mp hs with ⟨hs, hsi⟩
      rw [Finset.mem_biUnion]
      refine ⟨s, hsi, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hs⟩
    calc T.card ≤ (S.biUnion
          (fun s : Fin Λ => Finset.univ.filter (fun i => s ∈ (F i).support))).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ s ∈ S, (Finset.univ.filter (fun i => s ∈ (F i).support)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S, occ := by
        refine Finset.sum_le_sum fun s _ => ?_
        have hocc := hF.2.2 s
        show (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ
        exact hocc
      _ = S.card * occ := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have hUcard : (T.biUnion (fun i => (F i).support)).card ≤ T.card * d := by
    calc (T.biUnion (fun i => (F i).support)).card ≤
          ∑ i ∈ T, (F i).support.card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ T, d := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hd := hF.2.1 i
        omega
      _ = T.card * d := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have hcard : (supportThickening F S).card ≤ S.card + (T.biUnion (fun i => (F i).support)).card := by
    rw [supportThickening, ← hT]
    exact Finset.card_union_le _ _
  calc (supportThickening F S).card ≤ S.card + (T.biUnion (fun i => (F i).support)).card := hcard
    _ ≤ S.card + T.card * d := by gcongr
    _ ≤ S.card + (S.card * occ) * d := by gcongr
    _ = S.card + S.card * occ * d := by ring

/-- After `r` thickening steps, the light-cone site count is at most `S.card * (1 + occ * d) ^
r`. -/
theorem clause52_light_cone_site_count_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (hF : FiniteRangeBounded F b d occ) (S : Finset (Fin Λ))
    (r : ℕ) :
    (lightConeSites F S r).card ≤ S.card * (1 + occ * d) ^ r := by
  induction r with
  | zero =>
    simp [lightConeSites]
  | succ r ih =>
    have hstep := clause52_support_thickening_card_le F b d occ hF (lightConeSites F S r)
    have hrec : lightConeSites F S (r + 1) = supportThickening F (lightConeSites F S r) := by
      rfl
    rw [hrec]
    calc (supportThickening F (lightConeSites F S r)).card ≤
          (lightConeSites F S r).card + (lightConeSites F S r).card * occ * d := hstep
      _ ≤ (lightConeSites F S r).card * (1 + occ * d) := by ring_nf; exact le_rfl
      _ ≤ S.card * (1 + occ * d) ^ r * (1 + occ * d) := by
        gcongr
      _ = S.card * (1 + occ * d) ^ (r + 1) := by rw [pow_succ]; ring

/-- The one-step support bound and the iterated light-cone site bound hold for bounded
finite-range families. -/
theorem clause52_endpoint : ∀ {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (S : Finset (Fin Λ)),
    FiniteRangeBounded F b d occ →
    ((supportThickening F S).card ≤ S.card + S.card * occ * d) ∧
    (∀ r, (lightConeSites F S r).card ≤ S.card * (1 + occ * d) ^ r) := by
  intro D Λ F b d occ S hF
  exact ⟨clause52_support_thickening_card_le F b d occ hF S, fun r =>
    clause52_light_cone_site_count_le F b d occ hF S r⟩

/-- The torus distance, cast to the reals, is nonnegative. -/
theorem clause53_torus_dist_nonneg {Λ : ℕ} (x y : Fin Λ) : 0 ≤ (torusDist Λ x y : ℝ) := by
  have habs : |((x : ℤ) - (y : ℤ))| ≤ (Λ : ℤ) := by
    have hx : (x : ℤ) = (x.val : ℤ) := by simp
    have hy : (y : ℤ) = (y.val : ℤ) := by simp
    rw [hx, hy]
    have h0 : (0 : ℤ) ≤ (Λ : ℤ) := by omega
    exact (abs_le).2 ⟨by omega, by omega⟩
  have hnonneg : 0 ≤ (Λ : ℤ) - |((x : ℤ) - (y : ℤ))| := by
    omega
  unfold torusDist
  rw [Int.cast_min, le_min_iff]
  constructor
  · rw [Int.cast_abs]
    exact abs_nonneg _
  · exact Int.cast_nonneg hnonneg

/-- The norm of the long-range truncation gap is at most `Λ ^ 2 * C / (1 + R) ^ α` under
`LongRangeFamily`. -/
theorem clause53_gap_le {D Λ : ℕ} (C α : ℝ) (H : Fin Λ → Fin Λ → Operator D)
    (hfam : LongRangeFamily D Λ C α H) (R : ℕ) :
    ‖longRangeGap R H‖ ≤ (Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α := by
  classical
  have hα : 0 < α := hfam.2.1
  have hC : 0 ≤ C := hfam.1
  have hpair' : ∀ x y : Fin Λ, R < torusDist Λ x y →
      ‖H x y - longRangeTruncated D Λ R H x y‖ ≤ C / (1 + (R : ℝ)) ^ α := by
    intro x y h
    have htrunc : longRangeTruncated D Λ R H x y = 0 := by
      rw [longRangeTruncated, if_neg (by omega)]
    rw [htrunc, sub_zero]
    have hfam' := hfam.2.2 x y
    have hdist : (1 + (R : ℝ)) ≤ 1 + (torusDist Λ x y : ℝ) := by
      have hR : (R : ℝ) ≤ (torusDist Λ x y : ℝ) := by
        exact_mod_cast (le_of_lt h)
      linarith
    have hpow : (1 + (R : ℝ)) ^ α ≤ (1 + (torusDist Λ x y : ℝ)) ^ α := by
      exact Real.rpow_le_rpow (by positivity) hdist (by positivity)
    calc ‖H x y‖ ≤ C / (1 + (torusDist Λ x y : ℝ)) ^ α := hfam'
      _ ≤ C / (1 + (R : ℝ)) ^ α := by
        gcongr
  have hsum : ‖longRangeGap R H‖ ≤ ∑ x : Fin Λ, ∑ y : Fin Λ,
      ‖H x y - longRangeTruncated D Λ R H x y‖ := by
    rw [longRangeGap]
    calc ‖∑ x, ∑ y, (H x y - longRangeTruncated D Λ R H x y)‖
        ≤ ∑ x, ‖∑ y, (H x y - longRangeTruncated D Λ R H x y)‖ := norm_sum_le _ _
      _ ≤ ∑ x, ∑ y, ‖H x y - longRangeTruncated D Λ R H x y‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact norm_sum_le _ _
  calc ‖longRangeGap R H‖ ≤ ∑ x : Fin Λ, ∑ y : Fin Λ,
      ‖H x y - longRangeTruncated D Λ R H x y‖ := hsum
    _ ≤ ∑ x : Fin Λ, ∑ y : Fin Λ, C / (1 + (R : ℝ)) ^ α := by
      refine Finset.sum_le_sum fun x _ => ?_
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases h : R < torusDist Λ x y
      · exact hpair' x y h
      · rw [longRangeTruncated, if_pos (by omega), sub_self, norm_zero]
        exact div_nonneg hC (by positivity)
    _ = (Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α := by
      have h1 : (∑ y : Fin Λ, C / (1 + (R : ℝ)) ^ α)
          = (Λ : ℝ) * (C / (1 + (R : ℝ)) ^ α) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
      have h2 : (∑ x : Fin Λ, ∑ y : Fin Λ, C / (1 + (R : ℝ)) ^ α)
          = (Λ : ℝ) * ((Λ : ℝ) * (C / (1 + (R : ℝ)) ^ α)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, h1]
      rw [h2]
      ring

/-- Multiplying the long-range gap bound by `|t|` gives the corresponding time-weighted budget. -/
theorem clause53_corrected_budget {D Λ : ℕ} (C α : ℝ) (H : Fin Λ → Fin Λ → Operator D)
    (hfam : LongRangeFamily D Λ C α H) (R : ℕ) (t : ℝ) :
    |t| * ‖longRangeGap R H‖ ≤ |t| * ((Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α) := by
  have h := clause53_gap_le C α H hfam R
  exact mul_le_mul_of_nonneg_left h (abs_nonneg t)

/-- The long-range truncation gap and its time-weighted budget satisfy the stated decay bounds. -/
theorem clause53_endpoint : ∀ {D Λ : ℕ} (C α : ℝ) (H : Fin Λ → Fin Λ → Operator D)
    (R : ℕ) (t : ℝ), LongRangeFamily D Λ C α H →
    (‖longRangeGap R H‖ ≤ (Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α) ∧
    (|t| * ‖longRangeGap R H‖ ≤ |t| * ((Λ : ℝ) ^ 2 * C / (1 + (R : ℝ)) ^ α)) := by
  intro D Λ C α H R t hfam
  exact ⟨clause53_gap_le C α H hfam R, clause53_corrected_budget C α H hfam R t⟩

/-- The number of cone labels is at most the site occupancy bound times the light-cone site
count. -/
theorem clause54_cone_label_count_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (hF : FiniteRangeBounded F b d occ) (S : Finset (Fin Λ))
    (r : ℕ) :
    (coneLabels F S r).card ≤ occ * (lightConeSites F S r).card := by
  classical
  have hcover : coneLabels F S r ⊆ (lightConeSites F S r).biUnion
      (fun s : Fin Λ => Finset.univ.filter (fun i => s ∈ (F i).support)) := by
    intro i hi
    unfold coneLabels at hi
    rw [Finset.mem_filter] at hi
    have hne : (F i).support ∩ (lightConeSites F S r) ≠ ∅ := by
      intro hcon
      exact hi.2 (Finset.disjoint_iff_inter_eq_empty.mpr hcon)
    obtain ⟨s, hs⟩ := (Finset.nonempty_iff_ne_empty).mpr hne
    rcases Finset.mem_inter.mp hs with ⟨hs, hsi⟩
    rw [Finset.mem_biUnion]
    refine ⟨s, hsi, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hs⟩
  calc (coneLabels F S r).card ≤ ((lightConeSites F S r).biUnion
      (fun s : Fin Λ => Finset.univ.filter (fun i => s ∈ (F i).support))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ s ∈ lightConeSites F S r,
        (Finset.univ.filter (fun i => s ∈ (F i).support)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ s ∈ lightConeSites F S r, occ := by
      refine Finset.sum_le_sum fun s _ => ?_
      have hocc := hF.2.2 s
      show (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ
      exact hocc
    _ = occ * (lightConeSites F S r).card := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]

/-- The cone-label count is controlled by occupancy times the light-cone site count for bounded
finite-range families. -/
theorem clause54_endpoint : ∀ {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (S : Finset (Fin Λ)) (r : ℕ),
    FiniteRangeBounded F b d occ →
    (coneLabels F S r).card ≤ occ * (lightConeSites F S r).card := by
  intro D Λ F b d occ S r hF
  exact clause54_cone_label_count_le F b d occ hF S r

/-- A segment multiplicative defect bounded by `η < 1` gives the inverse norm bound
`inverseStabilityFactor η`. -/
theorem clause55_segment_defect_stability (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ) (r : ℕ) (η : ℝ)
    (hdef : ‖segmentMultiplicativeDefect xs H t r‖ ≤ η) (hη : η < 1) :
    ‖Ring.inverse (1 + segmentMultiplicativeDefect xs H t r)‖ ≤
      inverseStabilityFactor η := by
  exact (inverse_stability_of_norm_le (segmentMultiplicativeDefect xs H t r) η hdef hη).2

/-- Every real `η < 1` satisfies `inversePropagationWindow η`. -/
theorem clause55_inverse_window (η : ℝ) (hη : η < 1) :
    inversePropagationWindow η := by
  exact hη

/-- The inverse-propagation window and inverse norm bound hold when the segment defect is
bounded by `η < 1`. -/
theorem clause55_endpoint : ∀ (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (t : ℝ) (r : ℕ) (η : ℝ),
    (‖segmentMultiplicativeDefect xs H t r‖ ≤ η) → η < 1 →
    (inversePropagationWindow η ∧
      ‖Ring.inverse (1 + segmentMultiplicativeDefect xs H t r)‖ ≤
        inverseStabilityFactor η) := by
  intro xs H t r η hdef hη
  exact ⟨clause55_inverse_window η hη, clause55_segment_defect_stability xs H t r η hdef hη⟩

/-- A positive lower bound `P` for the ideal partition norm bounds the relative partition error
by the additive error norm divided by `P`. -/
theorem clause56_relative_error_le {D : ℕ} (A B : Operator D) (t : ℝ) (r : ℕ)
    (P : ℝ) (hP : 0 < P) (hIdeal : P ≤ ‖tfimIdealPartition A B t‖) :
    tfimRelativePartitionError A B t r ≤
      ‖tfimAdditivePartitionError A B t r‖ / P := by
  unfold tfimRelativePartitionError tfimAdditivePartitionError
  have hne : 0 < ‖tfimIdealPartition A B t‖ := lt_of_lt_of_le hP hIdeal
  gcongr

/-- The selected TFIM segment count is positive. -/
theorem clause56_segment_choice_pos {D : ℕ} (A B : Operator D) (t ε : ℝ) :
    0 < tfimSegmentChoice A B t ε := by
  unfold tfimSegmentChoice nextPow2
  positivity

/-- A positive lower bound on the ideal partition norm yields the stated relative partition
error estimate. -/
theorem clause56_endpoint : ∀ {D : ℕ} (A B : Operator D) (t : ℝ) (r : ℕ) (P : ℝ),
    0 < P → P ≤ ‖tfimIdealPartition A B t‖ →
    tfimRelativePartitionError A B t r ≤
      ‖tfimAdditivePartitionError A B t r‖ / P := by
  intro D A B t r P hP hIdeal
  exact clause56_relative_error_le A B t r P hP hIdeal

/-- The Gibbs density has trace one when its partition function is nonzero. -/
theorem clause57_density_trace_one {D : ℕ} (H : Operator D) (β : ℝ)
    (hZ : gibbsPartition H β ≠ 0) :
    Matrix.trace (gibbsDensity H β) = 1 := by
  unfold gibbsDensity
  rw [Matrix.trace_smul, gibbsPartition]
  simp only [smul_eq_mul]
  exact inv_mul_cancel₀ hZ

/-- The output-norm field of the constructed Gibbs consumption ledger equals `gibbsOutputNorm H
β`. -/
theorem clause57_ledger_charges_output_norm {D : ℕ} (H : Operator D) (β : ℝ)
    (prepCalls amplificationRounds readoutShots : ℕ) :
    (GibbsConsumptionLedger.mk prepCalls amplificationRounds readoutShots
      (gibbsOutputNorm H β)).outputNorm = gibbsOutputNorm H β := rfl

/-- The Gibbs output norm is nonnegative. -/
theorem clause57_output_norm_nonneg {D : ℕ} (H : Operator D) (β : ℝ) :
    0 ≤ gibbsOutputNorm H β := by
  unfold gibbsOutputNorm
  exact norm_nonneg _

/-- A nonzero Gibbs partition function yields a trace-one density and a nonnegative output norm. -/
theorem clause57_endpoint : ∀ {D : ℕ} (H : Operator D) (β : ℝ),
    gibbsPartition H β ≠ 0 →
    (Matrix.trace (gibbsDensity H β) = 1) ∧
    (0 ≤ gibbsOutputNorm H β) := by
  intro D H β hZ
  exact ⟨clause57_density_trace_one H β hZ, clause57_output_norm_nonneg H β⟩

/-- The squared selected time-dependent segment count dominates `L ^ 2 * |t| ^ 3 / (3 * ε)` for
positive tolerance. -/
theorem clause58_segment_choice_dominates (L t ε : ℝ) (hε : 0 < ε) :
    (timeDependentSegments L t ε : ℝ) ^ 2 ≥ L ^ 2 * |t| ^ 3 / (3 * ε) := by
  have hX : 0 ≤ L ^ 2 * |t| ^ 3 / (3 * ε) := by positivity
  have hceil : L ^ 2 * |t| ^ 3 / (3 * ε) ≤
      (Nat.ceil (L ^ 2 * |t| ^ 3 / (3 * ε)) : ℝ) := by
    exact Nat.le_ceil _
  have hmax : (timeDependentSegments L t ε : ℝ) ≥
      (Nat.ceil (L ^ 2 * |t| ^ 3 / (3 * ε)) : ℝ) := by
    unfold timeDependentSegments
    rw [Nat.cast_max]
    exact le_max_right ((1 : ℕ) : ℝ) ((Nat.ceil (L ^ 2 * |t| ^ 3 / (3 * ε)) : ℕ) : ℝ)
  have hr1 : (1 : ℝ) ≤ (timeDependentSegments L t ε : ℝ) := by
    unfold timeDependentSegments
    rw [Nat.cast_max]
    simpa only [Nat.cast_one] using!
      (le_max_left ((1 : ℕ) : ℝ) ((Nat.ceil (L ^ 2 * |t| ^ 3 / (3 * ε)) : ℕ) : ℝ))
  by_cases h : (1 : ℝ) ≤ L ^ 2 * |t| ^ 3 / (3 * ε)
  · nlinarith [hmax]
  · nlinarith [hr1]

/-- The time-dependent error budget evaluated at the selected segment count is at most the
positive tolerance `ε`. -/
theorem clause58_total_error_le (L t ε : ℝ) (hε : 0 < ε) :
    L ^ 2 * |t| ^ 3 / (3 * (timeDependentSegments L t ε : ℝ) ^ 2) ≤ ε := by
  have hdom := clause58_segment_choice_dominates L t ε hε
  have hrpos : 0 < (timeDependentSegments L t ε : ℝ) := by
    unfold timeDependentSegments
    positivity
  have h3r : 0 < 3 * (timeDependentSegments L t ε : ℝ) ^ 2 := by positivity
  have hkey : (L : ℝ) ^ 2 * |t| ^ 3 ≤
      3 * ε * (timeDependentSegments L t ε : ℝ) ^ 2 := by
    have hmul : 3 * ε * (L ^ 2 * |t| ^ 3 / (3 * ε)) = L ^ 2 * |t| ^ 3 := by
      field_simp
    have hge : 3 * ε * (timeDependentSegments L t ε : ℝ) ^ 2 ≥
        3 * ε * (L ^ 2 * |t| ^ 3 / (3 * ε)) := by
      gcongr
    linarith
  rw [div_le_iff₀ h3r]
  linarith

/-- The selected time-dependent segment count satisfies both the required squared-count lower
bound and the error budget. -/
theorem clause58_endpoint : ∀ (L t ε : ℝ), 0 < ε →
    ((timeDependentSegments L t ε : ℝ) ^ 2 ≥ L ^ 2 * |t| ^ 3 / (3 * ε)) ∧
    (L ^ 2 * |t| ^ 3 / (3 * (timeDependentSegments L t ε : ℝ) ^ 2) ≤ ε) := by
  intro L t ε hε
  exact ⟨clause58_segment_choice_dominates L t ε hε, clause58_total_error_le L t ε hε⟩

/-- If numeric and gate synthesis errors are each at most half the tolerance, their total
synthesis error is at most the tolerance. -/
theorem clause59_synthesis_error_le (l : SynthesisLedger) (ε : ℝ)
    (h1 : l.numericError ≤ ε / 2) (h2 : l.gateError ≤ ε / 2) :
    synthesisError l ≤ ε := by
  unfold synthesisError
  linarith

/-- The supplied access-matrix error estimate is retained as the bound by floating-point and
gate errors. -/
theorem clause59_access_error_le {n : ℕ} (s : StrangAccessSynthesis n) (H : Operator (2 ^ n))
    (t : ℝ) (r : ℕ)
    (herror : ‖synthAccessMatrix s - HamiltonianEvolution H (t / (2 * (r : ℝ)))‖ ≤
      s.floatError + s.gateError) :
    ‖synthAccessMatrix s - HamiltonianEvolution H (t / (2 * (r : ℝ)))‖ ≤
      s.floatError + s.gateError := by
  exact herror

/-- The two half-tolerance synthesis bounds imply the full synthesis-error bound. -/
theorem clause59_endpoint : ∀ (l : SynthesisLedger) (ε : ℝ),
    l.numericError ≤ ε / 2 → l.gateError ≤ ε / 2 → synthesisError l ≤ ε := by
  intro l ε h1 h2
  exact clause59_synthesis_error_le l ε h1 h2

/-- A matrix of norm at most one has real-scaled norm at most the absolute value of the scalar. -/
theorem clause60_normalisation_bound (n : ℝ) (M : Matrix I I ℂ) (hM : ‖M‖ ≤ 1) :
    ‖n • M‖ ≤ |n| := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg n) hM

/-- For continuous coefficient and forcing fields, the forced solution factors into homogeneous
ordered evolution and an integral of the transported forcing. -/
theorem clause60_forced_factor {D : ℕ} (Lfield Hfield : ℝ → Matrix (Fin D) (Fin D) ℂ)
    (b : ℝ → QState (Fin D)) (T : ℝ) (v : QState (Fin D))
    (hL : Continuous Lfield) (hH : Continuous Hfield) (hb : Continuous b) :
    orderedForcedSolution (lchsForcedGenerator Lfield Hfield) b 0 v T =
      orderedEvolution (lchsForcedGenerator Lfield Hfield) 0 T *ᵥ
        (v + ∫ u in 0..T,
          orderedEvolution (lchsForcedGenerator Lfield Hfield) u 0 *ᵥ b u) := by
  exact lchs_forced_duhamel Lfield Hfield b T v hL hH hb

/-- Real scaling of a matrix of norm at most one is bounded by the absolute scale. -/
theorem clause60_endpoint : ∀ (n : ℝ) (M : Matrix I I ℂ), ‖M‖ ≤ 1 → ‖n • M‖ ≤ |n| := by
  intro n M hM
  exact clause60_normalisation_bound n M hM

/-- If Trotter and synthesis errors are each at most half the tolerance, the ferromagnetic
relative error is at most the tolerance. -/
theorem clause61_relative_error_le (l : FerroLedger) (ε : ℝ)
    (h1 : l.trotterError ≤ ε / 2) (h2 : l.synthesisError ≤ ε / 2) :
    ferroRelativeError l ≤ ε := by
  unfold ferroRelativeError
  linarith

/-- The ferromagnetic relative error equals the sum of its Trotter and synthesis contributions. -/
theorem clause61_relative_error_eq (l : FerroLedger) :
    ferroRelativeError l = l.trotterError + l.synthesisError := rfl

/-- The two half-tolerance bounds imply the ferromagnetic relative-error bound. -/
theorem clause61_endpoint : ∀ (l : FerroLedger) (ε : ℝ),
    l.trotterError ≤ ε / 2 → l.synthesisError ≤ ε / 2 → ferroRelativeError l ≤ ε := by
  intro l ε h1 h2
  exact clause61_relative_error_le l ε h1 h2

/-- Support conflict is symmetric. -/
theorem clause52Conflict_comm {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i j : Fin Λ) :
    clause52Conflict F i j ↔ clause52Conflict F j i := by
  unfold clause52Conflict
  exact not_congr (disjoint_comm)

/-- Two local terms conflict exactly when their support intersection is nonempty. -/
theorem clause52Conflict_iff_nonempty {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i j : Fin Λ) :
    clause52Conflict F i j ↔ ((F i).support ∩ (F j).support).Nonempty := by
  classical
  unfold clause52Conflict
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.nonempty_iff_ne_empty]

/-- The least unused natural number does not belong to the used set. -/
theorem clause52LeastFree_spec (used : Finset ℕ) : clause52LeastFree used ∉ used :=
  Nat.find_spec (clause52FreeExists used)

/-- The least unused natural number is at most the cardinality of the used set. -/
theorem clause52LeastFree_le_card (used : Finset ℕ) : clause52LeastFree used ≤ used.card := by
  have hsub : Finset.range (clause52LeastFree used) ⊆ used := by
    intro c hc
    exact of_not_not (Nat.find_min (clause52FreeExists used) (Finset.mem_range.mp hc))
  have h2 := Finset.card_le_card hsub
  simpa using! h2

/-- The first-fit layer is absent from the layers already used by conflicting terms. -/
theorem clause52FirstFit_fresh {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ)
    (a : Fin Λ → Option ℕ) :
    clause52FirstFit F i a ∉ clause52UsedLayers F i a := by
  exact clause52LeastFree_spec _

/-- The assigned color of any distinct conflicting term belongs to the used-layer set. -/
theorem clause52UsedLayers_mem {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ)
    (a : Fin Λ → Option ℕ) (k : Fin Λ) (ck : ℕ) (hk : a k = some ck) (hne : k ≠ i)
    (hconf : clause52Conflict F i k) : ck ∈ clause52UsedLayers F i a := by
  refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne, hconf, ?_⟩
    simp [hk]
  · simp [hk]

/-- The number of used layers is at most the number of distinct conflicting terms. -/
theorem clause52UsedLayers_card_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ)
    (a : Fin Λ → Option ℕ) :
    (clause52UsedLayers F i a).card ≤
      (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j)).card := by
  refine Nat.le_trans Finset.card_image_le ?_
  refine Finset.card_le_card ?_
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ j, ⟨hj.2.1, hj.2.2.1⟩⟩

/-- Updating one term with a color different from all assigned conflicting terms preserves
properness. -/
theorem clause52Proper_update {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) (hk : k < Λ)
    (a : Fin Λ → Option ℕ) (c : ℕ) (hproper : clause52Proper F a)
    (hfresh : ∀ (m : Fin Λ) (cm : ℕ), a m = some cm → m.val ≠ k →
      clause52Conflict F ⟨k, hk⟩ m → cm ≠ c) :
    clause52Proper F (fun j => if j.val = k then some c else a j) := by
  intro j m ci cm hj hm hjm hconf
  by_cases hj' : j.val = k
  · simp only [if_pos hj'] at hj
    have hcj : c = ci := by simpa using! hj
    have hj_eq : j = ⟨k, hk⟩ := Fin.ext hj'
    by_cases hm' : m.val = k
    · simp only [if_pos hm'] at hm
      exact fun _ => hjm (Fin.ext (by omega))
    · simp only [if_neg hm'] at hm
      have hne : m.val ≠ k := hm'
      rw [hj_eq] at hconf
      have hconf' : clause52Conflict F ⟨k, hk⟩ m := hconf
      have hne' : cm ≠ c := hfresh m cm hm hne hconf'
      rw [← hcj]
      exact fun h => hne' h.symm
  · simp only [if_neg hj'] at hj
    by_cases hm' : m.val = k
    · simp only [if_pos hm'] at hm
      have hcm : c = cm := by simpa using! hm
      have hne : j.val ≠ k := hj'
      have hm_eq : m = ⟨k, hk⟩ := Fin.ext hm'
      rw [hm_eq] at hconf
      have hconf' : clause52Conflict F ⟨k, hk⟩ j := (clause52Conflict_comm F j ⟨k, hk⟩).mp hconf
      have hne' : ci ≠ c := hfresh j ci hj hne hconf'
      rw [← hcm]
      exact hne'
    · simp only [if_neg hm'] at hm
      exact hproper j m ci cm hj hm hjm hconf

/-- Coloring the first `k` terms preserves a proper partial coloring. -/
theorem clause52ColourUpTo_proper {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    ∀ (k : ℕ) (hk : k ≤ Λ) (a : Fin Λ → Option ℕ),
      clause52Proper F a → clause52Proper F (clause52ColourUpTo F k hk a) := by
  intro k
  induction k with
  | zero =>
      intro hk a h
      simpa [clause52ColourUpTo] using! h
  | succ k ih =>
      intro hk a hproper
      have hs : clause52Proper F (clause52ColourUpTo F k (by omega) a) := ih _ _ hproper
      have hfresh : ∀ (m : Fin Λ) (cm : ℕ),
          (clause52ColourUpTo F k (by omega) a) m = some cm → m.val ≠ k →
            clause52Conflict F ⟨k, by omega⟩ m → cm ≠ clause52FirstFit F ⟨k, by omega⟩
              (clause52ColourUpTo F k (by omega) a) := by
        intro m cm hm hne hconf
        have hmem : cm ∈ clause52UsedLayers F ⟨k, by omega⟩ (clause52ColourUpTo F k (by omega) a) := by
          refine clause52UsedLayers_mem F ⟨k,
              by omega⟩ (clause52ColourUpTo F k (by omega) a) m cm hm ?_ ?_
          · intro hcon
            apply hne
            exact congrArg Fin.val hcon
          · exact hconf
        intro heq
        rw [heq] at hmem
        exact (clause52FirstFit_fresh F ⟨k, by omega⟩ (clause52ColourUpTo F k (by omega) a)) hmem
      have hnew := clause52Proper_update F k (by omega) (clause52ColourUpTo F k (by omega) a)
        (clause52FirstFit F ⟨k, by omega⟩ (clause52ColourUpTo F k (by omega) a)) hs hfresh
      simpa [clause52ColourUpTo] using! hnew

/-- After coloring the first `k` terms, every term below `k` has an assigned color. -/
theorem clause52ColourUpTo_some {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    ∀ (k : ℕ) (hk : k ≤ Λ) (a : Fin Λ → Option ℕ) (i : Fin Λ), i.val < k →
      ∃ c, (clause52ColourUpTo F k hk a) i = some c := by
  intro k
  induction k with
  | zero =>
      intro hk a i hi
      simp at hi
  | succ k ih =>
      intro hk a i hi
      by_cases hik : i.val = k
      · simp only [clause52ColourUpTo]
        rw [if_pos hik]
        exact ⟨clause52FirstFit F ⟨k, by omega⟩ (clause52ColourUpTo F k (by omega) a), rfl⟩
      · simp only [clause52ColourUpTo]
        rw [if_neg hik]
        exact ih _ _ i (by omega)

/-- The complete coloring assigns a color to every term. -/
theorem clause52Colouring_some {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    ∃ c, clause52Colouring F i = some c := by
  have h := clause52ColourUpTo_some F Λ (by omega) (fun _ => none) i (by omega)
  simpa [clause52Colouring] using! h

/-- The color assigned below `k` is the first-fit color computed after coloring the preceding
terms. -/
theorem clause52ColourUpTo_layer {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    ∀ (k : ℕ) (hk : k ≤ Λ) (a : Fin Λ → Option ℕ) (i : Fin Λ), i.val < k →
      (clause52ColourUpTo F k hk a) i
        = some (clause52FirstFit F i (clause52ColourUpTo F i.val (by omega) a)) := by
  intro k
  induction k with
  | zero =>
      intro hk a i hi
      simp at hi
  | succ k ih =>
      intro hk a i hi
      by_cases hik : i.val = k
      · have hi_eq : i = ⟨k, by omega⟩ := Fin.ext hik
        simp only [clause52ColourUpTo]
        rw [if_pos hik, hi_eq]
      · simp only [clause52ColourUpTo]
        rw [if_neg hik]
        exact ih _ _ i (by omega)

/-- The selected layer of a term equals its first-fit color after processing earlier terms. -/
theorem clause52Layer_eq_firstFit {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    clause52Layer F i = clause52FirstFit F i (clause52ColourUpTo F i.val (by omega) (fun _ => none)) := by
  have h := clause52ColourUpTo_layer F Λ (by omega) (fun _ => none) i (by omega)
  rw [clause52Layer, clause52Colouring]
  rw [h]
  simp

/-- The selected layer of a term is at most its conflict degree. -/
theorem clause52Layer_le_overlap {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (i : Fin Λ) :
    clause52Layer F i ≤ clause52ConflictDegree F i := by
  rw [clause52Layer_eq_firstFit]
  calc clause52FirstFit F i _ = clause52LeastFree (clause52UsedLayers F i _) := rfl
    _ ≤ (clause52UsedLayers F i _).card := clause52LeastFree_le_card _
    _ ≤ (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j)).card :=
        clause52UsedLayers_card_le F i _
    _ = clause52ConflictDegree F i := rfl

/-- The complete first-fit coloring is proper. -/
theorem clause52Colouring_proper {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) :
    clause52Proper F (clause52Colouring F) := by
  have h := clause52ColourUpTo_proper F Λ (by omega) (fun _ : Fin Λ => none)
    (fun i j ci cj hj hk hjk hconf => absurd hj (by simp))
  simpa [clause52Colouring] using! h

/-- If all selected layers are below `L`, the flattened schedule contains every term. -/
theorem clause52Schedule_covers {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (L : ℕ)
    (hL : ∀ i, clause52Layer F i < L) (i : Fin Λ) :
    i ∈ (clause52Schedule F L).flatten := by
  refine List.mem_flatten.mpr
    ⟨(List.finRange Λ).filter (fun j => clause52Layer F j = clause52Layer F i), ?_, ?_⟩
  · simp only [clause52Schedule, List.mem_map, List.mem_range]
    exact ⟨clause52Layer F i, hL i, rfl⟩
  · simp only [List.mem_filter]
    exact ⟨List.mem_finRange i, rfl⟩

/-- Distinct terms in a common scheduled layer have disjoint supports. -/
theorem clause52Schedule_layer_disjoint {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (L : ℕ)
    (l : List (Fin Λ)) (hl : l ∈ clause52Schedule F L) (i j : Fin Λ) (hi : i ∈ l) (hj : j ∈ l)
    (hne : i ≠ j) : Disjoint (F i).support (F j).support := by
  obtain ⟨c, hc, hcl⟩ := List.mem_map.mp hl
  have hci : clause52Layer F i = c := by
    have h1 : i ∈ (List.finRange Λ).filter (fun j => clause52Layer F j = c) := by
      rw [hcl]
      exact hi
    exact of_decide_eq_true (List.mem_filter.mp h1).2
  have hcj : clause52Layer F j = c := by
    have h1 : j ∈ (List.finRange Λ).filter (fun j => clause52Layer F j = c) := by
      rw [hcl]
      exact hj
    exact of_decide_eq_true (List.mem_filter.mp h1).2
  obtain ⟨ci, hci'⟩ := clause52Colouring_some F i
  obtain ⟨cj, hcj'⟩ := clause52Colouring_some F j
  have hli : clause52Layer F i = ci := by simp [clause52Layer, hci']
  have hlj : clause52Layer F j = cj := by simp [clause52Layer, hcj']
  have hconf : ¬ clause52Conflict F i j := by
    intro hc
    have hne' := clause52Colouring_proper F i j ci cj hci' hcj' hne hc
    have hcc : ci = cj := by
      calc ci = clause52Layer F i := hli.symm
        _ = c := hci
        _ = clause52Layer F j := hcj.symm
        _ = cj := hlj
    exact hne' hcc
  exact not_not.mp hconf

/-- The selected layers define a parallel schedule whenever they are all below `L`. -/
theorem clause52_isParallelSchedule {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (L : ℕ)
    (hL : ∀ i, clause52Layer F i < L) :
    IsParallelSchedule (fun i => (F i).support) (fun i => ⟨clause52Layer F i, hL i⟩) := by
  intro i j hij
  by_cases hne : i = j
  · exact Or.inl hne
  · right
    obtain ⟨ci, hci'⟩ := clause52Colouring_some F i
    obtain ⟨cj, hcj'⟩ := clause52Colouring_some F j
    have hli : clause52Layer F i = ci := by simp [clause52Layer, hci']
    have hlj : clause52Layer F j = cj := by simp [clause52Layer, hcj']
    have hconf : ¬ clause52Conflict F i j := by
      intro hc
      have hne' := clause52Colouring_proper F i j ci cj hci' hcj' hne hc
      exact hne' (calc ci = clause52Layer F i := hli.symm
        _ = clause52Layer F j := congrArg Fin.val hij
        _ = cj := hlj)
    exact not_not.mp hconf

/-- The conflict degree is at most the support size times `occ - 1` under the site occupancy
bound. -/
theorem clause52ConflictDegree_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (occ : ℕ)
    (hocc : ∀ s : Fin Λ, (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ)
    (i : Fin Λ) :
    clause52ConflictDegree F i ≤ (F i).support.card * (occ - 1) := by
  classical
  have hcover : (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j))
      ⊆ (F i).support.biUnion (fun s : Fin Λ =>
        Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ s ∈ (F j).support)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨-, ⟨hne, hconf⟩⟩ := hj
    have hex : ∃ s, s ∈ (F i).support ∧ s ∈ (F j).support := by
      by_contra hcon
      have hd : Disjoint (F i).support (F j).support :=
        Finset.disjoint_left.mpr (fun a ha hb => hcon ⟨a, ha, hb⟩)
      exact hconf hd
    obtain ⟨s, hmem⟩ := hex
    obtain ⟨hs, hs'⟩ := hmem
    exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne, hs'⟩⟩
  calc (clause52ConflictDegree F i)
      = (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ clause52Conflict F i j)).card := rfl
    _ ≤ ((F i).support.biUnion (fun s : Fin Λ =>
        Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ s ∈ (F j).support))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ s ∈ (F i).support,
        (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ s ∈ (F j).support)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ s ∈ (F i).support, (occ - 1) := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hsi : s ∈ (F i).support := hs
      have hmem : i ∈ Finset.univ.filter (fun j : Fin Λ => s ∈ (F j).support) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsi⟩
      have hsub : (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ s ∈ (F j).support))
          ⊆ (Finset.univ.filter (fun j : Fin Λ => s ∈ (F j).support)).erase i := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_erase]
        exact ⟨hj.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.2.2⟩⟩
      calc (Finset.univ.filter (fun j : Fin Λ => j ≠ i ∧ s ∈ (F j).support)).card
          ≤ ((Finset.univ.filter (fun j : Fin Λ => s ∈ (F j).support)).erase i).card :=
            Finset.card_le_card hsub
        _ = (Finset.univ.filter (fun j : Fin Λ => s ∈ (F j).support)).card - 1 :=
          Finset.card_erase_of_mem hmem
        _ ≤ occ - 1 := by
          have := hocc s
          omega
    _ = (F i).support.card * (occ - 1) := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]

/-- Support size at most `d` and site occupancy at most `occ` bound every selected layer by `d *
(occ - 1)`. -/
theorem clause52Layer_le_occupancy {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (d occ : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d)
    (hocc : ∀ s : Fin Λ, (Finset.univ.filter (fun i => s ∈ (F i).support)).card ≤ occ)
    (i : Fin Λ) :
    clause52Layer F i ≤ d * (occ - 1) := by
  have h1 := clause52Layer_le_overlap F i
  have h2 := clause52ConflictDegree_le F occ hocc i
  calc clause52Layer F i ≤ clause52ConflictDegree F i := h1
    _ ≤ (F i).support.card * (occ - 1) := h2
    _ ≤ d * (occ - 1) := Nat.mul_le_mul_right _ (hsupp i)

/-- The bounded layer assignment gives a parallel schedule for a bounded finite-range family. -/
theorem clause52_parallel_schedule_endpoint : ∀ {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (hlayer : ∀ i, clause52Layer F i ≤ d * (occ - 1)),
    FiniteRangeBounded F b d occ →
    IsParallelSchedule (fun i => (F i).support) (clause52LayerFin F d occ hlayer) := by
  intro D Λ F b d occ hlayer hF
  have hlayer' : ∀ i, clause52Layer F i ≤ d * (occ - 1) :=
    fun i => clause52Layer_le_occupancy F d occ (fun i => hF.2.1 i) (fun s => hF.2.2 s) i
  exact clause52_isParallelSchedule F (d * (occ - 1) + 1) (by
    intro i
    have h := hlayer' i
    omega)

/-- The recursive Suzuki macro word has `2 * Λ * 5 ^ k` gates. -/
theorem clause52MacroGates_eq {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    clause52MacroGates F k = 2 * Λ * 5^k := by
  unfold clause52MacroGates clause52MacroWord clause52FamilyWord
  calc (recursiveSuzukiGenerators ((List.finRange Λ).map (fun i => (F i).op)) k).length
      = 2 * ((List.finRange Λ).map (fun i => (F i).op)).length * 5^k :=
        (recursive_suzuki_length_and_mass (Fin D) ((List.finRange Λ).map (fun i => (F i).op)) k).1
    _ = 2 * Λ * 5^k := by simp

/-- The total macro gate count over all segments is `segments * 2 * Λ * 5 ^ k`. -/
theorem clause52MacroTotalGates_eq {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k segments : ℕ) :
    clause52MacroTotalGates F k segments = segments * 2 * Λ * 5^k := by
  unfold clause52MacroTotalGates
  rw [clause52MacroGates_eq]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Multiplication of real scale factors agrees with successive scalar actions on an operator. -/
private theorem clause52_smul_mul_smul_comm {D : ℕ} (a m : ℝ) (X : Operator D) :
    (m * a) • X = m • (a • X) := by
  simp only [Algebra.smul_def]
  rw [map_mul, mul_assoc]

/-- Mapping each element within nested lists commutes with flattening. -/
private theorem clause52_flatten_map_map {α β : Type} (l : List (List α)) (g : α → β) :
    (l.map (fun s => s.map g)).flatten = l.flatten.map g := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append]
      rw [ih]

/-- Mapping within each generated list and then flattening equals mapping after flattening the
generated lists. -/
private theorem clause52_flatten_map_map' {α β γ : Type} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.map (fun s => (f s).map g)).flatten = (l.map f).flatten.map g := by
  induction l with
  | nil => rfl
  | cons s l ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append]
      rw [ih]

/-- Flattening distributes over list append. -/
private theorem clause52_flatten_append {α : Type} (l₁ l₂ : List (List α)) :
    (l₁ ++ l₂).flatten = l₁.flatten ++ l₂.flatten := by
  induction l₁ with
  | nil => rfl
  | cons s l ih =>
      simp only [List.cons_append, List.flatten_cons]
      rw [ih]
      simp only [List.append_assoc]

/-- Mapping, reversing, and mapping again equals reversing and mapping the composite function. -/
private theorem clause52_reverse_map {α β γ : Type} (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).reverse.map g = l.reverse.map (fun i => g (f i)) := by
  rw [← List.map_reverse, List.map_map]
  rfl

/-- The next recursive Suzuki word consists of five scaled copies of the preceding word, with
the middle scale `1 - 4 * recursiveSuzukiScale k`. -/
private theorem clause52_suzuki_five_copies {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) :
    recursiveSuzukiGenerators hs (k + 1) =
      (recursiveSuzukiGenerators hs k).map (fun X => recursiveSuzukiScale k • X) ++
      (recursiveSuzukiGenerators hs k).map (fun X => recursiveSuzukiScale k • X) ++
      (recursiveSuzukiGenerators hs k).map
        (fun X => (1 - 4 * recursiveSuzukiScale k) • X) ++
      (recursiveSuzukiGenerators hs k).map (fun X => recursiveSuzukiScale k • X) ++
      (recursiveSuzukiGenerators hs k).map (fun X => recursiveSuzukiScale k • X) := by
  simp only [recursiveSuzukiGenerators]

/-- The macro stage count is `2 * 5 ^ k`. -/
theorem clause52StageCount_eq (k : ℕ) : clause52StageCount k = 2 * 5^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [clause52StageCount, ih, pow_succ]
      ring

/-- The macro stage list has length `clause52StageCount k`. -/
theorem clause52MacroStageList_length {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    (clause52MacroStageList F k).length = clause52StageCount k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [clause52MacroStageList, clause52StageCount, List.length_append, List.length_map,
        ih]
      omega

/-- Every scaled macro stage has the same term list as some original stage. -/
private theorem clause52_stage_of_map {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ)
    (m : ℝ) (st : ℝ × List (Fin Λ))
    (hst : st ∈ (clause52MacroStageList F k).map (clause52ScaleStage m)) :
    ∃ s : ℝ × List (Fin Λ), s ∈ clause52MacroStageList F k ∧ st.2 = s.2 := by
  obtain ⟨s, hs, hfst⟩ := List.mem_map.mp hst
  exact ⟨s, hs, (congrArg Prod.snd hfst).symm⟩

/-- Every stage at recursion level `k + 1` has the same term list as some stage at level `k`. -/
private theorem clause52_stage_mem_succ {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ)
    (st : ℝ × List (Fin Λ)) (hst : st ∈ clause52MacroStageList F (k + 1)) :
    ∃ s : ℝ × List (Fin Λ), s ∈ clause52MacroStageList F k ∧ st.2 = s.2 := by
  rw [clause52MacroStageList] at hst
  rcases List.mem_append.mp hst with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · rcases List.mem_append.mp h2 with h3 | h3
      · rcases List.mem_append.mp h3 with h4 | h4
        · exact clause52_stage_of_map F k _ st h4
        · exact clause52_stage_of_map F k _ st h4
      · exact clause52_stage_of_map F k _ st h3
    · exact clause52_stage_of_map F k _ st h2
  · exact clause52_stage_of_map F k _ st h1

/-- Each macro stage lists every family term exactly once and has length `Λ`. -/
theorem clause52MacroStageTerms {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ)
    (st : ℝ × List (Fin Λ)) (hst : st ∈ clause52MacroStageList F k) :
    st.2.length = Λ ∧ (∀ i : Fin Λ, i ∈ st.2) ∧ st.2.Nodup := by
  induction k generalizing st with
  | zero =>
      have hst' : st = (1 / 2, (List.finRange Λ))
          ∨ st = (1 / 2, (List.finRange Λ).reverse) := by
        simpa only [clause52MacroStageList, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] using! hst
      rcases hst' with h | h
      · rw [h]
        exact ⟨List.length_finRange, fun i => List.mem_finRange i,
          List.nodup_finRange Λ⟩
      · rw [h]
        refine ⟨List.length_reverse.trans List.length_finRange,
          fun i => List.mem_reverse.mpr (List.mem_finRange i), ?_⟩
        exact List.nodup_reverse.mpr (List.nodup_finRange Λ)
  | succ k ih =>
      obtain ⟨s, hs, hterm⟩ := clause52_stage_mem_succ F k st hst
      obtain ⟨hlen, hmem, hnodup⟩ := ih s hs
      exact ⟨by rw [hterm]; exact hlen, by rw [hterm]; exact hmem,
        by rw [hterm]; exact hnodup⟩

/-- Scaling all macro stages scales every operator in the flattened stage words. -/
private theorem clause52_stage_flatten_scale {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (k : ℕ) (m : ℝ) :
    ((List.map (clause52ScaleStage m) (clause52MacroStageList F k)).map (clause52StageWord F)).flatten
      = (clause52MacroStageWords F k).flatten.map (fun X => m • X) := by
  have hinner :
      (List.map (clause52ScaleStage m) (clause52MacroStageList F k)).map (clause52StageWord F)
        = (clause52MacroStageList F k).map
          (fun st => (clause52StageWord F st).map (fun X => m • X)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro st _
    simp only [Function.comp_apply, clause52ScaleStage, clause52StageWord, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact clause52_smul_mul_smul_comm st.1 m (F i).op
  rw [hinner]
  exact clause52_flatten_map_map' (clause52MacroStageList F k) (clause52StageWord F)
      (fun X => m • X)

/-- The macro word is the flattening of the macro stage words. -/
theorem clause52MacroWord_eq_stages {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    clause52MacroWord F k = (clause52MacroStageWords F k).flatten := by
  induction k with
  | zero =>
      have h1 : clause52MacroWord F 0
          = (clause52FamilyWord F).map (fun X => (1 / 2 : ℝ) • X)
            ++ (clause52FamilyWord F).reverse.map (fun X => (1 / 2 : ℝ) • X) := by
        rw [clause52MacroWord, clause52FamilyWord, recursiveSuzukiGenerators]
      have h2 : (clause52MacroStageWords F 0).flatten
          = (clause52FamilyWord F).map (fun X => (1 / 2 : ℝ) • X)
            ++ (clause52FamilyWord F).reverse.map (fun X => (1 / 2 : ℝ) • X) := by
        simp only [clause52MacroStageWords, clause52MacroStageList, clause52StageWord, clause52FamilyWord,
          List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.map_map, Function.comp_def]
        rw [clause52_reverse_map]
      rw [h1, h2]
  | succ k ih =>
      have hrec : recursiveSuzukiGenerators (clause52FamilyWord F) k
          = (clause52MacroStageWords F k).flatten := ih
      have hstage : (clause52MacroStageList F (k + 1))
          = (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k))
            ++ (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k))
            ++ (clause52MacroStageList F k).map
                (clause52ScaleStage (1 - 4 * recursiveSuzukiScale k))
            ++ (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k))
            ++ (clause52MacroStageList F k).map (clause52ScaleStage (recursiveSuzukiScale k)) := by
        rw [clause52MacroStageList]
      have hflat : (clause52MacroStageWords F (k + 1)).flatten
          = (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X)
            ++ (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X)
            ++ (clause52MacroStageWords F k).flatten.map
                (fun X => (1 - 4 * recursiveSuzukiScale k) • X)
            ++ (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X)
            ++ (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X) := by
        rw [clause52MacroStageWords, hstage]
        simp only [List.map_append]
        rw [clause52_flatten_append, clause52_flatten_append, clause52_flatten_append,
          clause52_flatten_append]
        simp only [List.append_assoc]
        rw [clause52_stage_flatten_scale F k (recursiveSuzukiScale k),
          clause52_stage_flatten_scale F k (1 - 4 * recursiveSuzukiScale k)]
      calc
        clause52MacroWord F (k + 1)
            = (recursiveSuzukiGenerators (clause52FamilyWord F) k).map
                (fun X => recursiveSuzukiScale k • X)
              ++ (recursiveSuzukiGenerators (clause52FamilyWord F) k).map
                (fun X => recursiveSuzukiScale k • X)
              ++ (recursiveSuzukiGenerators (clause52FamilyWord F) k).map
                (fun X => (1 - 4 * recursiveSuzukiScale k) • X)
              ++ (recursiveSuzukiGenerators (clause52FamilyWord F) k).map
                (fun X => recursiveSuzukiScale k • X)
              ++ (recursiveSuzukiGenerators (clause52FamilyWord F) k).map
                (fun X => recursiveSuzukiScale k • X) := by
              rw [clause52MacroWord]
              exact clause52_suzuki_five_copies (clause52FamilyWord F) k
        _ = (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X)
              ++ (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X)
              ++ (clause52MacroStageWords F k).flatten.map
                (fun X => (1 - 4 * recursiveSuzukiScale k) • X)
              ++ (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X)
              ++ (clause52MacroStageWords F k).flatten.map
                (fun X => recursiveSuzukiScale k • X) := by
              rw [hrec]
        _ = (clause52MacroStageWords F (k + 1)).flatten := hflat.symm

/-- The macro gate count equals the number of terms times the stage count. -/
theorem clause52MacroGates_eq_stages {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    clause52MacroGates F k = Λ * clause52StageCount k := by
  rw [clause52MacroGates_eq, clause52StageCount_eq]
  ring

/-- The macro depth is the stage count times the number of parallel layers. -/
theorem clause52MacroDepth_eq (k L : ℕ) : clause52MacroDepth k L = clause52StageCount k * L := rfl

/-- Using `d * (occ - 1) + 1` layers gives depth `2 * 5 ^ k * (d * (occ - 1) + 1)`. -/
theorem clause52MacroDepth_occupancy (k d occ : ℕ) :
    clause52MacroDepth k (d * (occ - 1) + 1) = 2 * 5^k * (d * (occ - 1) + 1) := by
  rw [clause52MacroDepth_eq, clause52StageCount_eq]

/-- The routing-swap count for each term is at most `d - 1` when all supports have size at most
`d`. -/
theorem clause52TermRouteSwaps_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (d : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d) (i : Fin Λ) :
    clause52TermRouteSwaps F i ≤ d - 1 := by
  unfold clause52TermRouteSwaps
  have h := hsupp i
  omega

/-- The routing-swap count of a layer is at most its length times `d - 1` under the support-size
bound. -/
theorem clause52LayerRouteSwaps_le {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (d : ℕ)
    (hsupp : ∀ i, (F i).support.card ≤ d) (l : List (Fin Λ)) :
    clause52LayerRouteSwaps F l ≤ l.length * (d - 1) := by
  unfold clause52LayerRouteSwaps
  calc
    Finset.sum l.toFinset (fun i => clause52TermRouteSwaps F i)
        ≤ Finset.sum l.toFinset (fun _ => d - 1) := by
          refine Finset.sum_le_sum fun i _hi => ?_
          exact clause52TermRouteSwaps_le F d hsupp i
    _ = l.toFinset.card * (d - 1) := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ l.length * (d - 1) := by
          exact Nat.mul_le_mul_right _ (List.toFinset_card_le l)

/-- The routing-swap count of each macro stage equals the family routing-swap count. -/
theorem clause52StageRouteSwaps_eq {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ)
    (st : ℝ × List (Fin Λ)) (hst : st ∈ clause52MacroStageList F k) :
    clause52LayerRouteSwaps F st.2 = clause52FamilyRouteSwaps F := by
  have h := clause52MacroStageTerms F k st hst
  have hset : st.2.toFinset = (Finset.univ : Finset (Fin Λ)) := by
    apply Finset.ext
    intro i
    constructor
    · intro _
      exact Finset.mem_univ i
    · intro _
      exact List.mem_toFinset.mpr (h.2.1 i)
  unfold clause52LayerRouteSwaps clause52FamilyRouteSwaps
  rw [hset]

/-- The macro routing-swap count equals the stage count times the family routing-swap count. -/
theorem clause52MacroRouteSwaps_eq {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    clause52MacroRouteSwaps F k = clause52StageCount k * clause52FamilyRouteSwaps F := rfl

/-- The macro routing-swap count is `2 * 5 ^ k` times the sum of support sizes minus one, with
natural subtraction. -/
theorem clause52MacroRouteSwaps_levels {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ) (k : ℕ) :
    clause52MacroRouteSwaps F k = 2 * 5^k * (∑ i : Fin Λ, ((F i).support.card - 1)) := by
  rw [clause52MacroRouteSwaps_eq, clause52StageCount_eq]
  rfl

/-- The macro routing-swap formula is independent of the layer count, while macro depth scales
linearly with that count. -/
theorem clause52MacroRouteSwaps_schedule_independent {D Λ : ℕ}
    (F : Fin Λ → LocalTerm D Λ) (k L : ℕ) :
    clause52MacroRouteSwaps F k = clause52StageCount k * clause52FamilyRouteSwaps F ∧
      clause52MacroDepth k L = clause52StageCount k * L ∧
      clause52MacroDepth k L = clause52MacroDepth k 1 * L := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [clause52MacroDepth_eq]
  ring

/-- The finite-range macro construction satisfies the stated stage, word, depth, gate-count, and
routing-swap identities. -/
theorem clause52_parallel_depth_endpoint : ∀ {D Λ : ℕ} (F : Fin Λ → LocalTerm D Λ)
    (b d occ : ℕ) (k : ℕ),
    FiniteRangeBounded F b d occ →
    (clause52MacroStageList F k).length = 2 * 5^k ∧
    (∀ st ∈ clause52MacroStageList F k, st.2.length = Λ ∧ (∀ i : Fin Λ, i ∈ st.2)) ∧
    clause52MacroWord F k = (clause52MacroStageWords F k).flatten ∧
    clause52MacroDepth k (d * (occ - 1) + 1) = 2 * 5^k * (d * (occ - 1) + 1) ∧
    clause52MacroGates F k = 2 * Λ * 5^k ∧
    clause52MacroRouteSwaps F k = 2 * 5^k * (∑ i : Fin Λ, ((F i).support.card - 1)) := by
  intro D Λ F b d occ k hF
  have hstages : (clause52MacroStageList F k).length = 2 * 5^k := by
    rw [clause52MacroStageList_length, clause52StageCount_eq]
  have hterms : ∀ st ∈ clause52MacroStageList F k, st.2.length = Λ ∧ (∀ i : Fin Λ, i ∈ st.2) :=
    fun st hst => ⟨(clause52MacroStageTerms F k st hst).1, (clause52MacroStageTerms F k st hst).2.1⟩
  have hdepth : clause52MacroDepth k (d * (occ - 1) + 1) = 2 * 5^k * (d * (occ - 1) + 1) :=
    clause52MacroDepth_occupancy k d occ
  have hgates : clause52MacroGates F k = 2 * Λ * 5^k := clause52MacroGates_eq F k
  have hroute : clause52MacroRouteSwaps F k
      = 2 * 5^k * (∑ i : Fin Λ, ((F i).support.card - 1)) := clause52MacroRouteSwaps_levels F k
  exact ⟨hstages, hterms, clause52MacroWord_eq_stages F k, hdepth, hgates, hroute⟩

/-- The ferromagnetic half gate word has one entry per site and two entries per listed pair. -/
theorem clause61_gate_half_length {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    (ferroGateHalf F β r).length = n + 2 * (ferroPairList n).length := by
  simp [ferroGateHalf]
  ring

/-- The ferromagnetic gate word has twice the length of its half word. -/
theorem clause61_gate_word_length {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    (ferroGateWord F β r).length = 2 * (n + 2 * (ferroPairList n).length) := by
  simp [ferroGateWord, clause61_gate_half_length]
  ring

/-- The ferromagnetic step word has twice the length of the half gate word. -/
theorem clause61_step_word_length {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    (ferroStepWord F β r).length = 2 * (n + 2 * (ferroPairList n).length) := by
  simp [ferroStepWord, ferroStepHalf]
  ring

/-- The full ferromagnetic gate word has `r` times the length of a single gate word. -/
theorem clause61_full_gate_word_length {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    (ferroFullGateWord F β r).length = r * (2 * (n + 2 * (ferroPairList n).length)) := by
  simp [ferroFullGateWord, clause61_gate_word_length]

/-- A ledger whose layer count matches the full gate word satisfies the stated error
decomposition and gate-word length identities. -/
theorem clause61_gate_count_endpoint : ∀ {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ)
    (l : FerroLedger), l.layers = r * (2 * (n + 2 * (ferroPairList n).length)) →
    l.trotterError + l.synthesisError = ferroRelativeError l ∧
      (ferroFullGateWord F β r).length = l.layers ∧
      (ferroGateWord F β r).length = 2 * (n + 2 * (ferroPairList n).length) ∧
      (ferroStepWord F β r).length = (ferroGateWord F β r).length := by
  intro n F β r l hlayers
  have h1 : ferroRelativeError l = l.trotterError + l.synthesisError := rfl
  have h2 : (ferroFullGateWord F β r).length = l.layers := by
    rw [clause61_full_gate_word_length, hlayers]
  have h3 : (ferroGateWord F β r).length = 2 * (n + 2 * (ferroPairList n).length) :=
    clause61_gate_word_length F β r
  have h4 : (ferroStepWord F β r).length = (ferroGateWord F β r).length := by
    rw [clause61_step_word_length, clause61_gate_word_length]
  exact ⟨h1 ▸ rfl, h2, h3, h4⟩

end Qatlib.Concepts.TrotterFormula.GeneralOrder
