/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Field.Rat
import Qatlib.Concepts.ShadowModels.UStatBackend.OrderedHigherUStatistic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Dynamic evaluation of separable U-statistics

This module evaluates separable ordered U-statistics by a rational table indexed by subsets of
kernel positions. The cached entries equal sums over injective sample assignments; the
implementation has `2 ^ r` table entries and counts `m * r * 2 ^ (r - 1)` updates. Unbiasedness,
variance, and tail bounds connect it to nonlinear shadow estimation [HuangKuengPreskill2020].

## Main statements

* `separable_u_actual_cached_mask_injection_sum`: the cached-table invariant.
* `separable_u_actual_fold_work`: the exact counted update total.
* `separable_u_same_records_variance_and_tail`: finite-sample error bounds.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.UStatBackend
open scoped Classical BigOperators

/-- Read the first table entry with subset key `S`, returning zero when that key is absent. -/
def separableTableRead {r : ℕ} (D : List (Finset (Fin r)×ℚ)) (S : Finset (Fin r)) : ℚ :=
 ((D.find? (fun p => p.1=S)).map Prod.snd).getD 0

/-- Update every subset entry by its old value plus the sum of `v j` times the old entry with
`j` removed, counting one update summand for each element of each subset. -/
def separableTableStep {r : ℕ} (v : Fin r → ℚ) (D : List (Finset (Fin r)×ℚ)) :
 List (Finset (Fin r)×ℚ) × ℕ :=
 ((Finset.univ : Finset (Fin r)).powerset.toList).foldl (fun z S =>
  let a := S.toList.foldl (fun a j =>
   (a.1+v j*separableTableRead D (S.erase j),a.2+1)) (separableTableRead D S,0)
  (z.1++[(S,a.1)],z.2+a.2)) ([],0)

/-- Fold the subset-table update over the sample vectors, starting from one on the empty subset
and zero elsewhere, and accumulate the counted updates. -/
def separableURun {m r : ℕ} (v : Fin m → Fin r → ℚ) :
 List (Finset (Fin r)×ℚ) × ℕ :=
 (List.ofFn v).foldl (fun z x =>
  let a := separableTableStep x z.1; (a.1,z.2+a.2))
  (((Finset.univ : Finset (Fin r)).powerset.toList.map
    (fun S => (S,if S=∅ then 1 else 0))),0)

/-- The final rational dynamic-programming value at a given subset of kernel positions. -/
def separableUDP {m r : ℕ} (v : Fin m → Fin r → ℚ) : Finset (Fin r) → ℚ :=
 fun S => separableTableRead (separableURun v).1 S

/-- The full-subset dynamic-programming value divided by the falling factorial `m.descFactorial
r`. -/
def separableUValue {m r : ℕ} (v : Fin m → Fin r → ℚ) : ℚ :=
 separableUDP v Finset.univ / (m.descFactorial r : ℚ)

/-- The counted update total of the separable U-statistic program on zero-valued sample vectors
of the given dimensions. -/
def separableUWork (m r : ℕ) : ℕ :=
 (separableURun (fun _ : Fin m => fun _ : Fin r => (0:ℚ))).2

/-- Reading a table mapped from subset keys returns the mapped value when the requested key
occurs, and zero otherwise. -/
private theorem separable_read_map {r : ℕ} (ks : List (Finset (Fin r)))
    (f : Finset (Fin r) → ℚ) (S : Finset (Fin r)) :
    separableTableRead (ks.map (fun T => (T,f T))) S = if S∈ks then f S else 0 := by
  induction ks with
  | nil => simp [separableTableRead]
  | cons T ks ih =>
    by_cases hT : T=S
    · subst T; simp [separableTableRead]
    · simpa [separableTableRead, hT, Ne.symm hT] using ih

/-- The counted inner additive fold returns the initial value plus the mapped sum and increases
the count by the list length. -/
private theorem separable_inner_fold {r : ℕ} (g : Fin r → ℚ) (xs : List (Fin r)) (a : ℚ×ℕ) :
    xs.foldl (fun a j => (a.1+g j,a.2+1)) a = (a.1+(xs.map g).sum,a.2+xs.length) := by
  induction xs generalizing a with
  | nil => simp
  | cons j xs ih => simp [ih,add_assoc,Nat.add_comm]

/-- The outer table fold appends the mapped key-value entries and increases the work count by
the sum of their assigned costs. -/
private theorem separable_outer_fold {r : ℕ} (f : Finset (Fin r) → ℚ) (w : Finset (Fin r) → ℕ)
    (ks : List (Finset (Fin r))) (z : List (Finset (Fin r)×ℚ)×ℕ) :
    ks.foldl (fun z S => (z.1++[(S,f S)],z.2+w S)) z =
      (z.1++ks.map (fun S => (S,f S)),z.2+(ks.map w).sum) := by
  induction ks generalizing z with
  | nil => simp
  | cons S ks ih => simp [ih,List.append_assoc,Nat.add_assoc]

/-- A table step returns the explicit subset recurrence table and the sum of the cardinalities
of all subsets as its update count. -/
private theorem separable_step_eq {r : ℕ} (v : Fin r → ℚ) (D : List (Finset (Fin r)×ℚ)) :
    separableTableStep v D =
      (((Finset.univ : Finset (Fin r)).powerset.toList.map (fun S =>
        (S,separableTableRead D S+∑ j∈S, v j*separableTableRead D (S.erase j)))),
        ∑ S∈(Finset.univ : Finset (Fin r)).powerset, S.card) := by
  unfold separableTableStep
  simp_rw [separable_inner_fold]
  have hs (S : Finset (Fin r)) :
      (S.toList.map (fun j => v j*separableTableRead D (S.erase j))).sum =
        ∑ j∈S, v j*separableTableRead D (S.erase j) := by
    simp [← List.sum_toFinset (fun j => v j*separableTableRead D (S.erase j)) S.nodup_toList]
  simp_rw [hs]
  simp only [zero_add, Finset.length_toList]
  rw [separable_outer_fold]
  simp only [List.nil_append, zero_add]
  congr 1
  simp

/-- Reading a subset after a table step gives its old value plus the sum of `v j` times the old
value on the subset with `j` erased. -/
theorem separable_table_step_read {r : ℕ} (v : Fin r → ℚ) (D : List (Finset (Fin r)×ℚ))
    (S : Finset (Fin r)) :
    separableTableRead (separableTableStep v D).1 S =
      separableTableRead D S+∑ j∈S, v j*separableTableRead D (S.erase j) := by
  rw [separable_step_eq, separable_read_map]
  simp

/-- The sum of the sizes of all subsets of `Fin r` is `r * 2 ^ (r - 1)`. -/
private theorem separable_mask_work (r : ℕ) :
    (∑ S∈(Finset.univ : Finset (Fin r)).powerset, S.card) = r*2^(r-1) := by
  rw [Finset.sum_powerset_apply_card (fun n : ℕ => n)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [Nat.mul_comm]
  exact Nat.sum_range_mul_choose r

/-- Folding table steps over a list adds its length times `r * 2 ^ (r - 1)` to the initial
update count. -/
private theorem separable_run_work_list {r : ℕ} (xs : List (Fin r → ℚ))
    (z : List (Finset (Fin r)×ℚ)×ℕ) :
    (xs.foldl (fun z x => let a := separableTableStep x z.1; (a.1,z.2+a.2)) z).2 =
      z.2+xs.length*(r*2^(r-1)) := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons,ih,List.length_cons]
      simp only [separable_step_eq,separable_mask_work]
      ring

/-- The actual update count is independent of the sample values and equals `m * r * 2 ^ (r -
1)`, with zero updates when `r = 0`. See [HuangKuengPreskill2020]. -/
theorem separable_u_actual_fold_work (m r : ℕ) (v : Fin m → Fin r → ℚ) :
    (separableURun v).2 = separableUWork m r ∧
      separableUWork m r = m*r*2^(r-1) ∧ (r=0 → separableUWork m r=0) := by
  have hv : (separableURun v).2 = m*r*2^(r-1) := by
    simp only [separableURun,separable_run_work_list,List.length_ofFn,zero_add]
    ring
  have hw : separableUWork m r = m*r*2^(r-1) := by
    dsimp only [separableUWork]
    simp only [separableURun,separable_run_work_list,List.length_ofFn,zero_add]
    ring
  refine ⟨hv.trans hw.symm,hw,?_⟩
  intro hr
  rw [hw,hr]
  simp

/-- Folding table steps preserves the list of all subset keys when it is present in the initial
table. -/
private theorem separable_run_keys_list {r : ℕ} (xs : List (Fin r → ℚ))
    (z : List (Finset (Fin r)×ℚ)×ℕ)
    (hz : z.1.map Prod.fst = (Finset.univ : Finset (Fin r)).powerset.toList) :
    (xs.foldl (fun z x => let a := separableTableStep x z.1; (a.1,z.2+a.2)) z).1.map Prod.fst =
      (Finset.univ : Finset (Fin r)).powerset.toList := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
      apply ih
      simp only [separable_step_eq]
      simp [Function.comp_def]

/-- The final table contains exactly `2 ^ r` entries and has no duplicate subset keys. -/
theorem separable_u_actual_table_cells (m r : ℕ) (v : Fin m → Fin r → ℚ) :
    (separableURun v).1.length = 2^r ∧ ((separableURun v).1.map Prod.fst).Nodup := by
  have hk : ((separableURun v).1.map Prod.fst) = (Finset.univ : Finset (Fin r)).powerset.toList := by
    apply separable_run_keys_list
    simp [Function.comp_def]
  refine ⟨?_,?_⟩
  · have hh := congrArg List.length hk
    simpa using hh
  · rw [hk]
    exact Finset.nodup_toList _

/-- Extend an embedding into `Fin m` to one into `Fin (m + 1)` by casting every index into the
initial segment. -/
private def sepLiftOld {A : Type} {m : ℕ} (f : A ↪ Fin m) : A ↪ Fin (m+1) where
  toFun x := (f x).castSucc
  inj' := by
    intro x y h
    apply f.injective
    apply Fin.ext
    exact congrArg (fun z : Fin (m+1) => z.val) h

/-- Extend an embedding of all elements except `a` into `Fin m` by sending `a` to the new last
index. -/
private def sepLiftFresh {A : Type} [DecidableEq A] {m : ℕ} (a : A)
    (g : {x : A // x ≠ a} ↪ Fin m) : A ↪ Fin (m+1) where
  toFun x := if hx : x=a then Fin.last m else (g ⟨x,hx⟩).castSucc
  inj' := by
    intro x y h
    by_cases hx : x=a <;> by_cases hy : y=a
    · exact hx.trans hy.symm
    · have hv := congrArg (fun z : Fin (m+1) => z.val) h
      dsimp only at hv
      simp only [dif_pos hx,dif_neg hy,Fin.val_castSucc,Fin.val_last] at hv
      have hh := (g ⟨y,hy⟩).isLt
      omega
    · have hv := congrArg (fun z : Fin (m+1) => z.val) h
      dsimp only at hv
      simp only [dif_neg hx,dif_pos hy,Fin.val_castSucc,Fin.val_last] at hv
      have hh := (g ⟨x,hx⟩).isLt
      omega
    · have he : g ⟨x,hx⟩ = g ⟨y,hy⟩ := by
        apply Fin.ext
        have hv := congrArg (fun z : Fin (m+1) => z.val) h
        dsimp only at hv
        simpa only [dif_neg hx,dif_neg hy] using! hv
      exact congrArg Subtype.val (g.injective he)

/-- Construct an embedding into `Fin (m + 1)` either from an old embedding or by assigning one
distinguished domain element to the new last index. -/
private def sepLiftSplit {A : Type} [DecidableEq A] (m : ℕ) :
    (A ↪ Fin m) ⊕ (Σ a : A, {x : A // x ≠ a} ↪ Fin m) → (A ↪ Fin (m+1))
  | Sum.inl f => sepLiftOld f
  | Sum.inr ⟨a,g⟩ => sepLiftFresh a g

/-- The construction splitting embeddings according to use of the new last index is injective. -/
private theorem sepLiftSplit_injective {A : Type} [DecidableEq A] (m : ℕ) :
    Function.Injective (sepLiftSplit (A := A) m) := by
  intro u v he
  cases u with
  | inl f =>
      cases v with
      | inl g =>
          apply congrArg Sum.inl
          apply Function.Embedding.ext
          intro x
          apply Fin.ext
          exact congrArg (fun z : Fin (m+1) => z.val) (congrArg (fun e : A ↪ Fin (m+1) => e x) he)
      | inr ag =>
          obtain ⟨a,g⟩ := ag
          have hx := congrArg (fun e : A ↪ Fin (m+1) => (e a).val) he
          simp [sepLiftSplit,sepLiftOld,sepLiftFresh] at hx
          have hh := (f a).isLt
          omega
  | inr af =>
      obtain ⟨a,f⟩ := af
      cases v with
      | inl g =>
          have hx := congrArg (fun e : A ↪ Fin (m+1) => (e a).val) he
          simp [sepLiftSplit,sepLiftOld,sepLiftFresh] at hx
          have hh := (g a).isLt
          omega
      | inr bg =>
          obtain ⟨b,g⟩ := bg
          have hab : a=b := by
            by_contra hn
            have hx := congrArg (fun e : A ↪ Fin (m+1) => (e a).val) he
            simp [sepLiftSplit,sepLiftFresh,hn] at hx
            have hh := (g ⟨a,hn⟩).isLt
            omega
          subst b
          have hfg : f=g := by
            apply Function.Embedding.ext
            intro x
            apply Fin.ext
            have hx := congrArg (fun e : A ↪ Fin (m+1) => (e x.val).val) he
            simpa only [sepLiftSplit,sepLiftFresh,Function.Embedding.coeFn_mk,dif_neg x.property,
              Fin.val_castSucc] using hx
          subst g
          rfl

/-- An element of `Fin (m + 1)` different from the last index has value strictly less than `m`. -/
private theorem sep_not_last_lt {m : ℕ} (x : Fin (m+1)) (hx : x ≠ Fin.last m) : x.val < m := by
  have hh := x.isLt
  by_contra! hn
  have he : x.val=m := by omega
  exact hx (Fin.ext he)

/-- Every embedding into `Fin (m + 1)` arises from the construction splitting by use of the new
last index. -/
private theorem sepLiftSplit_surjective {A : Type} [DecidableEq A] (m : ℕ) :
    Function.Surjective (sepLiftSplit (A := A) m) := by
  intro f
  by_cases hf : ∃ a : A, f a=Fin.last m
  · obtain ⟨a,ha⟩ := hf
    have hne (x : {x : A // x ≠ a}) : f x.val ≠ Fin.last m := by
      intro he
      exact x.property (f.injective (he.trans ha.symm))
    let g : {x : A // x ≠ a} ↪ Fin m := {
      toFun := fun x => ⟨(f x.val).val,sep_not_last_lt _ (hne x)⟩
      inj' := by
        intro x y he
        apply Subtype.ext
        apply f.injective
        apply Fin.ext
        exact congrArg (fun z : Fin m => z.val) he }
    refine ⟨Sum.inr ⟨a,g⟩,?_⟩
    apply Function.Embedding.ext
    intro x
    by_cases hx : x=a
    · subst x
      simpa [sepLiftSplit,sepLiftFresh] using ha.symm
    · apply Fin.ext
      simp only [sepLiftSplit,sepLiftFresh,Function.Embedding.coeFn_mk,dif_neg hx,Fin.val_castSucc]
      rfl
  · have hne (x : A) : f x ≠ Fin.last m := by intro he; exact hf ⟨x,he⟩
    let g : A ↪ Fin m := {
      toFun := fun x => ⟨(f x).val,sep_not_last_lt _ (hne x)⟩
      inj' := by
        intro x y he
        apply f.injective
        apply Fin.ext
        exact congrArg (fun z : Fin m => z.val) he }
    refine ⟨Sum.inl g,?_⟩
    apply Function.Embedding.ext
    intro x
    rfl

/-- The equivalence splitting embeddings into those avoiding the last index and those sending a
distinguished domain element to it. -/
private def sepEmbeddingSplit {A : Type} [DecidableEq A] (m : ℕ) :
    ((A ↪ Fin m) ⊕ (Σ a : A, {x : A // x ≠ a} ↪ Fin m)) ≃ (A ↪ Fin (m+1)) :=
  Equiv.ofBijective (sepLiftSplit m) ⟨sepLiftSplit_injective m,sepLiftSplit_surjective m⟩

/-- A sum of separable products over embeddings into `Fin (m + 1)` splits into embeddings
avoiding the new index and terms assigning exactly one domain element to it. -/
private theorem sepEmbedding_sum_succ {A : Type} [Fintype A] [DecidableEq A] (m : ℕ)
    (v : Fin (m+1) → A → ℚ) :
    (∑ f : A ↪ Fin (m+1), ∏ x : A, v (f x) x) =
      (∑ f : A ↪ Fin m, ∏ x : A, v (f x).castSucc x) +
      ∑ a : A, v (Fin.last m) a *
        (∑ g : {x : A // x ≠ a} ↪ Fin m, ∏ x : {x : A // x ≠ a}, v (g x).castSucc x.val) := by
  rw [← (sepEmbeddingSplit (A := A) m).sum_comp, Fintype.sum_sum_type, Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  (try dsimp only)
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  change (∏ x : A, v (sepLiftFresh a g x) x) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ a]
  simp only [sepLiftFresh,Function.Embedding.coeFn_mk]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  simp only [dif_neg x.property]

/-- The equivalence between the elements of a finite subset other than `a` and the subtype
associated with erasing `a` from that subset. -/
private def sepEraseEquiv {r : ℕ} (S : Finset (Fin r)) (a : S) :
    {x : S // x ≠ a} ≃ (S.erase a.val) where
  toFun x := ⟨x.val.val,Finset.mem_erase.mpr ⟨by
    intro he; exact x.property (Subtype.ext he),x.val.property⟩⟩
  invFun x := ⟨⟨x.val,(Finset.mem_erase.mp x.property).2⟩,by
    intro he; exact (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val he)⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- The sum of products of sample values over injective assignments of the positions in a subset
to sample indices. -/
private def sepMaskInjectionSum {m r : ℕ} (v : Fin m → Fin r → ℚ) (S : Finset (Fin r)) : ℚ :=
  ∑ f : S ↪ Fin m, ∏ j : S, v (f j) j.val

/-- Adding a sample splits the subset injection sum into assignments avoiding the new sample and
assignments using it at one subset position. -/
private theorem sepMaskInjectionSum_succ {m r : ℕ} (v : Fin (m+1) → Fin r → ℚ) (S : Finset (Fin r)) :
    sepMaskInjectionSum v S = sepMaskInjectionSum (fun i j => v i.castSucc j) S+
      ∑ a∈S, v (Fin.last m) a*sepMaskInjectionSum (fun i j => v i.castSucc j) (S.erase a) := by
  rw [sepMaskInjectionSum,sepEmbedding_sum_succ m (fun i (j : S) => v i j.val)]
  have he (a : S) :
      (∑ g : {x : S // x ≠ a} ↪ Fin m, ∏ x : {x : S // x ≠ a}, v (g x).castSucc x.val.val) =
        sepMaskInjectionSum (fun i j => v i.castSucc j) (S.erase a.val) := by
    let e := sepEraseEquiv S a
    let E := Equiv.embeddingCongr e (Equiv.refl (Fin m))
    have hp (g : {x : S // x ≠ a} ↪ Fin m) :
        (∏ x : {x : S // x ≠ a}, v (g x).castSucc x.val.val) =
          ∏ j : S.erase a.val, v (E g j).castSucc j.val := by
      rw [← e.prod_comp]
      apply Finset.prod_congr rfl
      intro x _
      rfl
    simp_rw [hp]
    rw [E.sum_comp (fun g : S.erase a.val ↪ Fin m => ∏ j : S.erase a.val, v (g j).castSucc j.val)]
    rfl
  simp_rw [he]
  rw [Finset.sum_coe_sort S (fun a => v (Fin.last m) a*sepMaskInjectionSum (fun i j => v i.castSucc j) (S.erase a))]
  rfl

/-- With zero samples, the subset injection sum is one for the empty subset and zero for every
nonempty subset. -/
private theorem sepMaskInjectionSum_zero {r : ℕ} (v : Fin 0 → Fin r → ℚ) (S : Finset (Fin r)) :
    sepMaskInjectionSum v S = if S=∅ then 1 else 0 := by
  by_cases hS : S=∅
  · subst S
    simp [sepMaskInjectionSum]
  · have hs := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨a,ha⟩ := hs
    letI : IsEmpty (S ↪ Fin 0) := ⟨fun f => Fin.elim0 (f ⟨a,ha⟩)⟩
    simp [sepMaskInjectionSum,hS]

/-- The full-subset injection sum equals the sum of separable products over embeddings of `Fin
r` into `Fin m`. -/
private theorem sepMaskInjectionSum_univ {m r : ℕ} (v : Fin m → Fin r → ℚ) :
    sepMaskInjectionSum v Finset.univ = ∑ f : Fin r ↪ Fin m, ∏ j : Fin r, v (f j) j := by
  let e : (Finset.univ : Finset (Fin r)) ≃ Fin r :=
    { toFun := Subtype.val
      invFun := fun j => ⟨j,Finset.mem_univ _⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  let E := Equiv.embeddingCongr e (Equiv.refl (Fin m))
  have hp (g : (Finset.univ : Finset (Fin r)) ↪ Fin m) :
      (∏ j : (Finset.univ : Finset (Fin r)), v (g j) j.val) = ∏ j : Fin r, v (E g j) j := by
    rw [← e.prod_comp]
    apply Finset.prod_congr rfl
    intro j _
    rfl
  dsimp only [sepMaskInjectionSum]
  simp_rw [hp]
  exact E.sum_comp (fun f : Fin r ↪ Fin m => ∏ j : Fin r, v (f j) j)

/-- Adding the last sample updates each cached subset by its prefix value plus the last-sample
contributions from cached subsets with one position removed. -/
theorem separable_u_actual_prefix_step {m r : ℕ} (v : Fin (m+1) → Fin r → ℚ) (S : Finset (Fin r)) :
    separableUDP v S = separableUDP (fun i j => v i.castSucc j) S+
      ∑ j∈S, v (Fin.last m) j*separableUDP (fun i j => v i.castSucc j) (S.erase j) := by
  have ht : (separableURun v).1 =
      (separableTableStep (v (Fin.last m)) (separableURun (fun i j => v i.castSucc j)).1).1 := by
    unfold separableURun
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    rfl
  dsimp only [separableUDP]
  rw [ht,separable_table_step_read]

/-- Every cached subset value equals the sum of separable products over injective assignments of
its positions to samples. -/
theorem separable_u_actual_cached_mask_injection_sum {m r : ℕ}
    (v : Fin m → Fin r → ℚ) (S : Finset (Fin r)) :
    separableUDP v S = ∑ f : S ↪ Fin m, ∏ j : S, v (f j) j.val := by
  change separableUDP v S = sepMaskInjectionSum v S
  induction m generalizing S with
  | zero =>
      rw [sepMaskInjectionSum_zero]
      dsimp only [separableUDP,separableURun]
      simp only [List.ofFn_zero,List.foldl_nil]
      rw [separable_read_map]
      simp
  | succ m ih =>
      rw [separable_u_actual_prefix_step,sepMaskInjectionSum_succ]
      simp_rw [ih]

/-- The full-subset dynamic-programming value equals the sum of separable products over
embeddings of all `r` positions into the `m` samples. See [HuangKuengPreskill2020]. -/
theorem separable_u_actual_dynamic_program_injection_sum (m r : ℕ) (v : Fin m → Fin r → ℚ) :
    separableUDP v Finset.univ = ∑ f : Fin r ↪ Fin m, ∏ j : Fin r, v (f j) j :=
  (separable_u_actual_cached_mask_injection_sum v Finset.univ).trans (sepMaskInjectionSum_univ v)

/-- The expectation of a product of coordinatewise rational functions on independent draws
equals the product of their expectations. -/
private theorem sep_fresh_product_mean {X : Type} [Fintype X] (p : FinDist X) (r : ℕ)
    (h : Fin r → X → ℚ) :
    (∑ x : Fin r → X, p.probOf x*(∏ j : Fin r, (h j (x j) : ℝ))) =
      ∏ j : Fin r, ∑ x : X, p.prob x*(h j x : ℝ) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [FinDist.probOf, Finset.prod_mul_distrib]

/-- For `r ≤ m`, the separable U-statistic has expectation equal to the product of the `r`
individual factor means. See [HuangKuengPreskill2020]. -/
theorem separable_u_fresh_unbiased_consumer (X : Type) [Fintype X] (p : FinDist X) (m r : ℕ)
    (h : Fin r → X → ℚ) (hr : r ≤ m) :
    (∑ ω : Fin m → X, p.probOf ω*(separableUValue (fun i j => h j (ω i)) : ℝ)) =
      ∏ j : Fin r, ∑ x : X, p.prob x*(h j x : ℝ) := by
  have he (ω : Fin m → X) : (separableUValue (fun i j => h j (ω i)) : ℝ) =
      (∑ f : Fin r ↪ Fin m, ∏ j : Fin r, (h j (ω (f j)) : ℝ))/(m.descFactorial r : ℝ) := by
    rw [separableUValue,separable_u_actual_dynamic_program_injection_sum]
    push_cast
    rfl
  have hm (f : Fin r ↪ Fin m) :
      (∑ ω : Fin m → X, p.probOf ω*(∏ j : Fin r, (h j (ω (f j)) : ℝ))) =
        ∏ j : Fin r, ∑ x : X, p.prob x*(h j x : ℝ) := by
    have hh :=
        finite_pair_record_marginal p f f.injective (fun x : Fin r → X => ∏ j, (h j (x j) : ℝ))
    change (∑ ω : Fin m → X, p.probOf ω*(∏ j : Fin r, (h j (ω (f j)) : ℝ))) =
      (∑ x : Fin r → X, p.probOf x*(∏ j : Fin r, (h j (x j) : ℝ))) at hh
    exact hh.trans (sep_fresh_product_mean p r h)
  simp_rw [he, ← mul_div_assoc]
  rw [← Finset.sum_div]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hm]
  simp only [Finset.sum_const,
      Finset.card_univ,Fintype.card_embedding_eq,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.descFactorial_pos.mpr hr).ne')

/-- The product of the position-dependent rational factors on a list of length `r`, and zero for
lists of other lengths. -/
def separableOrderedKernel {X : Type} {r : ℕ} (h : Fin r → X → ℚ) (xs : List X) : ℚ :=
  if hx : xs.length = r then ∏ j : Fin r, h j (xs[j.val]'(by rw [hx]; exact j.isLt)) else 0

/-- On a list formed from a function on `Fin r`, the separable ordered kernel equals the product
of the corresponding factors. -/
@[simp] theorem separableOrderedKernel_ofFn {X : Type} {r : ℕ} (h : Fin r → X → ℚ) (x : Fin r → X) :
    separableOrderedKernel h (List.ofFn x) = ∏ j : Fin r, h j (x j) := by
  simp [separableOrderedKernel]

/-- Casting the separable dynamic-programming estimate to the reals gives the ordered higher
U-statistic for the separable list kernel on the same records. -/
theorem separable_u_same_record_real_value {X : Type} (m r : ℕ) (h : Fin r → X → ℚ) (ω : Fin m → X) :
    (separableUValue (fun i j => h j (ω i)) : ℝ) =
      (higherUCounted m r (fun xs => (separableOrderedKernel h xs : ℝ)) ω).1 := by
  rw [(higher_u_ordered_enumeration_and_cost m r).2.2.2 X _ ω |>.2,higherUTuples_sum]
  simp only [List.map_ofFn,separableOrderedKernel_ofFn,Rat.cast_prod]
  rw [separableUValue,separable_u_actual_dynamic_program_injection_sum]
  push_cast
  rfl

/-- A uniform bound on the absolute product of the factor values bounds the separable ordered
kernel on every list of length `r`. -/
private theorem sep_kernel_bound {X : Type} {r : ℕ} (h : Fin r → X → ℚ) (B : ℝ)
    (hb : ∀ x : Fin r → X, |∏ j : Fin r, (h j (x j) : ℝ)| ≤ B) :
    ∀ xs : List X, xs.length = r → |(separableOrderedKernel h xs : ℝ)| ≤ B := by
  intro xs hxs
  rw [separableOrderedKernel,dif_pos hxs,Rat.cast_prod]
  exact hb (fun j => xs[j.val]'(by rw [hxs]; exact j.isLt))

/-- The independent-sample mean of the separable ordered kernel equals the product of the
individual factor means. -/
private theorem sep_kernel_mean {X : Type} [Fintype X] (p : FinDist X) (r : ℕ) (h : Fin r → X → ℚ) :
    higherUMean p r (fun xs => (separableOrderedKernel h xs : ℝ)) =
      ∏ j : Fin r, ∑ x : X, p.prob x*(h j x : ℝ) := by
  dsimp only [higherUMean]
  simp only [separableOrderedKernel_ofFn,Rat.cast_prod]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [FinDist.probOf,Finset.prod_mul_distrib]

/-- For positive `m`, `r ≤ m`, and product kernel bounded by `B`, the separable estimator has
mean squared error at most `4 * r ^ 2 * B ^ 2 / m` and deviation probability at most that
quantity divided by `eps ^ 2`. -/
theorem separable_u_same_records_variance_and_tail (X : Type) [Fintype X] (p : FinDist X)
    (m r : ℕ) (h : Fin r → X → ℚ) (B eps : ℝ) (hm : 0 < m) (hr : r ≤ m)
    (hB : 0 ≤ B) (heps : 0 < eps)
    (hb : ∀ x : Fin r → X, |∏ j : Fin r, (h j (x j) : ℝ)| ≤ B) :
    let μ := ∏ j : Fin r, ∑ x : X, p.prob x*(h j x : ℝ)
    (∑ ω : Fin m → X, p.probOf ω*((separableUValue (fun i j => h j (ω i)) : ℝ)-μ)^2) ≤
      4*(r : ℝ)^2*B^2/m ∧
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → X => eps ≤
      |(separableUValue (fun i j => h j (ω i)) : ℝ)-μ|),p.probOf ω) ≤ 4*(r : ℝ)^2*B^2/(m*eps^2) := by
  (try dsimp only)
  have hbound := sep_kernel_bound h B hb
  have hv := higher_u_overlap_covariance_and_variance X p m r
    (fun xs => (separableOrderedKernel h xs : ℝ)) B hm hr hB hbound
  have ht := (higher_u_same_records_tail_and_rational_fold X p m r
    (separableOrderedKernel h) B eps hm hr hB heps hbound).2
  have he (ω : Fin m → X) : ((higherUCountedQ m r (separableOrderedKernel h) ω).1 : ℝ) =
      (separableUValue (fun i j => h j (ω i)) : ℝ) :=
    (higherUCountedQ_cast m r (separableOrderedKernel h) ω).1.trans (separable_u_same_record_real_value m r h ω).symm
  rw [sep_kernel_mean] at hv ht
  constructor
  · simpa only [separable_u_same_record_real_value] using hv
  · simpa only [he] using ht

/-- With zero samples, the cached value is one on the empty subset and zero on every other
subset. -/
theorem separable_u_actual_zero_samples {r : ℕ} (v : Fin 0 → Fin r → ℚ) (S : Finset (Fin r)) :
    separableUDP v S = if S=∅ then 1 else 0 := by
  dsimp only [separableUDP,separableURun]
  simp only [List.ofFn_zero,List.foldl_nil]
  rw [separable_read_map]
  simp

/-- For `r ≤ m`, the expectation of a finite sum of separable U-statistics equals the sum of the
products of their individual factor means. -/
theorem separable_u_finite_rank_fresh_unbiased_consumer (X : Type) [Fintype X]
    (p : FinDist X) (m r k : ℕ) (h : Fin k → Fin r → X → ℚ) (hr : r ≤ m) :
    (∑ ω : Fin m → X, p.probOf ω*∑ a : Fin k,
      (separableUValue (fun i j => h a j (ω i)) : ℝ)) =
        ∑ a : Fin k, ∏ j : Fin r, ∑ x : X, p.prob x*(h a j x : ℝ) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => separable_u_fresh_unbiased_consumer X p m r (h a) hr)

end Qatlib.Concepts.ShadowModels.UStatBackend
