/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.List.FinRange
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.UStatBackend
open scoped Classical BigOperators

def higherUTuples (m : ℕ) : ℕ → List (List (Fin m))
  | 0 => [[]]
  | r+1 => (List.finRange m).flatMap (fun i => (higherUTuples m r).filterMap
      (fun xs => if i ∈ xs then none else some (i::xs)))

noncomputable def higherUMean {X : Type} [Fintype X] (p : FinDist X) (r : ℕ) (h : List X → ℝ) : ℝ :=
  ∑ ω : Fin r → X, p.probOf ω * h (List.ofFn ω)

noncomputable def higherUCounted {X : Type} (m r : ℕ) (h : List X → ℝ) (ω : Fin m → X) : ℝ × ℕ :=
  let a := (higherUTuples m r).foldl (fun a xs => (a.1+h (xs.map ω),a.2+1)) (0,0)
  (a.1/(higherUTuples m r).length,a.2)

def higherUCountedQ {X : Type} (m r : ℕ) (h : List X → ℚ) (ω : Fin m → X) : ℚ × ℕ :=
  let a := (higherUTuples m r).foldl (fun a xs => (a.1+h (xs.map ω),a.2+1)) (0,0)
  (a.1/(higherUTuples m r).length,a.2)

private theorem higher_filterMap_cons {α : Type} [DecidableEq α] (i : α) (xs : List (List α)) :
    xs.filterMap (fun ys => if i∈ys then none else some (i::ys))=
      (xs.filter (fun ys => decide (i∉ys))).map (List.cons i) := by
  induction xs with
  | nil => rfl
  | cons ys xs ih => by_cases hy : i∈ys <;> simp [hy,ih]

theorem higherUTuples_mem (m r : ℕ) (xs : List (Fin m)) :
    xs∈higherUTuples m r ↔ xs.length=r ∧ xs.Nodup := by
  induction r generalizing xs with
  | zero => cases xs <;> simp [higherUTuples]
  | succ r ih =>
    simp only [higherUTuples,higher_filterMap_cons,List.mem_flatMap,List.mem_finRange,
      true_and,List.mem_map,List.mem_filter,decide_eq_true_eq]
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.cons.injEq,List.length_cons,List.nodup_cons,Nat.succ.injEq]
      constructor
      · rintro ⟨i,ys,⟨hy,hi⟩,he,hys⟩
        subst i
        subst ys
        exact ⟨(ih xs).mp hy |>.1,hi,(ih xs).mp hy |>.2⟩
      · rintro ⟨hl,hi,hn⟩
        exact ⟨x,xs,⟨(ih xs).mpr ⟨hl,hn⟩,hi⟩,rfl,rfl⟩

theorem higherUTuples_nodup (m r : ℕ) : (higherUTuples m r).Nodup := by
  induction r with
  | zero => simp [higherUTuples]
  | succ r ih =>
    rw [higherUTuples,List.nodup_flatMap]
    simp only [higher_filterMap_cons]
    constructor
    · intro i _
      exact (ih.filter _).map (fun xs ys he => (List.cons.inj he).2)
    · apply (List.nodup_finRange m).imp
      intro i j hij
      apply List.disjoint_left.mpr
      intro xs hxi hxj
      obtain ⟨ys,_,hi⟩ := List.mem_map.mp hxi
      obtain ⟨zs,_,hj⟩ := List.mem_map.mp hxj
      exact hij (List.cons.inj (hi.trans hj.symm)).1

private noncomputable def higherTupleEquiv (m r : ℕ) :
    (Fin r ↪ Fin m) ≃ (higherUTuples m r).toFinset := by
  classical
  let T := (higherUTuples m r).toFinset
  have hlen (xs : T) : xs.1.length=r :=
      (higherUTuples_mem m r xs.1).mp (List.mem_toFinset.mp xs.2) |>.1
  have hnd (xs : T) : xs.1.Nodup := (higherUTuples_mem m r xs.1).mp (List.mem_toFinset.mp xs.2) |>.2
  exact {
    toFun := fun f => ⟨List.ofFn f,by
      apply List.mem_toFinset.mpr
      apply (higherUTuples_mem m r _).mpr
      exact ⟨List.length_ofFn,List.nodup_ofFn.mpr f.injective⟩⟩
    invFun := fun xs => {
      toFun := fun i => xs.1[i.val]'(by rw [hlen xs]; exact i.isLt)
      inj' := by
        intro i j he
        apply Fin.ext
        exact (hnd xs).getElem_inj_iff.mp he }
    left_inv := by
      intro f
      ext i
      simp
    right_inv := by
      intro xs
      apply Subtype.ext
      apply List.ext_getElem
      · simp [hlen xs]
      · intro i hi hi'
        simp }

theorem higherUTuples_length (m r : ℕ) : (higherUTuples m r).length=m.descFactorial r := by
  classical
  have hc := Fintype.card_congr (higherTupleEquiv m r)
  simp only [Fintype.card_coe,Fintype.card_embedding_eq,Fintype.card_fin] at hc
  rw [← List.toFinset_card_of_nodup (higherUTuples_nodup m r)]
  exact hc.symm

private theorem higher_fold_value_count {α R : Type} [AddMonoid R]
    (f : α → R) (xs : List α) (a : R×ℕ) :
    xs.foldl (fun a x => (a.1+f x,a.2+1)) a =
      (a.1+(xs.map f).sum,a.2+xs.length) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc,Nat.add_comm]

theorem higher_u_ordered_enumeration_and_cost :
    ∀ (m r : ℕ), (higherUTuples m r).Nodup ∧
    (higherUTuples m r).length=m.descFactorial r ∧
    (∀ xs : List (Fin m), xs∈higherUTuples m r ↔ xs.length=r ∧ xs.Nodup) ∧
    ∀ (X : Type) (h : List X→ℝ) (ω : Fin m→X),
    (higherUCounted m r h ω).2=m.descFactorial r ∧
    (higherUCounted m r h ω).1=((higherUTuples m r).map (fun xs=>h (xs.map ω))).sum/(m.descFactorial r:ℝ) := by
  intro m r
  refine ⟨higherUTuples_nodup m r,higherUTuples_length m r,higherUTuples_mem m r,?_⟩
  intro X h ω
  simp [higherUCounted,higher_fold_value_count,higherUTuples_length]

theorem higherUTuples_sum (m r : ℕ) (f : List (Fin m)→ℝ) :
    ((higherUTuples m r).map f).sum =
      ∑ a : Fin r ↪ Fin m,f (List.ofFn a) := by
  classical
  rw [← List.sum_toFinset f (higherUTuples_nodup m r)]
  have he := (higherTupleEquiv m r).sum_comp
    (fun xs : (higherUTuples m r).toFinset=>f xs.1)
  simpa only [Finset.sum_coe_sort,higherTupleEquiv] using! he.symm

private theorem higher_expect_list {Ω A : Type} [Fintype Ω] (w : Ω→ℝ)
    (xs : List A) (f : Ω→A→ℝ) :
    (∑ ω,w ω*(xs.map (f ω)).sum)=
      (xs.map (fun a=>∑ ω,w ω*f ω a)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib,ih]

private theorem higher_tuple_expect {X : Type} [Fintype X] (p : FinDist X)
    (m r : ℕ) (h : List X→ℝ) (xs : List (Fin m)) (hx : xs∈higherUTuples m r) :
    (∑ ω : Fin m→X,p.probOf ω*h (xs.map ω))=higherUMean p r h := by
  classical
  let f := (higherTupleEquiv m r).symm ⟨xs,List.mem_toFinset.mpr hx⟩
  have hf : List.ofFn f=xs :=
    congrArg Subtype.val ((higherTupleEquiv m r).apply_symm_apply ⟨xs,List.mem_toFinset.mpr hx⟩)
  have hmap (ω : Fin m→X) : List.ofFn (ω∘f)=xs.map ω := by
    rw [← List.map_ofFn,hf]
  have he := finite_pair_record_marginal p f f.injective (fun v=>h (List.ofFn v))
  simpa only [FinDist.probOf,hmap,higherUMean] using he

theorem higher_u_asymmetric_unbiased_and_empty :
    ∀ (X : Type) [Fintype X] (p : FinDist X) (m r : ℕ) (h : List X→ℝ),r ≤ m →
    (∑ ω : Fin m→X,p.probOf ω*(higherUCounted m r h ω).1)=higherUMean p r h ∧
    (∀ omega : Fin m→X,(higherUCounted m 0 h omega).2=1) := by
  intro X _ p m r h hr
  constructor
  · simp only [higherUCounted,higher_fold_value_count,zero_add,higherUTuples_length,
      ← mul_div_assoc]
    rw [← Finset.sum_div,higher_expect_list]
    have he : (higherUTuples m r).map (fun xs=>∑ ω : Fin m→X,p.probOf ω*h (xs.map ω))=
        (higherUTuples m r).map (fun _=>higherUMean p r h) :=
      List.map_congr_left (fun xs hx=>higher_tuple_expect p m r h xs hx)
    rw [he]
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,higherUTuples_length]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.descFactorial_pos.mpr hr).ne')
  · intro omega
    simp [higherUCounted,higherUTuples]

private theorem higher_embedding_coordinate_count (m r : ℕ) (hm : 0 < m)
    (j : Fin r) (i : Fin m) :
    (∑ f : Fin r ↪ Fin m,if f j=i then (1:ℝ) else 0)=(m.descFactorial r:ℝ)/(m:ℝ) := by
  classical
  let C : Fin m→ℝ := fun i=>∑ f : Fin r ↪ Fin m,if f j=i then (1:ℝ) else 0
  have hsame (i k : Fin m) : C i=C k := by
    let e := Equiv.embeddingCongr (Equiv.refl (Fin r)) (Equiv.swap i k)
    have heq (f : Fin r ↪ Fin m) : (e f) j=k ↔ f j=i := by
      change Equiv.swap i k (f j)=k ↔ f j=i
      constructor
      · intro he
        have hh := congrArg (Equiv.swap i k) he
        simpa using hh
      · intro he
        rw [he,Equiv.swap_apply_left]
    have he := e.sum_comp (fun f : Fin r ↪ Fin m=>if f j=k then (1:ℝ) else 0)
    simp_rw [heq] at he
    exact he
  have htotal : (∑ i : Fin m,C i)=(m.descFactorial r:ℝ) := by
    dsimp only [C]
    rw [Finset.sum_comm]
    simp [Fintype.card_embedding_eq]
  have hmul : (m:ℝ)*C i=(m.descFactorial r:ℝ) := by
    calc
      _ = ∑ k : Fin m,C i := by simp
      _ = ∑ k : Fin m,C k := Finset.sum_congr rfl (fun k _=>hsame i k)
      _ = _ := htotal
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  apply (eq_div_iff hmR.ne').mpr
  simpa only [mul_comm] using hmul

private theorem higher_embedding_overlap_count (m r : ℕ) (hm : 0 < m) :
    (∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,
      if ∃ i j,f i=g j then (1:ℝ) else 0) ≤
      (r:ℝ)^2*(m.descFactorial r:ℝ)^2/(m:ℝ) := by
  classical
  have hpoint (f g : Fin r ↪ Fin m) :
      (if ∃ i j,f i=g j then (1:ℝ) else 0) ≤
        ∑ i : Fin r,∑ j : Fin r,if f i=g j then (1:ℝ) else 0 := by
    by_cases hc : ∃ i j,f i=g j
    · rw [if_pos hc]
      obtain ⟨i,j,hij⟩ := hc
      calc
        1 = if f i=g j then (1:ℝ) else 0 := by simp [hij]
        _ ≤ ∑ j : Fin r,if f i=g j then (1:ℝ) else 0 :=
          Finset.single_le_sum (f:=fun j : Fin r=>if f i=g j then (1:ℝ) else 0)
            (fun _ _=>by (try dsimp only); split_ifs <;> norm_num) (Finset.mem_univ j)
        _ ≤ ∑ i : Fin r,∑ j : Fin r,if f i=g j then (1:ℝ) else 0 :=
          Finset.single_le_sum (f:=fun i : Fin r=>∑ j : Fin r,if f i=g j then (1:ℝ) else 0)
            (fun _ _=>Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num)) (Finset.mem_univ i)
    · rw [if_neg hc]
      exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num))
  have hinner (f : Fin r ↪ Fin m) :
      (∑ g : Fin r ↪ Fin m,∑ i : Fin r,∑ j : Fin r,if f i=g j then (1:ℝ) else 0)=
        (r:ℝ)^2*(m.descFactorial r:ℝ)/(m:ℝ) := by
    rw [Finset.sum_comm]
    have he (i j : Fin r) : (∑ g : Fin r ↪ Fin m,if f i=g j then (1:ℝ) else 0)=
        (m.descFactorial r:ℝ)/(m:ℝ) := by
      simpa only [eq_comm] using higher_embedding_coordinate_count m r hm j (f i)
    have hi (i : Fin r) :
        (∑ g : Fin r ↪ Fin m,∑ j : Fin r,if f i=g j then (1:ℝ) else 0)=
          (r:ℝ)*((m.descFactorial r:ℝ)/(m:ℝ)) := by
      rw [Finset.sum_comm]
      simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  calc
    _ ≤ ∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,
        ∑ i : Fin r,∑ j : Fin r,if f i=g j then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun f _=>Finset.sum_le_sum (fun g _=>hpoint f g))
    _ = _ := by
      simp only [hinner,Finset.sum_const,Finset.card_univ,Fintype.card_embedding_eq,
        Fintype.card_fin,nsmul_eq_mul]
      ring

private theorem higherUMean_abs_le {X : Type} [Fintype X] (p : FinDist X)
    (r : ℕ) (h : List X→ℝ) (B : ℝ) (hB : 0≤B)
    (hb : ∀ xs : List X,xs.length=r → |h xs|≤B) : |higherUMean p r h|≤B := by
  classical
  have hn (ω : Fin r→X) : 0≤p.probOf ω := Finset.prod_nonneg (fun _ _=>p.nonneg _)
  calc
    _ ≤ ∑ ω : Fin r→X,|p.probOf ω*h (List.ofFn ω)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω : Fin r→X,p.probOf ω*B := by
      apply Finset.sum_le_sum
      intro ω _
      rw [abs_mul,abs_of_nonneg (hn ω)]
      exact mul_le_mul_of_nonneg_left (hb _ List.length_ofFn) (hn ω)
    _ = B := by rw [← Finset.sum_mul,p.sum_probOf r,one_mul]

private theorem higher_center_mean {X : Type} [Fintype X] (p : FinDist X)
    (r : ℕ) (h : List X→ℝ) :
    (∑ v : Fin r→X,p.probOf v*(h (List.ofFn v)-higherUMean p r h))=0 := by
  classical
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,p.sum_probOf,one_mul]
  exact sub_self _

private theorem higher_disjoint_covariance {X : Type} [Fintype X] (p : FinDist X)
    (m r : ℕ) (h : List X→ℝ) (f g : Fin r ↪ Fin m)
    (hd : ∀ i j,f i≠g j) :
    (∑ ω : Fin m→X,p.probOf ω*
      ((h (List.ofFn (ω∘f))-higherUMean p r h)*
        (h (List.ofFn (ω∘g))-higherUMean p r h)))=0 := by
  classical
  let k : Fin r ⊕ Fin r→Fin m := Sum.elim f g
  have hk : Function.Injective k := by
    intro a b he
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (f.injective he)
      | inr j => exact False.elim (hd i j he)
    | inr i =>
      cases b with
      | inl j => exact False.elim (hd j i he.symm)
      | inr j => exact congrArg Sum.inr (g.injective he)
  let c : (Fin r→X)→ℝ := fun v=>h (List.ofFn v)-higherUMean p r h
  have he := finite_pair_record_marginal p k hk
    (fun v=>c (v∘Sum.inl)*c (v∘Sum.inr))
  change (∑ ω : Fin m→X,p.probOf ω*
      ((h (List.ofFn (ω∘f))-higherUMean p r h)*
        (h (List.ofFn (ω∘g))-higherUMean p r h)))=_ at he
  rw [he,← (Equiv.sumArrowEquivProdArrow (Fin r) (Fin r) X).symm.sum_comp,Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type,Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  change (∑ a : Fin r→X,∑ b : Fin r→X,
    (∏ i,p.prob (a i))*(∏ i,p.prob (b i))*(c a*c b))=0
  have hf : (∑ a : Fin r→X,∑ b : Fin r→X,
      (∏ i,p.prob (a i))*(∏ i,p.prob (b i))*(c a*c b))=
        (∑ a : Fin r→X,p.probOf a*c a)*(∑ b : Fin r→X,p.probOf b*c b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [FinDist.probOf]
    ring
  rw [hf,higher_center_mean p r h,zero_mul]

private theorem higher_covariance_le_overlap {X : Type} [Fintype X] (p : FinDist X)
    (m r : ℕ) (h : List X→ℝ) (B : ℝ) (hB : 0≤B)
    (hb : ∀ xs : List X,xs.length=r → |h xs|≤B) (f g : Fin r ↪ Fin m) :
    (∑ ω : Fin m→X,p.probOf ω*
      ((h (List.ofFn (ω∘f))-higherUMean p r h)*
        (h (List.ofFn (ω∘g))-higherUMean p r h))) ≤
      4*B^2*(if ∃ i j,f i=g j then (1:ℝ) else 0) := by
  classical
  by_cases hc : ∃ i j,f i=g j
  · rw [if_pos hc,mul_one]
    have hn (ω : Fin m→X) : 0≤p.probOf ω := Finset.prod_nonneg (fun _ _=>p.nonneg _)
    have hcenter (v : Fin r→X) : |h (List.ofFn v)-higherUMean p r h|≤2*B :=
      (abs_sub _ _).trans (by linarith [hb (List.ofFn v) List.length_ofFn,higherUMean_abs_le p r h B hB hb])
    calc
      _ ≤ ∑ ω : Fin m→X,p.probOf ω*(4*B^2) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hn ω)
        apply (le_abs_self _).trans
        rw [abs_mul]
        have hh := mul_le_mul (hcenter (ω∘f)) (hcenter (ω∘g)) (abs_nonneg _) (by positivity : 0≤2*B)
        nlinarith
      _ = _ := by rw [← Finset.sum_mul,p.sum_probOf m,one_mul]
  · have hd : ∀ i j,f i≠g j := by intro i j he; exact hc ⟨i,j,he⟩
    rw [if_neg hc,higher_disjoint_covariance p m r h f g hd,mul_zero]

private theorem higher_counted_embedding_mean {X : Type} (m r : ℕ)
    (h : List X→ℝ) (ω : Fin m→X) :
    (higherUCounted m r h ω).1=
      (∑ f : Fin r ↪ Fin m,h (List.ofFn (ω∘f)))/(m.descFactorial r:ℝ) := by
  rw [(higher_u_ordered_enumeration_and_cost m r).2.2.2 X h ω |>.2,higherUTuples_sum]
  simp only [List.map_ofFn]

theorem higher_u_overlap_covariance_and_variance :
    ∀ (X : Type) [Fintype X] (p : FinDist X) (m r : ℕ) (h : List X→ℝ) (B : ℝ),
    0 < m → r ≤ m → 0≤B → (∀ xs : List X,xs.length=r → |h xs|≤B) →
    (∑ ω : Fin m→X,p.probOf ω*((higherUCounted m r h ω).1-higherUMean p r h)^2)
      ≤4*(r:ℝ)^2*B^2/m := by
  intro X _ p m r h B hm hr hB hb
  classical
  let N : ℝ := m.descFactorial r
  let μ := higherUMean p r h
  let c : (Fin m→X)→(Fin r ↪ Fin m)→ℝ := fun ω f=>h (List.ofFn (ω∘f))-μ
  let C : (Fin r ↪ Fin m)→(Fin r ↪ Fin m)→ℝ :=
    fun f g=>∑ ω : Fin m→X,p.probOf ω*(c ω f*c ω g)
  have hN : 0<N := by
    change 0<(m.descFactorial r:ℝ)
    exact_mod_cast Nat.descFactorial_pos.mpr hr
  have hcenter (ω : Fin m→X) : (higherUCounted m r h ω).1-μ=(∑ f : Fin r ↪ Fin m,c ω f)/N := by
    rw [higher_counted_embedding_mean]
    simp only [c,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_embedding_eq,Fintype.card_fin,nsmul_eq_mul]
    change (∑ f : Fin r ↪ Fin m,h (List.ofFn (ω∘f)))/N-μ=
      ((∑ f : Fin r ↪ Fin m,h (List.ofFn (ω∘f)))-N*μ)/N
    field_simp
  have hvar : (∑ ω : Fin m→X,p.probOf ω*((higherUCounted m r h ω).1-μ)^2)=
      (∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,C f g)/N^2 := by
    simp only [hcenter,div_pow,← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    have hexpand (ω : Fin m→X) : (∑ f : Fin r ↪ Fin m,c ω f)^2=
        ∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,c ω f*c ω g := by
      rw [pow_two,Finset.sum_mul_sum]
    simp_rw [hexpand,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.sum_comm]
  have hsum : (∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,C f g) ≤
      4*B^2*((r:ℝ)^2*N^2/(m:ℝ)) := by
    calc
      _ ≤ ∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,
          4*B^2*(if ∃ i j,f i=g j then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun f _=>Finset.sum_le_sum
          (fun g _=>higher_covariance_le_overlap p m r h B hB hb f g))
      _ = 4*B^2*(∑ f : Fin r ↪ Fin m,∑ g : Fin r ↪ Fin m,
          if ∃ i j,f i=g j then (1:ℝ) else 0) := by simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (higher_embedding_overlap_count m r hm) (by positivity)
  change (∑ ω : Fin m→X,p.probOf ω*((higherUCounted m r h ω).1-μ)^2) ≤ _
  rw [hvar]
  calc
    _ ≤ (4*B^2*((r:ℝ)^2*N^2/(m:ℝ)))/N^2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg N)
    _ = _ := by field_simp

private theorem higher_list_sum_cast (xs : List ℚ) :
    (xs.sum:ℝ)=(xs.map (fun q : ℚ=>(q:ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Rat.cast_add,ih]

theorem higherUCountedQ_cast {X : Type} (m r : ℕ) (h : List X→ℚ) (ω : Fin m→X) :
    ((higherUCountedQ m r h ω).1:ℝ)=(higherUCounted m r (fun xs=>(h xs:ℝ)) ω).1 ∧
      (higherUCountedQ m r h ω).2=m.descFactorial r := by
  simp only [higherUCountedQ,higherUCounted,higher_fold_value_count,zero_add,
    Rat.cast_div,Rat.cast_natCast,higher_list_sum_cast,List.map_map,Function.comp_def,
    higherUTuples_length]
  simp

private theorem higher_finite_chebyshev {Ω : Type} [Fintype Ω]
    (w f : Ω→ℝ) (μ V eps : ℝ) (hw : ∀ ω,0≤w ω) (heps : 0<eps)
    (hv : (∑ ω,w ω*(f ω-μ)^2)≤V) :
    (∑ ω∈Finset.univ.filter (fun ω=>eps≤|f ω-μ|),w ω)≤V/eps^2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos heps)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ ω∈Finset.univ.filter (fun ω=>eps≤|f ω-μ|),w ω*(f ω-μ)^2 := by
      apply Finset.sum_le_sum
      intro ω hω
      have he := (Finset.mem_filter.mp hω).2
      have hs : eps^2≤(f ω-μ)^2 := by nlinarith [sq_abs (f ω-μ),abs_nonneg (f ω-μ)]
      exact mul_le_mul_of_nonneg_left hs (hw ω)
    _ ≤ ∑ ω,w ω*(f ω-μ)^2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun ω _ _=>mul_nonneg (hw ω) (sq_nonneg _))
    _ ≤ V := hv

theorem higher_u_same_records_tail_and_rational_fold :
    ∀ (X : Type) [Fintype X] (p : FinDist X) (m r : ℕ) (h : List X→ℚ) (B eps : ℝ),
    0 < m → r ≤ m → 0≤B → 0<eps → (∀ xs : List X,xs.length=r → |(h xs:ℝ)|≤B) →
    (∀ ω : Fin m→X,((higherUCountedQ m r h ω).1:ℝ)=
      (higherUCounted m r (fun xs=>(h xs:ℝ)) ω).1 ∧ (higherUCountedQ m r h ω).2=m.descFactorial r) ∧
    (∑ ω∈Finset.univ.filter (fun ω : Fin m→X=>eps≤
      |((higherUCountedQ m r h ω).1:ℝ)-higherUMean p r (fun xs=>(h xs:ℝ))|),p.probOf ω)
      ≤4*(r:ℝ)^2*B^2/(m*eps^2) := by
  intro X _ p m r h B eps hm hr hB heps hb
  classical
  refine ⟨higherUCountedQ_cast m r h,?_⟩
  have hv := higher_u_overlap_covariance_and_variance X p m r (fun xs=>(h xs:ℝ)) B hm hr hB hb
  have hh := higher_finite_chebyshev (fun ω : Fin m→X=>p.probOf ω)
    (fun ω=>(higherUCounted m r (fun xs=>(h xs:ℝ)) ω).1)
    (higherUMean p r (fun xs=>(h xs:ℝ))) (4*(r:ℝ)^2*B^2/m) eps
    (fun ω=>Finset.prod_nonneg (fun _ _=>p.nonneg _)) heps hv
  have hc (ω : Fin m→X) := (higherUCountedQ_cast m r h ω).1
  simpa only [hc,div_div] using hh

end Qatlib.Concepts.ShadowModels.UStatBackend
