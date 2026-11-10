/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ShadowModels.UStatBackend

namespace Qatlib.Papers.ClassShadows20.HigherMoments
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev TripleIndex (m : ℕ) := Fin m × Fin m × Fin m

def tripleIndexList : (m : ℕ) → List (TripleIndex m)
  | 0 => []
  | m+1 => (tripleIndexList m).map (fun t =>
      (t.1.castSucc,t.2.1.castSucc,t.2.2.castSucc)) ++
      (pairIndexList m).map (fun q => (q.1.castSucc,q.2.castSucc,Fin.last m))

noncomputable def tripleKernelMean {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, p.prob x*p.prob y*p.prob z*h x y z

def tripleKernelSymmetric {X : Type} (h : X → X → X → ℝ) : Prop :=
  ∀ x y z, h x y z = h y x z ∧ h x y z = h x z y

noncomputable def tripleOverlapOne {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → X → ℝ) : ℝ :=
  ∑ x, p.prob x*((∑ y, ∑ z, p.prob y*p.prob z*h x y z)-tripleKernelMean p h)^2
noncomputable def tripleOverlapTwo {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, p.prob x*p.prob y*((∑ z, p.prob z*h x y z)-tripleKernelMean p h)^2
noncomputable def tripleOverlapThree {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, p.prob x*p.prob y*p.prob z*(h x y z-tripleKernelMean p h)^2

noncomputable def tripleVarianceBudget {X : Type} [Fintype X] (p : FinDist X)
    (m : ℕ) (h : X → X → X → ℝ) : ℝ :=
  (3*((m-3).choose 2):ℝ)/(m.choose 3:ℝ)*tripleOverlapOne p h +
  (3*(m-3):ℝ)/(m.choose 3:ℝ)*tripleOverlapTwo p h +
  (1:ℝ)/(m.choose 3:ℝ)*tripleOverlapThree p h

noncomputable def tripleUStatistic {X : Type} {m : ℕ} (h : X → X → X → ℝ)
    (ω : Fin m → X) : ℝ :=
  ((tripleIndexList m).map (fun t => h (ω t.1) (ω t.2.1) (ω t.2.2))).sum/(m.choose 3:ℝ)

noncomputable def tripleUCounted {X : Type} {m : ℕ} (h : X → X → X → ℝ)
    (ω : Fin m → X) : ℝ × ℕ :=
  let a := (tripleIndexList m).foldl
    (fun a t => (a.1+h (ω t.1) (ω t.2.1) (ω t.2.2),a.2+1)) (0,0)
  (a.1/(m.choose 3:ℝ),a.2)

theorem tripleIndexList_ordered (m : ℕ) (t : TripleIndex m)
    (ht : t ∈ tripleIndexList m) : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
  induction m with
  | zero => simp [tripleIndexList] at ht
  | succ m ih =>
    simp only [tripleIndexList, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · exact ih q hq
    · exact ⟨pairIndexList_ordered m q hq, q.2.isLt⟩

theorem tripleIndexList_length (m : ℕ) : (tripleIndexList m).length = m.choose 3 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [tripleIndexList, List.length_append, List.length_map, ih, pairIndexList_length]
    rw [Nat.choose_succ_succ]
    exact Nat.add_comm _ _

theorem tripleIndexList_nodup (m : ℕ) : (tripleIndexList m).Nodup := by
  induction m with
  | zero => simp [tripleIndexList]
  | succ m ih =>
    rw [tripleIndexList, List.nodup_append]
    refine ⟨List.Nodup.map ?_ ih, List.Nodup.map ?_ (pairIndexList_nodup m), ?_⟩
    · intro a b hab
      apply Prod.ext
      · exact Fin.castSucc_inj.mp (congrArg (fun t => t.1) hab)
      · apply Prod.ext
        · exact Fin.castSucc_inj.mp (congrArg (fun t => t.2.1) hab)
        · exact Fin.castSucc_inj.mp (congrArg (fun t => t.2.2) hab)
    · intro a b hab
      exact Prod.ext (Fin.castSucc_inj.mp (congrArg (fun t => t.1) hab))
        (Fin.castSucc_inj.mp (congrArg (fun t => t.2.1) hab))
    · intro a ha b hb hab
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
      exact Fin.castSucc_ne_last _ (congrArg (fun t => t.2.2) hab)

private theorem pair_mem_of_ordered (m : ℕ) (i j : Fin m) (hij : i < j) :
    (i,j) ∈ pairIndexList m := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    revert hij
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> intro hij
      · exact False.elim (lt_irrefl _ hij)
      · simp [pairIndexList]
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> intro hij
      · have := j.isLt; simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hij; omega
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨(i,j),ih i j hij,rfl⟩

theorem tripleIndexList_mem_iff (m : ℕ) (t : TripleIndex m) :
    t ∈ tripleIndexList m ↔ t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
  refine ⟨tripleIndexList_ordered m t, ?_⟩
  rcases t with ⟨i,j,k⟩
  intro ht
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    revert ht
    refine Fin.lastCases ?_ (fun k => ?_) k
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro ht; exact False.elim (lt_irrefl _ ht.2)
      · refine Fin.lastCases ?_ (fun i => ?_) i <;> intro ht
        · have := j.isLt; simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at ht; omega
        · exact List.mem_append_right _ (List.mem_map.mpr
            ⟨(i,j),pair_mem_of_ordered m i j ht.1,rfl⟩)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro ht; have := k.isLt; simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at ht; omega
      · refine Fin.lastCases ?_ (fun i => ?_) i <;> intro ht
        · have := j.isLt; simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at ht; omega
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨(i,j,k),ih i j k ht,rfl⟩)

private theorem triple_fold_value_count {T : Type} (f : T → ℝ)
    (ts : List T) (a : ℝ × ℕ) :
    ts.foldl (fun a t => (a.1+f t,a.2+1)) a =
      (a.1+(ts.map f).sum,a.2+ts.length) := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih => simp [ih, add_assoc, Nat.add_comm]

theorem triple_u_enumeration_and_actual_cost (m : ℕ) :
    (tripleIndexList m).Nodup ∧ (tripleIndexList m).length=m.choose 3 ∧
    (∀ t, t ∈ tripleIndexList m ↔ t.1<t.2.1 ∧ t.2.1<t.2.2) ∧
    ∀ (X : Type) (h : X → X → X → ℝ) (ω : Fin m → X),
      (tripleUCounted h ω).1=tripleUStatistic h ω ∧ (tripleUCounted h ω).2=m.choose 3 := by
  refine ⟨tripleIndexList_nodup m,tripleIndexList_length m,tripleIndexList_mem_iff m,?_⟩
  intro X h ω
  simp [tripleUCounted,triple_fold_value_count,tripleUStatistic,tripleIndexList_length]

private theorem triple_expect_three {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : X → X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω*h (ω i) (ω j) (ω k) = tripleKernelMean p h := by
  classical
  let f : Fin 3 → Fin m := ![i,j,k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  have he := finite_pair_record_marginal p f hf (fun v => h (v 0) (v 1) (v 2))
  change (∑ ω : Fin m → X, p.probOf ω*h (ω i) (ω j) (ω k)) = _ at he
  rw [he, ← (Fin.consEquiv (fun _ : Fin 3 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  unfold tripleKernelMean
  apply Finset.sum_congr rfl
  intro x _
  rw [← (finTwoArrowEquiv X).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv,mul_assoc]

private theorem triple_expect_list {Ω T : Type} [Fintype Ω] (w : Ω → ℝ)
    (ts : List T) (f : Ω → T → ℝ) :
    ∑ ω, w ω*(ts.map (f ω)).sum = (ts.map (fun t => ∑ ω, w ω*f ω t)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib,ih]

theorem triple_u_actual_unbiased (X : Type) [Fintype X] (p : FinDist X) (m : ℕ)
    (h : X → X → X → ℝ) (hm : 3 ≤ m) :
    (∑ ω : Fin m → X, p.probOf ω*tripleUStatistic h ω)=tripleKernelMean p h := by
  classical
  simp only [tripleUStatistic, ← mul_div_assoc]
  rw [← Finset.sum_div,triple_expect_list]
  have he : (tripleIndexList m).map (fun t =>
      ∑ ω : Fin m → X, p.probOf ω*h (ω t.1) (ω t.2.1) (ω t.2.2)) =
      (tripleIndexList m).map (fun _ => tripleKernelMean p h) := by
    apply List.map_congr_left
    intro t ht
    obtain ⟨hij,hjk⟩ := tripleIndexList_ordered m t ht
    exact triple_expect_three p _ _ _ (ne_of_lt hij) (ne_of_lt (hij.trans hjk)) (ne_of_lt hjk) h
  rw [he]
  simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,tripleIndexList_length]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.choose_pos hm).ne')

private theorem triple_expect_4 {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (f : Fin 4 → Fin m) (hf : Function.Injective f) (g : X → X → X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω*g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3)) =
      ∑ x, ∑ y, ∑ z, ∑ u, p.prob x*p.prob y*p.prob z*p.prob u*g x y z u := by
  classical
  have he := finite_pair_record_marginal p f hf (fun v => g (v 0) (v 1) (v 2) (v 3))
  change (∑ ω : Fin m → X, p.probOf ω*g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3))) = _ at he
  rw [he]
  rw [← (Fin.consEquiv (fun _ : Fin 4 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro x _
  rw [← (Fin.consEquiv (fun _ : Fin 3 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro y _
  rw [← (finTwoArrowEquiv X).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv, Fin.consEquiv, Fin.cons, Fin.cases, mul_assoc]
  rfl

private theorem triple_expect_5 {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (f : Fin 5 → Fin m) (hf : Function.Injective f) (g : X → X → X → X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω*g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3)) (ω (f 4)) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, p.prob x*p.prob y*p.prob z*p.prob u*p.prob v*g x y z u v := by
  classical
  have he := finite_pair_record_marginal p f hf (fun v => g (v 0) (v 1) (v 2) (v 3) (v 4))
  change (∑ ω : Fin m → X, p.probOf ω*g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3)) (ω (f 4))) = _ at he
  rw [he]
  rw [← (Fin.consEquiv (fun _ : Fin 5 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro x _
  rw [← (Fin.consEquiv (fun _ : Fin 4 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro y _
  rw [← (Fin.consEquiv (fun _ : Fin 3 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro z _
  rw [← (finTwoArrowEquiv X).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv, Fin.consEquiv, Fin.cons, Fin.cases, mul_assoc]
  rfl

private theorem triple_expect_6 {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (f : Fin 6 → Fin m) (hf : Function.Injective f) (g : X → X → X → X → X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω*g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3)) (ω (f 4)) (ω (f 5)) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, p.prob x*p.prob y*p.prob z*p.prob u*p.prob v*p.prob w*g x y z u v w := by
  classical
  have he := finite_pair_record_marginal p f hf (fun v => g (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
  change (∑ ω : Fin m → X,
      p.probOf ω*g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3)) (ω (f 4)) (ω (f 5))) = _ at he
  rw [he]
  rw [← (Fin.consEquiv (fun _ : Fin 6 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro x _
  rw [← (Fin.consEquiv (fun _ : Fin 5 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro y _
  rw [← (Fin.consEquiv (fun _ : Fin 4 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro z _
  rw [← (Fin.consEquiv (fun _ : Fin 3 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro u _
  rw [← (finTwoArrowEquiv X).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv, Fin.consEquiv, Fin.cons, Fin.cases, mul_assoc]
  rfl

theorem triple_shared_two_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → X → ℝ) (f : Fin 4 → Fin m) (hf : Function.Injective f) :
    (∑ ω : Fin m → X, p.probOf ω*
      ((h (ω (f 0)) (ω (f 1)) (ω (f 2))-tripleKernelMean p h)*
       (h (ω (f 0)) (ω (f 1)) (ω (f 3))-tripleKernelMean p h))) = tripleOverlapTwo p h := by
  classical
  rw [triple_expect_4 p f hf
    (fun x y z w => (h x y z-tripleKernelMean p h)*(h x y w-tripleKernelMean p h))]
  unfold tripleOverlapTwo
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hm : ∑ z, p.prob z*(h x y z-tripleKernelMean p h) =
      (∑ z, p.prob z*h x y z)-tripleKernelMean p h := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,p.sum_one,one_mul]
  calc
    _ = p.prob x*p.prob y*(∑ z, p.prob z*(h x y z-tripleKernelMean p h))^2 := by
      rw [pow_two,Finset.sum_mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [hm]

theorem triple_shared_one_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → X → ℝ) (f : Fin 5 → Fin m) (hf : Function.Injective f) :
    (∑ ω : Fin m → X, p.probOf ω*
      ((h (ω (f 0)) (ω (f 1)) (ω (f 2))-tripleKernelMean p h)*
       (h (ω (f 0)) (ω (f 3)) (ω (f 4))-tripleKernelMean p h))) = tripleOverlapOne p h := by
  classical
  rw [triple_expect_5 p f hf
    (fun x y z u v => (h x y z-tripleKernelMean p h)*(h x u v-tripleKernelMean p h))]
  unfold tripleOverlapOne
  apply Finset.sum_congr rfl
  intro x _
  have hm : ∑ y, ∑ z, p.prob y*p.prob z*(h x y z-tripleKernelMean p h) =
      (∑ y, ∑ z, p.prob y*p.prob z*h x y z)-tripleKernelMean p h := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
      p.sum_one,one_mul,mul_one]
  calc
    _ = p.prob x*(∑ y, ∑ z, p.prob y*p.prob z*(h x y z-tripleKernelMean p h))^2 := by
      rw [pow_two,Finset.sum_mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by rw [hm]

private theorem triple_center_mean {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → X → ℝ) :
    tripleKernelMean p (fun x y z => h x y z-tripleKernelMean p h) = 0 := by
  classical
  unfold tripleKernelMean
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
    p.sum_one,one_mul,mul_one,sub_self]

theorem triple_disjoint_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → X → ℝ) (f : Fin 6 → Fin m) (hf : Function.Injective f) :
    (∑ ω : Fin m → X, p.probOf ω*
      ((h (ω (f 0)) (ω (f 1)) (ω (f 2))-tripleKernelMean p h)*
       (h (ω (f 3)) (ω (f 4)) (ω (f 5))-tripleKernelMean p h))) = 0 := by
  classical
  rw [triple_expect_6 p f hf
    (fun x y z u v w => (h x y z-tripleKernelMean p h)*(h u v w-tripleKernelMean p h))]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro z _
  calc
    _ = (p.prob x*p.prob y*p.prob z*(h x y z-tripleKernelMean p h))*
        tripleKernelMean p (fun u v w => h u v w-tripleKernelMean p h) := by
      unfold tripleKernelMean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 0 := by rw [triple_center_mean,mul_zero]

theorem triple_same_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → X → ℝ) (t : TripleIndex m) (ht : t ∈ tripleIndexList m) :
    (∑ ω : Fin m → X, p.probOf ω*(h (ω t.1) (ω t.2.1) (ω t.2.2)-tripleKernelMean p h)^2) =
      tripleOverlapThree p h := by
  obtain ⟨hij,hjk⟩ := tripleIndexList_ordered m t ht
  exact triple_expect_three p _ _ _ (ne_of_lt hij) (ne_of_lt (hij.trans hjk)) (ne_of_lt hjk)
    (fun x y z => (h x y z-tripleKernelMean p h)^2)

private def tripleCoordinates {m : ℕ} (t : TripleIndex m) : Finset (Fin m) :=
  {t.1,t.2.1,t.2.2}

private theorem tripleCoordinates_card {m : ℕ} (t : TripleIndex m)
    (ht : t ∈ tripleIndexList m) : (tripleCoordinates t).card = 3 := by
  obtain ⟨hij,hjk⟩ := tripleIndexList_ordered m t ht
  simp [tripleCoordinates, ne_of_lt hij, ne_of_lt hjk, ne_of_lt (hij.trans hjk)]

private theorem tripleCoordinates_sort {m : ℕ} (t : TripleIndex m)
    (ht : t ∈ tripleIndexList m) :
    (tripleCoordinates t).sort (· ≤ ·) = [t.1,t.2.1,t.2.2] := by
  obtain ⟨hij,hjk⟩ := tripleIndexList_ordered m t ht
  have hn : [t.1,t.2.1,t.2.2].Nodup := by
    simp [ne_of_lt hij, ne_of_lt hjk, ne_of_lt (hij.trans hjk)]
  have hp : [t.1,t.2.1,t.2.2].Pairwise (· ≤ ·) := by
    simp [hij.le,hjk.le,(hij.trans hjk).le]
  simpa [tripleCoordinates] using (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp

private theorem tripleCoordinates_injective {m : ℕ} :
    Set.InjOn (@tripleCoordinates m) ↑(tripleIndexList m).toFinset := by
  intro a ha b hb hab
  have he := congrArg (fun s : Finset (Fin m) => s.sort (· ≤ ·)) hab
  (try dsimp only at he)
  rw [tripleCoordinates_sort a (List.mem_toFinset.mp ha),
    tripleCoordinates_sort b (List.mem_toFinset.mp hb)] at he
  have he' : a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2 := by simpa using he
  exact Prod.ext he'.1 (Prod.ext he'.2.1 he'.2.2)

private theorem tripleCoordinates_image (m : ℕ) :
    (tripleIndexList m).toFinset.image tripleCoordinates =
      (Finset.univ : Finset (Fin m)).powersetCard 3 := by
  classical
  ext s
  constructor
  · rintro hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      tripleCoordinates_card t (List.mem_toFinset.mp ht)⟩
  · intro hs
    have hcard := (Finset.mem_powersetCard.mp hs).2
    let f := s.orderEmbOfFin hcard
    have ht : (f 0,f 1,f 2) ∈ tripleIndexList m :=
      (tripleIndexList_mem_iff m _).mpr
        ⟨f.strictMono (by decide),f.strictMono (by decide)⟩
    refine Finset.mem_image.mpr ⟨(f 0,f 1,f 2),List.mem_toFinset.mpr ht,?_⟩
    have he := s.image_orderEmbOfFin_univ hcard
    simpa [tripleCoordinates,Fin.univ_succ,f] using he

private theorem triple_incidence_count (m : ℕ) (s : Finset (Fin m)) (hs : s.card ≤ 3) :
    ((tripleIndexList m).toFinset.filter (fun t => s ⊆ tripleCoordinates t)).card =
      (m-s.card).choose (3-s.card) := by
  classical
  have he : ((tripleIndexList m).toFinset.filter (fun t => s ⊆ tripleCoordinates t)).image
      tripleCoordinates = ((Finset.univ : Finset (Fin m)).powersetCard 3).filter (s ⊆ ·) := by
    rw [← tripleCoordinates_image]
    ext t
    simp only [Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨a,⟨ha,hsa⟩,rfl⟩
      exact ⟨⟨a,ha,rfl⟩,hsa⟩
    · rintro ⟨⟨a,ha,rfl⟩,hsa⟩
      exact ⟨a,⟨ha,hsa⟩,rfl⟩
  rw [← Finset.card_image_of_injOn (tripleCoordinates_injective.mono (Finset.filter_subset _ _)),he]
  simpa using Finset.card_filter_powersetCard_subset s Finset.univ 3 (Finset.subset_univ _) hs

private theorem triple_covariance_incidence {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → X → ℝ) (hsym : tripleKernelSymmetric h)
    (i j k u v w : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (∑ ω : Fin m → X, p.probOf ω *
      ((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*
       (h (ω u) (ω v) (ω w)-tripleKernelMean p h))) =
    tripleOverlapOne p h *
      ((if i ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0)+
       (if j ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0)+
       (if k ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0)) +
    (tripleOverlapTwo p h-2*tripleOverlapOne p h) *
      ((if i ∈ ({u,v,w} : Finset (Fin m)) ∧ j ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0)+
       (if i ∈ ({u,v,w} : Finset (Fin m)) ∧ k ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0)+
       (if j ∈ ({u,v,w} : Finset (Fin m)) ∧ k ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0)) +
    (tripleOverlapThree p h-3*tripleOverlapTwo p h+3*tripleOverlapOne p h) *
      (if i ∈ ({u,v,w} : Finset (Fin m)) ∧ j ∈ ({u,v,w} : Finset (Fin m)) ∧
          k ∈ ({u,v,w} : Finset (Fin m)) then 1 else 0) := by
  classical
  by_cases hui : u = i
  · subst u
    by_cases hvi : v = i
    · subst v
      contradiction
    · by_cases hvj : v = j
      · subst v
        by_cases hwi : w = i
        · subst w
          contradiction
        · by_cases hwj : w = j
          · subst w
            contradiction
          · by_cases hwk : w = k
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn12 : j ≠ k := by omega
              simp only [← pow_two]
              rw [triple_expect_three p i j k hij hik hjk (fun x y z => (h x y z-tripleKernelMean p h)^2)]
              change tripleOverlapThree p h = _
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, hn02,
                  Ne.symm hn02, hn12, Ne.symm hn12, or_false, or_true, and_true, ite_true, mul_one]
              ring
            · have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn03 : i ≠ w := by omega
              have hn12 : j ≠ k := by omega
              have hn13 : j ≠ w := by omega
              have hn23 : k ≠ w := by omega
              have hf : Function.Injective (![i,j,k,w] : Fin 4 → Fin m) := by
                intro a b hab
                fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
              have hc := triple_shared_two_covariance p h ![i,j,k,w] hf
              change (∑ ω : Fin m → X,
                  p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω j) (ω w)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
              rw [hc]
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, Ne.symm hn02,
                  hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]
              ring
      · by_cases hvk : v = k
        · subst v
          by_cases hwi : w = i
          · subst w
            contradiction
          · by_cases hwj : w = j
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn12 : j ≠ k := by omega
              have he₂ (ω : Fin m → X) : h (ω i) (ω k) (ω j) = h (ω i) (ω j) (ω k) :=
                  (hsym (ω i) (ω k) (ω j)).2
              simp_rw [he₂]
              simp only [← pow_two]
              rw [triple_expect_three p i j k hij hik hjk (fun x y z => (h x y z-tripleKernelMean p h)^2)]
              change tripleOverlapThree p h = _
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, hn02,
                  Ne.symm hn02, hn12, Ne.symm hn12, or_false, or_true, and_true, ite_true, mul_one]
              ring
            · by_cases hwk : w = k
              · subst w
                contradiction
              · have hn01 : i ≠ k := by omega
                have hn02 : i ≠ j := by omega
                have hn03 : i ≠ w := by omega
                have hn12 : k ≠ j := by omega
                have hn13 : k ≠ w := by omega
                have hn23 : j ≠ w := by omega
                have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω i) (ω k) (ω j) :=
                    (hsym (ω i) (ω j) (ω k)).2
                simp_rw [he₁]
                have hf : Function.Injective (![i,k,j,w] : Fin 4 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_two_covariance p h ![i,k,j,w] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω k) (ω j)-tripleKernelMean p h)*(h (ω i) (ω k) (ω w)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                    Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                ring
        · by_cases hwi : w = i
          · subst w
            contradiction
          · by_cases hwj : w = j
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn03 : i ≠ v := by omega
              have hn12 : j ≠ k := by omega
              have hn13 : j ≠ v := by omega
              have hn23 : k ≠ v := by omega
              have he₂ (ω : Fin m → X) : h (ω i) (ω v) (ω j) = h (ω i) (ω j) (ω v) :=
                  (hsym (ω i) (ω v) (ω j)).2
              simp_rw [he₂]
              have hf : Function.Injective (![i,j,k,v] : Fin 4 → Fin m) := by
                intro a b hab
                fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
              have hc := triple_shared_two_covariance p h ![i,j,k,v] hf
              change (∑ ω : Fin m → X,
                  p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω j) (ω v)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
              rw [hc]
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, Ne.symm hn02,
                  hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]
              ring
            · by_cases hwk : w = k
              · subst w
                have hn01 : i ≠ k := by omega
                have hn02 : i ≠ j := by omega
                have hn03 : i ≠ v := by omega
                have hn12 : k ≠ j := by omega
                have hn13 : k ≠ v := by omega
                have hn23 : j ≠ v := by omega
                have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω i) (ω k) (ω j) :=
                    (hsym (ω i) (ω j) (ω k)).2
                have he₂ (ω : Fin m → X) : h (ω i) (ω v) (ω k) = h (ω i) (ω k) (ω v) :=
                    (hsym (ω i) (ω v) (ω k)).2
                simp_rw [he₁]
                simp_rw [he₂]
                have hf : Function.Injective (![i,k,j,v] : Fin 4 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_two_covariance p h ![i,k,j,v] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω k) (ω j)-tripleKernelMean p h)*(h (ω i) (ω k) (ω v)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                    Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                ring
              · have hn01 : i ≠ j := by omega
                have hn02 : i ≠ k := by omega
                have hn03 : i ≠ v := by omega
                have hn04 : i ≠ w := by omega
                have hn12 : j ≠ k := by omega
                have hn13 : j ≠ v := by omega
                have hn14 : j ≠ w := by omega
                have hn23 : k ≠ v := by omega
                have hn24 : k ≠ w := by omega
                have hn34 : v ≠ w := by omega
                have hf : Function.Injective (![i,j,k,v,w] : Fin 5 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_one_covariance p h ![i,j,k,v,w] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω v) (ω w)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                    hn03, hn04, hn13, hn14, hn23, hn24, or_false, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]

  · by_cases huj : u = j
    · subst u
      by_cases hvi : v = i
      · subst v
        by_cases hwi : w = i
        · subst w
          contradiction
        · by_cases hwj : w = j
          · subst w
            contradiction
          · by_cases hwk : w = k
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn12 : j ≠ k := by omega
              have he₂ (ω : Fin m → X) : h (ω j) (ω i) (ω k) = h (ω i) (ω j) (ω k) :=
                  (hsym (ω j) (ω i) (ω k)).1
              simp_rw [he₂]
              simp only [← pow_two]
              rw [triple_expect_three p i j k hij hik hjk (fun x y z => (h x y z-tripleKernelMean p h)^2)]
              change tripleOverlapThree p h = _
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, hn02,
                  Ne.symm hn02, hn12, Ne.symm hn12, or_false, or_true, and_true, ite_true, mul_one]
              ring
            · have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn03 : i ≠ w := by omega
              have hn12 : j ≠ k := by omega
              have hn13 : j ≠ w := by omega
              have hn23 : k ≠ w := by omega
              have he₂ (ω : Fin m → X) : h (ω j) (ω i) (ω w) = h (ω i) (ω j) (ω w) :=
                  (hsym (ω j) (ω i) (ω w)).1
              simp_rw [he₂]
              have hf : Function.Injective (![i,j,k,w] : Fin 4 → Fin m) := by
                intro a b hab
                fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
              have hc := triple_shared_two_covariance p h ![i,j,k,w] hf
              change (∑ ω : Fin m → X,
                  p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω j) (ω w)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
              rw [hc]
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, Ne.symm hn02,
                  hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]
              ring
      · by_cases hvj : v = j
        · subst v
          contradiction
        · by_cases hvk : v = k
          · subst v
            by_cases hwi : w = i
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn12 : j ≠ k := by omega
              have he₂ (ω : Fin m → X) : h (ω j) (ω k) (ω i) = h (ω i) (ω j) (ω k) :=
                  ((hsym (ω j) (ω k) (ω i)).2).trans ((hsym (ω j) (ω i) (ω k)).1)
              simp_rw [he₂]
              simp only [← pow_two]
              rw [triple_expect_three p i j k hij hik hjk (fun x y z => (h x y z-tripleKernelMean p h)^2)]
              change tripleOverlapThree p h = _
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, hn02,
                  Ne.symm hn02, hn12, Ne.symm hn12, or_false, or_true, and_true, ite_true, mul_one]
              ring
            · by_cases hwj : w = j
              · subst w
                contradiction
              · by_cases hwk : w = k
                · subst w
                  contradiction
                · have hn01 : j ≠ k := by omega
                  have hn02 : j ≠ i := by omega
                  have hn03 : j ≠ w := by omega
                  have hn12 : k ≠ i := by omega
                  have hn13 : k ≠ w := by omega
                  have hn23 : i ≠ w := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω k) (ω i) :=
                      ((hsym (ω i) (ω j) (ω k)).1).trans ((hsym (ω j) (ω i) (ω k)).2)
                  simp_rw [he₁]
                  have hf : Function.Injective (![j,k,i,w] : Fin 4 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_two_covariance p h ![j,k,i,w] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω k) (ω i)-tripleKernelMean p h)*(h (ω j) (ω k) (ω w)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                      Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                  ring
          · by_cases hwi : w = i
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn03 : i ≠ v := by omega
              have hn12 : j ≠ k := by omega
              have hn13 : j ≠ v := by omega
              have hn23 : k ≠ v := by omega
              have he₂ (ω : Fin m → X) : h (ω j) (ω v) (ω i) = h (ω i) (ω j) (ω v) :=
                  ((hsym (ω j) (ω v) (ω i)).2).trans ((hsym (ω j) (ω i) (ω v)).1)
              simp_rw [he₂]
              have hf : Function.Injective (![i,j,k,v] : Fin 4 → Fin m) := by
                intro a b hab
                fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
              have hc := triple_shared_two_covariance p h ![i,j,k,v] hf
              change (∑ ω : Fin m → X,
                  p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω j) (ω v)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
              rw [hc]
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, Ne.symm hn02,
                  hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]
              ring
            · by_cases hwj : w = j
              · subst w
                contradiction
              · by_cases hwk : w = k
                · subst w
                  have hn01 : j ≠ k := by omega
                  have hn02 : j ≠ i := by omega
                  have hn03 : j ≠ v := by omega
                  have hn12 : k ≠ i := by omega
                  have hn13 : k ≠ v := by omega
                  have hn23 : i ≠ v := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω k) (ω i) :=
                      ((hsym (ω i) (ω j) (ω k)).1).trans ((hsym (ω j) (ω i) (ω k)).2)
                  have he₂ (ω : Fin m → X) : h (ω j) (ω v) (ω k) = h (ω j) (ω k) (ω v) :=
                      (hsym (ω j) (ω v) (ω k)).2
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,k,i,v] : Fin 4 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_two_covariance p h ![j,k,i,v] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω k) (ω i)-tripleKernelMean p h)*(h (ω j) (ω k) (ω v)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                      Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                  ring
                · have hn01 : j ≠ i := by omega
                  have hn02 : j ≠ k := by omega
                  have hn03 : j ≠ v := by omega
                  have hn04 : j ≠ w := by omega
                  have hn12 : i ≠ k := by omega
                  have hn13 : i ≠ v := by omega
                  have hn14 : i ≠ w := by omega
                  have hn23 : k ≠ v := by omega
                  have hn24 : k ≠ w := by omega
                  have hn34 : v ≠ w := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω i) (ω k) :=
                      (hsym (ω i) (ω j) (ω k)).1
                  simp_rw [he₁]
                  have hf : Function.Injective (![j,i,k,v,w] : Fin 5 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_one_covariance p h ![j,i,k,v,w] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω i) (ω k)-tripleKernelMean p h)*(h (ω j) (ω v) (ω w)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                      hn03, hn04, hn13, hn14, hn23, hn24, or_false, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]

    · by_cases huk : u = k
      · subst u
        by_cases hvi : v = i
        · subst v
          by_cases hwi : w = i
          · subst w
            contradiction
          · by_cases hwj : w = j
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn12 : j ≠ k := by omega
              have he₂ (ω : Fin m → X) : h (ω k) (ω i) (ω j) = h (ω i) (ω j) (ω k) :=
                  ((hsym (ω k) (ω i) (ω j)).1).trans ((hsym (ω i) (ω k) (ω j)).2)
              simp_rw [he₂]
              simp only [← pow_two]
              rw [triple_expect_three p i j k hij hik hjk (fun x y z => (h x y z-tripleKernelMean p h)^2)]
              change tripleOverlapThree p h = _
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, hn02,
                  Ne.symm hn02, hn12, Ne.symm hn12, or_false, or_true, and_true, ite_true, mul_one]
              ring
            · by_cases hwk : w = k
              · subst w
                contradiction
              · have hn01 : i ≠ k := by omega
                have hn02 : i ≠ j := by omega
                have hn03 : i ≠ w := by omega
                have hn12 : k ≠ j := by omega
                have hn13 : k ≠ w := by omega
                have hn23 : j ≠ w := by omega
                have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω i) (ω k) (ω j) :=
                    (hsym (ω i) (ω j) (ω k)).2
                have he₂ (ω : Fin m → X) : h (ω k) (ω i) (ω w) = h (ω i) (ω k) (ω w) :=
                    (hsym (ω k) (ω i) (ω w)).1
                simp_rw [he₁]
                simp_rw [he₂]
                have hf : Function.Injective (![i,k,j,w] : Fin 4 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_two_covariance p h ![i,k,j,w] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω k) (ω j)-tripleKernelMean p h)*(h (ω i) (ω k) (ω w)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                    Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                ring
        · by_cases hvj : v = j
          · subst v
            by_cases hwi : w = i
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn12 : j ≠ k := by omega
              have he₂ (ω : Fin m → X) : h (ω k) (ω j) (ω i) = h (ω i) (ω j) (ω k) :=
                  (((hsym (ω k) (ω j) (ω i)).1).trans ((hsym (ω j) (ω k) (ω i)).2)).trans
                  ((hsym (ω j) (ω i) (ω k)).1)
              simp_rw [he₂]
              simp only [← pow_two]
              rw [triple_expect_three p i j k hij hik hjk (fun x y z => (h x y z-tripleKernelMean p h)^2)]
              change tripleOverlapThree p h = _
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, hn02,
                  Ne.symm hn02, hn12, Ne.symm hn12, or_false, or_true, and_true, ite_true, mul_one]
              ring
            · by_cases hwj : w = j
              · subst w
                contradiction
              · by_cases hwk : w = k
                · subst w
                  contradiction
                · have hn01 : j ≠ k := by omega
                  have hn02 : j ≠ i := by omega
                  have hn03 : j ≠ w := by omega
                  have hn12 : k ≠ i := by omega
                  have hn13 : k ≠ w := by omega
                  have hn23 : i ≠ w := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω k) (ω i) :=
                      ((hsym (ω i) (ω j) (ω k)).1).trans ((hsym (ω j) (ω i) (ω k)).2)
                  have he₂ (ω : Fin m → X) : h (ω k) (ω j) (ω w) = h (ω j) (ω k) (ω w) :=
                      (hsym (ω k) (ω j) (ω w)).1
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,k,i,w] : Fin 4 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_two_covariance p h ![j,k,i,w] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω k) (ω i)-tripleKernelMean p h)*(h (ω j) (ω k) (ω w)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                      Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                  ring
          · by_cases hvk : v = k
            · subst v
              contradiction
            · by_cases hwi : w = i
              · subst w
                have hn01 : i ≠ k := by omega
                have hn02 : i ≠ j := by omega
                have hn03 : i ≠ v := by omega
                have hn12 : k ≠ j := by omega
                have hn13 : k ≠ v := by omega
                have hn23 : j ≠ v := by omega
                have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω i) (ω k) (ω j) :=
                    (hsym (ω i) (ω j) (ω k)).2
                have he₂ (ω : Fin m → X) : h (ω k) (ω v) (ω i) = h (ω i) (ω k) (ω v) :=
                    ((hsym (ω k) (ω v) (ω i)).2).trans ((hsym (ω k) (ω i) (ω v)).1)
                simp_rw [he₁]
                simp_rw [he₂]
                have hf : Function.Injective (![i,k,j,v] : Fin 4 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_two_covariance p h ![i,k,j,v] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω k) (ω j)-tripleKernelMean p h)*(h (ω i) (ω k) (ω v)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                    Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                ring
              · by_cases hwj : w = j
                · subst w
                  have hn01 : j ≠ k := by omega
                  have hn02 : j ≠ i := by omega
                  have hn03 : j ≠ v := by omega
                  have hn12 : k ≠ i := by omega
                  have hn13 : k ≠ v := by omega
                  have hn23 : i ≠ v := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω k) (ω i) :=
                      ((hsym (ω i) (ω j) (ω k)).1).trans ((hsym (ω j) (ω i) (ω k)).2)
                  have he₂ (ω : Fin m → X) : h (ω k) (ω v) (ω j) = h (ω j) (ω k) (ω v) :=
                      ((hsym (ω k) (ω v) (ω j)).2).trans ((hsym (ω k) (ω j) (ω v)).1)
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,k,i,v] : Fin 4 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_two_covariance p h ![j,k,i,v] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω k) (ω i)-tripleKernelMean p h)*(h (ω j) (ω k) (ω v)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                      Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                  ring
                · by_cases hwk : w = k
                  · subst w
                    contradiction
                  · have hn01 : k ≠ i := by omega
                    have hn02 : k ≠ j := by omega
                    have hn03 : k ≠ v := by omega
                    have hn04 : k ≠ w := by omega
                    have hn12 : i ≠ j := by omega
                    have hn13 : i ≠ v := by omega
                    have hn14 : i ≠ w := by omega
                    have hn23 : j ≠ v := by omega
                    have hn24 : j ≠ w := by omega
                    have hn34 : v ≠ w := by omega
                    have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω k) (ω i) (ω j) :=
                        ((hsym (ω i) (ω j) (ω k)).2).trans ((hsym (ω i) (ω k) (ω j)).1)
                    simp_rw [he₁]
                    have hf : Function.Injective (![k,i,j,v,w] : Fin 5 → Fin m) := by
                      intro a b hab
                      fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                    have hc := triple_shared_one_covariance p h ![k,i,j,v,w] hf
                    change (∑ ω : Fin m → X,
                        p.probOf ω *((h (ω k) (ω i) (ω j)-tripleKernelMean p h)*(h (ω k) (ω v) (ω w)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                    rw [hc]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                        hn03, hn04, hn13, hn14, hn23, hn24, or_false, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]

      · by_cases hvi : v = i
        · subst v
          by_cases hwi : w = i
          · subst w
            contradiction
          · by_cases hwj : w = j
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn03 : i ≠ u := by omega
              have hn12 : j ≠ k := by omega
              have hn13 : j ≠ u := by omega
              have hn23 : k ≠ u := by omega
              have he₂ (ω : Fin m → X) : h (ω u) (ω i) (ω j) = h (ω i) (ω j) (ω u) :=
                  ((hsym (ω u) (ω i) (ω j)).1).trans ((hsym (ω i) (ω u) (ω j)).2)
              simp_rw [he₂]
              have hf : Function.Injective (![i,j,k,u] : Fin 4 → Fin m) := by
                intro a b hab
                fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
              have hc := triple_shared_two_covariance p h ![i,j,k,u] hf
              change (∑ ω : Fin m → X,
                  p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω j) (ω u)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
              rw [hc]
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, Ne.symm hn02,
                  hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]
              ring
            · by_cases hwk : w = k
              · subst w
                have hn01 : i ≠ k := by omega
                have hn02 : i ≠ j := by omega
                have hn03 : i ≠ u := by omega
                have hn12 : k ≠ j := by omega
                have hn13 : k ≠ u := by omega
                have hn23 : j ≠ u := by omega
                have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω i) (ω k) (ω j) :=
                    (hsym (ω i) (ω j) (ω k)).2
                have he₂ (ω : Fin m → X) : h (ω u) (ω i) (ω k) = h (ω i) (ω k) (ω u) :=
                    ((hsym (ω u) (ω i) (ω k)).1).trans ((hsym (ω i) (ω u) (ω k)).2)
                simp_rw [he₁]
                simp_rw [he₂]
                have hf : Function.Injective (![i,k,j,u] : Fin 4 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_two_covariance p h ![i,k,j,u] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω k) (ω j)-tripleKernelMean p h)*(h (ω i) (ω k) (ω u)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                    Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                ring
              · have hn01 : i ≠ j := by omega
                have hn02 : i ≠ k := by omega
                have hn03 : i ≠ u := by omega
                have hn04 : i ≠ w := by omega
                have hn12 : j ≠ k := by omega
                have hn13 : j ≠ u := by omega
                have hn14 : j ≠ w := by omega
                have hn23 : k ≠ u := by omega
                have hn24 : k ≠ w := by omega
                have hn34 : u ≠ w := by omega
                have he₂ (ω : Fin m → X) : h (ω u) (ω i) (ω w) = h (ω i) (ω u) (ω w) :=
                    (hsym (ω u) (ω i) (ω w)).1
                simp_rw [he₂]
                have hf : Function.Injective (![i,j,k,u,w] : Fin 5 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_one_covariance p h ![i,j,k,u,w] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω u) (ω w)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                    hn03, hn04, hn13, hn14, hn23, hn24, or_false, or_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]

        · by_cases hvj : v = j
          · subst v
            by_cases hwi : w = i
            · subst w
              have hn01 : i ≠ j := by omega
              have hn02 : i ≠ k := by omega
              have hn03 : i ≠ u := by omega
              have hn12 : j ≠ k := by omega
              have hn13 : j ≠ u := by omega
              have hn23 : k ≠ u := by omega
              have he₂ (ω : Fin m → X) : h (ω u) (ω j) (ω i) = h (ω i) (ω j) (ω u) :=
                  (((hsym (ω u) (ω j) (ω i)).1).trans ((hsym (ω j) (ω u) (ω i)).2)).trans
                  ((hsym (ω j) (ω i) (ω u)).1)
              simp_rw [he₂]
              have hf : Function.Injective (![i,j,k,u] : Fin 4 → Fin m) := by
                intro a b hab
                fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
              have hc := triple_shared_two_covariance p h ![i,j,k,u] hf
              change (∑ ω : Fin m → X,
                  p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω j) (ω u)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
              rw [hc]
              simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01, Ne.symm hn02,
                  hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]
              ring
            · by_cases hwj : w = j
              · subst w
                contradiction
              · by_cases hwk : w = k
                · subst w
                  have hn01 : j ≠ k := by omega
                  have hn02 : j ≠ i := by omega
                  have hn03 : j ≠ u := by omega
                  have hn12 : k ≠ i := by omega
                  have hn13 : k ≠ u := by omega
                  have hn23 : i ≠ u := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω k) (ω i) :=
                      ((hsym (ω i) (ω j) (ω k)).1).trans ((hsym (ω j) (ω i) (ω k)).2)
                  have he₂ (ω : Fin m → X) : h (ω u) (ω j) (ω k) = h (ω j) (ω k) (ω u) :=
                      ((hsym (ω u) (ω j) (ω k)).1).trans ((hsym (ω j) (ω u) (ω k)).2)
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,k,i,u] : Fin 4 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_two_covariance p h ![j,k,i,u] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω k) (ω i)-tripleKernelMean p h)*(h (ω j) (ω k) (ω u)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                      Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                  ring
                · have hn01 : j ≠ i := by omega
                  have hn02 : j ≠ k := by omega
                  have hn03 : j ≠ u := by omega
                  have hn04 : j ≠ w := by omega
                  have hn12 : i ≠ k := by omega
                  have hn13 : i ≠ u := by omega
                  have hn14 : i ≠ w := by omega
                  have hn23 : k ≠ u := by omega
                  have hn24 : k ≠ w := by omega
                  have hn34 : u ≠ w := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω i) (ω k) :=
                      (hsym (ω i) (ω j) (ω k)).1
                  have he₂ (ω : Fin m → X) : h (ω u) (ω j) (ω w) = h (ω j) (ω u) (ω w) :=
                      (hsym (ω u) (ω j) (ω w)).1
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,i,k,u,w] : Fin 5 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_one_covariance p h ![j,i,k,u,w] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω i) (ω k)-tripleKernelMean p h)*(h (ω j) (ω u) (ω w)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                      hn03, hn04, hn13, hn14, hn23, hn24, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]

          · by_cases hvk : v = k
            · subst v
              by_cases hwi : w = i
              · subst w
                have hn01 : i ≠ k := by omega
                have hn02 : i ≠ j := by omega
                have hn03 : i ≠ u := by omega
                have hn12 : k ≠ j := by omega
                have hn13 : k ≠ u := by omega
                have hn23 : j ≠ u := by omega
                have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω i) (ω k) (ω j) :=
                    (hsym (ω i) (ω j) (ω k)).2
                have he₂ (ω : Fin m → X) : h (ω u) (ω k) (ω i) = h (ω i) (ω k) (ω u) :=
                    (((hsym (ω u) (ω k) (ω i)).1).trans ((hsym (ω k) (ω u) (ω i)).2)).trans
                    ((hsym (ω k) (ω i) (ω u)).1)
                simp_rw [he₁]
                simp_rw [he₂]
                have hf : Function.Injective (![i,k,j,u] : Fin 4 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_two_covariance p h ![i,k,j,u] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω k) (ω j)-tripleKernelMean p h)*(h (ω i) (ω k) (ω u)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                    Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                ring
              · by_cases hwj : w = j
                · subst w
                  have hn01 : j ≠ k := by omega
                  have hn02 : j ≠ i := by omega
                  have hn03 : j ≠ u := by omega
                  have hn12 : k ≠ i := by omega
                  have hn13 : k ≠ u := by omega
                  have hn23 : i ≠ u := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω k) (ω i) :=
                      ((hsym (ω i) (ω j) (ω k)).1).trans ((hsym (ω j) (ω i) (ω k)).2)
                  have he₂ (ω : Fin m → X) : h (ω u) (ω k) (ω j) = h (ω j) (ω k) (ω u) :=
                      (((hsym (ω u) (ω k) (ω j)).1).trans ((hsym (ω k) (ω u) (ω j)).2)).trans
                      ((hsym (ω k) (ω j) (ω u)).1)
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,k,i,u] : Fin 4 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_two_covariance p h ![j,k,i,u] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω k) (ω i)-tripleKernelMean p h)*(h (ω j) (ω k) (ω u)-tripleKernelMean p h))) = tripleOverlapTwo p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, hn01, Ne.symm hn01,
                      Ne.symm hn02, hn03, Ne.symm hn12, hn13, hn23, or_false, or_true, and_true, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]
                  ring
                · by_cases hwk : w = k
                  · subst w
                    contradiction
                  · have hn01 : k ≠ i := by omega
                    have hn02 : k ≠ j := by omega
                    have hn03 : k ≠ u := by omega
                    have hn04 : k ≠ w := by omega
                    have hn12 : i ≠ j := by omega
                    have hn13 : i ≠ u := by omega
                    have hn14 : i ≠ w := by omega
                    have hn23 : j ≠ u := by omega
                    have hn24 : j ≠ w := by omega
                    have hn34 : u ≠ w := by omega
                    have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω k) (ω i) (ω j) :=
                        ((hsym (ω i) (ω j) (ω k)).2).trans ((hsym (ω i) (ω k) (ω j)).1)
                    have he₂ (ω : Fin m → X) : h (ω u) (ω k) (ω w) = h (ω k) (ω u) (ω w) :=
                        (hsym (ω u) (ω k) (ω w)).1
                    simp_rw [he₁]
                    simp_rw [he₂]
                    have hf : Function.Injective (![k,i,j,u,w] : Fin 5 → Fin m) := by
                      intro a b hab
                      fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                    have hc := triple_shared_one_covariance p h ![k,i,j,u,w] hf
                    change (∑ ω : Fin m → X,
                        p.probOf ω *((h (ω k) (ω i) (ω j)-tripleKernelMean p h)*(h (ω k) (ω u) (ω w)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                    rw [hc]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                        hn03, hn04, hn13, hn14, hn23, hn24, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]

            · by_cases hwi : w = i
              · subst w
                have hn01 : i ≠ j := by omega
                have hn02 : i ≠ k := by omega
                have hn03 : i ≠ u := by omega
                have hn04 : i ≠ v := by omega
                have hn12 : j ≠ k := by omega
                have hn13 : j ≠ u := by omega
                have hn14 : j ≠ v := by omega
                have hn23 : k ≠ u := by omega
                have hn24 : k ≠ v := by omega
                have hn34 : u ≠ v := by omega
                have he₂ (ω : Fin m → X) : h (ω u) (ω v) (ω i) = h (ω i) (ω u) (ω v) :=
                    ((hsym (ω u) (ω v) (ω i)).2).trans ((hsym (ω u) (ω i) (ω v)).1)
                simp_rw [he₂]
                have hf : Function.Injective (![i,j,k,u,v] : Fin 5 → Fin m) := by
                  intro a b hab
                  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                have hc := triple_shared_one_covariance p h ![i,j,k,u,v] hf
                change (∑ ω : Fin m → X,
                    p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω i) (ω u) (ω v)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                rw [hc]
                simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                    hn03, hn04, hn13, hn14, hn23, hn24, or_false, or_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero]

              · by_cases hwj : w = j
                · subst w
                  have hn01 : j ≠ i := by omega
                  have hn02 : j ≠ k := by omega
                  have hn03 : j ≠ u := by omega
                  have hn04 : j ≠ v := by omega
                  have hn12 : i ≠ k := by omega
                  have hn13 : i ≠ u := by omega
                  have hn14 : i ≠ v := by omega
                  have hn23 : k ≠ u := by omega
                  have hn24 : k ≠ v := by omega
                  have hn34 : u ≠ v := by omega
                  have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω j) (ω i) (ω k) :=
                      (hsym (ω i) (ω j) (ω k)).1
                  have he₂ (ω : Fin m → X) : h (ω u) (ω v) (ω j) = h (ω j) (ω u) (ω v) :=
                      ((hsym (ω u) (ω v) (ω j)).2).trans ((hsym (ω u) (ω j) (ω v)).1)
                  simp_rw [he₁]
                  simp_rw [he₂]
                  have hf : Function.Injective (![j,i,k,u,v] : Fin 5 → Fin m) := by
                    intro a b hab
                    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                  have hc := triple_shared_one_covariance p h ![j,i,k,u,v] hf
                  change (∑ ω : Fin m → X,
                      p.probOf ω *((h (ω j) (ω i) (ω k)-tripleKernelMean p h)*(h (ω j) (ω u) (ω v)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                  rw [hc]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                      hn03, hn04, hn13, hn14, hn23, hn24, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]

                · by_cases hwk : w = k
                  · subst w
                    have hn01 : k ≠ i := by omega
                    have hn02 : k ≠ j := by omega
                    have hn03 : k ≠ u := by omega
                    have hn04 : k ≠ v := by omega
                    have hn12 : i ≠ j := by omega
                    have hn13 : i ≠ u := by omega
                    have hn14 : i ≠ v := by omega
                    have hn23 : j ≠ u := by omega
                    have hn24 : j ≠ v := by omega
                    have hn34 : u ≠ v := by omega
                    have he₁ (ω : Fin m → X) : h (ω i) (ω j) (ω k) = h (ω k) (ω i) (ω j) :=
                        ((hsym (ω i) (ω j) (ω k)).2).trans ((hsym (ω i) (ω k) (ω j)).1)
                    have he₂ (ω : Fin m → X) : h (ω u) (ω v) (ω k) = h (ω k) (ω u) (ω v) :=
                        ((hsym (ω u) (ω v) (ω k)).2).trans ((hsym (ω u) (ω k) (ω v)).1)
                    simp_rw [he₁]
                    simp_rw [he₂]
                    have hf : Function.Injective (![k,i,j,u,v] : Fin 5 → Fin m) := by
                      intro a b hab
                      fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                    have hc := triple_shared_one_covariance p h ![k,i,j,u,v] hf
                    change (∑ ω : Fin m → X,
                        p.probOf ω *((h (ω k) (ω i) (ω j)-tripleKernelMean p h)*(h (ω k) (ω u) (ω v)-tripleKernelMean p h))) = tripleOverlapOne p h at hc
                    rw [hc]
                    simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hn01, Ne.symm hn02,
                        hn03, hn04, hn13, hn14, hn23, hn24, or_false, or_true, and_true, and_false, ite_true, ite_false, mul_zero, mul_one, add_zero, zero_add]

                  · have hn01 : i ≠ j := by omega
                    have hn02 : i ≠ k := by omega
                    have hn03 : i ≠ u := by omega
                    have hn04 : i ≠ v := by omega
                    have hn05 : i ≠ w := by omega
                    have hn12 : j ≠ k := by omega
                    have hn13 : j ≠ u := by omega
                    have hn14 : j ≠ v := by omega
                    have hn15 : j ≠ w := by omega
                    have hn23 : k ≠ u := by omega
                    have hn24 : k ≠ v := by omega
                    have hn25 : k ≠ w := by omega
                    have hn34 : u ≠ v := by omega
                    have hn35 : u ≠ w := by omega
                    have hn45 : v ≠ w := by omega
                    have hf : Function.Injective (![i,j,k,u,v,w] : Fin 6 → Fin m) := by
                      intro a b hab
                      fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
                    have hc := triple_disjoint_covariance p h ![i,j,k,u,v,w] hf
                    change (∑ ω : Fin m → X,
                        p.probOf ω *((h (ω i) (ω j) (ω k)-tripleKernelMean p h)*(h (ω u) (ω v) (ω w)-tripleKernelMean p h))) = 0 at hc
                    rw [hc]
                    simp only [Finset.mem_insert, Finset.mem_singleton, hn03, hn04, hn05, hn13,
                        hn14, hn15, hn23, hn24, hn25, or_false, and_false, ite_false, mul_zero, add_zero]

private theorem triple_incidence_sum (m : ℕ) (s : Finset (Fin m)) (hs : s.card ≤ 3) :
    (∑ t ∈ (tripleIndexList m).toFinset, if s ⊆ tripleCoordinates t then (1:ℝ) else 0) =
      ((m-s.card).choose (3-s.card):ℝ) := by
  simpa only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using
      congrArg (fun a : ℕ => (a:ℝ)) (triple_incidence_count m s hs)

private theorem triple_centered_sum_variance {X : Type} [Fintype X] (p : FinDist X)
    (m : ℕ) (h : X → X → X → ℝ) (hm : 3 ≤ m) (hsym : tripleKernelSymmetric h) :
    (∑ ω : Fin m → X, p.probOf ω *
      ((tripleIndexList m).map (fun t => h (ω t.1) (ω t.2.1) (ω t.2.2)-tripleKernelMean p h)).sum^2) =
    (m.choose 3:ℝ) *
      (3*((m-3).choose 2:ℝ)*tripleOverlapOne p h+
       3*(m-3:ℕ)*tripleOverlapTwo p h+tripleOverlapThree p h) := by
  classical
  let P := (tripleIndexList m).toFinset
  have hP : P.card = m.choose 3 := by
    rw [List.toFinset_card_of_nodup (tripleIndexList_nodup m),tripleIndexList_length]
  have hi (i : Fin m) :
      (∑ b ∈ P, if i ∈ tripleCoordinates b then (1:ℝ) else 0) = ((m-1).choose 2:ℝ) := by
    simpa only [Finset.card_singleton,Finset.singleton_subset_iff] using
      triple_incidence_sum m {i} (by simp)
  have hij (i j : Fin m) (hij : i ≠ j) :
      (∑ b ∈ P, if i ∈ tripleCoordinates b ∧ j ∈ tripleCoordinates b then (1:ℝ) else 0) =
        (m-2:ℕ) := by
    simpa [Finset.insert_subset_iff,Finset.singleton_subset_iff,hij,Nat.choose_one_right] using
      triple_incidence_sum m {i,j} (by simp [hij])
  have hijk (a : TripleIndex m) (ha : a ∈ P) :
      (∑ b ∈ P, if a.1 ∈ tripleCoordinates b ∧ a.2.1 ∈ tripleCoordinates b ∧
        a.2.2 ∈ tripleCoordinates b then (1:ℝ) else 0) = 1 := by
    have hc := tripleCoordinates_card a (List.mem_toFinset.mp ha)
    have hh := triple_incidence_sum m (tripleCoordinates a) (by omega)
    rw [hc] at hh
    simpa only [tripleCoordinates,Finset.insert_subset_iff,Finset.singleton_subset_iff,
      Nat.sub_self,Nat.choose_zero_right,Nat.cast_one] using! hh
  have hchoose : ((m-1).choose 2:ℝ)-2*(m-2:ℕ)+1 = ((m-3).choose 2:ℝ) := by
    have h1 : m-1 = (m-3)+2 := by omega
    have h2 : m-2 = (m-3)+1 := by omega
    rw [h1,h2]
    simp only [Nat.choose_succ_succ,Nat.choose_one_right,Nat.choose_zero_right]
    push_cast
    ring
  have hcov (a : TripleIndex m) (ha : a ∈ P) :
      (∑ b ∈ P, ∑ ω : Fin m → X, p.probOf ω *
        ((h (ω a.1) (ω a.2.1) (ω a.2.2)-tripleKernelMean p h)*
         (h (ω b.1) (ω b.2.1) (ω b.2.2)-tripleKernelMean p h))) =
      3*((m-3).choose 2:ℝ)*tripleOverlapOne p h+
      3*(m-3:ℕ)*tripleOverlapTwo p h+tripleOverlapThree p h := by
    obtain ⟨hai,haj⟩ := tripleIndexList_ordered m a (List.mem_toFinset.mp ha)
    have he (b : TripleIndex m) (hb : b ∈ P) :=
      triple_covariance_incidence p h hsym a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2
        (ne_of_lt hai) (ne_of_lt (hai.trans haj)) (ne_of_lt haj)
        (ne_of_lt (tripleIndexList_ordered m b (List.mem_toFinset.mp hb)).1)
        (ne_of_lt ((tripleIndexList_ordered m b (List.mem_toFinset.mp hb)).1.trans
          (tripleIndexList_ordered m b (List.mem_toFinset.mp hb)).2))
        (ne_of_lt (tripleIndexList_ordered m b (List.mem_toFinset.mp hb)).2)
    rw [Finset.sum_congr rfl he]
    change (∑ b ∈ P, (tripleOverlapOne p h *
      ((if a.1 ∈ tripleCoordinates b then 1 else 0)+
       (if a.2.1 ∈ tripleCoordinates b then 1 else 0)+
       (if a.2.2 ∈ tripleCoordinates b then 1 else 0)) +
      (tripleOverlapTwo p h-2*tripleOverlapOne p h) *
      ((if a.1 ∈ tripleCoordinates b ∧ a.2.1 ∈ tripleCoordinates b then 1 else 0)+
       (if a.1 ∈ tripleCoordinates b ∧ a.2.2 ∈ tripleCoordinates b then 1 else 0)+
       (if a.2.1 ∈ tripleCoordinates b ∧ a.2.2 ∈ tripleCoordinates b then 1 else 0)) +
      (tripleOverlapThree p h-3*tripleOverlapTwo p h+3*tripleOverlapOne p h) *
      (if a.1 ∈ tripleCoordinates b ∧ a.2.1 ∈ tripleCoordinates b ∧ a.2.2 ∈ tripleCoordinates b
        then 1 else 0))) = _
    simp_rw [mul_add,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [hi,hi,hi,hij _ _ (ne_of_lt hai),hij _ _ (ne_of_lt (hai.trans haj)),
      hij _ _ (ne_of_lt haj),hijk a ha]
    have hpred : ((m-2:ℕ):ℝ) = (m-3:ℕ)+1 := by
      have he : m-2 = (m-3)+1 := by omega
      exact_mod_cast he
    rw [hpred] at hchoose ⊢
    have heq : ((m-1).choose 2:ℝ) = ((m-3).choose 2:ℝ)+2*((m-3:ℕ)+1)-1 := by
      linarith [hchoose]
    rw [heq]
    ring
  have hsum (ω : Fin m → X) :
      ((tripleIndexList m).map (fun t => h (ω t.1) (ω t.2.1) (ω t.2.2)-tripleKernelMean p h)).sum =
      ∑ a ∈ P, (h (ω a.1) (ω a.2.1) (ω a.2.2)-tripleKernelMean p h) :=
    (List.sum_toFinset _ (tripleIndexList_nodup m)).symm
  calc
    _ = ∑ a ∈ P, ∑ b ∈ P, ∑ ω : Fin m → X, p.probOf ω *
        ((h (ω a.1) (ω a.2.1) (ω a.2.2)-tripleKernelMean p h)*
         (h (ω b.1) (ω b.2.1) (ω b.2.2)-tripleKernelMean p h)) := by
      simp_rw [hsum,pow_two,Finset.sum_mul_sum,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_congr rfl hcov,Finset.sum_const,nsmul_eq_mul,hP]

theorem triple_u_exact_overlap_variance (X : Type) [Fintype X] (p : FinDist X) (m : ℕ)
    (h : X → X → X → ℝ) (hm : 3 ≤ m) (hsym : tripleKernelSymmetric h) :
    (∑ ω : Fin m → X, p.probOf ω*(tripleUStatistic h ω-tripleKernelMean p h)^2) =
      tripleVarianceBudget p m h := by
  classical
  have hc : (m.choose 3:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hcenter (ω : Fin m → X) :
      tripleUStatistic h ω-tripleKernelMean p h =
      ((tripleIndexList m).map (fun t => h (ω t.1) (ω t.2.1) (ω t.2.2)-tripleKernelMean p h)).sum /
        (m.choose 3:ℝ) := by
    have hs : ((tripleIndexList m).map (fun t => h (ω t.1) (ω t.2.1) (ω t.2.2)-tripleKernelMean p h)).sum =
        ((tripleIndexList m).map (fun t => h (ω t.1) (ω t.2.1) (ω t.2.2))).sum -
          (m.choose 3:ℝ)*tripleKernelMean p h := by
      simp only [sub_eq_add_neg,List.sum_map_add,List.map_const',List.sum_replicate,
        nsmul_eq_mul,tripleIndexList_length,mul_neg]
    rw [hs,tripleUStatistic]
    field_simp
  simp_rw [hcenter,div_pow,← mul_div_assoc]
  rw [← Finset.sum_div,triple_centered_sum_variance p m h hm hsym]
  unfold tripleVarianceBudget
  rw [Nat.cast_sub hm]
  push_cast
  field_simp

private theorem triple_mean_abs_bound {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) :
    |∑ x, p.prob x*f x| ≤ C := by
  classical
  calc
    _ ≤ ∑ x, |p.prob x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p.prob x*|f x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul,abs_of_nonneg (p.nonneg x)]
    _ ≤ ∑ x, p.prob x*C :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (p.nonneg x)
    _ = C := by rw [← Finset.sum_mul,p.sum_one,one_mul]

private theorem triple_variance_of_bound {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) :
    (∑ x, p.prob x*(f x-∑ y, p.prob y*f y)^2) ≤ C^2 := by
  apply (finite_pair_variance_le_second p f).trans
  calc
    _ ≤ ∑ x, p.prob x*C^2 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      nlinarith [hf x,sq_abs (f x),abs_nonneg (f x)]
    _ = _ := by rw [← Finset.sum_mul,p.sum_one,one_mul]

theorem triple_overlap_moments_le_bound {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → X → ℝ) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ x y z, |h x y z| ≤ C) :
    tripleOverlapOne p h ≤ C^2 ∧ tripleOverlapTwo p h ≤ C^2 ∧ tripleOverlapThree p h ≤ C^2 := by
  classical
  let q : FinDist (X × X) :=
    { prob := fun a => p.prob a.1*p.prob a.2
      nonneg := fun a => mul_nonneg (p.nonneg _) (p.nonneg _)
      sum_one := by simp [Fintype.sum_prod_type,← Finset.mul_sum,p.sum_one] }
  let v : FinDist (X × X × X) :=
    { prob := fun a => p.prob a.1*p.prob a.2.1*p.prob a.2.2
      nonneg := fun a => mul_nonneg (mul_nonneg (p.nonneg _) (p.nonneg _)) (p.nonneg _)
      sum_one := by simp [Fintype.sum_prod_type,← Finset.mul_sum,mul_assoc,p.sum_one] }
  have htwo (x y : X) : |∑ z, p.prob z*h x y z| ≤ C :=
    triple_mean_abs_bound p _ C (hh x y)
  have hone (x : X) : |∑ y, ∑ z, p.prob y*p.prob z*h x y z| ≤ C := by
    have he := triple_mean_abs_bound p (fun y => ∑ z, p.prob z*h x y z) C (htwo x)
    simpa only [Finset.mul_sum,mul_assoc] using he
  have hμ₁ : (∑ x, p.prob x*(∑ y, ∑ z, p.prob y*p.prob z*h x y z)) = tripleKernelMean p h := by
    simp only [tripleKernelMean,Finset.mul_sum,mul_assoc]
  have hμ₂ : (∑ a, q.prob a*(∑ z, p.prob z*h a.1 a.2 z)) = tripleKernelMean p h := by
    simp only [q,Fintype.sum_prod_type,tripleKernelMean,Finset.mul_sum,mul_assoc]
  have hμ₃ : (∑ a, v.prob a*h a.1 a.2.1 a.2.2) = tripleKernelMean p h := by
    simp only [v,Fintype.sum_prod_type,tripleKernelMean]
  refine ⟨?_,?_,?_⟩
  · have he := triple_variance_of_bound p _ C hC hone
    rw [hμ₁] at he
    exact he
  · have he := triple_variance_of_bound q (fun a => ∑ z, p.prob z*h a.1 a.2 z) C hC
      (fun a => htwo a.1 a.2)
    rw [hμ₂] at he
    simpa only [q,Fintype.sum_prod_type,tripleOverlapTwo] using he
  · have he := triple_variance_of_bound v (fun a => h a.1 a.2.1 a.2.2) C hC
      (fun a => hh a.1 a.2.1 a.2.2)
    rw [hμ₃] at he
    simpa only [v,Fintype.sum_prod_type,tripleOverlapThree] using he

theorem triple_u_variance_le_bound (X : Type) [Fintype X] (p : FinDist X) (m : ℕ)
    (h : X → X → X → ℝ) (hm : 3 ≤ m) (hsym : tripleKernelSymmetric h)
    (C : ℝ) (hC : 0 ≤ C) (hh : ∀ x y z, |h x y z| ≤ C) :
    (∑ ω : Fin m → X, p.probOf ω*(tripleUStatistic h ω-tripleKernelMean p h)^2) ≤
      9/(m:ℝ)*C^2 := by
  rw [triple_u_exact_overlap_variance X p m h hm hsym]
  have hN : 0 < (m.choose 3:ℝ) := by exact_mod_cast Nat.choose_pos hm
  have hM : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨h1,h2,h3⟩ := triple_overlap_moments_le_bound p h C hC hh
  have hchoose : (3*((m-3).choose 2:ℝ)+3*(m-3:ℕ)+1) ≤ 3*((m-1).choose 2:ℝ) := by
    have he : m-1 = (m-3)+2 := by omega
    rw [he]
    simp only [Nat.choose_succ_succ,Nat.choose_one_right,Nat.choose_zero_right]
    push_cast
    nlinarith [show (0:ℝ) ≤ (m-3:ℕ) by positivity]
  have hrel : (m:ℝ)*((m-1).choose 2:ℝ) = (m.choose 3:ℝ)*3 := by
    have he := Nat.add_one_mul_choose_eq (m-1) 2
    have he' : m-1+1 = m := by omega
    rw [he'] at he
    exact_mod_cast he
  have hsub : ((m-3:ℕ):ℝ) = (m:ℝ)-3 := by rw [Nat.cast_sub hm]; norm_num
  unfold tripleVarianceBudget
  rw [← hsub]
  calc
    _ ≤ (3*((m-3).choose 2:ℝ)/(m.choose 3:ℝ)+
      3*(m-3:ℕ)/(m.choose 3:ℝ)+1/(m.choose 3:ℝ))*C^2 := by
      calc
        _ ≤ (3*((m-3).choose 2:ℝ)/(m.choose 3:ℝ))*C^2+
          (3*(m-3:ℕ)/(m.choose 3:ℝ))*C^2+(1/(m.choose 3:ℝ))*C^2 := by
            gcongr
        _ = _ := by ring
    _ ≤ (3*((m-1).choose 2:ℝ)/(m.choose 3:ℝ))*C^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg C)
      rw [← add_div,← add_div]
      exact (div_le_div_iff_of_pos_right hN).mpr hchoose
    _ = _ := by
      have he : 3*((m-1).choose 2:ℝ)/(m.choose 3:ℝ) = 9/(m:ℝ) := by
        apply (div_eq_div_iff hN.ne' hM.ne').mpr
        nlinarith [hrel]
      rw [he]

end Qatlib.Papers.ClassShadows20.HigherMoments
