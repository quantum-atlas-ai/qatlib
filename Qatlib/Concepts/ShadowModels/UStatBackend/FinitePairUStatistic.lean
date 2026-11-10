/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.UStatBackend

open scoped BigOperators
set_option autoImplicit false

noncomputable def pairKernelMean {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) : ℝ := ∑ x, ∑ y, p.prob x * p.prob y * h x y

noncomputable def pairKernelVariance {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, p.prob x * p.prob y * (h x y - pairKernelMean p h) ^ 2

noncomputable def pairConditionalVariance {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) : ℝ :=
  ∑ x, p.prob x * ((∑ y, p.prob y * h x y) - pairKernelMean p h) ^ 2

def pairIndexList : (m : ℕ) → List (Fin m × Fin m)
  | 0 => []
  | m + 1 => (pairIndexList m).map (fun p => (p.1.castSucc, p.2.castSucc)) ++
      List.ofFn (fun i : Fin m => (i.castSucc, Fin.last m))

theorem pairIndexList_ordered (m : ℕ) (p : Fin m × Fin m) (hp : p ∈ pairIndexList m) :
    p.1 < p.2 := by
  induction m with
  | zero => simp [pairIndexList] at hp
  | succ m ih =>
      simp only [pairIndexList, List.mem_append, List.mem_map, List.mem_ofFn] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨i, rfl⟩
      · exact ih q hq
      · exact i.isLt

theorem pairIndexList_length (m : ℕ) : (pairIndexList m).length = m.choose 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [pairIndexList, List.length_append, List.length_map, List.length_ofFn, ih]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      simp [Nat.add_comm]

noncomputable def pairKernelSum {X : Type} {m : ℕ} (h : X → X → ℝ)
    (ω : Fin m → X) : ℝ := ((pairIndexList m).map (fun p => h (ω p.1) (ω p.2))).sum

noncomputable def pairUStatistic {X : Type} {m : ℕ} (h : X → X → ℝ)
    (ω : Fin m → X) : ℝ := pairKernelSum h ω / (m.choose 2 : ℝ)

noncomputable def pairUCounted {X : Type} {m : ℕ} (h : X → X → ℝ)
    (ω : Fin m → X) : ℝ × ℕ :=
  let a := (pairIndexList m).foldl
    (fun a p => (a.1 + h (ω p.1) (ω p.2), a.2 + 1)) (0, 0)
  (a.1 / (m.choose 2 : ℝ), a.2)

private theorem pair_fold_value_count {P : Type} (f : P → ℝ) (ps : List P) (a : ℝ × ℕ) :
    ps.foldl (fun a p => (a.1 + f p, a.2 + 1)) a =
      (a.1 + (ps.map f).sum, a.2 + ps.length) := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih => simp [ih, add_assoc, Nat.add_comm]

theorem finite_pair_u_statistic_actual_value_and_count (X : Type) (m : ℕ)
    (h : X → X → ℝ) (ω : Fin m → X) :
    (pairUCounted h ω).1 = pairUStatistic h ω ∧ (pairUCounted h ω).2 = m.choose 2 := by
  simp [pairUCounted, pair_fold_value_count, pairUStatistic, pairKernelSum, pairIndexList_length]

private theorem prod_law_sum_one {A X : Type} [Fintype A] [DecidableEq A] [Fintype X] (p : FinDist X) :
    ∑ ω : A → X, ∏ i, p.prob (ω i) = 1 := by
  classical
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp only [p.sum_one, Finset.prod_const_one]

theorem finite_pair_record_marginal {A B X : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype X]
    (p : FinDist X) (f : B → A) (hf : Function.Injective f) (g : (B → X) → ℝ) :
    ∑ ω : A → X, (∏ i, p.prob (ω i)) * g (ω ∘ f) =
      ∑ v : B → X, (∏ j, p.prob (v j)) * g v := by
  classical
  let ef : B ≃ Set.range f := Equiv.ofInjective f hf
  let er := Equiv.piEquivPiSubtypeProd (fun i : A => i ∈ Set.range f) (fun _ => X)
  let eb := (Equiv.piCongrLeft (fun _ : Set.range f => X) ef).symm
  let e : (A → X) ≃ (B → X) × ({i : A // i ∉ Set.range f} → X) :=
    er.trans (eb.prodCongr (Equiv.refl _))
  have hfirst (ω : A → X) : (e ω).1 = ω ∘ f := rfl
  have hprod (ω : A → X) : (∏ i, p.prob (ω i)) =
      (∏ j, p.prob ((e ω).1 j)) * ∏ j, p.prob ((e ω).2 j) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : A => i ∈ Set.range f)]
    congr 1
    convert! (ef.prod_comp (fun i => p.prob (ω i))).symm using 1
    apply Finset.prod_congr
    · ext i; simp
    · intro i hi; rfl
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [hprod]
  simp only [Equiv.apply_symm_apply]
  have hg (a : B → X) (b : {i : A // i ∉ Set.range f} → X) :
      g (e.symm (a,b) ∘ f) = g a := by rw [← hfirst, Equiv.apply_symm_apply]
  simp_rw [hg]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ((∏ j, p.prob (a j)) * g a) *
        (∑ b : {i : A // i ∉ Set.range f} → X, ∏ j, p.prob (b j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [prod_law_sum_one, mul_one]

private theorem pair_expect_two {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (i j : Fin m) (hij : i ≠ j) (h : X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω * h (ω i) (ω j) = pairKernelMean p h := by
  classical
  let f : Bool → Fin m := fun b => if b then j else i
  have hf : Function.Injective f := by
    intro b c hbc
    cases b <;> cases c <;> simp_all [f, Ne.symm hij]
  have he := finite_pair_record_marginal p f hf (fun v => h (v false) (v true))
  change (∑ ω : Fin m → X, p.probOf ω * h (ω i) (ω j)) = _ at he
  rw [he, ← (Equiv.boolArrowEquivProd X).symm.sum_comp, Fintype.sum_prod_type]
  simp [Equiv.boolArrowEquivProd, pairKernelMean, mul_comm]

private theorem pair_expect_list {Ω P : Type} [Fintype Ω] (w : Ω → ℝ)
    (ps : List P) (f : Ω → P → ℝ) :
    ∑ ω, w ω * (ps.map (f ω)).sum = (ps.map (fun p => ∑ ω, w ω * f ω p)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

theorem finite_pair_u_statistic_unbiased (X : Type) [Fintype X] (p : FinDist X)
    (m : ℕ) (h : X → X → ℝ) (hm : 2 ≤ m) :
    (∑ ω : Fin m → X, p.probOf ω * pairUStatistic h ω) = pairKernelMean p h := by
  classical
  simp only [pairUStatistic, pairKernelSum, ← mul_div_assoc]
  rw [← Finset.sum_div, pair_expect_list]
  have he : (pairIndexList m).map (fun ij =>
      ∑ ω : Fin m → X, p.probOf ω * h (ω ij.1) (ω ij.2)) =
      (pairIndexList m).map (fun _ => pairKernelMean p h) := by
    apply List.map_congr_left
    intro ij hij
    exact pair_expect_two p ij.1 ij.2 (ne_of_lt (pairIndexList_ordered m ij hij)) h
  rw [he]
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, pairIndexList_length]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.choose_pos hm).ne')

theorem pairIndexList_nodup (m : ℕ) : (pairIndexList m).Nodup := by
  induction m with
  | zero => simp [pairIndexList]
  | succ m ih =>
      rw [pairIndexList, List.nodup_append]
      refine ⟨List.Nodup.map ?_ ih, List.nodup_ofFn.mpr ?_, ?_⟩
      · intro a b hab
        exact Prod.ext (Fin.castSucc_inj.mp (congrArg Prod.fst hab))
          (Fin.castSucc_inj.mp (congrArg Prod.snd hab))
      · intro a b hab
        exact Fin.castSucc_inj.mp (congrArg Prod.fst hab)
      · intro a ha b hb hab
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
        obtain ⟨y, rfl⟩ := List.mem_ofFn.mp hb
        have he := congrArg Prod.snd hab
        exact Fin.castSucc_ne_last _ he

private theorem pair_incident_sum (m : ℕ) (i : Fin m) (c : ℝ) :
    ((pairIndexList m).map (fun p => if p.1 = i ∨ p.2 = i then c else 0)).sum =
      (m - 1 : ℕ) * c := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [pairIndexList, List.map_map, List.map_ofFn,
          Fin.castSucc_ne_last, Function.comp_def]
      · simp only [pairIndexList, List.map_append, List.sum_append, List.map_map,
          List.map_ofFn, List.sum_ofFn, Function.comp_def]
        have hold : ((pairIndexList m).map (fun p =>
            if p.1.castSucc = i.castSucc ∨ p.2.castSucc = i.castSucc then c else 0)).sum =
            (m - 1 : ℕ) * c := by simpa only [Fin.castSucc_inj] using ih i
        rw [hold]
        simp only [Fin.castSucc_inj,
            show Fin.last m ≠ i.castSucc from Ne.symm (Fin.castSucc_ne_last _), or_false]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) i.isLt
        have hmR : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast Nat.sub_add_cancel hm
        simp only [Nat.add_sub_cancel]
        calc _ = (((m - 1 : ℕ) : ℝ) + 1) * c := by ring
          _ = _ := by rw [hmR]

private theorem pair_expect_three {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (g : X → X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω * g (ω i) (ω j) (ω k) =
      ∑ x, ∑ y, ∑ z, p.prob x * p.prob y * p.prob z * g x y z := by
  classical
  let f : Fin 3 → Fin m := ![i, j, k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  have he := finite_pair_record_marginal p f hf (fun v => g (v 0) (v 1) (v 2))
  change (∑ ω : Fin m → X, p.probOf ω * g (ω i) (ω j) (ω k)) = _ at he
  rw [he, ← (Fin.consEquiv (fun _ : Fin 3 => X)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro x _
  rw [← (finTwoArrowEquiv X).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv, mul_assoc]

private theorem pair_shared_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → ℝ) (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ ω : Fin m → X, p.probOf ω *
      ((h (ω i) (ω j) - pairKernelMean p h) * (h (ω i) (ω k) - pairKernelMean p h)) =
        pairConditionalVariance p h := by
  classical
  rw [pair_expect_three p i j k hij hik hjk
    (fun x y z => (h x y - pairKernelMean p h) * (h x z - pairKernelMean p h))]
  unfold pairConditionalVariance
  apply Finset.sum_congr rfl
  intro x _
  have hm : ∑ y, p.prob y * (h x y - pairKernelMean p h) =
      (∑ y, p.prob y * h x y) - pairKernelMean p h := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_one, one_mul]
  calc
    _ = p.prob x * (∑ y, p.prob y * (h x y - pairKernelMean p h)) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [hm]

private theorem pair_expect_four {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (f : Fin 4 → Fin m) (hf : Function.Injective f) (g : X → X → X → X → ℝ) :
    ∑ ω : Fin m → X, p.probOf ω * g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3)) =
      ∑ x, ∑ y, ∑ z, ∑ w, p.prob x * p.prob y * p.prob z * p.prob w * g x y z w := by
  classical
  have he := finite_pair_record_marginal p f hf (fun v => g (v 0) (v 1) (v 2) (v 3))
  change (∑ ω : Fin m → X, p.probOf ω * g (ω (f 0)) (ω (f 1)) (ω (f 2)) (ω (f 3))) = _ at he
  rw [he, ← (Fin.consEquiv (fun _ : Fin 4 => X)).sum_comp, Fintype.sum_prod_type]
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

private theorem pair_center_mean {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) :
    pairKernelMean p (fun x y => h x y - pairKernelMean p h) = 0 := by
  classical
  unfold pairKernelMean
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    p.sum_one, one_mul, mul_one, sub_self]

private theorem pair_disjoint_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → ℝ) (f : Fin 4 → Fin m) (hf : Function.Injective f) :
    ∑ ω : Fin m → X, p.probOf ω *
      ((h (ω (f 0)) (ω (f 1)) - pairKernelMean p h) *
        (h (ω (f 2)) (ω (f 3)) - pairKernelMean p h)) = 0 := by
  classical
  rw [pair_expect_four p f hf
    (fun x y z w => (h x y - pairKernelMean p h) * (h z w - pairKernelMean p h))]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  calc
    _ = (p.prob x * p.prob y * (h x y - pairKernelMean p h)) *
        pairKernelMean p (fun z w => h z w - pairKernelMean p h) := by
      unfold pairKernelMean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 0 := by rw [pair_center_mean, mul_zero]

private theorem pair_covariance {X : Type} [Fintype X] (p : FinDist X) {m : ℕ}
    (h : X → X → ℝ) (hsym : ∀ x y, h x y = h y x)
    (i j k l : Fin m) (hij : i < j) (hkl : k < l) :
    ∑ ω : Fin m → X, p.probOf ω *
      ((h (ω i) (ω j) - pairKernelMean p h) * (h (ω k) (ω l) - pairKernelMean p h)) =
      pairConditionalVariance p h *
        ((if k = i ∨ l = i then 1 else 0) + (if k = j ∨ l = j then 1 else 0)) +
      (pairKernelVariance p h - 2 * pairConditionalVariance p h) *
        (if (k, l) = (i, j) then 1 else 0) := by
  classical
  have hijN := ne_of_lt hij
  have hklN := ne_of_lt hkl
  by_cases he : (k, l) = (i, j)
  · have hk : k = i := congrArg Prod.fst he
    have hl : l = j := congrArg Prod.snd he
    subst k
    subst l
    have hc : (∑ ω : Fin m → X, p.probOf ω *
        (h (ω i) (ω j) - pairKernelMean p h) ^ 2) =
        pairKernelVariance p h := by
      exact
        pair_expect_two p i j hijN (fun x y => (h x y - pairKernelMean p h) ^ 2)
    simp_rw [← pow_two]
    rw [hc]
    simp only [true_or, or_true, ite_true, mul_one]
    ring
  · by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := by intro hjl; subst l; exact he rfl
      rw [pair_shared_covariance p h i j l hijN (ne_of_lt hkl) hjl]
      simp [he, hijN, Ne.symm hjl]
    · by_cases hil : i = l
      · subst l
        have hjk : j ≠ k := ne_of_gt (lt_trans hkl hij)
        have hh : ∀ ω : Fin m → X, h (ω k) (ω i) = h (ω i) (ω k) := fun ω => hsym _ _
        simp_rw [hh]
        rw [pair_shared_covariance p h i j k hijN hik hjk]
        simp [he, Ne.symm hik, hijN, Ne.symm hjk]
      · by_cases hjk : j = k
        · subst k
          have hil' : i ≠ l := ne_of_lt (lt_trans hij hkl)
          have hh : ∀ ω : Fin m → X, h (ω i) (ω j) = h (ω j) (ω i) := fun ω => hsym _ _
          simp_rw [hh]
          rw [pair_shared_covariance p h j i l (Ne.symm hijN) (ne_of_lt hkl) hil']
          simp [he, Ne.symm hik, Ne.symm hil]
        · by_cases hjl : j = l
          · subst l
            have hh1 : ∀ ω : Fin m → X, h (ω i) (ω j) = h (ω j) (ω i) := fun ω => hsym _ _
            have hh2 : ∀ ω : Fin m → X, h (ω k) (ω j) = h (ω j) (ω k) := fun ω => hsym _ _
            simp_rw [hh1, hh2]
            rw [pair_shared_covariance p h j i k (Ne.symm hijN) hjk hik]
            simp [he, Ne.symm hik, Ne.symm hijN]
          · let f : Fin 4 → Fin m := ![i, j, k, l]
            have hf : Function.Injective f := by
              intro a b hab
              fin_cases a <;> fin_cases b <;>
                simp_all [f, Ne.symm hijN, Ne.symm hklN, Ne.symm hik,
                  Ne.symm hil, Ne.symm hjk, Ne.symm hjl]
            have hc := pair_disjoint_covariance p h f hf
            change (∑ ω : Fin m → X, p.probOf ω *
              ((h (ω i) (ω j) - pairKernelMean p h) *
                (h (ω k) (ω l) - pairKernelMean p h))) = 0 at hc
            rw [hc]
            simp [he, Ne.symm hik, Ne.symm hil, Ne.symm hjk, Ne.symm hjl]

private theorem pair_centered_sum_variance {X : Type} [Fintype X] (p : FinDist X)
    (m : ℕ) (h : X → X → ℝ) (hm : 2 ≤ m) (hsym : ∀ x y, h x y = h y x) :
    (∑ ω : Fin m → X, p.probOf ω *
      (pairKernelSum (fun x y => h x y - pairKernelMean p h) ω) ^ 2) =
      (m.choose 2 : ℝ) *
        (pairKernelVariance p h + 2 * (m - 2 : ℕ) * pairConditionalVariance p h) := by
  classical
  let P := (pairIndexList m).toFinset
  have hP : P.card = m.choose 2 := by
    rw [List.toFinset_card_of_nodup (pairIndexList_nodup m), pairIndexList_length]
  have hord (a : Fin m × Fin m) (ha : a ∈ P) : a.1 < a.2 :=
    pairIndexList_ordered m a (List.mem_toFinset.mp ha)
  have hinc (i : Fin m) : (∑ a ∈ P, if a.1 = i ∨ a.2 = i then (1 : ℝ) else 0) =
      (m - 1 : ℕ) := by
    rw [List.sum_toFinset _ (pairIndexList_nodup m)]
    simpa only [mul_one] using pair_incident_sum m i 1
  have hcov (a : Fin m × Fin m) (ha : a ∈ P) :
      (∑ b ∈ P, ∑ ω : Fin m → X, p.probOf ω *
        ((h (ω a.1) (ω a.2) - pairKernelMean p h) *
          (h (ω b.1) (ω b.2) - pairKernelMean p h))) =
        2 * (m - 1 : ℕ) * pairConditionalVariance p h +
          pairKernelVariance p h - 2 * pairConditionalVariance p h := by
    rw [Finset.sum_congr rfl (fun b hb => pair_covariance p h hsym a.1 a.2 b.1 b.2
      (hord a ha) (hord b hb))]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hinc, ← Finset.mul_sum, hinc, ← Finset.mul_sum]
    simp only [Prod.eta, Finset.sum_ite_eq', ha, ite_true, mul_one]
    ring
  have hsum (ω : Fin m → X) : pairKernelSum (fun x y => h x y - pairKernelMean p h) ω =
      ∑ a ∈ P, (h (ω a.1) (ω a.2) - pairKernelMean p h) :=
    (List.sum_toFinset (fun a : Fin m × Fin m => h (ω a.1) (ω a.2) - pairKernelMean p h)
      (pairIndexList_nodup m)).symm
  calc
    _ = ∑ a ∈ P, ∑ b ∈ P, ∑ ω : Fin m → X, p.probOf ω *
        ((h (ω a.1) (ω a.2) - pairKernelMean p h) *
          (h (ω b.1) (ω b.2) - pairKernelMean p h)) := by
      simp_rw [hsum, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = (P.card : ℝ) * (2 * (m - 1 : ℕ) * pairConditionalVariance p h +
        pairKernelVariance p h - 2 * pairConditionalVariance p h) := by
      rw [Finset.sum_congr rfl hcov, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      have hpred : m - 1 = (m - 2) + 1 := by omega
      rw [hP, hpred]
      push_cast
      ring

theorem finite_pair_u_statistic_exact_variance (X : Type) [Fintype X] (p : FinDist X)
    (m : ℕ) (h : X → X → ℝ) (hm : 2 ≤ m) (hsym : ∀ x y, h x y = h y x) :
    (∑ ω : Fin m → X, p.probOf ω * (pairUStatistic h ω - pairKernelMean p h) ^ 2) =
      (4 * (m - 2 : ℕ) : ℝ) / ((m : ℝ) * (m - 1 : ℕ)) * pairConditionalVariance p h +
        2 / ((m : ℝ) * (m - 1 : ℕ)) * pairKernelVariance p h := by
  classical
  have hc : (m.choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hcenter (ω : Fin m → X) :
      pairUStatistic h ω - pairKernelMean p h =
        pairKernelSum (fun x y => h x y - pairKernelMean p h) ω / (m.choose 2 : ℝ) := by
    have hs : pairKernelSum (fun x y => h x y - pairKernelMean p h) ω =
        pairKernelSum h ω - (m.choose 2 : ℝ) * pairKernelMean p h := by
      simp only [pairKernelSum, sub_eq_add_neg, List.sum_map_add, List.map_const',
        List.sum_replicate, nsmul_eq_mul, pairIndexList_length, mul_neg]
    rw [hs, pairUStatistic]
    field_simp
  simp_rw [hcenter, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div, pair_centered_sum_variance p m h hm hsym]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1 : (m - 1 : ℝ) ≠ 0 := by
    have hr : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [Nat.cast_choose_two, Nat.cast_sub (by omega : 1 ≤ m)]
  norm_num
  field_simp
  ring

theorem finite_pair_variance_le_second {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) :
    (∑ x, p.prob x * (f x - ∑ y, p.prob y * f y) ^ 2) ≤ ∑ x, p.prob x * f x ^ 2 := by
  classical
  let μ := ∑ x, p.prob x * f x
  have hterm (x : X) : p.prob x * (f x - μ) ^ 2 =
      p.prob x * f x ^ 2 - 2 * μ * (p.prob x * f x) + μ ^ 2 * p.prob x := by ring
  change (∑ x, p.prob x * (f x - μ) ^ 2) ≤ _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    p.sum_one]
  change (∑ x, p.prob x * f x ^ 2) - 2 * μ * μ + μ ^ 2 * 1 ≤ _
  nlinarith [sq_nonneg μ]

end Qatlib.Concepts.ShadowModels.UStatBackend
