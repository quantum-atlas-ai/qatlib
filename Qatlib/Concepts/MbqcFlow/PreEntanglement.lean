/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCounterexamples
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled
import Qatlib.Concepts.ClusterPatterns.WireComposition.ClusterWireInstrument
import Qatlib.Concepts.FiniteLocc.LOCCProgram.MbqcCausalGraph
import Qatlib.Concepts.FiniteLocc.LOCCProgram.MbqcCausalGraphDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ClusterPatterns.WireComposition
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.FiniteLocc.LOCCProgram

namespace Qatlib.Concepts.MbqcFlow.PreEntanglement

open Qatlib  Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.ChannelTheory.Stinespring
open Matrix
open scoped Classical ComplexOrder
set_option warningAsError false

set_option autoImplicit false

theorem flowDecide_isSome_iff_search_isSome {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    (mbqcFlowDecide G I O).isSome = true ↔ (mbqcFlowSearch G I O).isSome = true := by
  rw [clause6_clause3a n G I O, mbqcHasFlow_iff_search G I O]

theorem gflowSearch_sound_transfer {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (lam : Fin n → MbqcPlane) (h : (mbqcGFlowSearch G I O lam).isSome) :
    MbqcHasGFlow G I O lam :=
  mbqcHasGFlow_of_search G I O lam h

theorem relabelGate_one_fin {n : ℕ} :
    relabelGate (bitVecEquiv n) (1 : Matrix (Reg n) (Reg n) ℂ) = 1 := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

theorem czB_comm_czB {n : ℕ} (i j i' j' : Fin n) :
    networkCzGateB i j * networkCzGateB i' j'
      = networkCzGateB i' j' * networkCzGateB i j := by
  unfold networkCzGateB
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  simp only [mul_comm]

theorem czB_comm_regWireGate {n : ℕ} (i j v : Fin n) (U : Operator 2)
    (hvi : v ≠ i) (hvj : v ≠ j) :
    networkCzGateB i j * mbqcRegWireGate v U
      = mbqcRegWireGate v U * networkCzGateB i j := by
  have key : ∀ (x y : Reg n),
      (if x i && x j then (-1 : ℂ) else 1) * mbqcRegWireGate v U x y
        = mbqcRegWireGate v U x y * (if y i && y j then (-1 : ℂ) else 1) := by
    intro x y
    by_cases hxy : ∀ k : Fin n, k ≠ v → x k = y k
    · have hi : x i = y i := hxy i hvi.symm
      have hj : x j = y j := hxy j hvj.symm
      rw [hi, hj, mul_comm]
    · have hxy' : ∃ k : Fin n, k ≠ v ∧ x k ≠ y k := by
        by_contra hc
        exact hxy fun k hkv => by_contra fun hne => hc ⟨k, hkv, hne⟩
      obtain ⟨k, hkv, hkxy⟩ := hxy'
      have hk : (if x k = y k then (1 : ℂ) else 0) = 0 := if_neg hkxy
      have hzero : mbqcRegWireGate v U x y = 0 := by
        unfold mbqcRegWireGate
        simp only [Matrix.of_apply]
        calc U (boolEquivFin2 (x v)) (boolEquivFin2 (y v))
            * ∏ w ∈ (Finset.univ.erase v : Finset (Fin n)), (if x w = y w then (1 : ℂ) else 0)
            = U (boolEquivFin2 (x v)) (boolEquivFin2 (y v))
                * ((if x k = y k then (1 : ℂ) else 0)
                  * ∏ w ∈ (Finset.univ.erase v).erase k, (if x w = y w then (1 : ℂ) else 0)) := by
              rw [← Finset.mul_prod_erase (Finset.univ.erase v : Finset (Fin n))
                (fun w => (if x w = y w then (1 : ℂ) else 0))
                (Finset.mem_erase.mpr ⟨hkv, Finset.mem_univ k⟩)]
          _ = 0 := by rw [hk, zero_mul, mul_zero]
      rw [hzero, mul_zero, zero_mul]
  unfold networkCzGateB
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact key x y

noncomputable def czProd {n : ℕ} (es : List (Fin n × Fin n)) : Operator (2 ^ n) :=
  (es.map fun e => networkCzGate e.1 e.2).prod

theorem cz_comm_cz {n : ℕ} (e f : Fin n × Fin n) :
    networkCzGate e.1 e.2 * networkCzGate f.1 f.2
      = networkCzGate f.1 f.2 * networkCzGate e.1 e.2 := by
  unfold networkCzGate
  rw [clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul, czB_comm_czB]

theorem cz_comm_wire {n : ℕ} (e : Fin n × Fin n) (v : Fin n) (U : Operator 2)
    (hv1 : v ≠ e.1) (hv2 : v ≠ e.2) :
    networkCzGate e.1 e.2 * mbqcWireGate v U
      = mbqcWireGate v U * networkCzGate e.1 e.2 := by
  unfold networkCzGate mbqcWireGate
  rw [clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul,
      czB_comm_regWireGate e.1 e.2 v U hv1 hv2]

theorem czProd_cons {n : ℕ} (e : Fin n × Fin n) (es : List (Fin n × Fin n)) :
    czProd (e :: es) = networkCzGate e.1 e.2 * czProd es := by
  simp [czProd]

theorem cz_comm_czProd {n : ℕ} (e : Fin n × Fin n) (es : List (Fin n × Fin n)) :
    networkCzGate e.1 e.2 * czProd es = czProd es * networkCzGate e.1 e.2 := by
  induction es with
  | nil => simp [czProd, mul_one]
  | cons f rest ih =>
      rw [czProd_cons, ← mul_assoc, cz_comm_cz, mul_assoc, ih, ← mul_assoc]

theorem czProd_perm {n : ℕ} {l₁ l₂ : List (Fin n × Fin n)} (hp : l₁.Perm l₂) :
    czProd l₁ = czProd l₂ := by
  induction hp with
  | nil => rfl
  | cons _ _ ih => rw [czProd_cons, czProd_cons, ih]
  | swap =>
      rw [czProd_cons, czProd_cons, czProd_cons, czProd_cons, ← mul_assoc, ← mul_assoc,
        cz_comm_cz]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem czProd_filter_partition {n : ℕ} (p : Fin n × Fin n → Bool)
    (es : List (Fin n × Fin n)) :
    czProd es = czProd (es.filter p) * czProd (es.filter fun e => !p e) := by
  induction es with
  | nil => simp [czProd]
  | cons e rest ih =>
      by_cases hp : p e
      · have hf1 : (e :: rest).filter p = e :: rest.filter p := by simp [hp]
        have hf2 : (e :: rest).filter (fun x => !p x) = rest.filter (fun x => !p x) := by
          simp [hp]
        rw [hf1, hf2, czProd_cons, czProd_cons, ih, mul_assoc]
      · have hf1 : (e :: rest).filter p = rest.filter p := by simp [hp]
        have hf2 : (e :: rest).filter (fun x => !p x) = e :: rest.filter (fun x => !p x) := by
          simp [hp]
        rw [hf1, hf2, czProd_cons, czProd_cons, ih, ← mul_assoc, cz_comm_czProd, mul_assoc,
          cz_comm_czProd]

theorem czMatrix_cons {n : ℕ} (e : Fin n × Fin n) (S : Finset (Fin n × Fin n))
    (he : e ∉ S) :
    czMatrix (Finset.cons e S he) = networkCzGateB e.1 e.2 * czMatrix S := by
  have hphase : ∀ x : Reg n,
      ∏ f ∈ Finset.cons e S he, (if x f.1 && x f.2 then (-1 : ℂ) else 1)
        = (if x e.1 && x e.2 then (-1 : ℂ) else 1)
          * ∏ f ∈ S, (if x f.1 && x f.2 then (-1 : ℂ) else 1) := fun x => Finset.prod_cons he
  unfold czMatrix networkCzGateB
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  simpa only [Matrix.diagonal_apply] using! hphase x

theorem czProd_eq_entangler {n : ℕ} (S : Finset (Fin n × Fin n)) :
    czProd S.toList = relabelGate (bitVecEquiv n) (czMatrix S) := by
  classical
  induction S using Finset.cons_induction with
  | empty =>
      simp [czProd, czMatrix, Finset.prod_empty, Matrix.diagonal_one, relabelGate_one_fin]
  | @cons e S he ih =>
      have hform : czProd (Finset.cons e S he).toList
          = networkCzGate e.1 e.2 * czProd S.toList := by
        rw [czProd_perm (Finset.toList_cons he), czProd_cons]
      rw [hform, ih]
      show relabelGate (bitVecEquiv n) (networkCzGateB e.1 e.2)
          * relabelGate (bitVecEquiv n) (czMatrix S)
        = relabelGate (bitVecEquiv n) (czMatrix (Finset.cons e S he))
      rw [clause6Aux_relabelGate_mul, czMatrix_cons e S he]

theorem regWireGate_comm_pauliProd {n : ℕ} (v : Fin n) (U : Operator 2)
    (f : Fin n → Operator 2) (hv : f v = 1) :
    mbqcRegWireGate v U * pauliProductDensity f
      = pauliProductDensity f * mbqcRegWireGate v U := by
  rw [mbqcRegWireGate_eq, pauliProductDensity_mul, pauliProductDensity_mul]
  congr 1
  funext i
  by_cases hiv : i = v
  · subst hiv
    simp [hv]
  · simp [hiv]

theorem interleavedInit_comm_cz {n : ℕ} (O : Finset (Fin n))
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) (e : Fin n × Fin n)
    (h1 : e.1 ∉ O) (h2 : e.2 ∉ O) :
    (relabelGate (bitVecEquiv n)
        (pauliProductDensity fun v => if v ∈ O then corr s v else 1))
        * networkCzGate e.1 e.2
      = networkCzGate e.1 e.2
        * (relabelGate (bitVecEquiv n)
          (pauliProductDensity fun v => if v ∈ O then corr s v else 1)) := by
  have key : ∀ (x y : Reg n),
      (if x e.1 && x e.2 then (-1 : ℂ) else 1)
        * (pauliProductDensity (fun v => if v ∈ O then corr s v else 1)) x y
      = (pauliProductDensity (fun v => if v ∈ O then corr s v else 1)) x y
        * (if y e.1 && y e.2 then (-1 : ℂ) else 1) := by
    intro x y
    by_cases hxy : ∀ i : Fin n, (if i ∈ O then corr s i else (1 : Operator 2))
        = (1 : Operator 2) → x i = y i
    · have he1 : x e.1 = y e.1 := hxy e.1 (by simp [h1])
      have he2 : x e.2 = y e.2 := hxy e.2 (by simp [h2])
      rw [he1, he2, mul_comm]
    · have hxy' : ∃ i : Fin n,
          (if i ∈ O then corr s i else (1 : Operator 2)) = (1 : Operator 2) ∧ x i ≠ y i := by
        by_contra hc
        exact hxy fun i hf => by_contra fun hne => hc ⟨i, hf, hne⟩
      obtain ⟨i, hfi, hixy⟩ := hxy'
      have hzero : (pauliProductDensity (fun v => if v ∈ O then corr s v else 1)) x y = 0 := by
        unfold pauliProductDensity
        simp only [Matrix.of_apply]
        have hfac : ((if i ∈ O then corr s i else (1 : Operator 2))
            (boolEquivFin2 (x i)) (boolEquivFin2 (y i))) = 0 := by
          rw [hfi]
          exact Matrix.one_apply_ne (fun he => hixy (boolEquivFin2.injective he))
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hfac]
      rw [hzero, mul_zero, zero_mul]
  have hbool : (pauliProductDensity fun v => if v ∈ O then corr s v else 1)
        * networkCzGateB e.1 e.2
      = networkCzGateB e.1 e.2
        * (pauliProductDensity fun v => if v ∈ O then corr s v else 1) := by
    ext x y
    unfold networkCzGateB
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact (key x y).symm
  show relabelGate (bitVecEquiv n) _
      * relabelGate (bitVecEquiv n) (networkCzGateB e.1 e.2)
    = relabelGate (bitVecEquiv n) (networkCzGateB e.1 e.2) * _
  rw [clause6Aux_relabelGate_mul, clause6Aux_relabelGate_mul, hbool]

theorem cz_comm_prodList {n : ℕ} (e : Fin n × Fin n) (ls : List (Operator (2 ^ n)))
    (h : ∀ X ∈ ls, networkCzGate e.1 e.2 * X = X * networkCzGate e.1 e.2) :
    networkCzGate e.1 e.2 * ls.prod = ls.prod * networkCzGate e.1 e.2 := by
  induction ls with
  | nil => simp
  | cons X rest ih =>
      rw [List.prod_cons, ← mul_assoc, h X List.mem_cons_self, mul_assoc,
        ih fun X' hX' => h X' (List.mem_cons_of_mem X hX'), mul_assoc]

theorem czProd_comm_wire {n : ℕ} (es : List (Fin n × Fin n)) (v : Fin n) (U : Operator 2)
    (hv : ∀ e ∈ es, v ≠ e.1 ∧ v ≠ e.2) :
    czProd es * mbqcWireGate v U = mbqcWireGate v U * czProd es := by
  induction es with
  | nil => simp [czProd, mul_one]
  | cons e rest ih =>
      obtain ⟨hn1, hn2⟩ := hv e List.mem_cons_self
      rw [czProd_cons, mul_assoc, ih fun e' he' => hv e' (List.mem_cons_of_mem e he'),
        ← mul_assoc, cz_comm_wire e v U hn1 hn2, mul_assoc]

theorem czProd_comm_czProd {n : ℕ} (l₁ l₂ : List (Fin n × Fin n)) :
    czProd l₁ * czProd l₂ = czProd l₂ * czProd l₁ := by
  induction l₁ with
  | nil => simp [czProd, one_mul, mul_one]
  | cons e rest ih =>
      rw [czProd_cons, mul_assoc, ih, ← mul_assoc, cz_comm_czProd, mul_assoc]

theorem czProd_comm_of {n : ℕ} (es : List (Fin n × Fin n)) (acc : Operator (2 ^ n))
    (h : ∀ e ∈ es, networkCzGate e.1 e.2 * acc = acc * networkCzGate e.1 e.2) :
    czProd es * acc = acc * czProd es := by
  induction es with
  | nil => simp [czProd, one_mul]
  | cons e rest ih =>
      rw [czProd_cons, mul_assoc, ih fun e' he' => h e' (List.mem_cons_of_mem e he'),
        ← mul_assoc, h e List.mem_cons_self, mul_assoc]

theorem czProd_comm_prodList {n : ℕ} (es : List (Fin n × Fin n))
    (ls : List (Operator (2 ^ n)))
    (h : ∀ X ∈ ls, czProd es * X = X * czProd es) :
    czProd es * ls.prod = ls.prod * czProd es := by
  induction ls with
  | nil => simp
  | cons X rest ih =>
      rw [List.prod_cons, ← mul_assoc, h X List.mem_cons_self, mul_assoc,
        ih fun X' hX' => h X' (List.mem_cons_of_mem X hX'), mul_assoc]

noncomputable def interleavedGateGo {n : ℕ} (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    List (Fin n) → List (Fin n × Fin n) → Operator (2 ^ n) → Operator (2 ^ n)
  | [], _, acc => acc
  | v :: L, es, acc =>
      interleavedGateGo lam a corr s L (es.filter fun e => !decide (e.1 = v ∨ e.2 = v))
        (mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v))
          * mbqcWireGate v (corr s v)
          * czProd (es.filter fun e => decide (e.1 = v ∨ e.2 = v))
          * acc)

theorem interleavedGateGo_eq {n : ℕ} (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (L : List (Fin n)) (es : List (Fin n × Fin n)) (acc : Operator (2 ^ n))
    (hsub : ∀ e ∈ es, e.1 ∈ L ∧ e.2 ∈ L)
    (hacc : ∀ e ∈ es, networkCzGate e.1 e.2 * acc = acc * networkCzGate e.1 e.2) :
    interleavedGateGo lam a corr s L es acc
      = L.foldl
          (fun acc v =>
            mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)
              * acc)
          (czProd es * acc) := by
  induction L generalizing es acc with
  | nil =>
      have hes : es = [] := by
        cases es with
        | nil => rfl
        | cons e rest => exact absurd (hsub e List.mem_cons_self) (by simp)
      subst hes
      simp [interleavedGateGo, czProd]
  | cons v L ih =>
      set esT := es.filter fun e => decide (e.1 = v ∨ e.2 = v) with hesT
      set esR := es.filter fun e => !decide (e.1 = v ∨ e.2 = v) with hesR
      have hneOf : ∀ e ∈ esR, v ≠ e.1 ∧ v ≠ e.2 := by
        intro e he
        have h2 := (List.mem_filter.mp he).2
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_or] at h2
        exact ⟨fun h => h2.1 h.symm, fun h => h2.2 h.symm⟩
      have hdue : czProd es = czProd esT * czProd esR := czProd_filter_partition _ es
      have hrest : ∀ e ∈ esR, e.1 ∈ L ∧ e.2 ∈ L := by
        intro e he
        obtain ⟨hne1, hne2⟩ := hneOf e he
        obtain ⟨h1, h2⟩ := hsub e (List.mem_of_mem_filter he)
        refine ⟨?_, ?_⟩
        · rcases List.mem_cons.mp h1 with hev | hm1
          · exact absurd hev.symm hne1
          · exact hm1
        · rcases List.mem_cons.mp h2 with hev | hm2
          · exact absurd hev.symm hne2
          · exact hm2
      have hacc' : ∀ e ∈ esR, networkCzGate e.1 e.2
          * (mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)
            * czProd esT * acc)
          = (mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)
              * czProd esT * acc) * networkCzGate e.1 e.2 := by
        intro e he
        obtain ⟨hne1, hne2⟩ := hneOf e he
        have hprod : ([mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)),
            mbqcWireGate v (corr s v), czProd esT, acc] : List (Operator (2 ^ n))).prod
            = mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)
              * czProd esT * acc := by
          simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
        rw [← hprod]
        refine cz_comm_prodList e _ ?_
        intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · exact cz_comm_wire e v _ hne1 hne2
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact cz_comm_wire e v _ hne1 hne2
          · rcases List.mem_cons.mp hX with rfl | hX
            · exact cz_comm_czProd e esT
            · obtain rfl := List.mem_singleton.mp hX
              exact hacc e (List.mem_of_mem_filter he)
      rw [interleavedGateGo, List.foldl_cons, ih esR _ hrest hacc']
      have hlist : ([mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)),
          mbqcWireGate v (corr s v), czProd esT, acc] : List (Operator (2 ^ n))).prod
          = mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)
            * czProd esT * acc := by
        simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
      congr 1
      have hcomm : ∀ X ∈ [mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)),
          mbqcWireGate v (corr s v), czProd esT, acc], czProd esR * X = X * czProd esR := by
        intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · exact czProd_comm_wire esR v _ (fun e he => hneOf e he)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact czProd_comm_wire esR v _ (fun e he => hneOf e he)
          · rcases List.mem_cons.mp hX with rfl | hX
            · exact czProd_comm_czProd esR esT
            · obtain rfl := List.mem_singleton.mp hX
              exact czProd_comm_of esR _
                (fun e he => hacc e (List.mem_of_mem_filter he))
      have haccR : ∀ e ∈ esR,
          networkCzGate e.1 e.2 * acc = acc * networkCzGate e.1 e.2 :=
        fun e he => hacc e (List.mem_of_mem_filter he)
      rw [hdue, ← hlist, czProd_comm_prodList esR _ hcomm, hlist]
      simp only [mul_assoc]
      rw [czProd_comm_of esR acc haccR]

theorem interleavedInit_comm_of {n : ℕ} (O : Finset (Fin n))
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (es : List (Fin n × Fin n)) (hout : ∀ e ∈ es, e.1 ∉ O ∧ e.2 ∉ O) :
    czProd es * (relabelGate (bitVecEquiv n)
        (pauliProductDensity fun v => if v ∈ O then corr s v else 1))
      = (relabelGate (bitVecEquiv n)
          (pauliProductDensity fun v => if v ∈ O then corr s v else 1)) * czProd es := by
  induction es with
  | nil => simp [czProd, one_mul, mul_one]
  | cons e rest ih =>
      obtain ⟨h1, h2⟩ := hout e List.mem_cons_self
      rw [czProd_cons, mul_assoc, ih fun e' he' => hout e' (List.mem_cons_of_mem e he'),
        ← mul_assoc, ← interleavedInit_comm_cz O corr s e h1 h2, mul_assoc]

theorem foldl_mul_acc {α : Type} {M : Type} [Monoid M] (f : α → M) (init : M) (l : List α) :
    l.foldl (fun acc x => f x * acc) init = (l.map f).reverse.prod * init := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_singleton, mul_assoc]

theorem foldl_acc_mul {n : ℕ} (L : List (Fin n)) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (X : Operator (2 ^ n)) :
    L.foldl
        (fun acc v =>
          mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v) * acc)
        X
      = L.foldl
          (fun acc v =>
            mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)
              * acc)
          1 * X := by
  rw [foldl_mul_acc (fun v : Fin n =>
      mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)) X L,
    foldl_mul_acc (fun v : Fin n =>
      mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v)) * mbqcWireGate v (corr s v)) 1 L,
    mul_one]

theorem exchange_fin {M : Type} [Monoid M] {A B I C : M} (h : B * I = I * B) :
    A * (B * (I * C)) = (A * I) * (B * C) := by
  rw [← mul_assoc B I C, h, mul_assoc I B C, ← mul_assoc A I (B * C)]

noncomputable def interleavedCzGate {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    Operator (2 ^ n) :=
  interleavedGateGo lam a corr s (mbqcExecOrder O r)
    (G.edges.toList.filter fun e =>
      e.1 ∈ mbqcExecOrder O r ∧ e.2 ∈ mbqcExecOrder O r)
    (relabelGate (bitVecEquiv n)
        (pauliProductDensity fun v => if v ∈ O then corr s v else 1)
      * czProd (G.edges.toList.filter fun e =>
        !(e.1 ∈ mbqcExecOrder O r ∧ e.2 ∈ mbqcExecOrder O r)))

theorem interleavedCzGate_eq {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    interleavedCzGate G O r lam a corr s
      = mbqcInterleavedGate O r lam a corr s
        * relabelGate (bitVecEquiv n) (czMatrix G.edges) := by
  classical
  set L := mbqcExecOrder O r with hL
  set esBoth := G.edges.toList.filter fun e => e.1 ∈ L ∧ e.2 ∈ L with hesBoth
  set esEarly := G.edges.toList.filter fun e => !(e.1 ∈ L ∧ e.2 ∈ L) with hesEarly
  set I₀ := relabelGate (bitVecEquiv n)
    (pauliProductDensity fun v => if v ∈ O then corr s v else 1) with hI0

  have hout : ∀ e ∈ esBoth, e.1 ∉ O ∧ e.2 ∉ O := by
    intro e he
    obtain ⟨_, hpred⟩ := List.mem_filter.mp he
    have hp := of_decide_eq_true hpred
    have h1 : e.1 ∈ Finset.univ \ O :=
      (Finset.mem_sort (mbqcExecLe r)).mp (by simpa [mbqcExecOrder, hL] using! hp.1)
    have h2 : e.2 ∈ Finset.univ \ O :=
      (Finset.mem_sort (mbqcExecLe r)).mp (by simpa [mbqcExecOrder, hL] using! hp.2)
    exact ⟨fun h => (Finset.mem_sdiff.mp h1).2 h, fun h => (Finset.mem_sdiff.mp h2).2 h⟩
  have haccTop : ∀ e ∈ esBoth,
      networkCzGate e.1 e.2 * (I₀ * czProd esEarly)
        = (I₀ * czProd esEarly) * networkCzGate e.1 e.2 := by
    intro e he
    obtain ⟨h1, h2⟩ := hout e he
    have hprod2 : ([I₀, czProd esEarly] : List (Operator (2 ^ n))).prod
        = I₀ * czProd esEarly := by simp
    rw [← hprod2]
    refine cz_comm_prodList e _ ?_
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact (interleavedInit_comm_cz O corr s e h1 h2).symm
    · obtain rfl := List.mem_singleton.mp hX
      exact cz_comm_czProd e esEarly
  have hpart : czProd G.edges.toList = czProd esBoth * czProd esEarly :=
    czProd_filter_partition (fun e => e.1 ∈ L ∧ e.2 ∈ L) G.edges.toList
  have hcommI : czProd esBoth * I₀ = I₀ * czProd esBoth :=
    interleavedInit_comm_of O corr s esBoth hout
  show interleavedGateGo lam a corr s L esBoth (I₀ * czProd esEarly)
    = mbqcInterleavedGate O r lam a corr s
      * relabelGate (bitVecEquiv n) (czMatrix G.edges)
  have hint : mbqcInterleavedGate O r lam a corr s
      = L.foldl (fun acc v => mbqcWireGate v (MbqcPlaneBasis (lam v) (a v) (s v))
          * mbqcWireGate v (corr s v) * acc) I₀ := rfl
  rw [interleavedGateGo_eq lam a corr s L esBoth (I₀ * czProd esEarly)
    (fun e he => of_decide_eq_true (List.mem_filter.mp he).2) haccTop,
    foldl_acc_mul L lam a corr s (czProd esBoth * (I₀ * czProd esEarly)), hint,
    ← czProd_eq_entangler G.edges, hpart, foldl_acc_mul L lam a corr s I₀]
  exact exchange_fin hcommI

theorem patternKraus_exchange {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s z : Fin n → Bool) :
    mbqcOutputFrame O z * interleavedCzGate G O r lam a corr s * mbqcInputFrame I
      = mbqcPatternKraus G I O r lam a corr s z := by
  show mbqcOutputFrame O z * interleavedCzGate G O r lam a corr s * mbqcInputFrame I
      = mbqcOutputFrame O z * mbqcInterleavedGate O r lam a corr s * mbqcEntangler G
        * mbqcInputFrame I
  have hE : mbqcEntangler G = relabelGate (bitVecEquiv n) (czMatrix G.edges) := rfl
  rw [interleavedCzGate_eq G O r lam a corr s, hE]
  simp only [Matrix.mul_assoc]

noncomputable def seqPatternBranchMap {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool) :
    Operator (2 ^ I.card) →ₗ[ℂ] Operator (2 ^ O.card) :=
  ∑ z : Fin n → Bool,
    conjBranch (mbqcOutputFrame O z * interleavedCzGate G O r lam a corr s * mbqcInputFrame I)

noncomputable def seqPatternBranch {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (ρ : Operator (2 ^ I.card)) : Operator (2 ^ O.card) :=
  seqPatternBranchMap G I O r lam a corr s ρ

theorem seqPatternBranch_eq {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s : Fin n → Bool)
    (ρ : Operator (2 ^ I.card)) :
    seqPatternBranch G I O r lam a corr s ρ
      = mbqcPatternBranch G I O r lam a corr s ρ := by
  simp only [seqPatternBranch, seqPatternBranchMap, LinearMap.sum_apply, mbqcPatternBranch,
    mbqcPatternBranchMap, patternKraus_exchange G I O r lam a corr s]

theorem seqPatternBranch_zero_of_prob_zero {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2)
    (hTP : ∀ A : Operator (2 ^ I.card),
      Matrix.trace (∑ s : Fin n → Bool, mbqcPatternBranch G I O r lam a corr s A)
        = Matrix.trace A)
    (ρ : Operator (2 ^ I.card)) (hρ : ρ.PosSemidef) (s : Fin n → Bool)
    (hprob : instrumentProb (mbqcPatternInstrument G I O r lam a corr hTP) ρ s = 0) :
    seqPatternBranch G I O r lam a corr s ρ = 0 := by
  rw [seqPatternBranch_eq G I O r lam a corr s ρ]
  exact (instrumentProb_eq_zero_iff (mbqcPatternInstrument G I O r lam a corr hTP) hρ s).mp hprob

theorem flowCorrection_execCausal {n : ℕ} (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (r : Fin n → Fin n)
    (hF2 : ∀ v u : Fin n, f v = some u → mbqcRankPrec r v u)
    (hF3 : ∀ v w u : Fin n, f v = some w → u ≠ v → mbqcAdj G w u → mbqcRankPrec r v u) :
    MbqcCausalCorrection (mbqcExecPrec r) (flowCorrection G f) := by
  intro s s' u hagree
  exact flowCorrection_causal G f (mbqcRankPrec r) hF2 hF3 s s' u fun w hw =>
    hagree w (Or.inl hw)

theorem flowCorrection_congrOnDomain {n : ℕ} (G : MbqcGraph n) (f : Fin n → Option (Fin n))
    (s s' : Fin n → Bool)
    (hagree : ∀ v : Fin n, (f v).isSome = true → s v = s' v) :
    flowCorrection G f s = flowCorrection G f s' := by
  funext u
  unfold flowCorrection
  have hX : (∃ v : Fin n, s v = true ∧ f v = some u)
      ↔ (∃ v : Fin n, s' v = true ∧ f v = some u) := by
    constructor
    · rintro ⟨v, hv, hf⟩
      exact ⟨v, by rw [← hagree v (by simp [hf])]; exact hv, hf⟩
    · rintro ⟨v, hv, hf⟩
      exact ⟨v, by rw [hagree v (by simp [hf])]; exact hv, hf⟩
  have hZ : (∃ v w : Fin n, s v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u)
      ↔ (∃ v w : Fin n, s' v = true ∧ f v = some w ∧ u ≠ v ∧ mbqcAdj G w u) := by
    constructor
    · rintro ⟨v, w, hv, hf, hne, hadj⟩
      exact ⟨v, w, by rw [← hagree v (by simp [hf])]; exact hv, hf, hne, hadj⟩
    · rintro ⟨v, w, hv, hf, hne, hadj⟩
      exact ⟨v, w, by rw [hagree v (by simp [hf])]; exact hv, hf, hne, hadj⟩
  rw [if_congr hX (by rfl) (by rfl), if_congr hZ (by rfl) (by rfl)]

theorem interleavedGateGo_pastDependence {n : ℕ}
    (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s s' : Fin n → Bool)
    (Lfull : List (Fin n))
    (hcorr : ∀ (σ σ' : Fin n → Bool) (v : Fin n),
      (∀ w ∈ Lfull, σ w = σ' w) → corr σ v = corr σ' v)
    (L : List (Fin n)) (es : List (Fin n × Fin n)) (acc : Operator (2 ^ n))
    (hsub : ∀ w ∈ L, w ∈ Lfull) (hagree : ∀ w ∈ Lfull, s w = s' w) :
    interleavedGateGo lam a corr s L es acc
      = interleavedGateGo lam a corr s' L es acc := by
  induction L generalizing es acc with
  | nil => rfl
  | cons v L ih =>
      have hv : s v = s' v := hagree v (hsub v List.mem_cons_self)
      have hc : corr s v = corr s' v := hcorr s s' v hagree
      rw [interleavedGateGo, interleavedGateGo, hv, hc]
      exact ih _ _ fun w hw => hsub w (List.mem_cons_of_mem v hw)

structure FlowRunLedger where

  preEntangleCz : ℕ

  measureCount : ℕ

  feedbackBits : ℕ

  commBits : ℕ

def flowRunLedger {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) : FlowRunLedger where
  preEntangleCz := G.edges.card
  measureCount := (Finset.univ \ O).card
  feedbackBits := ((Finset.univ \ O).filter fun v => (f v).isSome = true).card
  commBits := ((Finset.univ \ O).filter fun v => (f v).isSome = true).card

theorem flowRunLedger_preEntangleCz_eq {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) :
    (flowRunLedger G O f).preEntangleCz = G.edges.card := rfl

theorem flowRunLedger_measureCount_eq {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (r : Fin n → Fin n) (f : Fin n → Option (Fin n)) :
    (flowRunLedger G O f).measureCount = (mbqcExecOrder O r).length := by
  show (Finset.univ \ O).card = ((Finset.univ \ O).sort (mbqcExecLe r)).length
  rw [Finset.length_sort]

theorem flowRunLedger_feedbackBits_eq_commBits {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (f : Fin n → Option (Fin n)) :
    (flowRunLedger G O f).feedbackBits = (flowRunLedger G O f).commBits := rfl

theorem flowRunLedger_dueEarly_split {n : ℕ} (G : MbqcGraph n) (O : Finset (Fin n))
    (r : Fin n → Fin n) (f : Fin n → Option (Fin n)) :
    (G.edges.toList.filter fun e => e.1 ∈ mbqcExecOrder O r ∧ e.2 ∈ mbqcExecOrder O r).length
      + (G.edges.toList.filter fun e =>
          !(e.1 ∈ mbqcExecOrder O r ∧ e.2 ∈ mbqcExecOrder O r)).length
      = (flowRunLedger G O f).preEntangleCz := by
  have h := List.length_eq_length_filter_add
    (fun e => decide (e.1 ∈ mbqcExecOrder O r ∧ e.2 ∈ mbqcExecOrder O r))
    (l := G.edges.toList)
  rw [← h, Finset.length_toList]
  rfl

theorem mbqcExecOrder_singleton {n : ℕ} (O : Finset (Fin n)) (v : Fin n)
    (r : Fin n → Fin n) (h : Finset.univ \ O = {v}) :
    mbqcExecOrder O r = [v] := by
  unfold mbqcExecOrder
  rw [h]
  exact Finset.sort_singleton (mbqcExecLe r) v

def teleWireInput : Finset (Fin 2) := ({0} : Finset (Fin 2))

def teleWireR : Fin 2 → Fin 2 := fun _ => 0

def teleWireCorr : (Fin 2 → Bool) → Fin 2 → Operator 2 :=
  fun σ v => if v = 1 then (if σ 0 then pauliX else 1) else 1

theorem teleWireCorr_zero (s : Fin 2 → Bool) : teleWireCorr s 0 = 1 := by
  simp [teleWireCorr]

theorem teleWireCorr_one (s : Fin 2 → Bool) :
    teleWireCorr s 1 = if s 0 then pauliX else 1 := by
  simp [teleWireCorr]

theorem teleWire_regBitInput (y : Fin 2) (i : Fin teleWireInput.card) :
    (bitVecEquiv teleWireInput.card).symm y i = boolEquivFin2.symm y := by
  fin_cases y <;> fin_cases i <;> rfl

theorem teleWire_regBitOutput (y : Fin 2) (i : Fin clause1OutputA.card) :
    (bitVecEquiv clause1OutputA.card).symm y i = boolEquivFin2.symm y := by
  fin_cases y <;> fin_cases i <;> rfl

theorem mbqcWireGate_one {n : ℕ} (v : Fin n) : mbqcWireGate v (1 : Operator 2) = 1 := by
  have hreg : mbqcRegWireGate v (1 : Operator 2) = 1 := by
    ext x y
    simp only [mbqcRegWireGate, Matrix.of_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      by_cases hiv : i = v
      · subst hiv
        have hne : boolEquivFin2 (x i) ≠ boolEquivFin2 (y i) :=
          fun he => hi (boolEquivFin2.injective he)
        rw [if_neg hne]
        ring
      · have hmem : i ∈ (Finset.univ.erase v : Finset (Fin n)) :=
          Finset.mem_erase.mpr ⟨hiv, Finset.mem_univ i⟩
        have hfac : (if x i = y i then (1 : ℂ) else 0) = 0 := if_neg hi
        rw [Finset.prod_eq_zero hmem hfac]
        ring
  rw [mbqcWireGate, hreg, relabelGate_one_fin]

theorem teleWire_inFrame_apply (x : Fin (2 ^ 2)) (y : Fin 2) :
    mbqcInputFrame teleWireInput x y
      = (Real.sqrt 2 : ℂ)⁻¹
        * (if (bitVecEquiv 2).symm x 0 = boolEquivFin2.symm y then (1 : ℂ) else 0) := by
  unfold mbqcInputFrame
  simp only [Matrix.of_apply, Fin.prod_univ_two]
  have h0 : (0 : Fin 2) ∈ teleWireInput := by decide
  have h1 : (1 : Fin 2) ∉ teleWireInput := by decide
  rw [dif_pos h0, dif_neg h1, teleWire_regBitInput y]
  ring

theorem teleWire_outFrame_apply (z : Fin 2 → Bool) (y : Fin 2) (x : Fin (2 ^ 2)) :
    mbqcOutputFrame clause1OutputA z y x
      = (if (bitVecEquiv 2).symm x 0 = z 0 then (1 : ℂ) else 0)
        * (if (bitVecEquiv 2).symm x 1 = boolEquivFin2.symm y then (1 : ℂ) else 0) := by
  unfold mbqcOutputFrame
  simp only [Matrix.of_apply, Fin.prod_univ_two]
  have h0 : (0 : Fin 2) ∉ clause1OutputA := by decide
  have h1 : (1 : Fin 2) ∈ clause1OutputA := by decide
  rw [dif_neg h0, dif_pos h1, teleWire_regBitOutput y]

theorem teleWire_czMatrix_apply (x y : Reg 2) :
    czMatrix clause1GraphHasFlow.edges x y
      = if x = y then bitPhase (x 0 && x 1) else 0 := by
  unfold czMatrix
  simp only [Matrix.diagonal_apply, clause1GraphHasFlow]
  rw [Finset.prod_singleton]
  by_cases h : x = y <;> simp [h, bitPhase]

theorem teleWire_regWireGate_zero (U : Operator 2) (x y : Reg 2) :
    mbqcRegWireGate 0 U x y
      = U (boolEquivFin2 (x 0)) (boolEquivFin2 (y 0))
        * (if x 1 = y 1 then (1 : ℂ) else 0) := by
  rw [mbqcRegWireGate]
  simp only [Matrix.of_apply]
  have h1 : ((Finset.univ.erase 0 : Finset (Fin 2)) = ({1} : Finset (Fin 2))) := by decide
  rw [h1, Finset.prod_singleton]

theorem teleWire_regWireGate_one (U : Operator 2) (x y : Reg 2) :
    mbqcRegWireGate 1 U x y
      = U (boolEquivFin2 (x 1)) (boolEquivFin2 (y 1))
        * (if x 0 = y 0 then (1 : ℂ) else 0) := by
  rw [mbqcRegWireGate]
  simp only [Matrix.of_apply]
  have h0 : ((Finset.univ.erase 1 : Finset (Fin 2)) = ({0} : Finset (Fin 2))) := by decide
  rw [h0, Finset.prod_singleton]

def reg2ProdEquiv : Reg 2 ≃ Bool × Bool where
  toFun y := (y 0, y 1)
  invFun p := ![p.1, p.2]
  left_inv y := funext fun k => by fin_cases k <;> rfl
  right_inv p := by cases p with | mk a b => rfl

theorem sum_reg2_eq (F : Reg 2 → ℂ) :
    (∑ y : Reg 2, F y)
      = F ![false, false] + F ![false, true] + F ![true, false] + F ![true, true] := by
  rw [← Equiv.sum_comp reg2ProdEquiv.symm F, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have e00 : reg2ProdEquiv.symm (false, false) = (![false, false] : Reg 2) := rfl
  have e01 : reg2ProdEquiv.symm (false, true) = (![false, true] : Reg 2) := rfl
  have e10 : reg2ProdEquiv.symm (true, false) = (![true, false] : Reg 2) := rfl
  have e11 : reg2ProdEquiv.symm (true, true) = (![true, true] : Reg 2) := rfl
  rw [e00, e01, e10, e11]
  ring

theorem sum_reg2_delta0 (x0 : Bool) (g : Reg 2 → ℂ) :
    (∑ y : Reg 2, (if x0 = y 0 then (1 : ℂ) else 0) * g y)
      = g ![x0, false] + g ![x0, true] := by
  have h := sum_reg2_eq (fun y : Reg 2 => (if x0 = y 0 then (1 : ℂ) else 0) * g y)
  (try simp only at h)
  have a00 : ((![false, false] : Reg 2) 0) = false := rfl
  have a01 : ((![false, true] : Reg 2) 0) = false := rfl
  have a10 : ((![true, false] : Reg 2) 0) = true := rfl
  have a11 : ((![true, true] : Reg 2) 0) = true := rfl
  rw [h, a00, a01, a10, a11]
  by_cases hx : x0 = false
  · subst hx
    simp
  · have hxt : x0 = true := by cases x0 <;> simp_all
    subst hxt
    simp

theorem sum_reg2_delta1 (x1 : Bool) (g : Reg 2 → ℂ) :
    (∑ y : Reg 2, (if x1 = y 1 then (1 : ℂ) else 0) * g y)
      = g ![false, x1] + g ![true, x1] := by
  have h := sum_reg2_eq (fun y : Reg 2 => (if x1 = y 1 then (1 : ℂ) else 0) * g y)
  (try simp only at h)
  have a00 : ((![false, false] : Reg 2) 1) = false := rfl
  have a01 : ((![false, true] : Reg 2) 1) = true := rfl
  have a10 : ((![true, false] : Reg 2) 1) = false := rfl
  have a11 : ((![true, true] : Reg 2) 1) = true := rfl
  rw [h, a00, a01, a10, a11]
  by_cases hx : x1 = false
  · subst hx
    simp
  · have hxt : x1 = true := by cases x1 <;> simp_all
    subst hxt
    simp

theorem sum_reg2_delta0' (x0 : Bool) (g : Reg 2 → ℂ) :
    (∑ y : Reg 2, (if y 0 = x0 then (1 : ℂ) else 0) * g y)
      = g ![x0, false] + g ![x0, true] := by
  rw [← sum_reg2_delta0 x0 g]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hc : y 0 = x0
  · rw [if_pos hc, if_pos hc.symm]
  · rw [if_neg hc, if_neg (fun he => hc he.symm)]

theorem teleWire_entangler_frame (x : Fin (2 ^ 2)) (j : Fin 2) :
    (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput) x j
      = (Real.sqrt 2 : ℂ)⁻¹
        * (if (bitVecEquiv 2).symm x 0 = boolEquivFin2.symm j then
            bitPhase ((bitVecEquiv 2).symm x 0 && (bitVecEquiv 2).symm x 1)
          else 0) := by
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (bitVecEquiv 2)
    (fun x' : Fin (2 ^ 2) =>
      mbqcEntangler clause1GraphHasFlow x x' * mbqcInputFrame teleWireInput x' j)]
  have hterm : ∀ y : Reg 2,
      (mbqcEntangler clause1GraphHasFlow x (bitVecEquiv 2 y)
          * mbqcInputFrame teleWireInput (bitVecEquiv 2 y) j)
        = (if (bitVecEquiv 2).symm x = y then
            (Real.sqrt 2 : ℂ)⁻¹
              * (bitPhase ((bitVecEquiv 2).symm x 0 && (bitVecEquiv 2).symm x 1)
                  * (if y 0 = boolEquivFin2.symm j then (1 : ℂ) else 0))
          else 0) := by
    intro y
    have hE : mbqcEntangler clause1GraphHasFlow x (bitVecEquiv 2 y)
        = czMatrix clause1GraphHasFlow.edges ((bitVecEquiv 2).symm x) y := by
      simp only [mbqcEntangler, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [Equiv.symm_apply_apply]
    have hI : mbqcInputFrame teleWireInput (bitVecEquiv 2 y) j
        = (Real.sqrt 2 : ℂ)⁻¹
          * (if y 0 = boolEquivFin2.symm j then (1 : ℂ) else 0) := by
      rw [teleWire_inFrame_apply]
      simp only [Equiv.symm_apply_apply]
    rw [hE, hI, teleWire_czMatrix_apply]
    by_cases h : (bitVecEquiv 2).symm x = y
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  rw [Finset.sum_eq_single ((bitVecEquiv 2).symm x)]
  · rw [if_pos rfl]
    by_cases h : (bitVecEquiv 2).symm x 0 = boolEquivFin2.symm j
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  · intro y _ hy
    rw [if_neg (fun he => hy he.symm)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem teleWire_corr_entangler_frame (U : Operator 2) (x : Fin (2 ^ 2)) (j : Fin 2) :
    (mbqcWireGate (1 : Fin 2) U
        * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput)) x j
      = (Real.sqrt 2 : ℂ)⁻¹
        * (if (bitVecEquiv 2).symm x 0 = boolEquivFin2.symm j then
            ∑ t : Bool,
              U (boolEquivFin2 ((bitVecEquiv 2).symm x 1)) (boolEquivFin2 t)
                * bitPhase (boolEquivFin2.symm j && t)
          else 0) := by
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (bitVecEquiv 2)
    (fun x' : Fin (2 ^ 2) =>
      mbqcWireGate (1 : Fin 2) U x x'
        * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput) x' j)]
  have hterm : ∀ y : Reg 2,
      (mbqcWireGate 1 U x (bitVecEquiv 2 y)
          * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput)
              (bitVecEquiv 2 y) j)
        = (if (bitVecEquiv 2).symm x 0 = y 0 then (1 : ℂ) else 0)
          * ((Real.sqrt 2 : ℂ)⁻¹
              * (if y 0 = boolEquivFin2.symm j then
                  U (boolEquivFin2 ((bitVecEquiv 2).symm x 1)) (boolEquivFin2 (y 1))
                    * bitPhase (y 0 && y 1)
                else 0)) := by
    intro y
    have hW : mbqcWireGate (1 : Fin 2) U x (bitVecEquiv 2 y)
        = U (boolEquivFin2 ((bitVecEquiv 2).symm x 1)) (boolEquivFin2 (y 1))
          * (if (bitVecEquiv 2).symm x 0 = y 0 then (1 : ℂ) else 0) := by
      simp only [mbqcWireGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [teleWire_regWireGate_one]
      simp only [Equiv.symm_apply_apply]
    have hS : (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput)
        (bitVecEquiv 2 y) j
        = (Real.sqrt 2 : ℂ)⁻¹
          * (if y 0 = boolEquivFin2.symm j then bitPhase (y 0 && y 1) else 0) := by
      rw [teleWire_entangler_frame]
      simp only [Equiv.symm_apply_apply]
    rw [hW, hS]
    by_cases hc : y 0 = boolEquivFin2.symm j
    · rw [if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc]
      ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y), sum_reg2_delta0]
  have c0 : ∀ b : Bool,
      ((![(bitVecEquiv 2).symm x 0, b] : Reg 2) 0) = (bitVecEquiv 2).symm x 0 := by
    intro b; rfl
  have e0 : ((![(bitVecEquiv 2).symm x 0, false] : Reg 2) 1) = false := rfl
  have e1 : ((![(bitVecEquiv 2).symm x 0, true] : Reg 2) 1) = true := rfl
  rw [c0 false, c0 true, e0, e1]
  by_cases hd : (bitVecEquiv 2).symm x 0 = boolEquivFin2.symm j
  · rw [if_pos hd, if_pos hd, if_pos hd, Fintype.sum_bool, hd]
    ring
  · rw [if_neg hd, if_neg hd, if_neg hd]
    ring

theorem teleWire_meas_corr_entangler_frame (P U : Operator 2) (x : Fin (2 ^ 2)) (j : Fin 2) :
    (mbqcWireGate (0 : Fin 2) P
        * (mbqcWireGate (1 : Fin 2) U
            * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput))) x j
      = (Real.sqrt 2 : ℂ)⁻¹ * P (boolEquivFin2 ((bitVecEquiv 2).symm x 0)) j
        * ∑ t : Bool,
            U (boolEquivFin2 ((bitVecEquiv 2).symm x 1)) (boolEquivFin2 t)
              * bitPhase (boolEquivFin2.symm j && t) := by
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (bitVecEquiv 2)
    (fun x' : Fin (2 ^ 2) =>
      mbqcWireGate (0 : Fin 2) P x x'
        * (mbqcWireGate (1 : Fin 2) U
            * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput)) x' j)]
  have hterm : ∀ y : Reg 2,
      (mbqcWireGate (0 : Fin 2) P x (bitVecEquiv 2 y)
          * (mbqcWireGate (1 : Fin 2) U
              * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput))
              (bitVecEquiv 2 y) j)
        = (if (bitVecEquiv 2).symm x 1 = y 1 then (1 : ℂ) else 0)
          * (P (boolEquivFin2 ((bitVecEquiv 2).symm x 0)) (boolEquivFin2 (y 0))
              * ((Real.sqrt 2 : ℂ)⁻¹
                  * (if y 0 = boolEquivFin2.symm j then
                      ∑ t : Bool,
                        U (boolEquivFin2 (y 1)) (boolEquivFin2 t)
                          * bitPhase (boolEquivFin2.symm j && t)
                    else 0))) := by
    intro y
    have hW : mbqcWireGate (0 : Fin 2) P x (bitVecEquiv 2 y)
        = P (boolEquivFin2 ((bitVecEquiv 2).symm x 0)) (boolEquivFin2 (y 0))
          * (if (bitVecEquiv 2).symm x 1 = y 1 then (1 : ℂ) else 0) := by
      simp only [mbqcWireGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [teleWire_regWireGate_zero]
      simp only [Equiv.symm_apply_apply]
    have hS : (mbqcWireGate (1 : Fin 2) U
        * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput))
        (bitVecEquiv 2 y) j
        = (Real.sqrt 2 : ℂ)⁻¹
          * (if y 0 = boolEquivFin2.symm j then
              ∑ t : Bool,
                U (boolEquivFin2 (y 1)) (boolEquivFin2 t)
                  * bitPhase (boolEquivFin2.symm j && t)
            else 0) := by
      rw [teleWire_corr_entangler_frame]
      simp only [Equiv.symm_apply_apply]
    rw [hW, hS]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y), sum_reg2_delta1]
  have c1 : ∀ b : Bool,
      ((![b, (bitVecEquiv 2).symm x 1] : Reg 2) 1) = (bitVecEquiv 2).symm x 1 := by
    intro b; rfl
  have e0 : ((![false, (bitVecEquiv 2).symm x 1] : Reg 2) 0) = false := rfl
  have e1 : ((![true, (bitVecEquiv 2).symm x 1] : Reg 2) 0) = true := rfl
  rw [c1 false, c1 true, e0, e1]
  by_cases hjd : boolEquivFin2.symm j = false
  · rw [hjd]
    have hj : j = 0 := by
      fin_cases j
      · rfl
      · exact absurd hjd (by simp [boolEquivFin2])
    rw [hj, if_pos rfl, if_neg (by decide : ¬(true = false))]
    have h0 : boolEquivFin2 false = 0 := rfl
    rw [h0]
    ring
  · have hdt : boolEquivFin2.symm j = true := by
      cases h : boolEquivFin2.symm j <;> simp_all
    rw [hdt]
    have hj : j = 1 := by
      fin_cases j
      · exact absurd hdt (by simp [boolEquivFin2])
      · rfl
    rw [hj, if_neg (by decide : ¬(false = true)), if_pos rfl]
    have h1 : boolEquivFin2 true = 1 := rfl
    rw [h1]
    ring

theorem teleWire_kraus_entry (a : Fin 2 → ℝ) (s z : Fin 2 → Bool) (j' j : Fin 2) :
    (mbqcOutputFrame clause1OutputA z
        * (mbqcWireGate (0 : Fin 2) (MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0))
            * (mbqcWireGate (1 : Fin 2) (if s 0 then pauliX else 1)
                * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput)))) j' j
      = (Real.sqrt 2 : ℂ)⁻¹
        * MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0) (boolEquivFin2 (z 0)) j
        * (if s 0
          then bitPhase (boolEquivFin2.symm j && !(boolEquivFin2.symm j'))
          else bitPhase (boolEquivFin2.symm j && boolEquivFin2.symm j')) := by
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (bitVecEquiv 2)
    (fun x' : Fin (2 ^ 2) =>
      mbqcOutputFrame clause1OutputA z j' x'
        * (mbqcWireGate (0 : Fin 2) (MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0))
            * (mbqcWireGate (1 : Fin 2) (if s 0 then pauliX else 1)
                * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput))) x' j)]
  have hterm : ∀ y : Reg 2,
      (mbqcOutputFrame clause1OutputA z j' (bitVecEquiv 2 y)
          * (mbqcWireGate (0 : Fin 2) (MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0))
              * (mbqcWireGate (1 : Fin 2) (if s 0 then pauliX else 1)
                  * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput)))
              (bitVecEquiv 2 y) j)
        = (if y 0 = z 0 then (1 : ℂ) else 0)
          * ((if y 1 = boolEquivFin2.symm j' then (1 : ℂ) else 0)
              * ((Real.sqrt 2 : ℂ)⁻¹
                  * MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0) (boolEquivFin2 (y 0)) j
                  * ∑ t : Bool,
                      (if s 0 then pauliX else (1 : Operator 2))
                        (boolEquivFin2 (y 1)) (boolEquivFin2 t)
                      * bitPhase (boolEquivFin2.symm j && t))) := by
    intro y
    have hO : mbqcOutputFrame clause1OutputA z j' (bitVecEquiv 2 y)
        = (if y 0 = z 0 then (1 : ℂ) else 0)
          * (if y 1 = boolEquivFin2.symm j' then (1 : ℂ) else 0) := by
      rw [teleWire_outFrame_apply]
      simp only [Equiv.symm_apply_apply]
    have hS := teleWire_meas_corr_entangler_frame
      (MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0)) (if s 0 then pauliX else (1 : Operator 2))
      (bitVecEquiv 2 y) j
    simp only [Equiv.symm_apply_apply] at hS
    rw [hO, hS]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y), sum_reg2_delta0']
  have c0 : ∀ b : Bool, ((![(z 0), b] : Reg 2) 0) = z 0 := by intro b; rfl
  have e0 : ((![(z 0), false] : Reg 2) 1) = false := rfl
  have e1 : ((![(z 0), true] : Reg 2) 1) = true := rfl
  rw [c0 false, c0 true, e0, e1]
  by_cases hj' : boolEquivFin2.symm j' = false
  · rw [hj', if_pos rfl, if_neg (by decide : ¬(true = false))]
    by_cases hs : s 0 = true
    · rw [hs]
      simp [boolEquivFin2, bitPhase, pauliX]
    · have hsf : s 0 = false := by cases h : s 0 <;> simp_all
      rw [hsf]
      simp [boolEquivFin2, bitPhase]
  · have hdt : boolEquivFin2.symm j' = true := by
      cases h : boolEquivFin2.symm j' <;> simp_all
    rw [hdt, if_neg (by decide : ¬(false = true)), if_pos rfl]
    by_cases hs : s 0 = true
    · rw [hs]
      simp [boolEquivFin2, bitPhase, pauliX]
    · have hsf : s 0 = false := by cases h : s 0 <;> simp_all
      rw [hsf]
      simp [boolEquivFin2, bitPhase]

theorem planeBasis_XY_entry (a : ℝ) (b : Bool) (u v : Fin 2) :
    MbqcPlaneBasis MbqcPlane.XY a b u v =
      if u = v then (2 : ℂ)⁻¹
      else if u = 0 then
        (2 : ℂ)⁻¹ * (if b then (-1 : ℂ) else 1) *
          (Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I)
      else
        (2 : ℂ)⁻¹ * (if b then (-1 : ℂ) else 1) *
          (Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I) := by
  fin_cases u <;> fin_cases v <;> cases b <;>
    simp [MbqcPlaneBasis, mbqcPlaneAxisA, mbqcPlaneAxisB, pauliX, pauliY] <;>
    ring

theorem exp_ofReal_I (a : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I)
      = Complex.cos (a : ℂ) + Complex.sin (a : ℂ) * Complex.I :=
  (Complex.cos_add_sin_I (a : ℂ)).symm

theorem exp_neg_ofReal_I (a : ℝ) :
    Complex.exp (-(a : ℂ) * Complex.I)
      = Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I := by
  have h := Complex.cos_add_sin_I (-(a : ℂ))
  rw [Complex.cos_neg, Complex.sin_neg] at h
  have h3 : Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I
      = Complex.cos (a : ℂ) + -Complex.sin (a : ℂ) * Complex.I := by ring
  rw [h3, ← h]

theorem mul_star_exp_one (a : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * star (Complex.exp ((a : ℂ) * Complex.I)) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem star_inv_two : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  show star (((2 : ℝ) : ℂ)⁻¹) = (((2 : ℝ) : ℂ)⁻¹)
  rw [← starRingEnd_apply]
  have h : (((2 : ℝ) : ℂ)⁻¹) = Complex.ofReal (2 : ℝ)⁻¹ := (Complex.ofReal_inv 2).symm
  rw [h, Complex.conj_ofReal]

theorem rbWireUnitary_entry (a : ℝ) (j' j : Fin 2) :
    rbWireUnitary a j' j
      = (Real.sqrt 2 : ℂ)⁻¹ *
        (if j = 0 then (1 : ℂ)
        else if j' = 0 then (Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I)
        else -(Complex.cos (a : ℂ) - Complex.sin (a : ℂ) * Complex.I)) := by
  rw [rbWireUnitary]
  simp only [Matrix.of_apply, Matrix.smul_apply]
  rw [exp_neg_ofReal_I]
  fin_cases j' <;> fin_cases j <;> simp

theorem conjBranch_smul {D : ℕ} (c : ℂ) (M : Matrix (Fin D) (Fin D) ℂ) (ρ : Operator D) :
    conjBranch (c • M) ρ = (c * star c) • (M * ρ * M.conjTranspose) := by
  rw [conjBranch_apply, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

theorem teleWire_execOrder : mbqcExecOrder clause1OutputA teleWireR = [0] :=
  mbqcExecOrder_singleton _ _ _ (by decide)

theorem teleWire_interleaved (a : Fin 2 → ℝ) (s : Fin 2 → Bool) :
    mbqcInterleavedGate clause1OutputA teleWireR (fun _ => MbqcPlane.XY) a teleWireCorr s
      = mbqcWireGate (0 : Fin 2) (MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0))
        * mbqcWireGate (1 : Fin 2) (if s 0 then pauliX else 1) := by
  rw [mbqcInterleavedGate, teleWire_execOrder]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [teleWireCorr_zero, mbqcWireGate_one, mul_one]
  have hfun : (fun v : Fin 2 => if v ∈ clause1OutputA then teleWireCorr s v else 1)
      = fun v : Fin 2 => if v = 1 then (if s 0 then pauliX else 1) else 1 := by
    funext v
    fin_cases v <;> simp [clause1OutputA, teleWireCorr]
  have hR : mbqcWireGate (1 : Fin 2) (if s 0 then pauliX else (1 : Operator 2))
      = relabelGate (bitVecEquiv 2)
          (pauliProductDensity fun v : Fin 2 =>
            if v = 1 then (if s 0 then pauliX else (1 : Operator 2)) else 1) := by
    rw [mbqcWireGate, mbqcRegWireGate_eq]
  rw [hfun, hR]

theorem teleWire_patternKraus_eq (a : Fin 2 → ℝ) (s z : Fin 2 → Bool) :
    mbqcPatternKraus clause1GraphHasFlow teleWireInput clause1OutputA teleWireR (fun _ => MbqcPlane.XY) a
        teleWireCorr s z
      = mbqcOutputFrame clause1OutputA z
        * (mbqcWireGate (0 : Fin 2) (MbqcPlaneBasis MbqcPlane.XY (a 0) (s 0))
            * (mbqcWireGate (1 : Fin 2) (if s 0 then pauliX else 1)
                * (mbqcEntangler clause1GraphHasFlow * mbqcInputFrame teleWireInput))) := by
  rw [mbqcPatternKraus, teleWire_interleaved]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 4000000 in

theorem teleWire_kraus_phase (a : Fin 2 → ℝ) (s z : Fin 2 → Bool) :
    mbqcPatternKraus clause1GraphHasFlow teleWireInput clause1OutputA teleWireR (fun _ => MbqcPlane.XY) a
        teleWireCorr s z
      = (if z 0 then (if s 0 then (-1 : ℂ) else 1) * Complex.exp ((a 0 : ℂ) * Complex.I)
          else (1 : ℂ))
        • ((2 : ℂ)⁻¹ • rbWireUnitary (a 0)) := by
  rw [teleWire_patternKraus_eq]
  refine Matrix.ext fun (j' j : Fin 2) => ?_
  rw [teleWire_kraus_entry, planeBasis_XY_entry]
  simp only [Matrix.smul_apply, Matrix.smul_apply]
  rw [rbWireUnitary_entry]
  generalize hx : (a 0 : ℝ) = x
  have keyA : ∀ y : ℝ, (Real.sqrt 2 : ℂ)⁻¹ * (1 / 2)
      = (Real.sqrt 2 : ℂ)⁻¹ * Complex.cos (y : ℂ) ^ 2 * (1 / 2)
        + (Real.sqrt 2 : ℂ)⁻¹ * Complex.sin (y : ℂ) ^ 2 * -1 * (-1 / 2) := by
    intro y
    linear_combination -(Complex.cos_sq_add_sin_sq (y : ℂ))
      * ((Real.sqrt 2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
  have keyB : ∀ y : ℝ, (Real.sqrt 2 : ℂ)⁻¹ * (-1 / 2)
      = (Real.sqrt 2 : ℂ)⁻¹ * Complex.cos (y : ℂ) ^ 2 * (-1 / 2)
        + (Real.sqrt 2 : ℂ)⁻¹ * Complex.sin (y : ℂ) ^ 2 * -1 * (1 / 2) := by
    intro y
    linear_combination (Complex.cos_sq_add_sin_sq (y : ℂ))
      * ((Real.sqrt 2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
  have keyC : ∀ y : ℝ, (Real.sqrt 2 : ℂ)⁻¹ * (-1 / 2)
      = (Real.sqrt 2 : ℂ)⁻¹ * Complex.sin (y : ℂ) ^ 2 * -1 * (1 / 2)
        + (Real.sqrt 2 : ℂ)⁻¹ * Complex.cos (y : ℂ) ^ 2 * (-1 / 2) := by
    intro y
    linear_combination (Complex.cos_sq_add_sin_sq (y : ℂ))
      * ((Real.sqrt 2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
  have keyD : ∀ y : ℝ, (Real.sqrt 2 : ℂ)⁻¹ * (1 / 2)
      = (Real.sqrt 2 : ℂ)⁻¹ * Complex.sin (y : ℂ) ^ 2 * -1 * (-1 / 2)
        + (Real.sqrt 2 : ℂ)⁻¹ * Complex.cos (y : ℂ) ^ 2 * (1 / 2) := by
    intro y
    linear_combination -(Complex.cos_sq_add_sin_sq (y : ℂ))
      * ((Real.sqrt 2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
  set_option linter.unusedSimpArgs false in
  cases z 0 <;> cases s 0 <;> fin_cases j' <;> fin_cases j <;>
    simp [boolEquivFin2, bitPhase, exp_ofReal_I, exp_neg_ofReal_I] <;>
    try ring
  all_goals try simp only [Complex.I_sq]
  all_goals
    first
    | exact keyA x
    | exact keyB x
    | exact keyC x
    | exact keyD x

theorem teleWire_kraus_branch (a : Fin 2 → ℝ) (s z : Fin 2 → Bool) (ρ : Operator 2) :
    conjBranch (mbqcPatternKraus clause1GraphHasFlow teleWireInput clause1OutputA teleWireR
      (fun _ => MbqcPlane.XY) a teleWireCorr s z) ρ =
    ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) •
      (rbWireUnitary (a 0) * ρ * (rbWireUnitary (a 0)).conjTranspose) := by
  have hphase : ∀ b b' : Bool,
      ((if b' then (if b then (-1 : ℂ) else 1) * Complex.exp ((a 0 : ℂ) * Complex.I)
          else (1 : ℂ))
        * star (if b' then (if b then (-1 : ℂ) else 1) * Complex.exp ((a 0 : ℂ) * Complex.I)
          else (1 : ℂ))) = 1 := by
    intro b b'
    cases b'
    · have hz : (if (false : Bool) then
            (if b then (-1 : ℂ) else 1) * Complex.exp ((a 0 : ℂ) * Complex.I)
          else (1 : ℂ)) = 1 := if_neg (by decide)
      rw [hz, star_one, mul_one]
    · have hz : (if (true : Bool) then
            (if b then (-1 : ℂ) else 1) * Complex.exp ((a 0 : ℂ) * Complex.I)
          else (1 : ℂ))
          = (if b then (-1 : ℂ) else 1) * Complex.exp ((a 0 : ℂ) * Complex.I) := if_pos rfl
      rw [hz]
      by_cases hb : b
      · rw [if_pos hb]
        have h2 : ((-1 : ℂ) * Complex.exp ((a 0 : ℂ) * Complex.I))
            * star ((-1 : ℂ) * Complex.exp ((a 0 : ℂ) * Complex.I))
            = Complex.exp ((a 0 : ℂ) * Complex.I)
                * star (Complex.exp ((a 0 : ℂ) * Complex.I)) := by
          rw [star_mul, star_neg, star_one]
          ring
        rw [h2]
        exact mul_star_exp_one (a 0)
      · rw [if_neg hb, one_mul]
        exact mul_star_exp_one (a 0)
  rw [teleWire_kraus_phase, smul_smul]
  refine (conjBranch_smul ((if z 0 then (if s 0 then (-1 : ℂ) else 1)
        * Complex.exp ((a 0 : ℂ) * Complex.I) else (1 : ℂ)) * (2 : ℂ)⁻¹)
      (rbWireUnitary (a 0)) ρ).trans ?_
  have hscal : ((if z 0 then (if s 0 then (-1 : ℂ) else 1)
          * Complex.exp ((a 0 : ℂ) * Complex.I) else (1 : ℂ)) * (2 : ℂ)⁻¹)
        * star ((if z 0 then (if s 0 then (-1 : ℂ) else 1)
            * Complex.exp ((a 0 : ℂ) * Complex.I) else (1 : ℂ)) * (2 : ℂ)⁻¹)
      = (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by
    rw [star_mul, star_inv_two]
    linear_combination (hphase (s 0) (z 0)) * ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
  rw [hscal]

theorem teleWire_branch_eq (a : Fin 2 → ℝ) (s : Fin 2 → Bool) (ρ : Operator 2) :
    mbqcPatternBranch clause1GraphHasFlow teleWireInput clause1OutputA teleWireR (fun _ => MbqcPlane.XY) a
        teleWireCorr s ρ
      = rbWireUnitary (a 0) * ρ * (rbWireUnitary (a 0)).conjTranspose := by
  rw [mbqcPatternBranch, mbqcPatternBranchMap, LinearMap.sum_apply]
  show (∑ z : Fin 2 → Bool,
      conjBranch (mbqcPatternKraus clause1GraphHasFlow teleWireInput clause1OutputA teleWireR
        (fun _ => MbqcPlane.XY) a teleWireCorr s z) ρ : Operator 2)
    = rbWireUnitary (a 0) * ρ * (rbWireUnitary (a 0)).conjTranspose
  have hterm := fun z : Fin 2 → Bool => teleWire_kraus_branch a s z ρ
  simp only [hterm]
  rw [← Equiv.sum_comp (finTwoArrowEquiv Bool).symm, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← add_smul, ← add_smul]
  have hq : (((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)
      + ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹)) = 1 := by norm_num
  rw [hq, one_smul]

theorem teleWire_pauliWire (s : Fin 2 → Bool) (v : Fin 2) :
    MbqcPauliWire (teleWireCorr s v) := by
  fin_cases v
  · show MbqcPauliWire (teleWireCorr s (0 : Fin 2))
    rw [teleWireCorr_zero]
    exact Or.inl rfl
  · show MbqcPauliWire (teleWireCorr s (1 : Fin 2))
    rw [teleWireCorr_one]
    cases s 0 <;> simp [MbqcPauliWire]

theorem teleWire_causal : MbqcCausalCorrection (mbqcExecPrec teleWireR) teleWireCorr := by
  intro s s' v hv
  fin_cases v
  · simp [teleWireCorr]
  · have h0 : s 0 = s' 0 := hv 0 (by simp [mbqcExecPrec, teleWireR])
    show teleWireCorr s (1 : Fin 2) = teleWireCorr s' (1 : Fin 2)
    rw [teleWireCorr_one, teleWireCorr_one, h0]

theorem teleWire_hasFlow : MbqcHasFlow clause1GraphHasFlow teleWireInput clause1OutputA := by
  refine ⟨clause1FlowA, fun u v => (u : ℕ) < (v : ℕ), inferInstance,
    { irrefl := fun _ => Nat.lt_irrefl _, trans := fun _ _ _ => Nat.lt_trans }, ?_⟩
  intro v hv
  fin_cases v
  · refine ⟨1, rfl, ?_, ?_, Nat.zero_lt_one, ?_⟩
    · simp [clause1GraphHasFlow, mbqcAdj]
    · simp [teleWireInput]
    · intro k hk hk'
      simp [clause1GraphHasFlow, mbqcAdj] at hk
      fin_cases k <;> simp_all
  · simp [clause1OutputA] at hv

theorem teleWire_strongDeterminism (a2 : Fin 2 → ℝ) :
    MbqcStronglyDeterministic clause1GraphHasFlow teleWireInput clause1OutputA
      (fun _ => MbqcPlane.XY) a2 :=
  ⟨teleWireR, teleWireCorr, teleWire_pauliWire, teleWire_causal,
    fun ρ _ _ _ => by rw [teleWire_branch_eq, teleWire_branch_eq]⟩

theorem teleWire_flow_determinism (a2 : Fin 2 → ℝ) :
    MbqcHasFlow clause1GraphHasFlow teleWireInput clause1OutputA ∧
      MbqcStronglyDeterministic clause1GraphHasFlow teleWireInput clause1OutputA
        (fun _ => MbqcPlane.XY) a2 :=
  ⟨teleWire_hasFlow, teleWire_strongDeterminism a2⟩

theorem frontier1 {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (r : Fin n → Fin n) (lam : Fin n → MbqcPlane) (a : Fin n → ℝ)
    (corr : (Fin n → Bool) → Fin n → Operator 2) (s z : Fin n → Bool)
    (ρ : Operator (2 ^ I.card)) (f : Fin n → Option (Fin n)) :
    ((mbqcFlowDecide G I O).isSome = true ↔ (mbqcFlowSearch G I O).isSome = true)
      ∧ interleavedCzGate G O r lam a corr s
          = mbqcInterleavedGate O r lam a corr s * relabelGate (bitVecEquiv n) (czMatrix G.edges)
      ∧ mbqcOutputFrame O z * interleavedCzGate G O r lam a corr s * mbqcInputFrame I
          = mbqcPatternKraus G I O r lam a corr s z
      ∧ seqPatternBranch G I O r lam a corr s ρ = mbqcPatternBranch G I O r lam a corr s ρ
      ∧ (flowRunLedger G O f).measureCount = (mbqcExecOrder O r).length
      ∧ ∀ a2 : Fin 2 → ℝ, MbqcHasFlow clause1GraphHasFlow teleWireInput clause1OutputA
          ∧ MbqcStronglyDeterministic clause1GraphHasFlow teleWireInput clause1OutputA
              (fun _ => MbqcPlane.XY) a2 :=
  ⟨flowDecide_isSome_iff_search_isSome G I O, interleavedCzGate_eq G O r lam a corr s,
    patternKraus_exchange G I O r lam a corr s z, seqPatternBranch_eq G I O r lam a corr s ρ,
    flowRunLedger_measureCount_eq G O r f, fun a2 => teleWire_flow_determinism a2⟩

def wireRecord (b : Bool) : Fin 2 → Bool := ![b, false]

noncomputable def wireBranchMap (a : Fin 2 → ℝ) (b : Bool) : Operator 2 →ₗ[ℂ] Operator 2 :=
  ∑ z : Bool, conjBranch (mbqcPatternKraus clause1GraphHasFlow teleWireInput clause1OutputA teleWireR
    (fun _ => MbqcPlane.XY) a teleWireCorr (wireRecord b) (wireRecord z))

theorem wireBranchMap_apply (a : Fin 2 → ℝ) (b : Bool) (ρ : Operator 2) :
    wireBranchMap a b ρ = (1 / 2 : ℂ) • conjBranch (rbWireUnitary (a 0)) ρ := by
  unfold wireBranchMap
  rw [LinearMap.sum_apply]
  have hs : (∑ z : Bool,
      conjBranch (mbqcPatternKraus clause1GraphHasFlow teleWireInput clause1OutputA teleWireR
        (fun _ => MbqcPlane.XY) a teleWireCorr (wireRecord b) (wireRecord z)) ρ) =
      ∑ _z : Bool, ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) •
        (rbWireUnitary (a 0) * ρ * (rbWireUnitary (a 0)).conjTranspose) := by
    apply Finset.sum_congr rfl
    intro z _
    exact teleWire_kraus_branch a (wireRecord b) (wireRecord z) ρ
  exact hs.trans (by rw [Fintype.sum_bool, ← add_smul]; norm_num [conjBranch_apply])

theorem wireBranchMap_exchange (a : Fin 2 → ℝ) (b : Bool) (ρ : Operator 2) :
    wireBranchMap a b ρ = ∑ z : Bool,
      conjBranch (mbqcOutputFrame clause1OutputA (wireRecord z) *
        interleavedCzGate clause1GraphHasFlow clause1OutputA teleWireR (fun _ => MbqcPlane.XY) a
          teleWireCorr (wireRecord b) * mbqcInputFrame teleWireInput) ρ := by
  simp only [wireBranchMap, LinearMap.sum_apply,
    patternKraus_exchange clause1GraphHasFlow teleWireInput clause1OutputA teleWireR
      (fun _ => MbqcPlane.XY) a teleWireCorr]
  rfl

theorem rbWireUnitary_eq_clusterJ (a : ℝ) :
    rbWireUnitary a = clusterJ (Complex.exp (-(a : ℂ) * Complex.I)) := by
  ext i j
  rw [rbWireUnitary_entry, clusterJ_entry, exp_neg_ofReal_I]
  fin_cases i <;> fin_cases j <;> simp

theorem rbWireUnitary_unitary (a : ℝ) :
    rbWireUnitary a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [rbWireUnitary_eq_clusterJ]
  apply clusterJ_unitary
  simp [Complex.norm_exp]

noncomputable def wireInstrument (a : Fin 2 → ℝ) : Instrument Bool 2 2 :=
  Instrument.ofBranches (wireBranchMap a)
    (fun _ => CompletelyPositive.sum (fun _ _ => completelyPositive_conjBranch _)) (by
      intro A
      simp only [wireBranchMap_apply, Fintype.sum_bool]
      rw [← add_smul]
      norm_num
      exact trace_conjBranch_unitary _ (rbWireUnitary_unitary (a 0)) A)

theorem wireInstrument_branch (a : Fin 2 → ℝ) (b : Bool) (ρ : Operator 2) :
    (wireInstrument a).branch b ρ = (1 / 2 : ℂ) • conjBranch (rbWireUnitary (a 0)) ρ :=
  wireBranchMap_apply a b ρ

theorem wireInstrument_probability (a : Fin 2 → ℝ) (ρ : Operator 2) (b : Bool) :
    instrumentProb (wireInstrument a) ρ b = (Matrix.trace ρ).re / 2 := by
  rw [instrumentProb, wireInstrument_branch, Matrix.trace_smul, smul_eq_mul,
    trace_conjBranch_unitary _ (rbWireUnitary_unitary (a 0))]
  simp [Complex.mul_re]
  ring

theorem wireInstrument_eq_clusterBranch (a : Fin 2 → ℝ) (ρ : Operator 2) (b : Bool) :
    (wireInstrument a).branch b ρ =
      (clusterWireInstrument (Complex.exp (-(a 0 : ℂ) * Complex.I))
        (by simp [Complex.norm_exp])).branch b ρ := by
  rw [wireInstrument_branch, clusterWireInstrument_branch_apply, rbWireUnitary_eq_clusterJ]

def wireFlow : Fin 2 → Option (Fin 2) := fun i => if i = 0 then some 1 else none

theorem wireInstrument_run (a : Fin 2 → ℝ) (ρ : Operator 2) (hρ : IsDensityOperator ρ) (b : Bool) :
    instrumentProb (wireInstrument a) ρ b = 1 / 2 ∧
    (wireInstrument a).branch b ρ = (1 / 2 : ℂ) • conjBranch (rbWireUnitary (a 0)) ρ ∧
    (flowRunLedger clause1GraphHasFlow clause1OutputA wireFlow).preEntangleCz = 1 ∧
    (flowRunLedger clause1GraphHasFlow clause1OutputA wireFlow).measureCount = (mbqcExecOrder clause1OutputA teleWireR).length ∧
    (flowRunLedger clause1GraphHasFlow clause1OutputA wireFlow).feedbackBits = 1 ∧
    (flowRunLedger clause1GraphHasFlow clause1OutputA wireFlow).commBits = 1 := by
  refine ⟨?_, wireInstrument_branch a b ρ, ?_,
    flowRunLedger_measureCount_eq _ _ _ _, ?_, ?_⟩
  · rw [wireInstrument_probability, hρ.2]
    norm_num
  · decide
  · decide
  · decide

theorem wireInstrument_conditional (a : Fin 2 → ℝ) (ρ : Operator 2)
    (hρ : IsDensityOperator ρ) (b : Bool)
    (hp : 0 < instrumentProb (wireInstrument a) ρ b) :
    (wireInstrument a).conditionalState ρ b hp = conjBranch (rbWireUnitary (a 0)) ρ := by
  unfold Instrument.conditionalState
  rw [wireInstrument_branch, wireInstrument_probability, hρ.2]
  norm_num [smul_smul]

end Qatlib.Concepts.MbqcFlow.PreEntanglement
