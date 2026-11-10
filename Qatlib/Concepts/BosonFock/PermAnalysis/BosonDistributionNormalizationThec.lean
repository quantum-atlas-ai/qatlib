/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.PermAnalysis.BosonDistributionNormalizationStat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Permanent
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib

open scoped Matrix Nat

private def occFn {m n : ℕ} (f : Fin n → Fin m) : Fin m → ℕ :=
  fun i => ∑ j : Fin n, if f j = i then 1 else 0

private theorem occFn_comp_perm {m n : ℕ} (f : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) :
    occFn (fun j => f (σ j)) = occFn f := by
  funext i
  simp only [occFn]
  exact Fintype.sum_equiv σ (fun j => if f (σ j) = i then (1 : ℕ) else 0)
    (fun j => if f j = i then (1 : ℕ) else 0) (fun _ => rfl)

private theorem occFn_sum {m n : ℕ} (f : Fin n → Fin m) : ∑ i, occFn f i = n := by
  have hcomm : ∑ i : Fin m, ∑ j : Fin n, (if f j = i then (1 : ℕ) else 0)
      = ∑ j : Fin n, ∑ i : Fin m, (if f j = i then (1 : ℕ) else 0) :=
    Finset.sum_comm (f := fun i j => if f j = i then (1 : ℕ) else 0)
  have hinner : ∀ j : Fin n, ∑ i : Fin m, (if f j = i then (1 : ℕ) else 0) = 1 := by
    intro j
    simp
  simp only [occFn]
  rw [hcomm]
  simp [hinner]

private theorem occFn_le {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) : occFn f i ≤ n := by
  have hle : occFn f i ≤ ∑ i', occFn f i' :=
    Finset.single_le_sum (fun i' _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [occFn_sum] at hle
  exact hle

private def occFin {m n : ℕ} (f : Fin n → Fin m) : Fin m → Fin (n + 1) :=
  fun i => ⟨occFn f i, by have := occFn_le f i; omega⟩

private theorem occFin_val {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) :
    ((occFin f i : Fin (n + 1)) : ℕ) = occFn f i := rfl

private theorem occFin_sum {m n : ℕ} (f : Fin n → Fin m) :
    ∑ i, ((occFin f i : Fin (n + 1)) : ℕ) = n := by
  refine (Finset.sum_congr rfl fun i _ => occFin_val f i).trans (occFn_sum f)

private theorem card_subtype_iff {α : Type*} (p q : α → Prop)
    [Fintype { x // p x }] [Fintype { x // q x }] (h : ∀ a, p a ↔ q a) :
    Fintype.card { x // p x } = Fintype.card { x // q x } := by
  classical
  exact Fintype.card_congr
    (Equiv.ofBijective (fun x : { x // p x } => (⟨(x : α), (h _).1 x.2⟩ : { x // q x }))
      ⟨fun x y hxy => Subtype.ext (by simpa using hxy),
        fun y => ⟨⟨(y : α), (h _).2 y.2⟩, Subtype.ext (by simp)⟩⟩)

private theorem card_filter_subtype {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card { x // p x } := by
  classical
  rw [card_subtype_iff p (fun x => x ∈ Finset.univ.filter p) (fun a => by simp),
    Fintype.card_coe]

private theorem card_fiber_subtype {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) :
    Fintype.card { j : Fin n // f j = i } = occFn f i := by
  classical
  rw [← card_filter_subtype (fun j => f j = i), Finset.card_filter]
  rfl

private theorem card_perm_equiv_perm {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
    [DecidableEq β] [Fintype (α ≃ β)] [Fintype (Equiv.Perm α)] (e : α ≃ β) :
    Fintype.card (α ≃ β) = Fintype.card (Equiv.Perm α) := by
  exact Fintype.card_congr
    (⟨fun φ : α ≃ β => φ.trans e.symm, fun ψ : α ≃ α => ψ.trans e,
      fun φ => Equiv.ext fun a => by simp,
      fun ψ => Equiv.ext fun a => by simp⟩ : (α ≃ β) ≃ Equiv.Perm α)

private theorem perm_fiber_card {m n : ℕ} (f g : Fin n → Fin m) (h : occFn f = occFn g) :
    Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j } = ∏ i, (occFn f i)! := by
  classical
  have hkey : ∀ (π : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}))
      (a : Fin n), Equiv.ofFiberEquiv π a
      = ((π (g a)) (⟨a, rfl⟩ : {j : Fin n // g j = g a}) : Fin n) := by
    intro π a
    simp
    rfl
  have hinj : ∀ π π' : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}),
      Equiv.ofFiberEquiv π = Equiv.ofFiberEquiv π' → π = π' := by
    intro π π' heq
    funext i
    ext x
    have htr : ∀ (πx : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i})),
        ((πx i) x : Fin n)
          = ((πx (g (x : Fin n))) (⟨(x : Fin n), rfl⟩ :
              {j : Fin n // g j = g (x : Fin n)}) : Fin n) := by
      intro πx
      cases x with
      | mk a ha => subst ha; rfl
    rw [htr π, htr π', ← hkey π (x : Fin n), ← hkey π' (x : Fin n)]
    exact congrArg (fun z : Fin n => (z : ℕ)) (Equiv.ext_iff.mp heq (x : Fin n))
  have hsurj : ∀ τ : { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j },
      ∃ π : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}),
        Equiv.ofFiberEquiv π = (τ : Equiv.Perm (Fin n)) := by
    intro τ
    set hblock : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}) := fun i =>
      Equiv.ofBijective
        (fun x : {j : Fin n // g j = i} =>
          (⟨(τ : Equiv.Perm (Fin n)) (x : Fin n), by
            have h1 := τ.2 (x : Fin n)
            rw [x.2] at h1
            exact h1⟩ : {j : Fin n // f j = i}))
        ⟨fun x y hxy =>
            Subtype.ext ((τ : Equiv.Perm (Fin n)).injective (by simpa using hxy)),
          fun y =>
            ⟨(⟨(τ : Equiv.Perm (Fin n)).symm (y : Fin n), by
                have h2 := τ.2 ((τ : Equiv.Perm (Fin n)).symm (y : Fin n))
                rw [Equiv.apply_symm_apply] at h2
                exact h2.symm.trans y.2⟩ : {j : Fin n // g j = i}),
              Subtype.ext (Equiv.apply_symm_apply _ _)⟩⟩
    refine ⟨hblock, ?_⟩
    refine (Equiv.ext fun a => ?_)
    show (Equiv.ofFiberEquiv hblock) a = ((τ : Equiv.Perm (Fin n)) a : Fin n)
    rw [hkey hblock a]
    rfl
  have hbij : (∀ i : Fin m, {j : Fin n // g j = i} ≃ {j : Fin n // f j = i}) ≃
      { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j } :=
    Equiv.ofBijective
      (fun π => ⟨Equiv.ofFiberEquiv π, fun j => Equiv.ofFiberEquiv_map π j⟩)
      ⟨fun π π' hpp => hinj π π' (congrArg Subtype.val hpp),
        fun τ => let ⟨π, hπ⟩ := hsurj τ; ⟨π, Subtype.ext hπ⟩⟩
  rw [Fintype.card_congr hbij.symm, Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hce : Fintype.card {j : Fin n // g j = i} = Fintype.card {j : Fin n // f j = i} := by
    rw [card_fiber_subtype, card_fiber_subtype, ← h]
  have e₀ : {j : Fin n // g j = i} ≃ {j : Fin n // f j = i} := Fintype.equivOfCardEq hce
  rw [card_perm_equiv_perm e₀, Fintype.card_perm, card_fiber_subtype g i, ← h]

private theorem card_perm_fiber {m n : ℕ} (f g : Fin n → Fin m) :
    Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j }
      = if occFn f = occFn g then ∏ i, (occFn f i)! else 0 := by
  classical
  by_cases h : occFn f = occFn g
  · rw [if_pos h, perm_fiber_card f g h]
  · rw [if_neg h, Fintype.card_eq_zero_iff]
    refine ⟨fun τ => h ?_⟩
    have h1 := τ.2
    have h2 : (fun j => f ((τ : Equiv.Perm (Fin n)) j)) = g := funext fun j => h1 j
    exact (occFn_comp_perm f (τ : Equiv.Perm (Fin n))).symm.trans (by rw [h2])

private theorem sum_perm_comp {m n : ℕ} (f₀ : Fin n → Fin m) (Φ : (Fin n → Fin m) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), Φ (fun j => f₀ (σ j))
      = (∏ i, (occFn f₀ i)! : ℕ) * ∑ g : Fin n → Fin m,
          (if occFn g = occFn f₀ then (1 : ℕ) else 0) * Φ g := by
  classical
  have hphi : ∀ (F : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
      (fun j => f₀ (σ j)) = F → Φ (fun j => f₀ (σ j)) = Φ F := by
    intro F σ h
    rw [h]
  rw [← Finset.sum_fiberwise_of_maps_to
      (t := (Finset.univ : Finset (Fin n → Fin m)))
      (g := fun σ : Equiv.Perm (Fin n) => fun j => f₀ (σ j))
      (fun σ _ => Finset.mem_univ _)
      (f := fun σ : Equiv.Perm (Fin n) => Φ (fun j => f₀ (σ j)))]
  have hterm : ∀ F : Fin n → Fin m,
      (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), Φ (fun j => f₀ (σ j)))
        = (↑(if occFn F = occFn f₀ then (1 : ℕ) else 0) * Φ F) *
          ↑(∏ i, (occFn f₀ i)! : ℕ) := by
    intro F
    have hone : (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), Φ F)
        = (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), (1 : ℂ)) * Φ F := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => (one_mul _).symm
    have hone2 : (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), (1 : ℂ))
        = ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)).card : ℂ) := by
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
    rw [Finset.sum_congr rfl
        (fun σ hσ => hphi F σ (by simpa [Finset.mem_filter] using hσ)),
      hone, hone2, card_filter_subtype,
      card_subtype_iff (fun τ : Equiv.Perm (Fin n) => (fun j => f₀ (τ j)) = F)
        (fun τ : Equiv.Perm (Fin n) => ∀ j, f₀ (τ j) = F j)
        (fun τ => funext_iff),
      card_perm_fiber f₀ F]
    by_cases h : occFn f₀ = occFn F
    · rw [if_pos h, if_pos h.symm, Nat.cast_one, one_mul]; ring
    · rw [if_neg h, if_neg (fun hc => h hc.symm), Nat.cast_zero, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun F _ => hterm F), ← Finset.sum_mul]
  exact mul_comm _ _

private theorem sum_get_count {α : Type*} [DecidableEq α] (L : List α) (a : α) :
    ∑ p : Fin L.length, (if L.get p = a then (1 : ℕ) else 0) = L.count a := by
  induction L with
  | nil => simp
  | cons x t ih =>
      show (∑ p : Fin (t.length + 1), (if (x :: t).get p = a then (1 : ℕ) else 0))
        = List.count a (x :: t)
      rw [Fin.sum_univ_succ]
      have e0 : (if (x :: t).get 0 = a then (1 : ℕ) else 0)
          = (if x = a then (1 : ℕ) else 0) := rfl
      have es : ∀ p : Fin t.length,
          (if (x :: t).get (Fin.succ p) = a then (1 : ℕ) else 0)
            = (if t.get p = a then (1 : ℕ) else 0) := fun p => rfl
      rw [e0, Finset.sum_congr rfl (fun p _ => es p), ih, List.count_cons]
      by_cases hxa : x = a
      · subst hxa; simp [Nat.add_comm]
      · simp [hxa]

private theorem count_bosonRows {m : ℕ} (s : Fin m → ℕ) (i₀ : Fin m) :
    (bosonRows s).count i₀ = s i₀ := by
  induction m with
  | zero => exact absurd i₀.isLt (Nat.not_lt_zero _)
  | succ m ih =>
      have hsplit : bosonRows s = List.replicate (s 0) (0 : Fin (m + 1))
          ++ List.map (Fin.succ : Fin m → Fin (m + 1))
              (bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j))) := by
        have hfun1 : (fun j : Fin m =>
              List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j))
                ((Fin.succ : Fin m → Fin (m + 1)) j))
            = (fun j : Fin m => List.map (Fin.succ : Fin m → Fin (m + 1))
                (List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j)) j)) :=
          funext fun j => List.map_replicate.symm
        rw [bosonRows, List.finRange_succ, List.flatMap_cons, List.flatMap_map, hfun1,
          ← List.map_flatMap,
          show (List.finRange m).flatMap
              (fun j : Fin m => List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j)) j)
            = bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j)) from rfl]
      rw [hsplit, List.count_append]
      rcases Fin.eq_zero_or_eq_succ i₀ with rfl | ⟨j, rfl⟩
      · have h0 : (List.map (Fin.succ : Fin m → Fin (m + 1))
            (bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j)))).count
            (0 : Fin (m + 1)) = 0 :=
          List.count_eq_zero_of_not_mem (fun hmem => by
            rcases List.mem_map.mp hmem with ⟨p, _, hp⟩
            exact Fin.succ_ne_zero p hp)
        rw [List.count_replicate_self, h0, Nat.add_zero]
      · rw [List.count_map_of_injective _ (Fin.succ : Fin m → Fin (m + 1))
          (Fin.succ_injective _) j]
        have hne : (List.replicate (s 0) (0 : Fin (m + 1))).count
            ((Fin.succ : Fin m → Fin (m + 1)) j) = 0 := by
          refine List.count_eq_zero_of_not_mem (fun hmem => ?_)
          rw [List.mem_replicate] at hmem
          exact Fin.succ_ne_zero j hmem.2
        rw [hne, Nat.zero_add, ih (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j))]

theorem bosonDistributionNormalization : BosonDistributionNormalization := by
  unfold BosonDistributionNormalization
  intro m n A hA
  classical

  set c : (Fin n → Fin m) → ℂ := fun u => ∏ j, A (u j) j
  have hnormC : ∀ z : ℂ, ↑(Complex.normSq z) = z * star z := fun z => by
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    ring
  have hstarprod : ∀ u : Fin n → Fin m, star (c u) = ∏ j, star (A (u j) j) := by
    intro u
    exact map_prod (starRingEnd ℂ) (fun j => A (u j) j) Finset.univ

  have hoccS : ∀ S : FockOccupation m n,
      occFn (fun p : Fin n => (bosonRows (fun i => ((S.1 i : ℕ)))).get
          ⟨(p : ℕ), by
            have hlen : (bosonRows (fun i => ((S.1 i : ℕ)))).length = n :=
              (bosonRows_length (fun i => ((S.1 i : ℕ)))).trans S.2
            rw [hlen]; exact p.isLt⟩)
        = (fun i => ((S.1 i : ℕ))) := by
    intro S
    funext i
    have hlen : (bosonRows (fun i => ((S.1 i : ℕ)))).length = n :=
      (bosonRows_length (fun i => ((S.1 i : ℕ)))).trans S.2
    simp only [occFn]
    rw [Fintype.sum_equiv (finCongr hlen.symm)
      (fun p : Fin n => (if (bosonRows (fun i => ((S.1 i : ℕ)))).get
        ⟨(p : ℕ), by
          have hlen : (bosonRows (fun i => ((S.1 i : ℕ)))).length = n :=
            (bosonRows_length (fun i => ((S.1 i : ℕ)))).trans S.2
          rw [hlen]; exact p.isLt⟩ = i then (1 : ℕ) else 0))
      (fun q : Fin (bosonRows (fun i => ((S.1 i : ℕ)))).length =>
        (if (bosonRows (fun i => ((S.1 i : ℕ)))).get q = i then (1 : ℕ) else 0))
      (fun _ => rfl), sum_get_count, count_bosonRows]

  have hPer : ∀ S : FockOccupation m n,
      Matrix.permanent (bosonRowMatrix A S)
        = ((∏ i, ((S.1 i : ℕ))! : ℕ) : ℂ) * (∑ g : Fin n → Fin m,
            (if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g) := by
    intro S
    have hrow : Matrix.permanent (bosonRowMatrix A S)
        = ∑ σ : Equiv.Perm (Fin n), c (fun j : Fin n =>
            (fun p : Fin n => (bosonRows (fun i => ((S.1 i : ℕ)))).get
              ⟨(p : ℕ), by
                have hlen : (bosonRows (fun i => ((S.1 i : ℕ)))).length = n :=
                  (bosonRows_length (fun i => ((S.1 i : ℕ)))).trans S.2
                rw [hlen]; exact p.isLt⟩) (σ j)) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rfl
    rw [hrow, sum_perm_comp (fun p : Fin n => (bosonRows (fun i => ((S.1 i : ℕ)))).get
      ⟨(p : ℕ), by
        have hlen : (bosonRows (fun i => ((S.1 i : ℕ)))).length = n :=
          (bosonRows_length (fun i => ((S.1 i : ℕ)))).trans S.2
        rw [hlen]; exact p.isLt⟩) c, hoccS S]

  have hsingle : ∀ g g' : Fin n → Fin m,
      (∑ S : FockOccupation m n,
        (((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
          (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) : ℕ) *
         ∏ i, ((S.1 i : ℕ))!))
      = ((if occFn g = occFn g' then (1 : ℕ) else 0) * ∏ i, (occFn g i)!) := by
    intro g g'
    by_cases hgg : occFn g = occFn g'
    · rw [Finset.sum_eq_single_of_mem
        (a := (⟨occFin g, occFin_sum g⟩ : FockOccupation m n))
        (f := fun S : FockOccupation m n =>
          ((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
            (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0)) *
          ∏ i, ((S.1 i : ℕ))!)
        (Finset.mem_univ _)
        (fun S _ hS => by
          have hne : occFn g ≠ (fun i => ((S.1 i : ℕ))) := by
            intro he
            refine hS (Subtype.ext (funext (fun i => Fin.ext (congrFun he i).symm)))
          show (((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
              (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) : ℕ) *
            ∏ i, ((S.1 i : ℕ))!) = 0
          rw [if_neg hne, Nat.zero_mul, Nat.zero_mul])]
      show ((if occFn g = occFn g then (1 : ℕ) else 0) *
            (if occFn g' = occFn g then (1 : ℕ) else 0) * ∏ i, (occFn g i)!)
            = ((if occFn g = occFn g' then (1 : ℕ) else 0) * ∏ i, (occFn g i)!)
      rw [if_pos rfl, if_pos hgg.symm, if_pos hgg]
    · rw [if_neg hgg, Nat.zero_mul]
      refine Finset.sum_eq_zero fun S _ => ?_
      by_cases h1 : occFn g = (fun i => ((S.1 i : ℕ)))
      · have h2 : occFn g' ≠ (fun i => ((S.1 i : ℕ))) := fun h2 => hgg (h1.trans h2.symm)
        rw [if_pos h1, if_neg h2, Nat.mul_zero, Nat.zero_mul]
      · rw [if_neg h1, Nat.zero_mul, Nat.zero_mul]

  have hperS : ∀ S : FockOccupation m n,
      (((Complex.normSq (Matrix.permanent (bosonRowMatrix A S))
          / ∏ i, ((S.1 i : ℕ))! : ℝ)) : ℂ)
        = ((∏ i, ((S.1 i : ℕ))! : ℕ) : ℂ) * ((∑ g : Fin n → Fin m,
            (if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g)
          * star (∑ g' : Fin n → Fin m,
            (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g')) := by
    intro S
    have h1 : Matrix.permanent (bosonRowMatrix A S)
        = ((∏ i, ((S.1 i : ℕ))! : ℕ) : ℂ) * (∑ g : Fin n → Fin m,
            (if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g) := hPer S
    have hFne : ((∏ i, ((S.1 i : ℕ))! : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
    rw [h1, Complex.normSq_mul, Complex.normSq_natCast, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_natCast, hnormC,
      mul_assoc, mul_div_cancel_left₀ _ hFne]

  have hCS : ∀ S : FockOccupation m n,
      ((∑ g : Fin n → Fin m,
            (if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g)
          * star (∑ g' : Fin n → Fin m,
            (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g'))
      = ∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
          (((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
            (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) : ℕ) : ℂ)
            * (c g * star (c g')) := by
    intro S
    have hsn : ∀ k : ℕ, (star ((k : ℕ) : ℂ)) = ((k : ℕ) : ℂ) := fun k => star_natCast k
    have hst : star (∑ g' : Fin n → Fin m,
          (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) * c g')
        = ∑ g' : Fin n → Fin m, star ((if occFn g' = (fun i => ((S.1 i : ℕ))) then
          (1 : ℕ) else 0) * c g') :=
      map_sum (starRingEnd ℂ) _ _
    rw [hst, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => ?_
    rw [star_mul', hsn, Nat.cast_mul]
    ring

  have step1 : Complex.ofReal (∑ S : FockOccupation m n, bosonWeight A S)
      = ∑ S : FockOccupation m n,
          ((∏ i, ((S.1 i : ℕ))! : ℕ) : ℂ) * (∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
            (((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
              (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) : ℕ) : ℂ)
              * (c g * star (c g'))) := by
    rw [Complex.ofReal_sum (Finset.univ : Finset (FockOccupation m n))
      (fun S : FockOccupation m n => bosonWeight A S)]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold bosonWeight
    rw [hperS S, hCS S]
  have step2 : ∑ S : FockOccupation m n,
          ((∏ i, ((S.1 i : ℕ))! : ℕ) : ℂ) * (∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
            (((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
              (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) : ℕ) : ℂ)
              * (c g * star (c g')))
      = ∑ S : FockOccupation m n, ∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
          ((((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
            (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
            ∏ i, ((S.1 i : ℕ))!) : ℕ) : ℂ) * (c g * star (c g')) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g' _ => by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; ring
  have step3 : ∑ S : FockOccupation m n, ∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
          ((((if occFn g = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
            (if occFn g' = (fun i => ((S.1 i : ℕ))) then (1 : ℕ) else 0) *
            ∏ i, ((S.1 i : ℕ))!) : ℕ) : ℂ) * (c g * star (c g'))
      = ∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
          ((((if occFn g = occFn g' then (1 : ℕ) else 0) *
            ∏ i, (occFn g i)!) : ℕ) : ℂ) * (c g * star (c g')) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [← Finset.sum_mul, ← Nat.cast_sum, hsingle g g']
  have hLHS : Complex.ofReal (∑ S : FockOccupation m n, bosonWeight A S)
      = ∑ g : Fin n → Fin m, ∑ g' : Fin n → Fin m,
          ((((if occFn g = occFn g' then (1 : ℕ) else 0) *
            ∏ i, (occFn g i)!) : ℕ) : ℂ) * (c g * star (c g')) :=
    step1.trans (step2.trans step3)

  have hentry : ∀ (x y : Fin n), (Aᴴ * A) x y = ∑ i : Fin m, star (A i x) * A i y := by
    intro x y; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hRHS0 : Matrix.permanent (Aᴴ * A)
      = ∑ σ : Equiv.Perm (Fin n), ∑ u : Fin n → Fin m,
          star (c (fun k : Fin n => u (σ.symm k))) * c u := by
    rw [Matrix.permanent]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_congr rfl (fun j _ => hentry (σ j) j), Finset.prod_univ_sum,
      Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.prod_mul_distrib (f := fun i : Fin n => star (A (u i) (σ i)))
      (g := fun i : Fin n => A (u i) i)]
    have hcU : (∏ j, A (u j) j) = c u := rfl
    have hprod1 : (∏ j, star (A (u j) (σ j)))
        = star (c (fun k : Fin n => u (σ.symm k))) := by
      have hstep1 : (∏ j, star (A (u j) (σ j)))
          = ∏ j, star (A (u ((σ.symm : Fin n → Fin n) (σ j))) (σ j)) :=
        Finset.prod_congr rfl fun j _ => by rw [Equiv.symm_apply_apply]
      rw [hstep1,
        show (∏ j, star (A (u ((σ.symm : Fin n → Fin n) (σ j))) (σ j)))
            = ∏ j : Fin n, (fun k : Fin n => star (A (u (σ.symm k)) k)) (σ j) from rfl,
        Equiv.prod_comp σ (fun k : Fin n => star (A (u (σ.symm k)) k))]
      exact (hstarprod (fun k : Fin n => u (σ.symm k))).symm
    rw [hprod1, hcU]
  have hRHS1 : ∑ σ : Equiv.Perm (Fin n), ∑ u : Fin n → Fin m,
      star (c (fun k : Fin n => u (σ.symm k))) * c u
    = ∑ u : Fin n → Fin m, ∑ g : Fin n → Fin m,
        ((((if occFn u = occFn g then (1 : ℕ) else 0) *
          ∏ i, (occFn u i)!) : ℕ) : ℂ) * (c u * star (c g)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul]
    have hes : (∑ σ : Equiv.Perm (Fin n), star (c (fun k : Fin n => u (σ.symm k))))
        = ∑ σ : Equiv.Perm (Fin n), star (c (fun j : Fin n => u (σ j))) := by
      exact Fintype.sum_equiv
        (⟨fun σ : Equiv.Perm (Fin n) => σ.symm, fun σ : Equiv.Perm (Fin n) => σ.symm,
          fun σ => Equiv.symm_symm σ, fun σ => Equiv.symm_symm σ⟩ :
          Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n))
        (fun σ : Equiv.Perm (Fin n) => star (c (fun k : Fin n => u (σ.symm k))))
        (fun τ : Equiv.Perm (Fin n) => star (c (fun j : Fin n => u (τ j))))
        (fun _ => rfl)
    rw [hes, sum_perm_comp u (fun g : Fin n → Fin m => star (c g)),
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hgu : occFn g = occFn u
    · rw [if_pos hgu, if_pos hgu.symm, Nat.cast_mul]; ring
    · rw [if_neg hgu, if_neg (fun h => hgu h.symm), Nat.cast_mul]; ring

  refine Complex.ofReal_inj.mp ?_
  rw [hLHS]
  show (∑ u : Fin n → Fin m, ∑ g : Fin n → Fin m,
      ((((if occFn u = occFn g then (1 : ℕ) else 0) *
        ∏ i, (occFn u i)!) : ℕ) : ℂ) * (c u * star (c g))) = ((1 : ℝ) : ℂ)
  rw [← hRHS1, ← hRHS0, hA, Matrix.permanent_one]
  rfl

end Qatlib.Concepts.BosonFock.PermAnalysis
