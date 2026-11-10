/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshCheckerCounting
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.FreshCheckerSoundness
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

def freshE {n : ℕ} (U : Finset (Fin n)) : Fin (Fintype.card ↥U) → Fin n :=
  fun i => ((Fintype.equivFin ↥U).symm i : Fin n)

def freshMarked {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)) : Fin n → Bool :=
  fun v => decide (∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ ≠ u₂ ∧ adj v u₁ ∧ adj v u₂ ∧ adj u₁ u₂)

def freshSubR {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)) (v : Fin n) :
    (Fin 2 → Fin (Fintype.card ↥U)) → Bool :=
  fun t => decide (t 0 ≠ t 1 ∧ adj v (freshE U (t 0)) ∧ adj v (freshE U (t 1)) ∧
    adj (freshE U (t 0)) (freshE U (t 1)))

def freshTest {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (r' c₀ : ℕ) (stape : ℕ → kcs.seed) : Fin n → Bool :=
  let m : ℕ := Fintype.card ↥U
  fun v =>
    ((List.range c₀).any fun i =>
      match kcs.run (n := m) (k := 2) r' (freshSubR adj U v) r' 1 0
          (stape (v.val * c₀ + i)) with
      | some t => adj v (freshE U (t 0)) && adj v (freshE U (t 1))
      | none => false)

def freshTcost (kcs : KCollisionSolver) (m r' c₀ : ℕ) : ℕ :=
  c₀ * (kcs.κ * (Nat.log 2 (m + 1) + 2) * (r' + (m / r') * Nat.sqrt r')) + 2

theorem triCheckFresh_eq {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (ntape : ncs.seed) :
    triCheckFresh adj U kcs ncs r' c₀ stape ntape =
    match ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ntape with
    | none => (none, ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ntape)
    | some v =>
        let ex := triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
          (fun i => stape (n * c₀ + i))
        match ex.1 with
        | some t => (some (freshE U (t 0), freshE U (t 1)),
            ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
              (freshTcost kcs (Fintype.card ↥U) r' c₀) n ntape + ex.2 + 2)
        | none => (none, ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
            (freshTcost kcs (Fintype.card ↥U) r' c₀) n ntape + ex.2 + 2) := rfl

theorem freshE_mem {n : ℕ} (U : Finset (Fin n)) (i : Fin (Fintype.card ↥U)) :
    freshE U i ∈ U := ((Fintype.equivFin ↥U).symm i).property

theorem freshE_inj {n : ℕ} (U : Finset (Fin n)) : Function.Injective (freshE U) := by
  intro a b hab
  exact (Fintype.equivFin ↥U).symm.injective (Subtype.ext hab)

theorem freshTest_sound {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (r' c₀ : ℕ) (stape : ℕ → kcs.seed) (v : Fin n)
    (h : freshTest adj U kcs r' c₀ stape v = true) :
    freshMarked adj U v = true := by
  simp only [freshTest, List.any_eq_true] at h
  rcases h with ⟨i, hi, hv⟩
  simp only [List.mem_range] at hi
  cases hr : kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0
      (stape (v.val * c₀ + i)) with
  | none => simp [hr] at hv
  | some t =>
    have hR := kcs.sound (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 _ hr
    have hcon : t 0 ≠ t 1 ∧ adj v (freshE U (t 0)) = true ∧ adj v (freshE U (t 1)) = true ∧
        adj (freshE U (t 0)) (freshE U (t 1)) = true := of_decide_eq_true hR
    simp only [hr, hcon.2.1, hcon.2.2.1, Bool.true_and] at hv
    exact decide_eq_true
      ⟨freshE U (t 0), freshE_mem U (t 0), freshE U (t 1), freshE_mem U (t 1),
        fun hEq => hcon.1 (freshE_inj U hEq), hcon.2.1, hcon.2.2.1, hcon.2.2.2⟩

theorem freshSubR_nonempty {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (v : Fin n) (h : freshMarked adj U v = true) :
    ∃ t : Fin 2 → Fin (Fintype.card ↥U), freshSubR adj U v t = true := by
  rcases of_decide_eq_true h with ⟨u₁, hu₁, u₂, hu₂, hne, hadj1, hadj2, hadj3⟩
  refine ⟨fun b => if hb : b = 0 then Fintype.equivFin ↥U ⟨u₁, hu₁⟩
      else Fintype.equivFin ↥U ⟨u₂, hu₂⟩, ?_⟩
  have key : ∀ b : Fin 2, freshE U (if hb : b = 0 then Fintype.equivFin ↥U ⟨u₁, hu₁⟩
      else Fintype.equivFin ↥U ⟨u₂, hu₂⟩) = if b = 0 then u₁ else u₂ := by
    intro b
    split_ifs with hb
    · simp only [freshE]
      exact congrArg Subtype.val ((Fintype.equivFin ↥U).symm_apply_apply ⟨u₁, hu₁⟩)
    · simp only [freshE]
      exact congrArg Subtype.val ((Fintype.equivFin ↥U).symm_apply_apply ⟨u₂, hu₂⟩)
  have h01 : (fun b : Fin 2 => if hb : b = 0 then Fintype.equivFin ↥U ⟨u₁, hu₁⟩
      else Fintype.equivFin ↥U ⟨u₂, hu₂⟩) 0 ≠
      (fun b : Fin 2 => if hb : b = 0 then Fintype.equivFin ↥U ⟨u₁, hu₁⟩
      else Fintype.equivFin ↥U ⟨u₂, hu₂⟩) 1 := by
    simp only [dif_neg (show ¬ (1 : Fin 2) = 0 by decide)]
    intro hEq
    exact hne (congrArg Subtype.val ((Fintype.equivFin ↥U).injective hEq))
  refine decide_eq_true ⟨h01, ?_, ?_, ?_⟩
  · rw [key 0, if_pos rfl]; exact hadj1
  · rw [key 1, if_neg (by decide : ¬ (1 : Fin 2) = 0)]; exact hadj2
  · rw [key 0, if_pos rfl, key 1, if_neg (by decide : ¬ (1 : Fin 2) = 0)]; exact hadj3

theorem fresh_E1_card {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (hex : ∃ v : Fin n, freshMarked adj U v = true) :
    haveI := ncs.seedFin
    haveI := kcs.seedFin
    ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
      ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
          (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none).card *
      (n + 1) ^ ncs.cExp ≤
      Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed)) := by
  letI := ncs.seedFin
  letI := kcs.seedFin
  have hfiber : ∀ τ : Fin (2 * n * c₀ + 1) → kcs.seed,
      ((Finset.univ.filter fun ρn : ncs.seed =>
        ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe τ))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = none).card : ℕ) *
        (n + 1) ^ ncs.cExp ≤ Fintype.card ncs.seed := by
    intro τ
    exact ncs.finds (freshMarked adj U) (freshTest adj U kcs r' c₀
      (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe τ))
      (freshTcost kcs (Fintype.card ↥U) r' c₀) n hex
      (fun v hv => freshTest_sound adj U kcs r' c₀ _ v hv)
  have hsum : (∑ τ : Fin (2 * n * c₀ + 1) → kcs.seed,
      ((Finset.univ.filter fun ρn : ncs.seed =>
        ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
            (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe τ))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = none).card : ℕ)) *
      (n + 1) ^ ncs.cExp ≤
      Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) := by
    calc (∑ τ : Fin (2 * n * c₀ + 1) → kcs.seed,
          ((Finset.univ.filter fun ρn : ncs.seed =>
            ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
                (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe τ))
              (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = none).card : ℕ)) *
        (n + 1) ^ ncs.cExp
        = ∑ τ : Fin (2 * n * c₀ + 1) → kcs.seed,
            (((Finset.univ.filter fun ρn : ncs.seed =>
              ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
                  (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe τ))
                (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = none).card : ℕ) *
              (n + 1) ^ ncs.cExp) := Finset.sum_mul _ _ _
      _ ≤ ∑ τ : Fin (2 * n * c₀ + 1) → kcs.seed, Fintype.card ncs.seed :=
          Finset.sum_le_sum fun τ _ => hfiber τ
      _ = Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  calc ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
      ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
          (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = none).card : ℕ) *
      (n + 1) ^ ncs.cExp
      = (∑ τ : Fin (2 * n * c₀ + 1) → kcs.seed,
          ((Finset.univ.filter fun ρn : ncs.seed =>
            ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
                (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe τ))
              (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = none).card : ℕ)) *
        (n + 1) ^ ncs.cExp := by
        rw [filter_product_card_sum_snd]
    _ ≤ Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) := hsum

theorem extSeed_prefix_read {S : Type} [Nonempty S] {B : ℕ} (τ : Fin B → S) (k : ℕ)
    (hk : k < B) : @extSeed B S _ τ k = τ ⟨k, hk⟩ := by
  rw [extSeed, dif_pos hk]

theorem fresh_prefix_lt (n c₀ k i : ℕ) (hv : k < n) (hi : i < c₀) :
    k * c₀ + i < n * c₀ := by
  have h2 : (k + 1) * c₀ ≤ n * c₀ := Nat.mul_le_mul_right c₀ (by omega)
  calc k * c₀ + i < k * c₀ + c₀ := by omega
    _ = (k + 1) * c₀ := by ring
    _ ≤ n * c₀ := h2

theorem freshTest_tapeUnsplit {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (r' c₀ : ℕ) (π : Fin (n * c₀) → kcs.seed)
    (σ : Fin (n * c₀ + 1) → kcs.seed) :
    freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe (tapeUnsplit π σ)) =
      freshTest adj U kcs r' c₀ (@extSeed (n * c₀) kcs.seed kcs.seedNe π) := by
  funext v
  simp only [freshTest]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  apply exists_congr
  intro i
  simp only [List.mem_range]
  constructor
  · rintro ⟨hi, hv⟩
    have hlt : v.val * c₀ + i < n * c₀ :=
      fresh_prefix_lt n c₀ v.val i v.isLt hi
    rw [@extSeed_tapeUnsplit_prefix kcs.seed kcs.seedNe n c₀ π σ _ hlt] at hv
    rw [@extSeed_prefix_read kcs.seed kcs.seedNe (n * c₀) π _ hlt]
    exact ⟨hi, hv⟩
  · rintro ⟨hi, hv⟩
    have hlt : v.val * c₀ + i < n * c₀ :=
      fresh_prefix_lt n c₀ v.val i v.isLt hi
    rw [@extSeed_prefix_read kcs.seed kcs.seedNe (n * c₀) π _ hlt] at hv
    rw [@extSeed_tapeUnsplit_prefix kcs.seed kcs.seedNe n c₀ π σ _ hlt]
    exact ⟨hi, hv⟩

theorem fresh_E2_fiber_some {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (ρn : ncs.seed) (π : Fin (n * c₀) → kcs.seed) (v : Fin n)
    (hrn : ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
        (@extSeed (n * c₀) kcs.seed kcs.seedNe π))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = some v) :
    haveI := ncs.seedFin
    haveI := kcs.seedFin
    ((Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
          (tapeUnsplit π σ) (n * c₀ + i))).1 = none).card *
      (U.card + 1) ^ (c₀ * kcs.cExp) ≤
      Fintype.card kcs.seed ^ (n * c₀ + 1)) := by
  letI := ncs.seedFin
  letI := kcs.seedFin
  have hn1 : 0 < n := Fin.pos v
  have hnc : c₀ ≤ n * c₀ := Nat.le_mul_of_pos_left c₀ hn1
  have hmarked : freshMarked adj U v = true :=
    ncs.sound (freshMarked adj U) (freshTest adj U kcs r' c₀
      (@extSeed (n * c₀) kcs.seed kcs.seedNe π)) (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn hrn
  obtain ⟨tw, htw⟩ := freshSubR_nonempty adj U v hmarked
  have hfinds : (Finset.univ.filter fun σ' : kcs.seed =>
      kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none).card *
      (U.card + 1) ^ kcs.cExp ≤ Fintype.card kcs.seed := by
    have h := kcs.finds (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 ⟨tw, htw⟩
    calc (Finset.univ.filter fun σ' : kcs.seed =>
          kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none).card *
        (U.card + 1) ^ kcs.cExp
        ≤ (Finset.univ.filter fun σ' : kcs.seed =>
          kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none).card *
          (Fintype.card ↥U + 1) ^ kcs.cExp :=
          Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left (by rw [Fintype.card_coe]) kcs.cExp)
      _ ≤ Fintype.card kcs.seed := h
  have hbox : (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
          (tapeUnsplit π σ) (n * c₀ + i))).1 = none) ⊆
      Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
        ∀ i : Fin c₀, σ ⟨v.val * c₀ + i.val, by
          have := fresh_prefix_lt n c₀ v.val i.val v.isLt i.isLt
          omega⟩ ∈ Finset.univ.filter fun σ' : kcs.seed =>
        kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    have hiff := triCheckAmpExtract_none_iff adj (freshE U) kcs r' (freshSubR adj U v) v c₀
      (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
        (tapeUnsplit π σ) (n * c₀ + i))
      (fun t ht => by
        have hcon := of_decide_eq_true ht
        simp only [Bool.and_eq_true, hcon.2.1, hcon.2.2.1, and_self])
    have hall := hiff.mp hσ
    intro i
    have hi := hall i.val (by simp)
    change kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0
        (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe (tapeUnsplit π σ)
          (n * c₀ + (v.val * c₀ + i.val))) = none at hi
    have hread : @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe (tapeUnsplit π σ)
        (n * c₀ + (v.val * c₀ + i.val)) = σ ⟨v.val * c₀ + i.val, by
          have := fresh_prefix_lt n c₀ v.val i.val v.isLt i.isLt
          omega⟩ :=
      @extSeed_tapeUnsplit_suffix kcs.seed kcs.seedNe n c₀ π σ (v.val * c₀ + i.val) (by
        have := fresh_prefix_lt n c₀ v.val i.val v.isLt i.isLt
        omega)
    rwa [hread] at hi
  have hcard : (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
          (tapeUnsplit π σ) (n * c₀ + i))).1 = none).card ≤
      (Finset.univ.filter fun σ' : kcs.seed =>
        kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none).card ^ c₀ *
      Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀) := by
    refine le_trans (Finset.card_le_card hbox) ?_
    refine Eq.le ?_
    have hinj : Function.Injective (fun (i : Fin c₀) =>
        (⟨v.val * c₀ + i.val, by
          have := fresh_prefix_lt n c₀ v.val i.val v.isLt i.isLt
          omega⟩ : Fin (n * c₀ + 1))) := by
      intro a b hab
      have h : v.val * c₀ + a.val = v.val * c₀ + b.val :=
        congrArg (fun t : Fin (n * c₀ + 1) => t.val) hab
      exact Fin.ext (by omega)
    exact bad_box_card (Finset.univ.filter fun σ' : kcs.seed =>
      kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none)
      (fun i : Fin c₀ => ⟨v.val * c₀ + i.val, by
        have := fresh_prefix_lt n c₀ v.val i.val v.isLt i.isLt
        omega⟩) hinj
  have hfinal : (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
          (tapeUnsplit π σ) (n * c₀ + i))).1 = none).card *
      (U.card + 1) ^ (c₀ * kcs.cExp) ≤
      Fintype.card kcs.seed ^ (n * c₀ + 1) := by
    have hexp : ((U.card + 1) ^ kcs.cExp) ^ c₀ = (U.card + 1) ^ (c₀ * kcs.cExp) := by
      rw [Nat.mul_comm c₀ kcs.cExp, Nat.pow_mul]
    rw [← hexp]
    calc (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
              (tapeUnsplit π σ) (n * c₀ + i))).1 = none).card *
        ((U.card + 1) ^ kcs.cExp) ^ c₀
        ≤ ((Finset.univ.filter fun σ' : kcs.seed =>
            kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none).card ^ c₀ *
          Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀)) *
          ((U.card + 1) ^ kcs.cExp) ^ c₀ :=
          mul_le_mul hcard (Nat.le_refl _) (Nat.zero_le _) (Nat.zero_le _)
      _ = ((Finset.univ.filter fun σ' : kcs.seed =>
            kcs.run (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 σ' = none).card *
          (U.card + 1) ^ kcs.cExp) ^ c₀ *
        Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀) := by
          rw [Nat.mul_pow]
          ring
      _ ≤ (Fintype.card kcs.seed) ^ c₀ * Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hfinds c₀)
      _ = Fintype.card kcs.seed ^ (n * c₀ + 1) := by
          have hN : n * c₀ + 1 - c₀ + c₀ = n * c₀ + 1 := by omega
          calc Fintype.card kcs.seed ^ c₀ * Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀)
              = Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀) * Fintype.card kcs.seed ^ c₀ :=
                Nat.mul_comm _ _
            _ = Fintype.card kcs.seed ^ (n * c₀ + 1 - c₀ + c₀) :=
                (Nat.pow_add _ _ _).symm
            _ = Fintype.card kcs.seed ^ (n * c₀ + 1) := by rw [hN]
  exact hfinal

theorem fresh_run_cost {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (r' : ℕ) (v : Fin n) (ρ : kcs.seed) :
    kcs.cost (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 ρ ≤
      kcs.κ * (Nat.log 2 (Fintype.card ↥U + 1) + 2) *
        (r' + (Fintype.card ↥U / r') ^ (2 / 2) * (0 + Nat.sqrt r' * 1)) :=
  kcs.charges (n := Fintype.card ↥U) (k := 2) r' (freshSubR adj U v) r' 1 0 ρ

theorem fresh_cost_le {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (hκn : 1 ≤ ncs.κ)
    (stape : ℕ → kcs.seed) (ntape : ncs.seed) :
    (triCheckFresh adj U kcs ncs r' c₀ stape ntape).2 ≤
      2 * cCOf kcs ncs n U.card r' c₀ := by
  have hcoe : U.card = Fintype.card ↥U := (Fintype.card_coe U).symm
  set m : ℕ := Fintype.card ↥U with hm
  set W : ℕ := kcs.κ * (Nat.log 2 (U.card + 1) + 2) * (r' + (U.card / r') * Nat.sqrt r') with hW
  have hL : 2 ≤ Nat.log 2 (n + 1) + 2 := by omega
  have hS : 1 ≤ Nat.sqrt (n + 1) + 1 := by omega
  have hch : ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
      (freshTcost kcs m r' c₀) n ntape ≤
      ncs.κ * (Nat.log 2 (n + 1) + 2) * (freshTcost kcs m r' c₀ + 1) *
        (Nat.sqrt (n + 1) + 1) :=
    ncs.charges (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
      (freshTcost kcs m r' c₀) n ntape
  have htcost : freshTcost kcs m r' c₀ + 1 = c₀ * W + 3 := by
    simp only [freshTcost]
    rw [hm, Fintype.card_coe, hW]
  have hex_cost : ∀ v : Fin n,
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => stape (n * c₀ + i))).2 ≤ c₀ * W := by
    intro v
    refine triCheckAmpExtract_cost_le adj (freshE U) kcs r' (freshSubR adj U v) v c₀
      (fun i => stape (n * c₀ + i)) W ?_
    intro i _
    have h := fresh_run_cost adj U kcs r' v (stape (n * c₀ + (v.val * c₀ + i)))
    norm_num [Nat.reduceDiv] at h
    exact h
  have hkey : c₀ * W + 2 ≤
      ncs.κ * (Nat.log 2 (n + 1) + 2) * (c₀ * W + 3) * (Nat.sqrt (n + 1) + 1) := by
    have hκLS : (2 : ℕ) ≤ ncs.κ * (Nat.log 2 (n + 1) + 2) * (Nat.sqrt (n + 1) + 1) := by
      calc (2 : ℕ) = (1 : ℕ) * 2 := by ring
        _ ≤ ncs.κ * (Nat.log 2 (n + 1) + 2) :=
            Nat.mul_le_mul hκn hL
        _ ≤ ncs.κ * (Nat.log 2 (n + 1) + 2) * (Nat.sqrt (n + 1) + 1) :=
            Nat.le_mul_of_pos_right _ hS
    calc c₀ * W + 2 ≤ c₀ * W + 3 := by omega
      _ ≤ 2 * (c₀ * W + 3) := by omega
      _ ≤ (ncs.κ * (Nat.log 2 (n + 1) + 2) * (Nat.sqrt (n + 1) + 1)) * (c₀ * W + 3) :=
          Nat.mul_le_mul_right _ hκLS
      _ = ncs.κ * (Nat.log 2 (n + 1) + 2) * (c₀ * W + 3) * (Nat.sqrt (n + 1) + 1) := by
          ring
  have hcomb0 : ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
      (freshTcost kcs m r' c₀) n ntape ≤ 2 * cCOf kcs ncs n m r' c₀ := by
    have hcCOf : cCOf kcs ncs n m r' c₀ =
        ncs.κ * (Nat.log 2 (n + 1) + 2) * (c₀ * W + 3) * (Nat.sqrt (n + 1) + 1) := by
      rw [cCOf, hm, Fintype.card_coe, hW]
    rw [hcCOf]
    exact (hch.trans_eq (by rw [htcost])).trans
      (Nat.le_mul_of_pos_left _ (by omega : 0 < 2))
  rw [triCheckFresh_eq]
  rw [hcoe]
  cases hrun : ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
      (freshTcost kcs m r' c₀) n ntape with
  | none =>
    exact hcomb0
  | some v =>
    have hex := hex_cost v
    have hcomb : ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
        (freshTcost kcs m r' c₀) n ntape +
        (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
          (fun i => stape (n * c₀ + i))).2 + 2 ≤ 2 * cCOf kcs ncs n m r' c₀ := by
      have hcCOf : cCOf kcs ncs n m r' c₀ =
          ncs.κ * (Nat.log 2 (n + 1) + 2) * (c₀ * W + 3) * (Nat.sqrt (n + 1) + 1) := by
        rw [cCOf, hm, Fintype.card_coe, hW]
      rw [hcCOf]
      have h1 : ncs.cost (freshMarked adj U) (freshTest adj U kcs r' c₀ stape)
          (freshTcost kcs m r' c₀) n ntape +
        (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
          (fun i => stape (n * c₀ + i))).2 + 2 ≤
        (ncs.κ * (Nat.log 2 (n + 1) + 2) * (freshTcost kcs m r' c₀ + 1) *
          (Nat.sqrt (n + 1) + 1)) + (c₀ * W) + 2 :=
        Nat.add_le_add (Nat.add_le_add hch hex) (Nat.le_refl _)
      have h2 : (ncs.κ * (Nat.log 2 (n + 1) + 2) * (freshTcost kcs m r' c₀ + 1) *
          (Nat.sqrt (n + 1) + 1)) + (c₀ * W) + 2 =
        ncs.κ * (Nat.log 2 (n + 1) + 2) * (c₀ * W + 3) * (Nat.sqrt (n + 1) + 1) +
        (c₀ * W + 2) := by
        rw [htcost]
        ring
      exact (h1.trans_eq h2).trans
        ((Nat.add_le_add (Nat.le_refl _) hkey).trans_eq (by ring))
    (try dsimp only)
    cases hext : (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
      (fun i => stape (n * c₀ + i))).1 with
    | some t => exact hcomb
    | none => exact hcomb

theorem fresh_E2_card {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ) :
    haveI := ncs.seedFin
    haveI := kcs.seedFin
    ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
      ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
          (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card *
      (U.card + 1) ^ (c₀ * kcs.cExp) ≤
      Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed)) := by
  letI := ncs.seedFin
  letI := kcs.seedFin

  have hfib : ∀ ρn : ncs.seed, ∀ π : Fin (n * c₀) → kcs.seed,
      ((Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
        ∃ v : Fin n, ncs.run (freshMarked adj U)
            (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
              (tapeUnsplit π σ)))
          (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = some v ∧
        (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
          (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
            (tapeUnsplit π σ) (n * c₀ + i))).1 = none).card : ℕ) *
      (U.card + 1) ^ (c₀ * kcs.cExp) ≤
      Fintype.card kcs.seed ^ (n * c₀ + 1) := by
    intro ρn π
    cases hrn : ncs.run (freshMarked adj U)
        (freshTest adj U kcs r' c₀ (@extSeed (n * c₀) kcs.seed kcs.seedNe π))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn with
    | none =>
      have hcard0 : (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
          ∃ v : Fin n, ncs.run (freshMarked adj U)
              (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                (tapeUnsplit π σ)))
            (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = some v ∧
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
              (tapeUnsplit π σ) (n * c₀ + i))).1 = none).card = 0 := by
        refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
        intro σ _
        rintro ⟨v, hv, -⟩
        rw [freshTest_tapeUnsplit adj U kcs r' c₀ π σ, hrn] at hv
        cases hv
      rw [hcard0, Nat.zero_mul]
      exact Nat.zero_le _
    | some v =>
      have hseteq : (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
          ∃ v : Fin n, ncs.run (freshMarked adj U)
              (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                (tapeUnsplit π σ)))
            (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρn = some v ∧
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
              (tapeUnsplit π σ) (n * c₀ + i))).1 = none) =
          (Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
              (tapeUnsplit π σ) (n * c₀ + i))).1 = none) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨v', hvrun, hex⟩
          rw [freshTest_tapeUnsplit adj U kcs r' c₀ π σ, hrn] at hvrun
          cases Option.some.inj hvrun
          exact hex
        · intro hex
          refine ⟨v, ?_, hex⟩
          rw [freshTest_tapeUnsplit adj U kcs r' c₀ π σ, hrn]
      rw [hseteq]
      exact fresh_E2_fiber_some adj U kcs ncs r' c₀ ρn π v hrn

  have hnbij : ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
      ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
          (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ) =
      ((Finset.univ.filter fun t : (ncs.seed × (Fin (n * c₀) → kcs.seed)) × (Fin (n * c₀ + 1) → kcs.seed) =>
      ∃ v : Fin n, ncs.run (freshMarked adj U)
          (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
            (tapeUnsplit t.1.2 t.2)))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n t.1.1 = some v ∧
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
          (tapeUnsplit t.1.2 t.2) (n * c₀ + i))).1 = none).card : ℕ) := by
    refine Finset.card_nbij
      (fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
        ((ρ.1, fun j => ρ.2 (prefixCoord j)), fun j => ρ.2 (suffixCoord j))) ?_ ?_ ?_
    · intro ρ hρ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      rw [tapeUnsplit_canonical ρ.2]
      exact hρ
    · intro ρ _ ρ' _ h
      rw [Prod.ext_iff]
      refine ⟨congrArg
        (fun p : (ncs.seed × (Fin (n * c₀) → kcs.seed)) × (Fin (n * c₀ + 1) → kcs.seed) =>
          p.1.1) h, ?_⟩
      rw [← tapeUnsplit_canonical ρ.2, ← tapeUnsplit_canonical ρ'.2]
      exact congrArg
        (fun q : (Fin (n * c₀) → kcs.seed) × (Fin (n * c₀ + 1) → kcs.seed) =>
          tapeUnsplit q.1 q.2)
        (congrArg
          (fun p : (ncs.seed × (Fin (n * c₀) → kcs.seed)) × (Fin (n * c₀ + 1) → kcs.seed) =>
            (p.1.2, p.2)) h)
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      refine ⟨(t.1.1, tapeUnsplit t.1.2 t.2), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ht
      · rw [Prod.mk.injEq]
        refine ⟨?_, tapeSuffix_unsplit t.1.2 t.2⟩
        rw [Prod.mk.injEq]
        exact ⟨rfl, tapePrefix_unsplit t.1.2 t.2⟩

  have hfinal : ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
      ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
          (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
        (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
      (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
        (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ) *
      (U.card + 1) ^ (c₀ * kcs.cExp) ≤
      Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) := by
    calc ((Finset.univ.filter fun ρ : ncs.seed × (Fin (2 * n * c₀ + 1) → kcs.seed) =>
          ∃ v : Fin n, ncs.run (freshMarked adj U) (freshTest adj U kcs r' c₀
              (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2))
            (freshTcost kcs (Fintype.card ↥U) r' c₀) n ρ.1 = some v ∧
          (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
            (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe ρ.2 (n * c₀ + i))).1 = none).card : ℕ) *
        (U.card + 1) ^ (c₀ * kcs.cExp)
        = ((Finset.univ.filter fun t : (ncs.seed × (Fin (n * c₀) → kcs.seed)) × (Fin (n * c₀ + 1) → kcs.seed) =>
            ∃ v : Fin n, ncs.run (freshMarked adj U)
                (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                  (tapeUnsplit t.1.2 t.2)))
              (freshTcost kcs (Fintype.card ↥U) r' c₀) n t.1.1 = some v ∧
            (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
              (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                (tapeUnsplit t.1.2 t.2) (n * c₀ + i))).1 = none).card : ℕ) *
          (U.card + 1) ^ (c₀ * kcs.cExp) := by
            rw [hnbij]
      _ = ((∑ a : (ncs.seed × (Fin (n * c₀) → kcs.seed)),
            ((Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
              ∃ v : Fin n, ncs.run (freshMarked adj U)
                  (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                    (tapeUnsplit a.2 σ)))
                (freshTcost kcs (Fintype.card ↥U) r' c₀) n a.1 = some v ∧
              (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
                (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                  (tapeUnsplit a.2 σ) (n * c₀ + i))).1 = none).card : ℕ)) : ℕ) *
          (U.card + 1) ^ (c₀ * kcs.cExp) := by
            rw [filter_product_card_sum_fst
              (fun t : (ncs.seed × (Fin (n * c₀) → kcs.seed)) × (Fin (n * c₀ + 1) → kcs.seed) =>
                ∃ v : Fin n, ncs.run (freshMarked adj U)
                    (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                      (tapeUnsplit t.1.2 t.2)))
                  (freshTcost kcs (Fintype.card ↥U) r' c₀) n t.1.1 = some v ∧
                (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
                  (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                    (tapeUnsplit t.1.2 t.2) (n * c₀ + i))).1 = none)]
      _ = ∑ a : (ncs.seed × (Fin (n * c₀) → kcs.seed)),
          (((Finset.univ.filter fun σ : Fin (n * c₀ + 1) → kcs.seed =>
            ∃ v : Fin n, ncs.run (freshMarked adj U)
                (freshTest adj U kcs r' c₀ (@extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                  (tapeUnsplit a.2 σ)))
              (freshTcost kcs (Fintype.card ↥U) r' c₀) n a.1 = some v ∧
            (triCheckAmpExtract adj (freshE U) kcs r' (freshSubR adj U v) v c₀
              (fun i => @extSeed (2 * n * c₀ + 1) kcs.seed kcs.seedNe
                (tapeUnsplit a.2 σ) (n * c₀ + i))).1 = none).card : ℕ) *
            (U.card + 1) ^ (c₀ * kcs.cExp)) := Finset.sum_mul _ _ _
      _ ≤ ∑ a : (ncs.seed × (Fin (n * c₀) → kcs.seed)),
          Fintype.card kcs.seed ^ (n * c₀ + 1) :=
          Finset.sum_le_sum fun a _ => hfib a.1 a.2
      _ = Fintype.card ncs.seed * Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) := by
          have hπ : Fintype.card (Fin (n * c₀) → kcs.seed) =
              Fintype.card kcs.seed ^ (n * c₀) := by
            rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have hτ : Fintype.card (Fin (2 * n * c₀ + 1) → kcs.seed) =
              Fintype.card kcs.seed ^ (n * c₀) * Fintype.card kcs.seed ^ (n * c₀ + 1) := by
            rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              ← Nat.pow_add]
            congr 1
            have := tape_two_mul n c₀
            omega
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, hπ, nsmul_eq_mul, hτ]
          push_cast
          ring
  exact hfinal

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
