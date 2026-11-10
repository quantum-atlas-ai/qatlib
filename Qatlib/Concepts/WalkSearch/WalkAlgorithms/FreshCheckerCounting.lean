/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

theorem tape_two_mul (n c₀ : ℕ) : 2 * (n * c₀) = 2 * n * c₀ := by ring

theorem filter_product_card_sum_fst {α β : Type*} [Fintype α] [Fintype β] (p : α × β → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ a : α, ((Finset.univ : Finset β).filter (fun b => p (a, b))).card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_nbij (fun y => ⟨y.1, y.2⟩) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe] at hy
    rw [Finset.mem_coe, Finset.mem_sigma]
    rw [Finset.mem_filter] at hy
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hy.2⟩
  · intro y _ z _ h
    have h1 : y.1 = z.1 := congrArg Sigma.fst h
    have h2 : y.2 = z.2 := by
      have := congrArg Sigma.snd h
      simpa using this
    rw [Prod.ext_iff]
    exact ⟨h1, h2⟩
  · intro b hb
    rw [Finset.mem_coe, Finset.mem_sigma] at hb
    have hb2 := (Finset.mem_filter).mp hb.2
    refine ⟨(b.1, b.2), ?_, Sigma.eta b⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hb2.2⟩

theorem filter_product_card_sum_snd {α β : Type*} [Fintype α] [Fintype β] (p : α × β → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ b : β, ((Finset.univ : Finset α).filter (fun a => p (a, b))).card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_nbij (fun y => ⟨y.2, y.1⟩) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe] at hy
    rw [Finset.mem_coe, Finset.mem_sigma]
    rw [Finset.mem_filter] at hy
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hy.2⟩
  · intro y _ z _ h
    have h1 : y.2 = z.2 := congrArg Sigma.fst h
    have h2 : y.1 = z.1 := by
      have := congrArg Sigma.snd h
      simpa using this
    rw [Prod.ext_iff]
    exact ⟨h2, h1⟩
  · intro b hb
    rw [Finset.mem_coe, Finset.mem_sigma] at hb
    have hb2 := (Finset.mem_filter).mp hb.2
    refine ⟨(b.2, b.1), ?_, Sigma.eta b⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hb2.2⟩

theorem bad_box_card {S : Type*} [Fintype S] [DecidableEq S] {N c : ℕ} (B : Finset S)
    (idx : Fin c → Fin N) (hinj : Function.Injective idx) :
    (Finset.univ.filter fun σ : Fin N → S => ∀ i, σ (idx i) ∈ B).card =
      B.card ^ c * Fintype.card S ^ (N - c) := by
  classical
  set img : Finset (Fin N) := Finset.univ.image idx with himg
  set t : Fin N → Finset S :=
    fun j => if h : ∃ i, idx i = j then B else Finset.univ with ht
  have himage : ∀ j : Fin N, j ∈ img ↔ ∃ i, idx i = j := by
    intro j
    simp only [himg, Finset.mem_image, Finset.mem_univ, true_and]
  have htimg : ∀ j ∈ img, t j = B := by
    intro j hj
    rw [ht]
    exact dif_pos ((himage j).mp hj)
  have htcompl : ∀ j ∈ imgᶜ, t j = Finset.univ := by
    intro j hj
    rw [ht]
    have hnotmem : j ∉ img := Finset.mem_compl.mp hj
    exact dif_neg (fun hex => hnotmem ((himage j).mpr hex))
  have hext : (Finset.univ.filter fun σ : Fin N → S => ∀ i, σ (idx i) ∈ B) =
      Fintype.piFinset t := by
    apply Finset.ext
    intro σ
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j ∈ img
      · rcases (himage j).mp hj with ⟨i, hi⟩
        rw [htimg j hj, ← hi]
        exact h.2 i
      · rw [htcompl j (by simpa using (Finset.mem_compl.mpr hj))]
        exact Finset.mem_univ _
    · intro h
      refine ⟨Finset.mem_univ _, fun i => ?_⟩
      have hi := h (idx i)
      have hex : ∃ i', idx i' = idx i := ⟨i, rfl⟩
      simp only [ht, dif_pos hex] at hi
      exact hi
  have himgcard : img.card = c := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcomplcard : imgᶜ.card = N - c := by
    rw [Finset.card_compl, himgcard, Fintype.card_fin]
  rw [hext, Fintype.card_piFinset]
  have hsplit2 : ∏ j, (t j).card =
      (∏ j ∈ img, B.card) * ∏ j ∈ imgᶜ, (Finset.univ : Finset S).card := by
    rw [← Finset.prod_mul_prod_compl img (fun j => (t j).card)]
    have hA : ∏ j ∈ img, (t j).card = ∏ j ∈ img, B.card :=
      Finset.prod_congr rfl fun j hj => by rw [htimg j hj]
    have hB : ∏ j ∈ imgᶜ, (t j).card = ∏ j ∈ imgᶜ, (Finset.univ : Finset S).card :=
      Finset.prod_congr rfl fun j hj => by rw [htcompl j hj]
    rw [hA, hB]
  rw [hsplit2, Finset.prod_const, Finset.prod_const, himgcard, hcomplcard, Finset.card_univ]

def tapeUnsplit {S : Type*} {n c₀ : ℕ} (π : Fin (n * c₀) → S) (σ : Fin (n * c₀ + 1) → S) :
    Fin (2 * n * c₀ + 1) → S :=
  fun k =>
    if h : k.val < n * c₀ then π ⟨k.val, h⟩
    else σ ⟨k.val - n * c₀, by
      have h2 := tape_two_mul n c₀
      have h1 := k.isLt
      omega⟩

def prefixCoord {n c₀ : ℕ} (j : Fin (n * c₀)) : Fin (2 * n * c₀ + 1) :=
  ⟨j.val, by have := tape_two_mul n c₀; have := j.isLt; omega⟩

def suffixCoord {n c₀ : ℕ} (j : Fin (n * c₀ + 1)) : Fin (2 * n * c₀ + 1) :=
  ⟨n * c₀ + j.val, by have := tape_two_mul n c₀; have := j.isLt; omega⟩

theorem tapeUnsplit_prefix_read {S : Type*} {n c₀ : ℕ} (π : Fin (n * c₀) → S)
    (σ : Fin (n * c₀ + 1) → S) (j : Fin (n * c₀)) :
    tapeUnsplit π σ (prefixCoord j) = π j := by
  have hd : j.val < n * c₀ := j.isLt
  show (if h : j.val < n * c₀ then π ⟨j.val, h⟩
      else σ ⟨j.val - n * c₀, _⟩) = π j
  rw [dif_pos hd]

theorem tapeUnsplit_suffix_read {S : Type*} {n c₀ : ℕ} (π : Fin (n * c₀) → S)
    (σ : Fin (n * c₀ + 1) → S) (j : Fin (n * c₀ + 1)) :
    tapeUnsplit π σ (suffixCoord j) = σ j := by
  have hd : ¬ (n * c₀ + j.val < n * c₀) := by omega
  show (if h : n * c₀ + j.val < n * c₀ then π ⟨n * c₀ + j.val, h⟩
      else σ ⟨n * c₀ + j.val - n * c₀, _⟩) = σ j
  rw [dif_neg hd]
  refine congrArg σ (Fin.ext ?_)
  show n * c₀ + j.val - n * c₀ = j.val
  omega

theorem extSeed_tapeUnsplit_prefix {S : Type} [Nonempty S] {n c₀ : ℕ}
    (π : Fin (n * c₀) → S) (σ : Fin (n * c₀ + 1) → S) (k : ℕ) (hk : k < n * c₀) :
    @extSeed (2 * n * c₀ + 1) S _ (tapeUnsplit π σ) k = π ⟨k, hk⟩ := by
  rw [extSeed, dif_pos (by have := tape_two_mul n c₀; omega)]
  exact tapeUnsplit_prefix_read π σ ⟨k, hk⟩

theorem extSeed_tapeUnsplit_suffix {S : Type} [Nonempty S] {n c₀ : ℕ}
    (π : Fin (n * c₀) → S) (σ : Fin (n * c₀ + 1) → S) (k : ℕ) (hk : k < n * c₀ + 1) :
    @extSeed (2 * n * c₀ + 1) S _ (tapeUnsplit π σ) (n * c₀ + k) = σ ⟨k, hk⟩ := by
  rw [extSeed, dif_pos (by have := tape_two_mul n c₀; omega)]
  exact tapeUnsplit_suffix_read π σ ⟨k, hk⟩

theorem tapeUnsplit_inj {S : Type*} {n c₀ : ℕ} {π π' : Fin (n * c₀) → S}
    {σ σ' : Fin (n * c₀ + 1) → S} (h : tapeUnsplit π σ = tapeUnsplit π' σ') :
    π = π' ∧ σ = σ' := by
  constructor
  · funext j
    have h1 := congrFun h (prefixCoord j)
    rw [tapeUnsplit_prefix_read, tapeUnsplit_prefix_read] at h1
    exact h1
  · funext j
    have h1 := congrFun h (suffixCoord j)
    rw [tapeUnsplit_suffix_read, tapeUnsplit_suffix_read] at h1
    exact h1

theorem tapeUnsplit_canonical {S : Type*} {n c₀ : ℕ} (τ : Fin (2 * n * c₀ + 1) → S) :
    tapeUnsplit (fun j => τ (prefixCoord j)) (fun j => τ (suffixCoord j)) = τ := by
  funext k
  rcases Nat.lt_or_ge k.val (n * c₀) with h | h
  · have hke : k = prefixCoord ⟨k.val, h⟩ := rfl
    rw [hke]
    exact tapeUnsplit_prefix_read _ _ _
  · have hlt : k.val - n * c₀ < n * c₀ + 1 := by
      have := tape_two_mul n c₀
      have := k.isLt
      omega
    have hke : k = suffixCoord ⟨k.val - n * c₀, hlt⟩ := by
      apply Fin.ext
      show k.val = n * c₀ + (k.val - n * c₀)
      have h1 := h
      omega
    rw [hke]
    exact tapeUnsplit_suffix_read _ _ _

theorem tapePrefix_unsplit {S : Type*} {n c₀ : ℕ} (π : Fin (n * c₀) → S)
    (σ : Fin (n * c₀ + 1) → S) :
    (fun j => tapeUnsplit π σ (prefixCoord j)) = π := by
  funext j
  exact tapeUnsplit_prefix_read π σ j

theorem tapeSuffix_unsplit {S : Type*} {n c₀ : ℕ} (π : Fin (n * c₀) → S)
    (σ : Fin (n * c₀ + 1) → S) :
    (fun j => tapeUnsplit π σ (suffixCoord j)) = σ := by
  funext j
  exact tapeUnsplit_suffix_read π σ j

theorem tapeUnsplit_surj {S : Type*} {n c₀ : ℕ} (τ : Fin (2 * n * c₀ + 1) → S) :
    ∃ π σ, tapeUnsplit π σ = τ :=
  ⟨_, _, tapeUnsplit_canonical τ⟩

theorem card_tape_split {S : Type*} [Fintype S] {n c₀ : ℕ}
    (q : (Fin (2 * n * c₀ + 1) → S) → Prop) [DecidablePred q] :
    ((Finset.univ : Finset (Fin (2 * n * c₀ + 1) → S)).filter q).card =
      ((Finset.univ : Finset ((Fin (n * c₀) → S) × (Fin (n * c₀ + 1) → S))).filter
        (fun p => q (tapeUnsplit p.1 p.2))).card := by
  classical
  refine Finset.card_nbij
    (fun τ : Fin (2 * n * c₀ + 1) → S =>
      (fun j => τ (prefixCoord j), fun j => τ (suffixCoord j))) ?_ ?_ ?_
  · intro τ hτ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    rw [tapeUnsplit_canonical τ]
    exact hτ
  · intro τ _ τ' _ h
    rw [← tapeUnsplit_canonical τ, ← tapeUnsplit_canonical τ']
    exact congrArg (fun q : (Fin (n * c₀) → S) × (Fin (n * c₀ + 1) → S) =>
      tapeUnsplit q.1 q.2) h
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨tapeUnsplit p.1 p.2, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp
    · rw [Prod.mk.injEq]
      exact ⟨tapePrefix_unsplit p.1 p.2, tapeSuffix_unsplit p.1 p.2⟩

theorem triCheckAmpExtract_none_iff {n m : ℕ} (adj : Fin n → Fin n → Bool) (e : Fin m → Fin n)
    (kcs : KCollisionSolver) (r' : ℕ) (subR : (Fin 2 → Fin m) → Bool) (v : Fin n) (c₀ : ℕ)
    (stape : ℕ → kcs.seed)
    (hver : ∀ t, subR t = true → (adj v (e (t 0)) && adj v (e (t 1))) = true) :
    (triCheckAmpExtract adj e kcs r' subR v c₀ stape).1 = none ↔
      ∀ i ∈ List.range c₀,
        kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) = none := by
  classical
  let step := fun (acc : Option (Fin 2 → Fin m) × ℕ) (i : ℕ) =>
    match acc with
    | (some a, q) => (some a, q)
    | (none, q) =>
        let qi := kcs.cost (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i))
        match kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) with
        | some a => if adj v (e (a 0)) && adj v (e (a 1)) then (some a, q + qi) else (none, q + qi)
        | none => (none, q + qi)
  have some_stays : ∀ (l : List ℕ) (a : Fin 2 → Fin m) (q : ℕ),
      (l.foldl step (some a, q)).1 = some a := by
    intro l
    induction l with
    | nil => intro a q; rfl
    | cons i l ih =>
      intro a q
      rw [List.foldl_cons]
      have hfr : step (some a, q) i = (some a, q) := by simp [step]
      rw [hfr]
      exact ih a q
  have key : ∀ (l : List ℕ) (acc : Option (Fin 2 → Fin m) × ℕ),
      (l.foldl step acc).1 = none ↔ (acc.1 = none ∧ ∀ i ∈ l,
        kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) = none) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons i l ih =>
      intro acc
      rcases acc with ⟨o, q⟩
      cases o with
      | none =>
        cases hr : kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) with
        | none =>
          rw [List.foldl_cons]
          have hfr : step (none, q) i
              = (none, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
                  (stape (v.val * c₀ + i))) := by simp [step, hr]
          rw [hfr]
          specialize ih (none, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
            (stape (v.val * c₀ + i)))
          simp only [ih]
          constructor
          · intro h
            refine ⟨trivial, ?_⟩
            intro i' hi'
            rcases List.mem_cons.mp hi' with rfl | hm
            · exact hr
            · exact h.2 i' hm
          · intro h
            exact ⟨trivial, fun i' hi' => h.2 i' (List.mem_cons_of_mem _ hi')⟩
        | some a =>
          have hv1 : adj v (e (a 0)) = true ∧ adj v (e (a 1)) = true := by
            simpa using hver a (kcs.sound (n := m) (k := 2) r' subR r' 1 0 _ hr)
          rw [List.foldl_cons]
          have hfr : step (none, q) i
              = (some a, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
                  (stape (v.val * c₀ + i))) := by simp [step, hr, hv1.1, hv1.2]
          rw [hfr, some_stays]
          constructor
          · intro h
            exact absurd h (by simp)
          · intro h
            have hnone := h.2 i (by simp)
            rw [hnone] at hr
            exact absurd hr (by simp)
      | some a =>
        rw [List.foldl_cons]
        have hfr : step (some a, q) i = (some a, q) := by simp [step]
        rw [hfr, some_stays]
        constructor
        · intro h
          exact absurd h (by simp)
        · intro h
          exact absurd h.1 (by simp)
  refine (key (List.range c₀) (none, 0)).trans ?_
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem triCheckAmpExtract_cost_le {n m : ℕ} (adj : Fin n → Fin n → Bool) (e : Fin m → Fin n)
    (kcs : KCollisionSolver) (r' : ℕ) (subR : (Fin 2 → Fin m) → Bool) (v : Fin n) (c₀ : ℕ)
    (stape : ℕ → kcs.seed) (W : ℕ)
    (hstep : ∀ i ∈ List.range c₀,
      kcs.cost (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) ≤ W) :
    (triCheckAmpExtract adj e kcs r' subR v c₀ stape).2 ≤ c₀ * W := by
  classical
  let step := fun (acc : Option (Fin 2 → Fin m) × ℕ) (i : ℕ) =>
    match acc with
    | (some a, q) => (some a, q)
    | (none, q) =>
        let qi := kcs.cost (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i))
        match kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) with
        | some a => if adj v (e (a 0)) && adj v (e (a 1)) then (some a, q + qi) else (none, q + qi)
        | none => (none, q + qi)
  have some_freezes : ∀ (l : List ℕ) (a : Fin 2 → Fin m) (q : ℕ),
      (l.foldl step (some a, q)).2 = q := by
    intro l
    induction l with
    | nil => intro a q; rfl
    | cons i l ih =>
      intro a q
      rw [List.foldl_cons]
      have hfr : step (some a, q) i = (some a, q) := by simp [step]
      rw [hfr]
      exact ih a q
  have key : ∀ (l : List ℕ), (∀ i' ∈ l,
      kcs.cost (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i')) ≤ W) →
    ∀ acc : Option (Fin 2 → Fin m) × ℕ, (l.foldl step acc).2 ≤ acc.2 + l.length * W := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons i l ih =>
      intro hmem acc
      have hqi : kcs.cost (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) ≤ W :=
        hmem i (by simp)
      have hlen : (i :: l).length = l.length + 1 := rfl
      have hprod : (i :: l).length * W = l.length * W + W := by rw [hlen]; ring
      have htail := fun i' hi' => hmem i' (List.mem_cons_of_mem i hi')
      rcases acc with ⟨o, q⟩
      cases o with
      | none =>
        cases hr : kcs.run (n := m) (k := 2) r' subR r' 1 0 (stape (v.val * c₀ + i)) with
        | none =>
          rw [List.foldl_cons]
          have hfr : step (none, q) i
              = (none, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
                  (stape (v.val * c₀ + i))) := by simp [step, hr]
          rw [hfr]
          have hrec := ih htail (none, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
            (stape (v.val * c₀ + i)))
          simp only at hrec ⊢
          omega
        | some a =>
          rw [List.foldl_cons]
          have hor : step (none, q) i
              = (some a, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
                  (stape (v.val * c₀ + i))) ∨ step (none, q) i
              = (none, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
                  (stape (v.val * c₀ + i))) := by
            simp only [step, hr]
            split_ifs <;> simp_all
          rcases hor with h | h
          · rw [h, some_freezes]
            simp only
            omega
          · rw [h]
            have hrec := ih htail (none, q + kcs.cost (n := m) (k := 2) r' subR r' 1 0
              (stape (v.val * c₀ + i)))
            simp only at hrec ⊢
            omega
      | some a =>
        rw [List.foldl_cons]
        have hfr : step (some a, q) i = (some a, q) := by simp [step]
        rw [hfr, some_freezes]
        simp only
        omega
  have h := key (List.range c₀) (fun i' hi' => hstep i' hi') (none, 0)
  simp only [triCheckAmpExtract] at h ⊢
  rwa [List.length_range, zero_add] at h

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
