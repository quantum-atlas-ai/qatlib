/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverQuan
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs
import Qatlib.Papers.QuantWalkSpec04.MainResults.Detection
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Papers.QuantWalkSpec04.MainResults.Detection

namespace Qatlib.Papers.QuantWalkSpec04.MainResults.Applications

def imageSet {X Y : Type} [DecidableEq Y] (f : X → Y) (H : Finset X) : Finset Y :=
  H.image f

def relationMark {X Y : Type} [Fintype X] [DecidableEq X]
    (R : Y → Y → Prop) [DecidableRel R] (f : X → Y) (k : ℕ) :
    Finset (JohnsonVertex X k) :=
  Finset.univ.filter (fun s =>
    ∃ a ∈ s.1, ∃ b ∈ s.1, R (f a) (f b))

noncomputable def relationHitProb {X Y : Type} [Fintype X] [DecidableEq X]
    (R : Y → Y → Prop) [DecidableRel R]
    (f : X → Y) (k : ℕ) : ℝ :=
  ((relationMark R f k).card : ℝ) / (Fintype.card (JohnsonVertex X k) : ℝ)

theorem markedFraction_relationMark {X Y : Type} [Fintype X] [DecidableEq X]
    (R : Y → Y → Prop) [DecidableRel R] (f : X → Y) (k : ℕ) :
    markedFraction (relationMark R f k) = relationHitProb R f k := rfl

theorem relationMark_eq_empty_of_zero {X Y : Type} [Fintype X] [DecidableEq X]
    (R : Y → Y → Prop) [DecidableRel R] (f : X → Y) (k : ℕ)
    [Nonempty (JohnsonVertex X k)] (h : relationHitProb R f k = 0) :
    relationMark R f k = ∅ := by
  have hpos : 0 < Fintype.card (JohnsonVertex X k) := Fintype.card_pos
  have hden : (Fintype.card (JohnsonVertex X k) : ℝ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hnum : ((relationMark R f k).card : ℝ) = 0 := by
    have h' := h
    unfold relationHitProb at h'
    rw [div_eq_iff hden] at h'
    simpa using! h'
  have hcard : (relationMark R f k).card = 0 := by exact_mod_cast hnum
  exact Finset.card_eq_zero.mp hcard

structure RelationSearchMachine (X Y : Type) where

  queryBudget : ℝ

  acceptProbability : (X → Y) → ℝ

theorem johnsonSubsetStep_comm {X : Type} [Fintype X] [DecidableEq X] (k : ℕ)
    (s t : JohnsonVertex X k) :
    johnsonSubsetStep X k s t = johnsonSubsetStep X k t s := by
  simp only [johnsonSubsetStep, Finset.inter_comm]

theorem relationSearch_detection
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (k : ℕ) (δ ε : ℝ) (j : I)
    (U : Matrix (I × I) (I × I) ℂ)
    (hk : 0 < k) (hδ1 : δ ≤ 1)
    (hgap : SymmetricChainGap P δ) (hkgap : (k : ℝ)⁻¹ ≤ δ)
    (hε : 0 < ε) (hεS : ε ≤ markedFraction S)
    (hU : U ∈ Matrix.unitaryGroup (I × I) ℂ)
    (hprep : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) :
    (∀ K : ℕ, detectionProbability U ∅ j K = 0) ∧
    (1 / 1000 : ℝ) ≤
      (∑ t : Fin (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε))),
        detectionProbability U S j (t.val + 1)) /
        (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hkgap
  have hde : 0 < δ * ε := mul_pos hδ hε
  have hscale : 1000 / Real.sqrt (δ * ε) ≤
      (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℝ) := by
    have h1 : 1 / Real.sqrt (δ * ε) ≤ Real.sqrt ((k : ℝ) / ε) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, one_pow, Real.sq_sqrt hde.le]
      rw [div_le_div_iff₀ hde hε]
      have hkδ : (1 : ℝ) ≤ δ * (k : ℝ) :=
        (div_le_iff₀ hkR).mp (by simpa only [one_div] using! hkgap)
      nlinarith [hkδ, hε]
    have h2 : 1000 * (1 / Real.sqrt (δ * ε)) ≤
        1000 * Real.sqrt ((k : ℝ) / ε) := by nlinarith [h1]
    have h3 : (1000 : ℝ) * Real.sqrt ((k : ℝ) / ε) ≤
        (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℝ) := Nat.le_ceil _
    calc 1000 / Real.sqrt (δ * ε) = 1000 * (1 / Real.sqrt (δ * ε)) := by ring
      _ ≤ 1000 * Real.sqrt ((k : ℝ) / ε) := h2
      _ ≤ (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℝ) := h3
  have hL : 0 < Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) := by
    rcases Nat.eq_zero_or_pos (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε))) with h | h
    · exfalso
      have hx : (0 : ℝ) < 1000 * Real.sqrt ((k : ℝ) / ε) := by
        have : (0 : ℝ) < (k : ℝ) / ε := div_pos hkR hε
        positivity
      have := Nat.le_ceil (1000 * Real.sqrt ((k : ℝ) / ε))
      rw [h, Nat.cast_zero] at this
      linarith
    · exact h
  exact szegedyTheorem2_detection P S δ ε
    (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε))) j U hδ hδ1 hgap hε hεS hL hscale hU hprep

theorem relationSearch_ledger (k : ℕ) (ε : ℝ) (hk : 0 < k) (hε : 0 < ε) :
    (k : ℝ) + 2 * (Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε)) : ℝ) ≤
      (k : ℝ) + 2000 * Real.sqrt ((k : ℝ) / ε) + 2 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have harg : (0 : ℝ) ≤ 1000 * Real.sqrt ((k : ℝ) / ε) := by
    have : (0 : ℝ) < (k : ℝ) / ε := div_pos hkR hε
    positivity
  have hceil := Nat.ceil_lt_add_one harg
  have hs : 0 ≤ Real.sqrt ((k : ℝ) / ε) := Real.sqrt_nonneg _
  nlinarith [hceil, hs]

theorem relationSearch_of_johnson_gap
    {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (R : Y → Y → Prop) [DecidableRel R]
    (k : ℕ) (δ ε : ℝ) (j : JohnsonVertex X k)
    (U : Matrix (JohnsonVertex X k × JohnsonVertex X k)
        (JohnsonVertex X k × JohnsonVertex X k) ℂ)
    [Nonempty (JohnsonVertex X k)]
    (hk : 0 < k) (hδ1 : δ ≤ 1)
    (hgap : SymmetricChainGap (johnsonSubsetStep X k) δ)
    (hkgap : (k : ℝ)⁻¹ ≤ δ) (hε : 0 < ε)
    (hU : U ∈ Matrix.unitaryGroup (JohnsonVertex X k × JohnsonVertex X k) ℂ)
    (hprep : ∀ i, U *ᵥ TensorState (Ket i) (Ket j) =
      SzegedyIsometry (johnsonSubsetStep X k) *ᵥ Ket i) :
    ∃ M : RelationSearchMachine X Y,
      M.queryBudget ≤ (k : ℝ) + 2000 * Real.sqrt ((k : ℝ) / ε) + 2 ∧
      (∀ f, relationHitProb R f k = 0 → M.acceptProbability f = 0) ∧
      (∀ f, ε ≤ relationHitProb R f k → (1 / 1000 : ℝ) ≤ M.acceptProbability f) := by
  let L : ℕ := Nat.ceil (1000 * Real.sqrt ((k : ℝ) / ε))
  let M : RelationSearchMachine X Y :=
    { queryBudget := (k : ℝ) + 2 * (L : ℝ)
      acceptProbability := fun f =>
        (∑ t : Fin L, detectionProbability U (relationMark R f k) j (t.val + 1)) /
          (L : ℝ) }
  refine ⟨M, ?_, ?_, ?_⟩
  · dsimp only [M, L]
    exact relationSearch_ledger k ε hk hε
  · intro f hf
    have hmark : relationMark R f k = ∅ := relationMark_eq_empty_of_zero R f k hf
    have hempty : ∀ K : ℕ, detectionProbability U (∅ : Finset (JohnsonVertex X k)) j K = 0 :=
      fun K => corrected_szegedy_empty_mark_one_sided (JohnsonVertex X k)
        (johnsonSubsetStep X k) j U K hgap.1 hgap.2.1 hU hprep
    dsimp only [M]
    rw [hmark]
    have hsum : (∑ t : Fin L,
        detectionProbability U (∅ : Finset (JohnsonVertex X k)) j (t.val + 1)) = 0 :=
      Finset.sum_eq_zero (fun t _ => hempty (t.val + 1))
    rw [hsum, zero_div]
  · intro f hf
    have hmass : ε ≤ markedFraction (relationMark R f k) := by
      rw [markedFraction_relationMark]
      exact hf
    have hdet := relationSearch_detection (johnsonSubsetStep X k) (relationMark R f k)
      k δ ε j U hk hδ1 hgap hkgap hε hmass hU hprep
    dsimp only [M]
    exact hdet.2

theorem card_collision_subsets {N k : ℕ} (hk : 2 ≤ k) (_hkN : k ≤ N)
    (a b : Fin N) (hab : a ≠ b) :
    (Finset.univ.filter (fun H : Finset (Fin N) =>
        H.card = k ∧ a ∈ H ∧ b ∈ H)).card = (N - 2).choose (k - 2) := by
  have hpair : ({a, b} : Finset (Fin N)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hcard : ({a, b} : Finset (Fin N)).card = 2 := by simp [hab]
  have h2 : ({a, b} : Finset (Fin N)).card ≤ k := by rw [hcard]; omega
  have h := Finset.card_filter_powersetCard_subset ({a, b} : Finset (Fin N))
    (Finset.univ : Finset (Fin N)) k hpair h2
  have hfilter : (Finset.univ.filter (fun H : Finset (Fin N) =>
        H.card = k ∧ a ∈ H ∧ b ∈ H)) =
      (Finset.univ.powersetCard k).filter
        (fun H => ({a, b} : Finset (Fin N)) ⊆ H) := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ,
      true_and, Finset.subset_univ]
    constructor
    · rintro ⟨hHk, ha, hb⟩
      exact ⟨hHk, by simp [Finset.insert_subset_iff, ha, hb]⟩
    · rintro ⟨hHk, hsub⟩
      exact ⟨hHk, hsub (by simp), hsub (by simp)⟩
  rw [hfilter, h]
  simp [hcard]

theorem edCollisionMarked_card_ge {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (x : Fin N → ℕ) {a b : Fin N} (hab : a ≠ b) (hfab : x a = x b) :
    (N - 2).choose (k - 2) ≤ (edCollisionMarked N x k).card := by
  let T : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun H => H.card = k ∧ a ∈ H ∧ b ∈ H)
  let vert : {H // H ∈ T} → JohnsonVertex (Fin N) k :=
    fun H => ⟨H.1, (Finset.mem_filter.mp H.2).2.1⟩
  have hT : T.card = (N - 2).choose (k - 2) := card_collision_subsets hk hkN a b hab
  have hinj : Function.Injective vert := by
    intro H1 H2 h
    apply Subtype.ext
    exact congrArg (fun s : JohnsonVertex (Fin N) k => s.1) h
  have hsub : T.attach.image vert ⊆ edCollisionMarked N x k := by
    intro s hs
    obtain ⟨H, _hH, hfH⟩ := Finset.mem_image.mp hs
    rw [← hfH]
    have hprop := (Finset.mem_filter.mp H.2).2
    simp only [edCollisionMarked, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, b, hprop.2.1, hprop.2.2, hab, hfab⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hT] at hle
  exact hle

theorem collisionMass_eq {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) :
    ((N - 2).choose (k - 2) : ℝ) / (N.choose k : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hk1 : 1 ≤ k := by omega
  have hN1 : 1 ≤ N := by omega
  have h1 := Nat.choose_mul (n := N) (k := k) (s := 1) hk1
  have h2 := Nat.choose_mul (n := N - 1) (k := k - 1) (s := 1) (by omega)
  simp only [Nat.choose_one_right] at h1 h2
  have h2' : (N - 1).choose (k - 1) * (k - 1) =
      (N - 1) * (N - 2).choose (k - 2) := by
    rwa [show (N - 1) - 1 = N - 2 by omega,
      show (k - 1) - 1 = k - 2 by omega] at h2
  have hnat : N.choose k * (k * (k - 1)) =
      N * (N - 1) * (N - 2).choose (k - 2) := by
    calc N.choose k * (k * (k - 1))
        = (N.choose k * k) * (k - 1) := by ring
      _ = (N * (N - 1).choose (k - 1)) * (k - 1) := by rw [h1]
      _ = N * ((N - 1).choose (k - 1) * (k - 1)) := by ring
      _ = N * ((N - 1) * (N - 2).choose (k - 2)) := by rw [h2']
      _ = N * (N - 1) * (N - 2).choose (k - 2) := by ring
  have hcast : (N.choose k : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) =
      (N : ℝ) * ((N : ℝ) - 1) * ((N - 2).choose (k - 2) : ℝ) := by
    have hc := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at hc
    rw [Nat.cast_sub hk1, Nat.cast_sub hN1] at hc
    simpa [Nat.cast_sub hk1, Nat.cast_sub hN1, mul_assoc] using! hc
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hden : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    nlinarith
  have hC : (0 : ℝ) < (N.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkN
  rw [div_eq_div_iff hC.ne' hden.ne']
  nlinarith [hcast]

theorem rpow_two_thirds_ge_four {N : ℕ} (hN : 8 ≤ N) :
    (4 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have h8 : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    have hbase : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
    rw [hbase]
    rw [← Real.rpow_natCast (x := (2 : ℝ)) (n := 3)]
    rw [← Real.rpow_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
      ((3 : ℕ) : ℝ) (2 / 3 : ℝ)]
    rw [show ((3 : ℕ) : ℝ) * (2 / 3 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_natCast]
    norm_num
  have hle : (8 : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)
  rwa [h8] at hle

theorem collisionMass_ge_inv_two_k {N : ℕ} (hN : 8 ≤ N) :
    (1 : ℝ) / (2 * (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ)) ≤
      ((Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) *
        ((Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  set k : ℝ := (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) with hk
  have hx : (0 : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have hk_ge : (N : ℝ) ^ (2 / 3 : ℝ) ≤ k := by
    rw [hk]; exact Nat.le_ceil _
  have hk_pos : 0 < k := lt_of_lt_of_le hx hk_ge
  have hx4 : (4 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := rpow_two_thirds_ge_four hN
  have hk1_ge : (N : ℝ) ^ (2 / 3 : ℝ) / 2 ≤ k - 1 := by
    linarith
  have hcube : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (x := (N : ℝ) ^ (2 / 3 : ℝ)) (n := 3)]
    rw [← Real.rpow_natCast (x := (N : ℝ)) (n := 2)]
    rw [← Real.rpow_mul (x := (N : ℝ)) (by positivity : (0 : ℝ) ≤ (N : ℝ))
      (2 / 3 : ℝ) ((3 : ℕ) : ℝ)]
    rw [show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    linarith
  have hden : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) := mul_pos hNpos hN1
  have hk2 : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 ≤ k ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hx) hk_ge 2
  have hprod : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 * ((N : ℝ) ^ (2 / 3 : ℝ) / 2) ≤
      k ^ 2 * (k - 1) :=
    mul_le_mul hk2 hk1_ge (by positivity) (by positivity)
  have hmass : (N : ℝ) * ((N : ℝ) - 1) ≤ 2 * (k * (k - 1) * k) := by
    nlinarith [hprod, hcube, hx, hk_pos, hNpos, hN1]
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * k) hden]
  nlinarith [hmass]

theorem edCollisionMarkedFraction_ge {N : ℕ} (hN : 8 ≤ N) (x : Fin N → ℕ)
    {a b : Fin N} (hab : a ≠ b) (hfab : x a = x b) :
    (1 : ℝ) / (2 * (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ)) ≤
      markedFraction (edCollisionMarked N x (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)))) := by
  set k : ℕ := Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) with hk
  have hk_ge : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (k : ℝ) := by
    rw [hk]; exact Nat.le_ceil _
  have hk2 : 2 ≤ k := by
    have hx4 := rpow_two_thirds_ge_four hN
    have h4 : (4 : ℝ) ≤ (k : ℝ) := le_trans hx4 hk_ge
    have h4' : 4 ≤ k := by exact_mod_cast h4
    omega
  have hkN : k ≤ N := by
    rw [hk, Nat.ceil_le]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hle : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    rwa [Real.rpow_one] at hle
  have hcard := edCollisionMarked_card_ge hk2 hkN x hab hfab
  have hVcard : Fintype.card (JohnsonVertex (Fin N) k) = N.choose k := by
    simpa using! (Fintype.card_finset_len (α := Fin N) k)
  have hden : (0 : ℝ) < (N.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkN
  have hfrac : ((N - 2).choose (k - 2) : ℝ) / (N.choose k : ℝ) ≤
      markedFraction (edCollisionMarked N x k) := by
    rw [markedFraction, hVcard]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le
  have hmass : ((N - 2).choose (k - 2) : ℝ) / (N.choose k : ℝ) =
      ((k : ℝ) * ((k : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) :=
    collisionMass_eq hk2 hkN
  have hbase : (1 : ℝ) / (2 * (k : ℝ)) ≤
      ((k : ℝ) * ((k : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    simpa only [← hk] using! collisionMass_ge_inv_two_k (N := N) hN
  calc (1 : ℝ) / (2 * (k : ℝ))
      ≤ ((k : ℝ) * ((k : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) := hbase
    _ = ((N - 2).choose (k - 2) : ℝ) / (N.choose k : ℝ) := hmass.symm
    _ ≤ markedFraction (edCollisionMarked N x k) := hfrac

theorem elementDistinctness_ledger {N : ℕ} (hN : 8 ≤ N) :
    (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) +
        2000 * Real.sqrt ((Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) /
          (1 / (2 * (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ)))) ≤
      3001 * (N : ℝ) ^ (2 / 3 : ℝ) + 3001 := by
  set k : ℝ := (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) with hk
  have hx : (0 : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have hk_lt : k < (N : ℝ) ^ (2 / 3 : ℝ) + 1 := by
    rw [hk]
    exact Nat.ceil_lt_add_one (le_of_lt hx)
  have hk_pos : 0 < k := by
    rw [hk]
    rcases Nat.eq_zero_or_pos (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ))) with h | h
    · exfalso
      have := Nat.le_ceil ((N : ℝ) ^ (2 / 3 : ℝ))
      rw [h, Nat.cast_zero] at this
      linarith
    · exact_mod_cast h
  have hratio : k / (1 / (2 * k)) = 2 * k ^ 2 := by
    field_simp [hk_pos.ne']
  rw [hratio]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (k ^ 2)]
  rw [Real.sqrt_sq (le_of_lt hk_pos)]
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  nlinarith [h2, hk_pos, hk_lt]

theorem szegedyTheorem4_expander_grover :
    Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGrover :=
  Qatlib.Concepts.WalkSearch.Th4Expander.szegedyTheorem4ExpanderGrover

end Qatlib.Papers.QuantWalkSpec04.MainResults.Applications
