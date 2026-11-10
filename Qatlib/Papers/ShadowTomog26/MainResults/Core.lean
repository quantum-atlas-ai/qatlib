/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def probSimplex (V : Type*) [Fintype V] : Set (V → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

omit [DecidableEq V] [Nonempty V] in

lemma mem_probSimplex {w : V → ℝ} (hw : w ∈ probSimplex V) : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 :=
  hw

omit [DecidableEq V] in

lemma probSimplex_nonempty : (probSimplex V).Nonempty := by
  refine ⟨fun _ => (Fintype.card V : ℝ)⁻¹, ?_, ?_⟩
  · intro i; positivity
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_inv_cancel₀ hc

def supportFun (K : Set (V → ℝ)) (w : V → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ v ∈ K, x = ∑ i, w i * v i}

def weightedIndepNum (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ i ∈ I, w i}

def FracCover (G : SimpleGraph V) (x : Finset V → ℝ) : Prop :=
  (∀ I : Finset V, G.IsIndepSet (I : Set V) → 0 ≤ x I) ∧
  (∀ I : Finset V, ¬ G.IsIndepSet (I : Set V) → x I = 0) ∧
  (∀ i : V, 1 ≤ ∑ I : Finset V, x I * (if i ∈ I then (1 : ℝ) else 0))

def fractionalChromatic (G : SimpleGraph V) : ℝ :=
  sInf {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I}

structure GraphBodies (V : Type*) [Fintype V] [DecidableEq V] where
  G : SimpleGraph V
  BETA : Set (V → ℝ)
  TH : Set (V → ℝ)
  lovaszComplement : ℝ
  beta_nonempty : BETA.Nonempty
  theta_nonempty : TH.Nonempty
  beta_subset_theta : BETA ⊆ TH
  beta_unit : ∀ v ∈ BETA, ∀ i, 0 ≤ v i ∧ v i ≤ 1
  theta_unit : ∀ v ∈ TH, ∀ i, 0 ≤ v i ∧ v i ≤ 1

  stab_subset_beta : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
    (fun i => if i ∈ I then (1 : ℝ) else 0) ∈ BETA

variable (B : GraphBodies V)

def alpha (w : V → ℝ) : ℝ := weightedIndepNum B.G w

def beta (w : V → ℝ) : ℝ := supportFun B.BETA w

def theta (w : V → ℝ) : ℝ := supportFun B.TH w

def delta : ℝ := sInf ((fun w => beta B w) '' probSimplex V)

def alphaMin : ℝ := sInf ((fun w => alpha B w) '' probSimplex V)

def thetaMin : ℝ := sInf ((fun w => theta B w) '' probSimplex V)

def IsHPerfect : Prop := ∀ w : V → ℝ, (∀ i, 0 ≤ w i) → beta B w = alpha B w

omit [DecidableEq V] [Nonempty V] in

lemma supportImage_bddAbove {K : Set (V → ℝ)}
    (hunit : ∀ v ∈ K, ∀ i, 0 ≤ v i ∧ v i ≤ 1) {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) :
    BddAbove {x : ℝ | ∃ v ∈ K, x = ∑ i, w i * v i} := by
  refine ⟨∑ i, w i, ?_⟩
  rintro x ⟨v, hv, rfl⟩
  exact Finset.sum_le_sum (fun i _ => by
    have h1 := (hunit v hv i).1
    have h2 := (hunit v hv i).2
    nlinarith [hw i])

omit [DecidableEq V] [Nonempty V] in

lemma supportFun_mono {K L : Set (V → ℝ)} (hKL : K ⊆ L) (w : V → ℝ)
    (hLbdd : BddAbove {x : ℝ | ∃ v ∈ L, x = ∑ i, w i * v i})
    (hKne : K.Nonempty) : supportFun K w ≤ supportFun L w := by
  unfold supportFun
  apply csSup_le
  · obtain ⟨v, hv⟩ := hKne; exact ⟨_, v, hv, rfl⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact le_csSup hLbdd ⟨v, hKL hv, rfl⟩

omit [DecidableEq V] [Nonempty V] in

lemma supportFun_nonneg {K : Set (V → ℝ)} (hK : K.Nonempty)
    (hunit : ∀ v ∈ K, ∀ i, 0 ≤ v i ∧ v i ≤ 1) {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) :
    0 ≤ supportFun K w := by
  unfold supportFun
  obtain ⟨v0, hv0⟩ := hK
  have hbdd := supportImage_bddAbove hunit hw
  have hmem : (∑ i, w i * v0 i) ∈ {x : ℝ | ∃ v ∈ K, x = ∑ i, w i * v i} := ⟨v0, hv0, rfl⟩
  have hnn : 0 ≤ ∑ i, w i * v0 i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hunit v0 hv0 i).1)
  exact le_trans hnn (le_csSup hbdd hmem)

omit [DecidableEq V] [Nonempty V] in

lemma weightedIndepNum_bddAbove (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) :
    BddAbove {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ i ∈ I, w i} := by
  refine ⟨∑ i, w i, ?_⟩
  rintro x ⟨I, _, rfl⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
    (fun i _ _ => hw i)

omit [DecidableEq V] [Nonempty V] in

lemma weightedIndepNum_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) :
    0 ≤ weightedIndepNum G w := by
  unfold weightedIndepNum
  have hbdd := weightedIndepNum_bddAbove G hw
  have hmem : (0 : ℝ) ∈ {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ i ∈ I, w i} :=
    ⟨∅, by simp, by simp⟩
  exact le_csSup hbdd hmem

omit [Fintype V] [DecidableEq V] [Nonempty V] in

lemma isIndepSet_coe_singleton (G : SimpleGraph V) (i : V) :
    G.IsIndepSet (({i} : Finset V) : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
  rw [hx, hy] at hxy
  exact (hxy rfl).elim

omit [Nonempty V] in

lemma fracCover_nonneg {G : SimpleGraph V} {x : Finset V → ℝ} (hx : FracCover G x)
    (I : Finset V) : 0 ≤ x I := by
  by_cases hI : G.IsIndepSet (I : Set V)
  · exact hx.1 I hI
  · rw [hx.2.1 I hI]

def singletonCover (_G : SimpleGraph V) : Finset V → ℝ :=
  fun I => if I.card = 1 then 1 else 0

omit [Nonempty V] in

lemma singletonCover_feasible (G : SimpleGraph V) : FracCover G (singletonCover G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _
    by_cases h : I.card = 1 <;> simp [singletonCover, h]
  · intro I hI
    by_cases h : I.card = 1
    · exfalso
      apply hI
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
      rw [hi]
      exact isIndepSet_coe_singleton G i
    · simp [singletonCover, h]
  · intro i
    have hf : ∀ I : Finset V,
        0 ≤ (singletonCover G) I * (if i ∈ I then (1 : ℝ) else 0) := by
      intro I
      have hnonneg : 0 ≤ singletonCover G I := by unfold singletonCover;split_ifs <;> norm_num
      exact mul_nonneg hnonneg (by split_ifs <;> norm_num)
    have hbound : (∑ I ∈ ({({i} : Finset V)} : Finset (Finset V)),
          (singletonCover G) I * (if i ∈ I then (1 : ℝ) else 0))
        ≤ ∑ I : Finset V, (singletonCover G) I * (if i ∈ I then (1 : ℝ) else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({({i} : Finset V)} : Finset (Finset V)))
        (fun I _ _ => hf I)
    have hsingle : (1 : ℝ)
        = ∑ I ∈ ({({i} : Finset V)} : Finset (Finset V)),
          (singletonCover G) I * (if i ∈ I then (1 : ℝ) else 0) := by
      rw [Finset.sum_singleton]
      simp [singletonCover]
    exact le_trans (le_of_eq hsingle) hbound

omit [Nonempty V] in

lemma fracChromatic_set_nonempty (G : SimpleGraph V) :
    {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I}.Nonempty :=
  ⟨∑ I : Finset V, singletonCover G I, singletonCover G, singletonCover_feasible G, rfl⟩

omit [Nonempty V] in

lemma one_le_sum_of_cover {G : SimpleGraph V} {x : Finset V → ℝ} (hx : FracCover G x)
    (i : V) : 1 ≤ ∑ I : Finset V, x I := by
  refine le_trans (hx.2.2 i) (Finset.sum_le_sum ?_)
  intro I _
  have hite : (if i ∈ I then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hmul := mul_le_mul_of_nonneg_left hite (fracCover_nonneg hx I)
  rwa [mul_one] at hmul

lemma one_le_fracChromatic (G : SimpleGraph V) : 1 ≤ fractionalChromatic G := by
  obtain ⟨i₀⟩ : Nonempty V := ‹Nonempty V›
  have hbdd : BddBelow {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I} :=
    ⟨1, by rintro s ⟨x, hx, rfl⟩; exact one_le_sum_of_cover hx i₀⟩
  exact (le_csInf_iff hbdd (fracChromatic_set_nonempty G)).2
    (fun s hs => by obtain ⟨x, hx, rfl⟩ := hs; exact one_le_sum_of_cover hx i₀)

lemma fracChromatic_pos (G : SimpleGraph V) : 0 < fractionalChromatic G :=
  lt_of_lt_of_le zero_lt_one (one_le_fracChromatic G)

omit [Nonempty V] in

lemma delta_bddBelow : BddBelow ((fun w => beta B w) '' probSimplex V) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact supportFun_nonneg B.beta_nonempty B.beta_unit (mem_probSimplex hw).1

omit [Nonempty V] in

lemma alpha_bddBelow : BddBelow ((fun w => alpha B w) '' probSimplex V) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact weightedIndepNum_nonneg B.G (mem_probSimplex hw).1

omit [Nonempty V] in

lemma theta_bddBelow : BddBelow ((fun w => theta B w) '' probSimplex V) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact supportFun_nonneg B.theta_nonempty B.theta_unit (mem_probSimplex hw).1

omit [Nonempty V] in

lemma alpha_le_beta (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) : alpha B w ≤ beta B w := by
  unfold alpha beta weightedIndepNum supportFun
  refine csSup_le ⟨(0 : ℝ), ∅, by simp, by simp⟩ ?_
  rintro x ⟨I, hI, rfl⟩
  have hind : (fun i => if i ∈ I then (1 : ℝ) else 0) ∈ B.BETA := B.stab_subset_beta I hI
  have hmem : (∑ i, w i * (if i ∈ I then (1 : ℝ) else 0))
      ∈ {x : ℝ | ∃ v ∈ B.BETA, x = ∑ i, w i * v i} := ⟨_, hind, rfl⟩
  have hconv : (∑ i ∈ I, w i) = ∑ i, w i * (if i ∈ I then (1 : ℝ) else 0) := by
    calc (∑ i ∈ I, w i)
        = ∑ i ∈ I, w i * (if i ∈ I then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun i hi => by rw [if_pos hi, mul_one])
      _ = ∑ i, w i * (if i ∈ I then (1 : ℝ) else 0) :=
          Finset.sum_subset (Finset.subset_univ I)
            (fun i _ hi => by rw [if_neg hi, mul_zero])
  rw [hconv]
  exact le_csSup (supportImage_bddAbove B.beta_unit hw) hmem

omit [Nonempty V] in

lemma beta_le_theta (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) : beta B w ≤ theta B w := by
  unfold beta theta
  exact supportFun_mono B.beta_subset_theta w (supportImage_bddAbove B.theta_unit hw)
    B.beta_nonempty

lemma alphaMin_le_delta : alphaMin B ≤ delta B := by
  unfold alphaMin delta
  refine (le_csInf_iff (delta_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro b ⟨w, hw, rfl⟩
  exact le_trans (csInf_le (alpha_bddBelow B) ⟨w, hw, rfl⟩)
    (alpha_le_beta B w (mem_probSimplex hw).1)

lemma delta_le_thetaMin : delta B ≤ thetaMin B := by
  unfold delta thetaMin
  refine (le_csInf_iff (theta_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro b ⟨w, hw, rfl⟩
  exact le_trans (csInf_le (delta_bddBelow B) ⟨w, hw, rfl⟩)
    (beta_le_theta B w (mem_probSimplex hw).1)

lemma delta_le_alphaMin_of_hperfect (h : IsHPerfect B) : delta B ≤ alphaMin B := by
  unfold delta alphaMin
  refine (le_csInf_iff (alpha_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro b ⟨w, hw, rfl⟩
  show sInf ((fun w => beta B w) '' probSimplex V) ≤ alpha B w
  rw [← h w (mem_probSimplex hw).1]
  exact csInf_le (delta_bddBelow B) ⟨w, hw, rfl⟩

theorem delta_eq_alphaMin_of_hperfect (h : IsHPerfect B) : delta B = alphaMin B :=
  le_antisymm (delta_le_alphaMin_of_hperfect B h) (alphaMin_le_delta B)

omit [Nonempty V] in

lemma one_le_alpha_mul_of_cover (G : SimpleGraph V) {w : V → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {x : Finset V → ℝ} (hx : FracCover G x) :
    1 ≤ weightedIndepNum G w * ∑ I : Finset V, x I := by
  have hstepA : ∑ i, w i
      ≤ ∑ i, w i * ∑ I : Finset V, x I * (if i ∈ I then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc w i = w i * 1 := (mul_one _).symm
      _ ≤ w i * ∑ I : Finset V, x I * (if i ∈ I then (1 : ℝ) else 0) :=
          mul_le_mul_of_nonneg_left (hx.2.2 i) (hw0 i)
  have hswap : ∀ i : V, w i * ∑ I : Finset V, x I * (if i ∈ I then (1 : ℝ) else 0)
      = ∑ I : Finset V, x I * (w i * (if i ∈ I then (1 : ℝ) else 0)) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun I _ => by ring)
  have hopen : ∀ I : Finset V, ∑ i, w i * (if i ∈ I then (1 : ℝ) else 0)
      = ∑ i ∈ I, w i := by
    intro I
    calc ∑ i, w i * (if i ∈ I then (1 : ℝ) else 0)
        = ∑ i ∈ I, w i * (if i ∈ I then (1 : ℝ) else 0) :=
          (Finset.sum_subset (Finset.subset_univ I)
            (fun i _ hi => by rw [if_neg hi, mul_zero])).symm
      _ = ∑ i ∈ I, w i := Finset.sum_congr rfl (fun i hi => by rw [if_pos hi, mul_one])
  have hterm : ∀ I : Finset V, x I * (∑ i, w i * (if i ∈ I then (1 : ℝ) else 0))
      ≤ x I * weightedIndepNum G w := by
    intro I
    by_cases hI : G.IsIndepSet (I : Set V)
    · refine mul_le_mul_of_nonneg_left ?_ (fracCover_nonneg hx I)
      rw [hopen I]
      exact le_csSup (weightedIndepNum_bddAbove G hw0) ⟨I, hI, rfl⟩
    · rw [hx.2.1 I hI, zero_mul, zero_mul]
  calc 1 = ∑ i, w i := hw1.symm
    _ ≤ ∑ i, w i * ∑ I : Finset V, x I * (if i ∈ I then (1 : ℝ) else 0) := hstepA
    _ = ∑ i, ∑ I : Finset V, x I * (w i * (if i ∈ I then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hswap i]
    _ = ∑ I : Finset V, ∑ i, x I * (w i * (if i ∈ I then (1 : ℝ) else 0)) :=
        Finset.sum_comm
    _ = ∑ I : Finset V, x I * (∑ i, w i * (if i ∈ I then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun I _ => ?_)
        exact (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ I : Finset V, x I * weightedIndepNum G w :=
        Finset.sum_le_sum (fun I _ => hterm I)
    _ = (∑ I : Finset V, x I) * weightedIndepNum G w := (Finset.sum_mul _ _ _).symm
    _ = weightedIndepNum G w * ∑ I : Finset V, x I := mul_comm _ _

omit [DecidableEq V] [Nonempty V] in

lemma alpha_pos_of_mem_probSimplex (G : SimpleGraph V) {w : V → ℝ}
    (hw : w ∈ probSimplex V) : 0 < weightedIndepNum G w := by
  obtain ⟨hw0, hw1⟩ := mem_probSimplex hw
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hzero : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hcon i) (hw0 i))
    rw [hzero] at hw1
    exact zero_ne_one hw1
  have hmem : (w i) ∈ {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ j ∈ I, w j} :=
    ⟨{i}, isIndepSet_coe_singleton G i, by simp⟩
  exact lt_of_lt_of_le hi (le_csSup (weightedIndepNum_bddAbove G hw0) hmem)

lemma alpha_mul_fracChromatic_ge_one (G : SimpleGraph V) {w : V → ℝ}
    (hw : w ∈ probSimplex V) : 1 ≤ weightedIndepNum G w * fractionalChromatic G := by
  by_contra hlt
  obtain ⟨hw0, hw1⟩ := mem_probSimplex hw
  have hα : 0 < weightedIndepNum G w := alpha_pos_of_mem_probSimplex G hw
  have hkey : fractionalChromatic G < 1 / weightedIndepNum G w :=
    (lt_div_iff₀ hα).mpr (by rw [mul_comm]; exact lt_of_not_ge hlt)
  have hbdd : BddBelow {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I} :=
    ⟨1, by rintro s ⟨x, hx, rfl⟩; exact one_le_sum_of_cover hx (Classical.arbitrary V)⟩
  unfold fractionalChromatic at hkey
  obtain ⟨s, ⟨x, hx, rfl⟩, hs⟩ :=
    (csInf_lt_iff hbdd (fracChromatic_set_nonempty G)).mp hkey
  have hcore := one_le_alpha_mul_of_cover G hw0 hw1 hx
  have hcontra : weightedIndepNum G w * ∑ I : Finset V, x I
      < weightedIndepNum G w * (1 / weightedIndepNum G w) :=
    mul_lt_mul_of_pos_left hs hα
  rw [one_div, mul_inv_cancel₀ hα.ne'] at hcontra
  exact lt_irrefl _ (lt_of_le_of_lt hcore hcontra)

lemma one_div_fracChromatic_le_alpha (G : SimpleGraph V) {w : V → ℝ}
    (hw : w ∈ probSimplex V) : 1 / fractionalChromatic G ≤ weightedIndepNum G w :=
  (div_le_iff₀ (fracChromatic_pos G)).mpr (alpha_mul_fracChromatic_ge_one G hw)

lemma one_div_fracChromatic_le_alphaMin (B : GraphBodies V) :
    1 / fractionalChromatic B.G ≤ alphaMin B := by
  unfold alphaMin
  refine (le_csInf_iff (alpha_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro x ⟨w, hw, rfl⟩
  exact one_div_fracChromatic_le_alpha B.G hw

end Qatlib.Papers.ShadowTomog26.MainResults
