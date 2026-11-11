/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Graph-body parameters for shadow tomography

This module provides the abstract graph-body framework used for the shadow-tomography bounds in
[XuEtAl2026]. `GraphBodies` records nonempty bodies in the unit cube, inclusion of
independent-set indicators in `BETA`, and containment of `BETA` in `TH`; `alpha`, `beta`, and
`theta` are their associated weighted objectives.

The simplex infima `alphaMin`, `delta`, and `thetaMin` inherit the pointwise comparison of these
objectives. Fractional covers give a reciprocal fractional-chromatic lower bound, while
`IsHPerfect` makes the first two infima coincide.

## Main statements

* `alpha_le_beta` and `beta_le_theta` compare nonnegative weighted objectives.
* `alphaMin_le_delta` and `delta_le_thetaMin` compare their simplex infima.
* `delta_eq_alphaMin_of_hperfect` identifies the two minima under `IsHPerfect`.
* `one_div_fracChromatic_le_alphaMin` supplies the fractional-chromatic lower bound.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The set of nonnegative real functions on the finite type `V` whose coordinates sum to one. -/
def probSimplex (V : Type*) [Fintype V] : Set (V → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

omit [DecidableEq V] [Nonempty V] in

/-- Membership in `probSimplex V` supplies coordinatewise nonnegativity and the identity that
the coordinates sum to one. -/
lemma mem_probSimplex {w : V → ℝ} (hw : w ∈ probSimplex V) : (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 :=
  hw

omit [DecidableEq V] in

/-- The probability simplex on a nonempty finite type is nonempty. The constant function with
value the reciprocal of its cardinality is a witness. -/
lemma probSimplex_nonempty : (probSimplex V).Nonempty := by
  refine ⟨fun _ => (Fintype.card V : ℝ)⁻¹, ?_, ?_⟩
  · intro i; positivity
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_inv_cancel₀ hc

/-- The support value of a set `K` at weight `w`, defined as the supremum of the finite sums `∑
i, w i * v i` over `v ∈ K`. -/
def supportFun (K : Set (V → ℝ)) (w : V → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ v ∈ K, x = ∑ i, w i * v i}

/-- The weighted independence number of `G`, defined as the supremum of `∑ i ∈ I, w i` over
finite independent vertex sets `I`. -/
def weightedIndepNum (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ i ∈ I, w i}

/-- A fractional cover assigns nonnegative weights to independent finite vertex sets, assigns
zero to all other sets, and gives each vertex total incident weight at least one. -/
def FracCover (G : SimpleGraph V) (x : Finset V → ℝ) : Prop :=
  (∀ I : Finset V, G.IsIndepSet (I : Set V) → 0 ≤ x I) ∧
  (∀ I : Finset V, ¬ G.IsIndepSet (I : Set V) → x I = 0) ∧
  (∀ i : V, 1 ≤ ∑ I : Finset V, x I * (if i ∈ I then (1 : ℝ) else 0))

/-- The fractional chromatic number defined as the infimum of the total weight of a fractional
cover over all finite vertex sets. -/
def fractionalChromatic (G : SimpleGraph V) : ℝ :=
  sInf {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I}

/-- An abstract graph-body system consisting of a graph, nonempty sets `BETA` and `TH` in the
coordinatewise unit cube, and a stored complementary Lovasz parameter. It requires `BETA ⊆
TH` and includes every independent-set indicator in `BETA`. -/
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

/-- The weighted independence number of the graph stored in `B`. -/
def alpha (w : V → ℝ) : ℝ := weightedIndepNum B.G w

/-- The support value of the body `B.BETA` at the weight function `w`. -/
def beta (w : V → ℝ) : ℝ := supportFun B.BETA w

/-- The support value of the outer body `B.TH` at the weight function `w`. -/
def theta (w : V → ℝ) : ℝ := supportFun B.TH w

/-- The infimum of `beta B w` over probability weights `w` on the vertices. -/
def delta : ℝ := sInf ((fun w => beta B w) '' probSimplex V)

/-- The infimum of `alpha B w` over probability weights `w` on the vertices. -/
def alphaMin : ℝ := sInf ((fun w => alpha B w) '' probSimplex V)

/-- The infimum of `theta B w` over probability weights `w` on the vertices. -/
def thetaMin : ℝ := sInf ((fun w => theta B w) '' probSimplex V)

/-- The condition that the beta support value equals the weighted independence number for every
nonnegative vertex weight. -/
def IsHPerfect : Prop := ∀ w : V → ℝ, (∀ i, 0 ≤ w i) → beta B w = alpha B w

omit [DecidableEq V] [Nonempty V] in

/-- If every point of `K` lies in the coordinatewise unit cube and `w` is nonnegative, then the
weighted sums over `K` are bounded above. Their common upper bound is `∑ i, w i`. -/
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

/-- Set inclusion `K ⊆ L` implies `supportFun K w ≤ supportFun L w` when `K` is nonempty and the
weighted sums over `L` are bounded above. -/
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

/-- The support value of a nonempty set in the coordinatewise unit cube is nonnegative at every
nonnegative weight. -/
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

/-- For nonnegative vertex weights, all independent-set weight sums are bounded above by the
total vertex weight. -/
lemma weightedIndepNum_bddAbove (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) :
    BddAbove {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ i ∈ I, w i} := by
  refine ⟨∑ i, w i, ?_⟩
  rintro x ⟨I, _, rfl⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
    (fun i _ _ => hw i)

omit [DecidableEq V] [Nonempty V] in

/-- The weighted independence number is nonnegative for every nonnegative weight function, as
witnessed by the empty independent set. -/
lemma weightedIndepNum_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) :
    0 ≤ weightedIndepNum G w := by
  unfold weightedIndepNum
  have hbdd := weightedIndepNum_bddAbove G hw
  have hmem : (0 : ℝ) ∈ {x : ℝ | ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ x = ∑ i ∈ I, w i} :=
    ⟨∅, by simp, by simp⟩
  exact le_csSup hbdd hmem

omit [Fintype V] [DecidableEq V] [Nonempty V] in

/-- Every singleton finite vertex set is independent in a simple graph. -/
lemma isIndepSet_coe_singleton (G : SimpleGraph V) (i : V) :
    G.IsIndepSet (({i} : Finset V) : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx hy
  rw [hx, hy] at hxy
  exact (hxy rfl).elim

omit [Nonempty V] in

/-- Every coordinate of a fractional cover is nonnegative, including coordinates indexed by sets
that are not independent. -/
lemma fracCover_nonneg {G : SimpleGraph V} {x : Finset V → ℝ} (hx : FracCover G x)
    (I : Finset V) : 0 ≤ x I := by
  by_cases hI : G.IsIndepSet (I : Set V)
  · exact hx.1 I hI
  · rw [hx.2.1 I hI]

/-- The finite-set weight function equal to one on sets of cardinality one and zero on all other
sets. -/
def singletonCover (_G : SimpleGraph V) : Finset V → ℝ :=
  fun I => if I.card = 1 then 1 else 0

omit [Nonempty V] in

/-- Assigning weight one to every singleton and zero elsewhere gives a fractional cover of any
finite simple graph. -/
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

/-- The set of total weights of fractional covers is nonempty. The singleton cover supplies a
feasible total weight. -/
lemma fracChromatic_set_nonempty (G : SimpleGraph V) :
    {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I}.Nonempty :=
  ⟨∑ I : Finset V, singletonCover G I, singletonCover G, singletonCover_feasible G, rfl⟩

omit [Nonempty V] in

/-- For any specified vertex, the total weight of a fractional cover is at least one because its
incident cover weight is at least one. -/
lemma one_le_sum_of_cover {G : SimpleGraph V} {x : Finset V → ℝ} (hx : FracCover G x)
    (i : V) : 1 ≤ ∑ I : Finset V, x I := by
  refine le_trans (hx.2.2 i) (Finset.sum_le_sum ?_)
  intro I _
  have hite : (if i ∈ I then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hmul := mul_le_mul_of_nonneg_left hite (fracCover_nonneg hx I)
  rwa [mul_one] at hmul

/-- The fractional chromatic number of a graph on a nonempty finite vertex type is at least one. -/
lemma one_le_fracChromatic (G : SimpleGraph V) : 1 ≤ fractionalChromatic G := by
  obtain ⟨i₀⟩ : Nonempty V := ‹Nonempty V›
  have hbdd : BddBelow {s : ℝ | ∃ x : Finset V → ℝ, FracCover G x ∧ s = ∑ I : Finset V, x I} :=
    ⟨1, by rintro s ⟨x, hx, rfl⟩; exact one_le_sum_of_cover hx i₀⟩
  exact (le_csInf_iff hbdd (fracChromatic_set_nonempty G)).2
    (fun s hs => by obtain ⟨x, hx, rfl⟩ := hs; exact one_le_sum_of_cover hx i₀)

/-- The fractional chromatic number of a graph on a nonempty finite vertex type is strictly
positive. -/
lemma fracChromatic_pos (G : SimpleGraph V) : 0 < fractionalChromatic G :=
  lt_of_lt_of_le zero_lt_one (one_le_fracChromatic G)

omit [Nonempty V] in

/-- The beta values on the probability simplex are bounded below by zero. -/
lemma delta_bddBelow : BddBelow ((fun w => beta B w) '' probSimplex V) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact supportFun_nonneg B.beta_nonempty B.beta_unit (mem_probSimplex hw).1

omit [Nonempty V] in

/-- The weighted independence numbers on the probability simplex are bounded below by zero. -/
lemma alpha_bddBelow : BddBelow ((fun w => alpha B w) '' probSimplex V) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact weightedIndepNum_nonneg B.G (mem_probSimplex hw).1

omit [Nonempty V] in

/-- The theta support values on the probability simplex are bounded below by zero. -/
lemma theta_bddBelow : BddBelow ((fun w => theta B w) '' probSimplex V) := by
  refine ⟨0, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact supportFun_nonneg B.theta_nonempty B.theta_unit (mem_probSimplex hw).1

omit [Nonempty V] in

/-- For every nonnegative weight function, the weighted independence number is at most the beta
support value. This follows from the inclusion of independent-set indicators in `B.BETA`
[XuEtAl2026]. -/
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

/-- For every nonnegative weight function, the beta support value is at most the theta support
value, using `B.BETA ⊆ B.TH`. -/
lemma beta_le_theta (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) : beta B w ≤ theta B w := by
  unfold beta theta
  exact supportFun_mono B.beta_subset_theta w (supportImage_bddAbove B.theta_unit hw)
    B.beta_nonempty

/-- The simplex infimum of the weighted independence number is at most the simplex infimum of
the beta support value. -/
lemma alphaMin_le_delta : alphaMin B ≤ delta B := by
  unfold alphaMin delta
  refine (le_csInf_iff (delta_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro b ⟨w, hw, rfl⟩
  exact le_trans (csInf_le (alpha_bddBelow B) ⟨w, hw, rfl⟩)
    (alpha_le_beta B w (mem_probSimplex hw).1)

/-- The simplex infimum of the beta support value is at most the simplex infimum of the theta
support value. -/
lemma delta_le_thetaMin : delta B ≤ thetaMin B := by
  unfold delta thetaMin
  refine (le_csInf_iff (theta_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro b ⟨w, hw, rfl⟩
  exact le_trans (csInf_le (delta_bddBelow B) ⟨w, hw, rfl⟩)
    (beta_le_theta B w (mem_probSimplex hw).1)

/-- If `B` is hbar-perfect, then its beta simplex infimum is at most its weighted-independence
simplex infimum. -/
lemma delta_le_alphaMin_of_hperfect (h : IsHPerfect B) : delta B ≤ alphaMin B := by
  unfold delta alphaMin
  refine (le_csInf_iff (alpha_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro b ⟨w, hw, rfl⟩
  show sInf ((fun w => beta B w) '' probSimplex V) ≤ alpha B w
  rw [← h w (mem_probSimplex hw).1]
  exact csInf_le (delta_bddBelow B) ⟨w, hw, rfl⟩

/-- For an hbar-perfect graph-body system, the beta and weighted-independence simplex infima are
equal [XuEtAl2026]. -/
theorem delta_eq_alphaMin_of_hperfect (h : IsHPerfect B) : delta B = alphaMin B :=
  le_antisymm (delta_le_alphaMin_of_hperfect B h) (alphaMin_le_delta B)

omit [Nonempty V] in

/-- For probability weights `w` and any fractional cover `x`, the weighted independence number
times the total cover weight is at least one. -/
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

/-- The weighted independence number is strictly positive for probability weights. Some vertex
has positive weight, and its singleton is independent. -/
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

/-- For probability weights, the product of the weighted independence number and the fractional
chromatic number is at least one. -/
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

/-- For every probability weight function, the reciprocal fractional chromatic number is at most
the weighted independence number. -/
lemma one_div_fracChromatic_le_alpha (G : SimpleGraph V) {w : V → ℝ}
    (hw : w ∈ probSimplex V) : 1 / fractionalChromatic G ≤ weightedIndepNum G w :=
  (div_le_iff₀ (fracChromatic_pos G)).mpr (alpha_mul_fracChromatic_ge_one G hw)

/-- The reciprocal fractional chromatic number is a lower bound for the simplex infimum of the
weighted independence number. -/
lemma one_div_fracChromatic_le_alphaMin (B : GraphBodies V) :
    1 / fractionalChromatic B.G ≤ alphaMin B := by
  unfold alphaMin
  refine (le_csInf_iff (alpha_bddBelow B)
    (Set.Nonempty.image _ probSimplex_nonempty)).2 ?_
  rintro x ⟨w, hw, rfl⟩
  exact one_div_fracChromatic_le_alpha B.G hw

end Qatlib.Papers.ShadowTomog26.MainResults
