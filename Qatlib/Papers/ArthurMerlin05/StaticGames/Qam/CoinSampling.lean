/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ArthurMerlin05.StaticGames.Qam.Proposition43
public import Qatlib.Papers.ArthurMerlin05.StaticGames.Core.Toolkit

@[expose] public section


/-!
# Actual strategy semantics for Proposition 4.3

Marriott--Watrous, *Quantum Arthur--Merlin Games*, cs/0506068v1, p. 17.
For a fixed input, Arthur chooses one of `2^s` coin strings uniformly and Merlin
chooses an arbitrary normalized witness after seeing that string. The maximum
acceptance profile is the supremum of these actual witness probabilities.

Completeness and soundness are used on their respective input branches. The
soundness proof chooses a witness above the threshold at every bad coin; it
does not assume an optimizer or the desired average bound on the supremum.
The final theorem instantiates this argument with positive quantum effects
bounded by the identity. Uniform circuit synthesis is irrelevant to this
finite probability implication and is not supplied by this module.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.CoinSampling

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- A bounded acceptance game with public uniform coin strings and arbitrary witnesses. -/
structure Game (s : ℕ) (W : Type*) where
  /-- The acceptance probability for a coin string and Merlin witness. -/
  payoff : Fin (Qdim s) → W → ℝ
  /-- Every actual witness has a probability in the unit interval. -/
  valid : ∀ y w, 0 ≤ payoff y w ∧ payoff y w ≤ 1

/-- The supremum acceptance probability for a fixed public coin string. -/
def coinMax {s : ℕ} {W : Type*} (G : Game s W) (y : Fin (Qdim s)) : ℝ :=
  sSup (Set.range (G.payoff y))

/-- Uniform probability of a predicate on Arthur's coin strings. -/
def coinFrac {s : ℕ} (p : Fin (Qdim s) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter p).card : ℝ) / (Qdim s : ℝ)

/-- Actual acceptance values form a bounded-above set. -/
theorem payoffBound {s : ℕ} {W : Type*} (G : Game s W) (y : Fin (Qdim s)) :
    BddAbove (Set.range (G.payoff y)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact (G.valid y w).2

/-- Every actual Merlin witness is bounded by the supremum acceptance value. -/
theorem payoff_le_max {s : ℕ} {W : Type*} (G : Game s W)
    (y : Fin (Qdim s)) (w : W) : G.payoff y w ≤ coinMax G y :=
  le_csSup (payoffBound G y) (Set.mem_range_self w)

/-- The supremum profile of a nonempty bounded game is a probability. -/
theorem max_valid {s : ℕ} {W : Type*} [Nonempty W] (G : Game s W)
    (y : Fin (Qdim s)) : 0 ≤ coinMax G y ∧ coinMax G y ≤ 1 := by
  constructor
  · exact le_trans (G.valid y (Classical.choice inferInstance)).1
      (payoff_le_max G y (Classical.choice inferInstance))
  · apply csSup_le (Set.range_nonempty (G.payoff y))
    rintro _ ⟨w, rfl⟩
    exact (G.valid y w).2

/-- Subtracting a coin profile from one complements its uniform mean. -/
theorem avg_complement {s : ℕ} (f : Fin (Qdim s) → ℝ) :
    coinAverage (fun y => 1 - f y) = 1 - coinAverage f := by
  have hN : (Qdim s : ℝ) ≠ 0 := by positivity
  unfold coinAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- One high-acceptance strategy yields many coins whose optimal value is high. -/
theorem sourceYes {s : ℕ} {W : Type*} [Nonempty W] (G : Game s W)
    (hyes : ∃ strategy : Fin (Qdim s) → W,
      (8 / 9 : ℝ) ≤ coinAverage (fun y => G.payoff y (strategy y))) :
    (2 / 3 : ℝ) ≤ coinFrac (fun y => 2 / 3 ≤ coinMax G y) := by
  obtain ⟨strategy, hstrategy⟩ := hyes
  have hmean : coinAverage (fun y => G.payoff y (strategy y)) ≤
      coinAverage (coinMax G) := by
    unfold coinAverage
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun y _ => payoff_le_max G y (strategy y)) (by positivity)
  have herror : coinAverage (fun y => 1 - coinMax G y) ≤ 1 / 9 := by
    rw [avg_complement]
    linarith
  exact Qatlib.Papers.ArthurMerlin05.StaticGames.Qam.prop_4_3_yes
    (coinMax G) (fun y => (max_valid G y).2) herror

/-- Universal strategy soundness yields many coins whose optimal value is low. -/
theorem sourceNo {s : ℕ} {W : Type*} [Nonempty W] (G : Game s W)
    (hno : ∀ strategy : Fin (Qdim s) → W,
      coinAverage (fun y => G.payoff y (strategy y)) ≤ (1 / 9 : ℝ)) :
    (2 / 3 : ℝ) ≤ coinFrac (fun y => coinMax G y ≤ 1 / 3) := by
  classical
  have hex (y : Fin (Qdim s)) :
      ∃ w : W, (1 / 3 : ℝ) < coinMax G y → 1 / 3 < G.payoff y w := by
    by_cases hbad : (1 / 3 : ℝ) < coinMax G y
    · have hw : ∃ w : W, (1 / 3 : ℝ) < G.payoff y w := by
        by_contra hnone
        have hbound : coinMax G y ≤ 1 / 3 := by
          apply csSup_le (Set.range_nonempty (G.payoff y))
          rintro _ ⟨w, rfl⟩
          exact le_of_not_gt (fun h => hnone ⟨w, h⟩)
        linarith
      obtain ⟨w, hw⟩ := hw
      exact ⟨w, fun _ => hw⟩
    · exact ⟨Classical.choice inferInstance, fun h => (hbad h).elim⟩
  choose strategy hstrategy using hex
  have hN : 0 < Fintype.card (Fin (Qdim s)) := by
    simp only [Fintype.card_fin]
    positivity
  have hmean : (∑ y, G.payoff y (strategy y)) /
      (Fintype.card (Fin (Qdim s)) : ℝ) ≤ (1 / 9 : ℝ) := by
    simpa only [coinAverage, Fintype.card_fin] using hno strategy
  have hsmall := Qatlib.Papers.ArthurMerlin05.StaticGames.Qam.markov_threshold
    (fun y => G.payoff y (strategy y)) hN
    (fun y => (G.valid y (strategy y)).1) hmean
  have hsubset :
      Finset.univ.filter (fun y => G.payoff y (strategy y) ≤ (1 / 3 : ℝ)) ⊆
      Finset.univ.filter (fun y => coinMax G y ≤ (1 / 3 : ℝ)) := by
    intro y hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
    have hpay := (Finset.mem_filter.mp hy).2
    by_contra hmax
    have := hstrategy y (lt_of_not_ge hmax)
    linarith
  have hcard :
      ((Finset.univ.filter (fun y => G.payoff y (strategy y) ≤ (1 / 3 : ℝ))).card : ℝ) ≤
      ((Finset.univ.filter (fun y => coinMax G y ≤ (1 / 3 : ℝ))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hfrac := div_le_div_of_nonneg_right hcard (show (0 : ℝ) ≤ Qdim s by positivity)
  exact le_trans (by simpa only [Fintype.card_fin] using hsmall) hfrac

/-- Proposition 4.3 uses completeness on yes inputs and soundness on no inputs. -/
theorem sourceProp43 {s : ℕ} {W : Type*} [Nonempty W] (G : Game s W)
    (P : Prop)
    (hyes : P → ∃ strategy : Fin (Qdim s) → W,
      (8 / 9 : ℝ) ≤ coinAverage (fun y => G.payoff y (strategy y)))
    (hno : ¬ P → ∀ strategy : Fin (Qdim s) → W,
      coinAverage (fun y => G.payoff y (strategy y)) ≤ (1 / 9 : ℝ)) :
    (P → (2 / 3 : ℝ) ≤ coinFrac (fun y => 2 / 3 ≤ coinMax G y)) ∧
      (¬ P → (2 / 3 : ℝ) ≤ coinFrac (fun y => coinMax G y ≤ 1 / 3)) :=
  ⟨fun h => sourceYes G (hyes h), fun h => sourceNo G (hno h)⟩

/-- Merlin's complete continuous space of normalized pure m-qubit witnesses. -/
abbrev BornWitness (m : ℕ) := {ψ : QState (Fin (Qdim m)) // Normalized ψ}

/-- A computational-basis witness inhabits every qubit witness space. -/
instance bornNonempty (m : ℕ) : Nonempty (BornWitness m) :=
  ⟨⟨Qatlib.Foundations.PureStateMath.Ket ⟨0, by positivity⟩, normalized_ket _⟩⟩

/-- A positive effect bounded by the identity has Born probabilities in [0,1]. -/
theorem bornBounds {m : ℕ} {Q : Operator (Qdim m)}
    (hQ : Q.PosSemidef) (hIQ : ((1 : Operator (Qdim m)) - Q).PosSemidef)
    (ψ : BornWitness m) : 0 ≤ acceptProb Q ψ.val ∧ acceptProb Q ψ.val ≤ 1 := by
  have hP : (outerProduct ψ.val).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (isOrthogonalProjector_outerProduct ψ.property).nonneg
  have hnonneg (A : Operator (Qdim m)) (hA : A.PosSemidef) :
      0 ≤ acceptProb A ψ.val := by
    rw [Qatlib.Papers.ArthurMerlin05.StaticGames.Core.acceptProb_eq_trace]
    exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg hA hP)).1
  have htrace : Matrix.trace (outerProduct ψ.val) = 1 := by
    calc
      Matrix.trace (outerProduct ψ.val) =
          Matrix.trace ((1 : Operator (Qdim m)) * outerProduct ψ.val) := by
            rw [Matrix.one_mul]
      _ = Qatlib.Foundations.PureStateMath.Inner ψ.val
          ((1 : Operator (Qdim m)) *ᵥ ψ.val) :=
        Qatlib.Papers.ArthurMerlin05.StaticGames.Core.trace_mul_outerProduct _ _
      _ = 1 := by
        rw [Matrix.one_mulVec]
        exact (normalized_iff_inner_self _).mp ψ.property
  have hsum : acceptProb ((1 : Operator (Qdim m)) - Q) ψ.val =
      1 - acceptProb Q ψ.val := by
    rw [Qatlib.Papers.ArthurMerlin05.StaticGames.Core.acceptProb_eq_trace,
      Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htrace]
    rw [Qatlib.Papers.ArthurMerlin05.StaticGames.Core.acceptProb_eq_trace]
    simp
  refine ⟨hnonneg Q hQ, ?_⟩
  have hc := hnonneg ((1 : Operator (Qdim m)) - Q) hIQ
  rw [hsum] at hc
  linarith

/-- The coin game defined by actual quantum effects on normalized witnesses. -/
def bornGame {m s : ℕ} (Q : Fin (Qdim s) → Operator (Qdim m))
    (hQ : ∀ y, (Q y).PosSemidef)
    (hIQ : ∀ y, ((1 : Operator (Qdim m)) - Q y).PosSemidef) : Game s (BornWitness m) where
  payoff y ψ := acceptProb (Q y) ψ.val
  valid y ψ := bornBounds (hQ y) (hIQ y) ψ

/-- Proposition 4.3 for a fixed input's actual positive acceptance effects. -/
theorem sourceBorn43 {m s : ℕ} (Q : Fin (Qdim s) → Operator (Qdim m))
    (hQ : ∀ y, (Q y).PosSemidef)
    (hIQ : ∀ y, ((1 : Operator (Qdim m)) - Q y).PosSemidef)
    (P : Prop)
    (hyes : P → ∃ strategy : Fin (Qdim s) → QState (Fin (Qdim m)),
      (∀ y, Normalized (strategy y)) ∧
        (8 / 9 : ℝ) ≤ coinAverage (fun y => acceptProb (Q y) (strategy y)))
    (hno : ¬ P → ∀ strategy : Fin (Qdim s) → QState (Fin (Qdim m)),
      (∀ y, Normalized (strategy y)) →
        coinAverage (fun y => acceptProb (Q y) (strategy y)) ≤ (1 / 9 : ℝ)) :
    (P → (2 / 3 : ℝ) ≤ coinFrac (fun y => 2 / 3 ≤ coinMax (bornGame Q hQ hIQ) y)) ∧
      (¬ P → (2 / 3 : ℝ) ≤ coinFrac
        (fun y => coinMax (bornGame Q hQ hIQ) y ≤ 1 / 3)) := by
  apply sourceProp43 (bornGame Q hQ hIQ) P
  · intro hP
    obtain ⟨strategy, hnorm, hstrategy⟩ := hyes hP
    exact ⟨fun y => ⟨strategy y, hnorm y⟩, hstrategy⟩
  · intro hP strategy
    exact hno hP (fun y => (strategy y).val) (fun y => (strategy y).property)

end Qatlib.Papers.ArthurMerlin05.StaticGames.CoinSampling
