/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs

/-!
# Disjoint unions and relabelings of MBQC flows

The predicate `HasFlowOn` expresses flow on a general vertex type, and agrees with `MbqcHasFlow`
on graph indices. This module constructs flows on disjoint unions and transports them along
equivalences, supporting the compositional setting of [DanosKashefi2006]. It also defines
adjacency and output data for gluing along an interface, and a branch-realization predicate.

## Main statements

* `hasFlowOn_sum`: The disjoint union of two flow graphs has flow with the disjoint unions of
  their input and output sets.
* `mbqcHasFlow_tensorization`: Two MBQC graphs with flow yield a flow on their disjoint-union
  adjacency and interfaces.
* `hasFlowOn_relabel`: Transporting adjacency and interfaces along a vertex equivalence
  preserves the existence of flow.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

/-- The existence of a partial successor map and strict order satisfying adjacency, input
exclusion, and causal flow conditions for every nonoutput vertex. -/
def HasFlowOn {V : Type*} [DecidableEq V] (Adj : V → V → Bool)
    (I O : Finset V) : Prop :=
  ∃ (f : V → Option V) (prec : V → V → Prop),
    IsStrictOrder V prec ∧
    ∀ v : V, v ∉ O → ∃ w : V,
      f v = some w ∧ Adj v w = true ∧ w ∉ I ∧ prec v w ∧
        ∀ k : V, Adj w k = true → k ≠ v → prec v k

/-- The graph-indexed MBQC flow predicate is equivalent to `HasFlowOn` for its Boolean adjacency
function. -/
theorem mbqcHasFlow_iff_hasFlowOn {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) :
    MbqcHasFlow G I O ↔ HasFlowOn (fun v w => mbqcAdj G v w) I O := by
  constructor
  · rintro ⟨f, prec, _dp, hord, hF⟩
    refine ⟨f, prec, hord, ?_⟩
    intro v hv
    obtain ⟨w, hw, hadj, hwI, hprec, hF3⟩ := hF v hv
    exact ⟨w, hw, hadj, hwI, hprec, fun k hk hne => hF3 k hk hne⟩
  · rintro ⟨f, prec, hord, hF⟩
    refine ⟨f, prec, Classical.decRel prec, hord, ?_⟩
    intro v hv
    obtain ⟨w, hw, hadj, hwI, hprec, hF3⟩ := hF v hv
    exact ⟨w, hw, hadj, hwI, hprec, fun k hk hne => hF3 k hk hne⟩

/-- The disjoint-union adjacency function, with no edges between the two vertex summands. -/
def sumAdj {V W : Type*} (A₁ : V → V → Bool) (A₂ : W → W → Bool) :
    V ⊕ W → V ⊕ W → Bool
  | .inl a, .inl b => A₁ a b
  | .inr a, .inr b => A₂ a b
  | _, _ => false

/-- The partial flow map on a disjoint union obtained by preserving each component flow within
its own summand. -/
def sumFlow {V W : Type*} (f₁ : V → Option V) (f₂ : W → Option W) :
    V ⊕ W → Option (V ⊕ W)
  | .inl a => (f₁ a).map (fun w => Sum.inl w)
  | .inr b => (f₂ b).map (fun w => Sum.inr w)

/-- The order preserving each component relation and placing every left-summand vertex before
every right-summand vertex. -/
def sumPrec {V W : Type*} (p₁ : V → V → Prop) (p₂ : W → W → Prop) :
    V ⊕ W → V ⊕ W → Prop
  | .inl a, .inl b => p₁ a b
  | .inr a, .inr b => p₂ a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False

/-- The ordered-sum relation is a strict order when both component relations are strict orders. -/
theorem isStrictOrder_sumPrec {V W : Type*} {p₁ : V → V → Prop} {p₂ : W → W → Prop}
    (h₁ : IsStrictOrder V p₁) (h₂ : IsStrictOrder W p₂) :
    IsStrictOrder (V ⊕ W) (sumPrec p₁ p₂) := by
  refine { irrefl := ?_, trans := ?_ }
  · intro x
    cases x with
    | inl a => simpa [sumPrec] using h₁.irrefl a
    | inr b => simpa [sumPrec] using h₂.irrefl b
  · intro a b c hab hbc
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        cases c with
        | inl c =>
          simpa [sumPrec] using
            h₁.trans a b c (by simpa [sumPrec] using hab) (by simpa [sumPrec] using hbc)
        | inr c => simp [sumPrec]
      | inr b =>
        cases c with
        | inl c => simp [sumPrec] at hbc
        | inr c => simp [sumPrec]
    | inr a =>
      cases b with
      | inl b => simp [sumPrec] at hab
      | inr b =>
        cases c with
        | inl c => simp [sumPrec] at hbc
        | inr c =>
          simpa [sumPrec] using
            h₂.trans a b c (by simpa [sumPrec] using hab) (by simpa [sumPrec] using hbc)

/-- The disjoint union of two flow graphs has flow with the disjoint unions of their input and
output sets [DanosKashefi2006]. -/
theorem hasFlowOn_sum {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {A₁ : V → V → Bool} {A₂ : W → W → Bool} {I₁ O₁ : Finset V} {I₂ O₂ : Finset W}
    (h₁ : HasFlowOn A₁ I₁ O₁) (h₂ : HasFlowOn A₂ I₂ O₂) :
    HasFlowOn (sumAdj A₁ A₂) (I₁.disjSum I₂) (O₁.disjSum O₂) := by
  obtain ⟨f₁, p₁, ho₁, hF₁⟩ := h₁
  obtain ⟨f₂, p₂, ho₂, hF₂⟩ := h₂
  refine ⟨sumFlow f₁ f₂, sumPrec p₁ p₂, isStrictOrder_sumPrec ho₁ ho₂, ?_⟩
  intro v hv
  cases v with
  | inl a =>
    have ha : a ∉ O₁ := by
      simpa [Finset.inl_mem_disjSum] using hv
    obtain ⟨w, hw, hadj, hwI, hprec, hF3⟩ := hF₁ a ha
    refine ⟨Sum.inl w, ?_, ?_, ?_, ?_, ?_⟩
    · simp [sumFlow, hw]
    · simpa [sumAdj] using hadj
    · simpa [Finset.inl_mem_disjSum] using hwI
    · simpa [sumPrec] using hprec
    · intro k hk hne
      cases k with
      | inl c =>
        exact by
          simpa [sumAdj, sumPrec] using
            hF3 c (by simpa [sumAdj] using hk) (by simpa using hne)
      | inr c => simp [sumAdj] at hk
  | inr b =>
    have hb : b ∉ O₂ := by
      simpa [Finset.inr_mem_disjSum] using hv
    obtain ⟨w, hw, hadj, hwI, hprec, hF3⟩ := hF₂ b hb
    refine ⟨Sum.inr w, ?_, ?_, ?_, ?_, ?_⟩
    · simp [sumFlow, hw]
    · simpa [sumAdj] using hadj
    · simpa [Finset.inr_mem_disjSum] using hwI
    · simpa [sumPrec] using hprec
    · intro k hk hne
      cases k with
      | inl c => simp [sumAdj] at hk
      | inr c =>
        exact by
          simpa [sumAdj, sumPrec] using
            hF3 c (by simpa [sumAdj] using hk) (by simpa using hne)

/-- Two MBQC graphs with flow yield a flow on their disjoint-union adjacency and interfaces
[DanosKashefi2006]. -/
theorem mbqcHasFlow_tensorization {n₁ n₂ : ℕ} (G₁ : MbqcGraph n₁) (G₂ : MbqcGraph n₂)
    (I₁ O₁ : Finset (Fin n₁)) (I₂ O₂ : Finset (Fin n₂))
    (h₁ : MbqcHasFlow G₁ I₁ O₁) (h₂ : MbqcHasFlow G₂ I₂ O₂) :
    HasFlowOn (sumAdj (fun v w => mbqcAdj G₁ v w) (fun v w => mbqcAdj G₂ v w))
      (I₁.disjSum I₂) (O₁.disjSum O₂) :=
  hasFlowOn_sum ((mbqcHasFlow_iff_hasFlowOn G₁ I₁ O₁).mp h₁)
    ((mbqcHasFlow_iff_hasFlowOn G₂ I₂ O₂).mp h₂)

/-- The adjacency on the first graph and the noninput vertices of the second, with cross edges
induced by the chosen identification of second inputs. -/
def compAdj {V W : Type*} [Fintype W] [DecidableEq W]
    (A₁ : V → V → Bool) (A₂ : W → W → Bool)
    (I₂ : Finset W) (e : {k : W // k ∈ I₂} → V) :
    V ⊕ {w : W // w ∉ I₂} → V ⊕ {w : W // w ∉ I₂} → Bool
  | .inl a, .inl b => A₁ a b
  | .inr a, .inr b => A₂ a.1 b.1
  | .inl a, .inr w =>
      decide (∃ k : {k : W // k ∈ I₂}, A₂ w.1 k.1 = true ∧ e k = a)
  | .inr w, .inl a =>
      decide (∃ k : {k : W // k ∈ I₂}, A₂ w.1 k.1 = true ∧ e k = a)

/-- The second graph output vertices that remain after restricting to its noninput vertices. -/
def compOutputs {W : Type*} [Fintype W] [DecidableEq W] (I₂ O₂ : Finset W) :
    Finset {w : W // w ∉ I₂} :=
  Finset.univ.filter (fun w => w.1 ∈ O₂)

/-- Transporting adjacency and interfaces along a vertex equivalence preserves the existence of
flow [DanosKashefi2006]. -/
theorem hasFlowOn_relabel {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {Adj : V → V → Bool} {I O : Finset V} (h : HasFlowOn Adj I O)
    (e : V ≃ W) :
    HasFlowOn (fun a b => Adj (e.symm a) (e.symm b))
      (I.map e.toEmbedding) (O.map e.toEmbedding) := by
  classical
  obtain ⟨f, prec, hord, hF⟩ := h
  have hmem : ∀ (S : Finset V) (w : W), w ∈ S.map e.toEmbedding ↔ e.symm w ∈ S := by
    intro S w
    constructor
    · intro hw
      rw [Finset.mem_map] at hw
      obtain ⟨a, ha, hae⟩ := hw
      rw [← hae]
      simpa using ha
    · intro hw
      rw [Finset.mem_map]
      exact ⟨e.symm w, hw, by simp⟩
  refine ⟨fun w => (f (e.symm w)).map e,
    fun a b => prec (e.symm a) (e.symm b), ?_, ?_⟩
  · refine { irrefl := ?_, trans := ?_ }
    · intro a
      exact hord.irrefl (e.symm a)
    · intro a b c hab hbc
      exact hord.trans (e.symm a) (e.symm b) (e.symm c) hab hbc
  · intro w hw
    have hwO : e.symm w ∉ O := fun hmemO => hw ((hmem O w).mpr hmemO)
    obtain ⟨v, hfv, hadj, hvI, hprec, hF3⟩ := hF (e.symm w) hwO
    refine ⟨e v, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hfv]
    · simpa using hadj
    · intro hmemI
      exact hvI (by simpa using (hmem I (e v)).mp hmemI)
    · simpa using hprec
    · intro k hk hne
      have hk' : Adj v (e.symm k) = true := by simpa using hk
      have hne' : e.symm k ≠ e.symm w := fun hh => hne (e.symm.injective hh)
      exact hF3 (e.symm k) hk' hne'

/-- The existence of an order and Pauli wire corrections making every XY-plane density branch
equal to conjugation by the specified matrix `U`. -/
def RealizesUnitary {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n))
    (a : Fin n → ℝ) (U : Matrix (Fin (2 ^ O.card)) (Fin (2 ^ I.card)) ℂ) : Prop :=
  ∃ (r : Fin n → Fin n) (corr : (Fin n → Bool) → Fin n → Operator 2),
    (∀ s : Fin n → Bool, ∀ v : Fin n, MbqcPauliWire (corr s v)) ∧
    ∀ ρ : Operator (2 ^ I.card), IsDensityOperator ρ →
      ∀ s : Fin n → Bool,
        mbqcPatternBranch G I O r (fun _ => MbqcPlane.XY) a corr s ρ
          = U * ρ * U.conjTranspose

end Qatlib.Papers.OneWayDanos05.MainResults
