/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel
import Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation.CompletionProduct

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Theorem 2: the reduction to Lemma 2 and Theorem 1

McNulty–Weigert, fixed arXiv:1203.6887v2, Theorem 2, p. 8:

> The product constellation `{5,5,4}⊗₆` cannot be part of a complete set of seven MU bases.

The paper's one-paragraph proof: if the constellation sat inside a complete set, Lemma 2
would turn three of the seven bases into a triple of MU *product* bases; any vector of a
fourth basis of the complete set is then MU to that triple, contradicting Theorem 1.

This file formalises that reduction as a genuine logical implication, taking as explicit
hypotheses the two paper results it invokes: the general (all-product-triple) form of
Theorem 1 and the full Lemma 2.  Both are separate claims of this paper (`c002`, `c004`);
the reduction itself is unconditional.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Theorem2NoCompleteSet

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel
open Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel

/-- **Theorem 2, reduced form** (arXiv:1203.6887v2, p. 8).

Assume the general form of Theorem 1 (no MU product triple admits a single MU vector) and
Lemma 2 (any MU triple containing the product constellation is a product triple).  Then no
complete set of seven MU bases contains the product constellation `{5,5,4}⊗₆`.

The three bases `rA, rB, rS` hosting the constellation give a MU triple `T`; a fourth basis
`r4` (which exists because `7 > 3`) supplies a vector MU to `T`, which Theorem 1 forbids. -/
theorem theorem2_reduction
    (hT1 : ∀ T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3), IsMuProductTriple T →
      ∀ ψ : QState (Fin 2 × Fin 3),
        ¬ (∀ r j, Complex.normSq (Inner (T r j) ψ) = 1 / 6))
    (hLemma2 : ∀ (C : Constellation554) (T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)),
      IsMuTriple T → ContainsConstellationInTriple T C → ∀ r k, IsProductState (T r k))
    (C : Constellation554) (M : Fin 7 → Fin 6 → QState (Fin 2 × Fin 3))
    (hM : IsCompleteMuSet M) :
    ¬ ContainsConstellationInSet M C := by
  rintro ⟨rA, rB, rS, hrAB, hrAS, hrBS, ⟨eA, hA⟩, ⟨eB, hB⟩, ⟨eS, hS⟩⟩
  -- A fourth basis index distinct from `rA, rB, rS` (there are seven, only three used).
  have hex : ∃ r4 : Fin 7, r4 ≠ rA ∧ r4 ≠ rB ∧ r4 ≠ rS := by
    by_contra h
    rw [not_exists] at h
    have hsurj : Function.Surjective ![rA, rB, rS] := by
      intro x
      have hx := h x
      by_cases h1 : x = rA
      · exact ⟨0, by simpa using h1.symm⟩
      · by_cases h2 : x = rB
        · exact ⟨1, by simpa using h2.symm⟩
        · have h3 : x = rS := by
            by_contra h3
            exact hx ⟨h1, h2, h3⟩
          exact ⟨2, by simpa using h3.symm⟩
    have hle := Fintype.card_le_of_surjective ![rA, rB, rS] hsurj
    simp only [Fintype.card_fin] at hle
    omega
  obtain ⟨r4, hr4A, hr4B, hr4S⟩ := hex
  -- The triple of bases `rA, rB, rS`.
  let g : Fin 3 → Fin 7 := ![rA, rB, rS]
  let T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3) := fun r => M (g r)
  have hg0 : g 0 = rA := by simp [g]
  have hg1 : g 1 = rB := by simp [g]
  have hg2 : g 2 = rS := by simp [g]
  have hginj : Function.Injective g := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all [g, hrAB, hrAS, hrBS]
  -- `T` is a MU triple, inherited from the complete set.
  have hTmu : IsMuTriple T := by
    refine ⟨fun r => hM.1 (g r), ?_⟩
    intro r s hrs i j
    exact hM.2 (g r) (g s) (fun h => hrs (hginj h)) i j
  -- `T` contains the constellation.
  have hcont : ContainsConstellationInTriple T C := by
    refine ⟨⟨eA, fun i => ?_⟩, ⟨eB, fun i => ?_⟩, ⟨eS, fun i => ?_⟩⟩
    · show M (g 0) (eA i) = C.finA i
      rw [hg0]; exact hA i
    · show M (g 1) (eB i) = C.finB i
      rw [hg1]; exact hB i
    · show M (g 2) (eS i) = C.four i
      rw [hg2]; exact hS i
  -- Lemma 2 makes `T` a triple of MU product bases.
  have hprod : ∀ r k, IsProductState (T r k) := hLemma2 C T hTmu hcont
  -- A vector from the fourth basis is MU to every state of `T`.
  have hψ : ∀ r j, Complex.normSq (Inner (T r j) (M r4 0)) = 1 / 6 := by
    intro r j
    have hne : g r ≠ r4 := by
      have hmem : g r = rA ∨ g r = rB ∨ g r = rS := by
        fin_cases r
        · exact Or.inl hg0
        · exact Or.inr (Or.inl hg1)
        · exact Or.inr (Or.inr hg2)
      rintro h
      rcases hmem with h' | h' | h'
      · exact hr4A (h.symm.trans h')
      · exact hr4B (h.symm.trans h')
      · exact hr4S (h.symm.trans h')
    exact hM.2 (g r) r4 hne j 0
  exact hT1 T ⟨hprod, hTmu⟩ (M r4 0) hψ

end Qatlib.Papers.MUBProduct12.TripleClassify.Theorem2NoCompleteSet
