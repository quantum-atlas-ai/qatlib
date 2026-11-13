/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore

/-!
# Flow injections and the cardinality consequence of bi-flow

The flow conditions of [DanosKashefi2006] imply an injection from nonoutput vertices to noninput
vertices and hence `I.card ≤ O.card`. Flow in both directions gives equal interface
cardinalities. The module also records the square-isometry implication and defines
`PatternRealizes` by equality of every corrected density branch with a prescribed matrix map.

## Main statements

* `flow_card_le`: If an MBQC graph has flow from inputs `I` to outputs `O`, then `I.card ≤
  O.card`.
* `biFlow_card_eq`: An MBQC graph with bi-flow has equally many inputs and outputs.
* `biFlow_unitary_core`: Bi-flow gives equal input and output cardinalities, and every isometry
  on the input register also satisfies the opposite unitary identity.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

/-- The adjacency relation of an MBQC graph is symmetric. -/
theorem mbqcAdj_comm {n : ℕ} (G : MbqcGraph n) (i j : Fin n) :
    mbqcAdj G i j = mbqcAdj G j i := by
  unfold mbqcAdj
  by_cases h1 : (i, j) ∈ G.edges <;> by_cases h2 : (j, i) ∈ G.edges <;>
    simp [h1, h2]

/-- Under the strict-order flow conditions, two nonoutput vertices with the same flow successor
are equal [DanosKashefi2006]. -/
theorem flow_injective_on_compl {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    {f : Fin n → Option (Fin n)} {prec : Fin n → Fin n → Prop}
    (hord : IsStrictOrder (Fin n) prec)
    (hF : ∀ v : Fin n, v ∉ O → ∃ w : Fin n,
      f v = some w ∧ mbqcAdj G v w ∧ w ∉ I ∧ prec v w ∧
        ∀ k : Fin n, mbqcAdj G w k → k ≠ v → prec v k)
    {v v' w : Fin n} (hv : v ∉ O) (hv' : v' ∉ O)
    (hfv : f v = some w) (hfv' : f v' = some w) : v = v' := by
  by_contra hne
  obtain ⟨w₁, hf₁, hadj₁, _, _, hF3₁⟩ := hF v hv
  obtain ⟨w₂, hf₂, hadj₂, _, _, hF3₂⟩ := hF v' hv'
  have hw₁ : w₁ = w := Option.some.inj (hf₁.symm.trans hfv)
  have hw₂ : w₂ = w := Option.some.inj (hf₂.symm.trans hfv')
  have hw21 : w₂ = w₁ := hw₂.trans hw₁.symm
  have hw12 : w₁ = w₂ := hw₁.trans hw₂.symm

  have hprec₂ : prec v' v := by
    refine hF3₂ v ?_ hne
    rw [hw21, mbqcAdj_comm G w₁ v]
    exact hadj₁

  have hprec₁ : prec v v' := by
    refine hF3₁ v' ?_ (fun h : v' = v => hne h.symm)
    rw [hw12, mbqcAdj_comm G w₂ v']
    exact hadj₂
  exact hord.irrefl v (hord.trans v v' v hprec₁ hprec₂)

/-- An MBQC flow gives an injection from the nonoutput vertices into the noninput vertices. -/
theorem flow_compl_injection {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    (h : MbqcHasFlow G I O) :
    ∃ φ : {v : Fin n // v ∉ O} → {w : Fin n // w ∉ I}, Function.Injective φ := by
  classical
  obtain ⟨f, prec, _dp, hord, hF⟩ := h
  refine ⟨fun v => ⟨(hF v.1 v.2).choose, (hF v.1 v.2).choose_spec.2.2.1⟩, ?_⟩
  intro v v' hvv
  apply Subtype.ext
  refine flow_injective_on_compl hord hF v.2 v'.2
    (hF v.1 v.2).choose_spec.1 ?_
  have hval : (hF v.1 v.2).choose = (hF v'.1 v'.2).choose := congrArg Subtype.val hvv
  rw [(hF v'.1 v'.2).choose_spec.1, hval]

/-- If an MBQC graph has flow from inputs `I` to outputs `O`, then `I.card ≤ O.card`. -/
theorem flow_card_le {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    (h : MbqcHasFlow G I O) : I.card ≤ O.card := by
  classical
  obtain ⟨φ, hφ⟩ := flow_compl_injection h
  have hle := Fintype.card_le_of_injective φ hφ
  have hcO : Fintype.card {v : Fin n // v ∉ O} = n - O.card := by
    rw [Fintype.card_subtype_compl (p := fun v : Fin n => v ∈ O), Fintype.card_fin,
      Fintype.card_coe]
  have hcI : Fintype.card {w : Fin n // w ∉ I} = n - I.card := by
    rw [Fintype.card_subtype_compl (p := fun v : Fin n => v ∈ I), Fintype.card_fin,
      Fintype.card_coe]
  rw [hcO, hcI] at hle
  have hOn : O.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ O)
    simpa using this
  have hIn : I.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ I)
    simpa using this
  omega

/-- The predicate that the graph has flow both from `I` to `O` and from `O` to `I`. -/
def MbqcHasBiFlow {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) : Prop :=
  MbqcHasFlow G I O ∧ MbqcHasFlow G O I

/-- An MBQC graph with bi-flow has equally many inputs and outputs [DanosKashefi2006]. -/
theorem biFlow_card_eq {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    (h : MbqcHasBiFlow G I O) : I.card = O.card := by
  have h1 : I.card ≤ O.card := flow_card_le h.1
  have h2 : O.card ≤ I.card := flow_card_le h.2
  omega

/-- A square complex matrix satisfying `Uᴴ * U = 1` also satisfies `U * Uᴴ = 1`
[DanosKashefi2006]. -/
theorem square_isometry_is_unitary {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (h : U.conjTranspose * U = 1) : U * U.conjTranspose = 1 :=
  mul_eq_one_comm.mp h

/-- Bi-flow gives equal input and output cardinalities, and every isometry on the input register
also satisfies the opposite unitary identity [DanosKashefi2006]. -/
theorem biFlow_unitary_core {n : ℕ} {G : MbqcGraph n} {I O : Finset (Fin n)}
    (hbi : MbqcHasBiFlow G I O) :
    I.card = O.card ∧
      ∀ U : Matrix (Fin (2 ^ I.card)) (Fin (2 ^ I.card)) ℂ,
        U.conjTranspose * U = 1 → U * U.conjTranspose = 1 := by
  refine ⟨biFlow_card_eq hbi, ?_⟩
  intro U hU
  exact square_isometry_is_unitary U hU

/-- The existence of a measurement order and Pauli wire corrections making every XY-plane
density branch equal to conjugation by the prescribed matrix `U`. -/
def PatternRealizes {n : ℕ} (G : MbqcGraph n) (I O : Finset (Fin n)) (a : Fin n → ℝ)
    (U : Matrix (Fin (2 ^ O.card)) (Fin (2 ^ I.card)) ℂ) : Prop :=
  ∃ (r : Fin n → Fin n) (corr : (Fin n → Bool) → Fin n → Operator 2),
    (∀ s : Fin n → Bool, ∀ v : Fin n, MbqcPauliWire (corr s v)) ∧
    ∀ ρ : Operator (2 ^ I.card), IsDensityOperator ρ → ∀ s : Fin n → Bool,
      mbqcPatternBranch G I O r (fun _ => MbqcPlane.XY) a corr s ρ
        = U * ρ * U.conjTranspose

end Qatlib.Papers.OneWayDanos05.MainResults
