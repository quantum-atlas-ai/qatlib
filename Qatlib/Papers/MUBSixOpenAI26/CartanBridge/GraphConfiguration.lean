/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.DistinctLabels

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Equation `exclude:graph-configuration`

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`exclusion.tex` lines 544--562 (Section 4.6, "Exact graph exclusion"),
displayed equation `exclude:graph-configuration`.

Two additional mutually unbiased orthonormal bases would give disjoint vertex
sets `A, B` with `|A| = |B| = 6`, both `𝒪`-cliques, and all `36` cross pairs in
`E(𝒰)`. Here `𝒪` retains possible orthogonal pairs and `𝒰` possible unbiased
pairs; extra edges are harmless, so only the necessary pattern is stated.

Reused FQNs: `Mub6BallCover.ExclusionCheck.labels_injective`
(see `MUB6GlobalTwoCliques.lean`) and `two_bases_force_pattern`. The statement
below spells out the paper's set-theoretic equation rather than the abbreviated
`TwoSixPattern`; the proof builds the two six-element `Finset`s from the
injective slot labelling and reads the clique/edge conditions off the retained
`𝒪`/`𝒰` edges.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ExclusionCheck
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- Equation `exclude:graph-configuration`: two disjoint six-cliques in `𝒪` with
all thirty-six cross edges in `𝒰`. -/
def TwoSixCliqueConfiguration {ι : Type*} (O U : ι → ι → Prop) : Prop :=
  ∃ A B : Finset ι,
    A.card = 6 ∧ B.card = 6 ∧ Disjoint A B ∧
    (∀ a ∈ A, ∀ b ∈ B, U a b) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → O a b)

/-- Equation `exclude:graph-configuration` (`exclusion.tex` lines 557--561):
two further mutually unbiased orthonormal bases whose vectors are covered by the
retained radius-`< 1/10` balls yield two disjoint six-cliques of `𝒪` with all
cross edges in `𝒰`. -/
theorem two_six_clique_configuration {ι : Type*}
    (v : ι → Phase6) (s : ι → ℝ) (hs : ∀ a, 0 ≤ s a ∧ s a < 1 / 10)
    (O U : ι → ι → Prop)
    (V : Fin 2 → Fin 6 → QState (Fin 6)) (hV : IsFamily V)
    (label : Fin 2 × Fin 6 → ι)
    (hcover : ∀ p, InBall (v (label p)) (s (label p)) (V p.1 p.2))
    (hO : ∀ r i j, i ≠ j → O (label (r, i)) (label (r, j)))
    (hU : ∀ i j, U (label (0, i)) (label (1, j))) :
    TwoSixCliqueConfiguration O U := by
  classical
  have hinj : Function.Injective label :=
    labels_injective v s hs V hV label hcover
  let A : Finset ι := (Finset.univ : Finset (Fin 6)).image (fun i => label (0, i))
  let B : Finset ι := (Finset.univ : Finset (Fin 6)).image (fun i => label (1, i))
  have hinjA : Function.Injective (fun i : Fin 6 => label (0, i)) :=
    fun i j hij => congrArg Prod.snd (hinj hij)
  have hinjB : Function.Injective (fun i : Fin 6 => label (1, i)) :=
    fun i j hij => congrArg Prod.snd (hinj hij)
  have hcardA : A.card = 6 := by
    show ((Finset.univ : Finset (Fin 6)).image (fun i => label (0, i))).card = 6
    rw [Finset.card_image_of_injective _ hinjA]
    simp
  have hcardB : B.card = 6 := by
    show ((Finset.univ : Finset (Fin 6)).image (fun i => label (1, i))).card = 6
    rw [Finset.card_image_of_injective _ hinjB]
    simp
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    change x ∈ (Finset.univ : Finset (Fin 6)).image (fun i => label (0, i)) at hxA
    change x ∈ (Finset.univ : Finset (Fin 6)).image (fun i => label (1, i)) at hxB
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxA hxB
    obtain ⟨i, hi⟩ := hxA
    obtain ⟨j, hj⟩ := hxB
    have heq : label (0, i) = label (1, j) := by rw [hi, hj]
    have hpair := hinj heq
    have hval : (0 : Fin 2).val = (1 : Fin 2).val := by
      simpa using congrArg (fun p : Fin 2 × Fin 6 => p.1.val) hpair
    exact absurd hval (by norm_num)
  refine ⟨A, B, hcardA, hcardB, hdisj, ?_, ?_⟩
  · intro a ha b hb
    change a ∈ (Finset.univ : Finset (Fin 6)).image (fun i => label (0, i)) at ha
    change b ∈ (Finset.univ : Finset (Fin 6)).image (fun i => label (1, i)) at hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    rw [← hi, ← hj]
    exact hU i j
  · intro a ha b hb hne
    change a ∈ (Finset.univ : Finset (Fin 6)).image (fun i => label (0, i)) at ha
    change b ∈ (Finset.univ : Finset (Fin 6)).image (fun i => label (0, i)) at hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    rw [← hi, ← hj]
    exact hO 0 i j (fun hij => hne (by rw [← hi, ← hj, hij]))

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
