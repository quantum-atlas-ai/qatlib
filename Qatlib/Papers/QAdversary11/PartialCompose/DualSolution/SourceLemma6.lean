/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration.SourceLemma1
import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan

set_option backward.isDefEq.respectTransparency false

/-!
# DualSolution — paper Lemma 6 (composition of dual adversary solutions)

Kimmel, *Quantum Adversary (Upper) Bound*, fixed arXiv:1101.0797v5 (16 May 2013).
Lemma 6, p. 10 and Appendix A pp. 10–12 (Eqs. (14)–(20)).

The paper constructs an explicit dual solution `(U, Υ)` for the composed problem
`f ∘ g` as

`(U', Υ') = (c · Ṽ' ∘ (d_g Ω + W)^{⊗ n}, c · d_g^{n-1} · Λ̃' ∘ Ω^{⊗ n})`,
`c = 2^n · d_g^{-(n-1)}`,

and concludes that `(U, Υ)` certifies `ADV±(f ∘ g) = d_g · d_f`. The two
matrices `Ṽ' ∘ (d_g Ω + W)^{⊗ n}` are precisely the library's weighted
composition `weightedAdvGamma` with the factor `‖G_g‖·I + G_g` folded in
(`WeightedAdversaryComposition.weightedAdvGamma`), and the normalisation
`c = d_g^{-(n-1)}` is the library's `C = d⁻¹ • H` with `d = ‖G_g‖^{m-1}`.

This file states Lemma 6 in the shared source models as the two-sided composition
inequality for the independent-input composed problem
`(x^1, …, x^n) ↦ f (g x^1, …, g x^n)`:

* **lower bound** (`≥ d_f · d_g`, the constructive half of Lemma 6):
  `sourceFunctionComposition_lower`, whose proof is exactly the `(U, Υ)`
  construction (the frozen `sourceFunctionComposition_matrix_lower` is the
  per-witness identity);
* **upper bound** on the constrained domain where the source problem is defined
  (`g (x^i) ∈ S`, the paper's validity condition): the matching
  `sourceFunctionComposition_upper`, with the inner rectangular value identified
  with `d_g = ADV±(g)` by the Boolean norm sandwich (`functionEvaluationNormSandwich`
  at `|E| = 2`, where the relaxation factor `2(1-1/|E|)` equals `1`).

The paper's equality `ADV±(f ∘ g) = d_g · d_f` therefore holds on the domain
`D` where `g (x^i) ∈ S`; on the full product domain the library only proves the
lower bound, which is what Lemma 6's dual construction delivers.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.QAdversary11.PartialCompose.DualSolution

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Papers.QAdversary11.PartialCompose.AdversaryIteration

/-- Output-relabelling invariance of the source adversary: if two output maps
have the same kernel (`f x = f y ↔ g x = g y`), every adversary witness serves
both, so the two adversary values coincide. In particular `Bool` and its
`Fin 2` encoding `sourceBooleanSymbol` have the same kernel. -/
theorem sourceAdversary_congr_output {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) {E F : Type} [DecidableEq E] [DecidableEq F]
    (f : X → E) (g : X → F) (h : ∀ x y, f x = f y ↔ g x = g y) :
    sourceAdversary (sourceAlphabetDelta input) f = sourceAdversary (sourceAlphabetDelta input) g := by
  unfold sourceAdversary
  apply le_antisymm
  · apply iSup_le
    intro Γ
    refine le_iSup_of_le ⟨Γ.val, Γ.property.1, Γ.property.2.1, ?_, Γ.property.2.2.2⟩ le_rfl
    intro x y hxy
    exact Γ.property.2.2.1 x y ((h x y).mpr hxy)
  · apply iSup_le
    intro Γ
    refine le_iSup_of_le ⟨Γ.val, Γ.property.1, Γ.property.2.1, ?_, Γ.property.2.2.2⟩ le_rfl
    intro x y hxy
    exact Γ.property.2.2.1 x y ((h x y).mp hxy)

/-- **Paper Lemma 6** (arXiv:1101.0797v5, p. 10; Appendix A pp. 10–12): the
dual composition. Let `inner : X → Fin n → Fin (q+1)` describe the inner query
input, `g : X → Bool` the inner function, and `f : (Fin m → Bool) → Bool` the
outer function. Then, for the independent-input composed problem
`sourceIndependentInput inner m`:

1. `ADV±(f) · ADV±(g) ≤ ADV±(f ∘ g)` — the constructed dual solution gives the
   lower bound (this is the content of `(U, Υ)`, Eq. (14)–(20));
2. on the domain `D` where the inner values are legal inputs of `f`
   (`booleanInput p.1 j = sourceBooleanSymbol (g (p.2 j))`, the paper's
   `g (x^i) ∈ S`), the matching upper bound holds, so `ADV±(f ∘ g) = d_g · d_f`
   on `D`.

The nondegeneracy hypothesis `hnd` is the paper's standing assumption that the
composed problem is not trivial (it excludes the degenerate `0 · ⊤` product). -/
theorem adversary_composition_dual_solution
    {X : Type} [Fintype X] [DecidableEq X] {n q : ℕ}
    (inner : X → Fin n → Fin (q+1)) (g : X → Bool) (m : ℕ)
    (f : (Fin m → Bool) → Bool)
    (hnd : sourceAdversary (sourceAlphabetDelta (booleanInput (n := m))) f < ⊤ ∨
      sourceRectValue (gramFunctionEvaluationMatrix (fun x => sourceBooleanSymbol (g x)))
        (sourceAlphabetDelta inner) ≠ 0) :
    (sourceAdversary (sourceAlphabetDelta (booleanInput (n := m))) f *
      sourceAdversary (sourceAlphabetDelta inner) g ≤
      sourceAdversary (sourceAlphabetDelta (sourceIndependentInput inner m))
        (fun xs => f (fun j => g (xs j)))) ∧
    (sourceAdversary
        (sourceAlphabetDelta (fun p : {p : (Fin m → Bool) × (Fin m → X) //
            ∀ j, booleanInput (n := m) p.1 j = sourceBooleanSymbol (g (p.2 j))} =>
          sourceIndependentInput inner m p.1.2))
        (fun p => f p.1.1) ≤
      sourceAdversary (sourceAlphabetDelta (booleanInput (n := m))) f *
        sourceAdversary (sourceAlphabetDelta inner) g) := by
  refine ⟨?_, ?_⟩
  · exact sourceFunctionComposition_lower inner g f
  · -- identify the inner rectangular value with `d_g = ADV±(g)` (Boolean `|E| = 2`)
    have hrect : sourceRectValue
        (gramFunctionEvaluationMatrix (fun x => sourceBooleanSymbol (g x)))
        (sourceAlphabetDelta inner) = sourceAdversary (sourceAlphabetDelta inner) g := by
      have hns := functionEvaluationNormSandwich X (Fin 2) n q inner
        (fun x => sourceBooleanSymbol (g x))
      dsimp only at hns
      obtain ⟨-, -, hle1, hle2⟩ := hns
      have hreal : 2 * (1 - 1 / ((Fintype.card (Fin 2)) : ℝ)) = 1 := by
        rw [Fintype.card_fin]; norm_num
      have hfac : ENNReal.ofReal (2 * (1 - 1 / ((Fintype.card (Fin 2)) : ℝ))) = 1 := by
        rw [hreal, ENNReal.ofReal_one]
      rw [hfac, one_mul] at hle2
      rw [le_antisymm hle2 hle1]
      exact (sourceAdversary_congr_output inner g (fun x => sourceBooleanSymbol (g x))
        (fun x y => ⟨fun hh => congrArg sourceBooleanSymbol hh,
          fun hh => sourceBooleanSymbol_injective hh⟩)).symm
    have hu := sourceFunctionComposition_upper (X := X) (Y := Fin m → Bool) (E := Bool)
      (inner := inner) (g := fun x : X => sourceBooleanSymbol (g x))
      (outer := booleanInput (n := m)) (f := f) hnd
    dsimp only at hu
    rwa [hrect] at hu

end Qatlib.Papers.QAdversary11.PartialCompose.DualSolution
