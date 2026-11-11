/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.GeneralAdversary

/-!
# Uniform Bounds for Adversary Composition

This module proves the upper side of the uniform-cost composition estimate from Corollary 14 of
[HoyerLeeSpalek2007]. For nonconstant outer and inner Boolean functions, a common finite upper
bound `b` on the inner `advValue` quantities bounds the composed value by `ENNReal.ofReal b`
times the outer value. The proof passes through `advAlphaENN` and `blockCosts`.

The lower estimate and the two-sided estimate are recorded separately as `corollary14LowerSpec`
and `corollary14SandwichSpec`, which define propositions rather than prove those estimates.

## Main statements

- `advAlphaENN_one_eq_advValue` identifies unit costs with the unweighted value.
* `advAlphaENN_mono` and `advAlphaENN_le_mul_advValue` compare weighted values with larger or
  uniformly bounded costs.
- `corollary14_upper` proves the upper composition estimate.
- `corollary14LowerSpec` and `corollary14SandwichSpec` formulate the remaining estimates.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Corollary 14.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Composition

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.DegreeMethod

noncomputable section

/-- The extended weighted nonnegative adversary value with every coordinate cost equal to one is
`advValue`. -/
theorem advAlphaENN_one_eq_advValue
    {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) :
    advAlphaENN input g (fun _ => 1) = advValue input g := by
  unfold advAlphaENN advValue advAlphaR advAlphaWitnessR
  congr 1
  funext Γ
  congr 1
  funext i
  simp only [ENNReal.ofReal_one, one_mul]

/-- Increasing every coordinate cost can only increase `advAlphaENN`. -/
theorem advAlphaENN_mono
    {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β β' : κ → ℝ≥0∞)
    (h : ∀ i, β i ≤ β' i) :
    advAlphaENN input g β ≤ advAlphaENN input g β' := by
  unfold advAlphaENN
  refine iSup_mono fun Γ => ?_
  refine iInf_mono fun i => ?_
  rw [mul_div_assoc, mul_div_assoc]
  gcongr
  exact h i

/-- If the coordinate type is nonempty and every extended cost is at most `ENNReal.ofReal b`,
the weighted value is at most `ENNReal.ofReal b` times `advValue`. -/
theorem advAlphaENN_le_mul_advValue
    {X κ : Type} [Fintype X] [DecidableEq X] [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (β : κ → ℝ≥0∞) (b : ℝ)
    (hκ : Nonempty κ) (hβ : ∀ i, β i ≤ ENNReal.ofReal b) :
    advAlphaENN input g β ≤ ENNReal.ofReal b * advValue input g := by
  haveI := hκ
  unfold advAlphaENN advValue advAlphaR advAlphaWitnessR
  refine iSup_le fun Γ => ?_
  have hstep : (⨅ i, β i * ENNReal.ofReal ‖Γ.1‖ /
        ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖) ≤
      ENNReal.ofReal b *
        (⨅ i, ENNReal.ofReal ((fun _ => (1 : ℝ)) i) * ENNReal.ofReal ‖Γ.1‖ /
          ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖) := by
    rw [ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_lt_top.ne)]
    refine iInf_mono fun i => ?_
    simp only [ENNReal.ofReal_one, one_mul]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (hβ i) zero_le
  refine hstep.trans ?_
  gcongr
  exact le_iSup (fun Γ : {Γ : Matrix X X ℝ // Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧
      (∀ x y, g x = g y → Γ x y = 0) ∧ Γ ≠ 0} =>
    ⨅ i, ENNReal.ofReal ((fun _ => (1 : ℝ)) i) * ENNReal.ofReal ‖Γ.1‖ /
      ENNReal.ofReal ‖genAdvFilter input Γ.1 i‖) Γ

/-- For nonconstant outer and inner functions, a common upper bound `b` on the inner adversary
values bounds the composed value by `ENNReal.ofReal b` times the outer value. This is the
upper estimate of Corollary 14 in [HoyerLeeSpalek2007]. -/
theorem corollary14_upper
    {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (b : ℝ)
    (hfn : ∃ u v : Fin k → Bool, f u ≠ f v)
    (hgn : ∀ i, ∃ a c : Y i, g i a ≠ g i c)
    (hhi : ∀ i, advValue (gin i) (g i) ≤ ENNReal.ofReal b) :
    advValue (composedInput gin) (composedFunction g f) ≤
      ENNReal.ofReal b * advValue (fun u : Fin k → Bool => u) f := by
  have hk0 : Nonempty (Fin k) := by
    obtain ⟨u, v, huv⟩ := hfn
    obtain ⟨a, _⟩ := Function.ne_iff.mp (fun h => huv (congrArg f h))
    exact ⟨a⟩
  haveI hk : Nonempty (Fin k) := hk0
  have hbc : ∀ i, blockCosts gin g (fun _ => (1 : ℝ)) i ≤ ENNReal.ofReal b := by
    intro i
    rw [blockCosts_eq_block_value]
    have h1 : (fun j : Fin (n i) => ENNReal.ofReal
          ((fun _ : ((i : Fin k) × Fin (n i)) => (1 : ℝ)) ⟨i, j⟩)) =
        (fun _ => (1 : ℝ≥0∞)) := by
      funext j
      simp
    rw [h1, advAlphaENN_one_eq_advValue]
    exact hhi i
  have hfin : ∀ i, blockCosts gin g (fun _ => (1 : ℝ)) i < ⊤ :=
    fun i => lt_of_le_of_lt (hbc i) ENNReal.ofReal_lt_top
  have hcomp := composition_upper_bound_on_source_scope gin g f (fun _ => (1 : ℝ))
    (fun _ => by norm_num) hfn hgn hfin
  simp only [ENNReal.ofReal_one] at hcomp
  rw [advAlphaENN_one_eq_advValue] at hcomp
  exact hcomp.trans (advAlphaENN_le_mul_advValue (fun u : Fin k → Bool => u) f
    (blockCosts gin g (fun _ => (1 : ℝ))) b hk hbc)

/-- Defines the proposition that a common lower bound `a` on all inner adversary values gives
the lower composition estimate `ENNReal.ofReal a` times the outer value, as in Corollary 14
of [HoyerLeeSpalek2007]. -/
def corollary14LowerSpec : Prop :=
  ∀ {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (a : ℝ)
    (_hlo : ∀ i, ENNReal.ofReal a ≤ advValue (gin i) (g i)),
    ENNReal.ofReal a * advValue (fun u : Fin k → Bool => u) f ≤
      advValue (composedInput gin) (composedFunction g f)

/-- Defines the two-sided composition estimate when every inner adversary value lies between `a`
and `b`, with `0 ≤ a ≤ b`. This is the sandwich statement of Corollary 14 in
[HoyerLeeSpalek2007]. -/
def corollary14SandwichSpec : Prop :=
  ∀ {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (gin : ∀ i, Y i → Fin (n i) → Bool) (g : ∀ i, Y i → Bool)
    (f : (Fin k → Bool) → Bool) (a b : ℝ),
    0 ≤ a → a ≤ b →
    (∀ i, ENNReal.ofReal a ≤ advValue (gin i) (g i)) →
    (∀ i, advValue (gin i) (g i) ≤ ENNReal.ofReal b) →
    ENNReal.ofReal a * advValue (fun u : Fin k → Bool => u) f ≤
        advValue (composedInput gin) (composedFunction g f) ∧
      advValue (composedInput gin) (composedFunction g f) ≤
        ENNReal.ofReal b * advValue (fun u : Fin k → Bool => u) f

end

end Qatlib.Concepts.SignedWeights.Representations.Composition
