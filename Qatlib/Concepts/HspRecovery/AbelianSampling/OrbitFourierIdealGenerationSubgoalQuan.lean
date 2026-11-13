/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierIdealGenerationSubgoalStat
import Qatlib.Concepts.HspRecovery.AbelianSampling.AbelianStabilizerGenerationSubgoalQuan

/-!
# Generation of the dual group from ideal Fourier samples

`orbitFourierIdealGenerationSubgoal` proves that ideal character samples are uniform and
generate the full character group with failure probability at most `1 / 3`. The proof transports
the character distribution to its additive type synonym and applies the stabilizer generation
bound to `n + 4` samples when the original group has size at most `2 ^ n`. [Kitaev1995]

## Main statements

* `orbitFourierIdealGenerationSubgoal`: establishes uniform character probabilities and the dual
  group generation bound.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open scoped Classical BigOperators

variable (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]

/-- The Fourier Born distribution transported to the additive type synonym of the complex
character group. -/
private noncomputable def additiveBornDist : FinDist (Additive (AddChar E ℂ)) where
  prob x := (fourierBornDist E).prob (Additive.toMul x)
  nonneg x := (fourierBornDist E).nonneg _
  sum_one := by
    show ∑ x : Additive (AddChar E ℂ), (fourierBornDist E).prob (Additive.toMul x) = 1
    rw [Equiv.sum_comp Additive.toMul (fourierBornDist E).prob]
    exact (fourierBornDist E).sum_one

/-- Every element of the additive character type has probability equal to the reciprocal of the
original group cardinality. -/
private theorem additiveBornDist_prob (x : Additive (AddChar E ℂ)) :
    (additiveBornDist E).prob x = (Fintype.card E : ℝ)⁻¹ :=
  fourierBornDist_apply E _

omit [DecidableEq E] in

/-- The full additive character subgroup has the same cardinality as the original finite abelian
group. -/
private theorem card_top_additive_addChar :
    Fintype.card ↥(⊤ : AddSubgroup (Additive (AddChar E ℂ))) = Fintype.card E := by
  have h1 : Fintype.card ↥(⊤ : AddSubgroup (Additive (AddChar E ℂ))) =
      Fintype.card (Additive (AddChar E ℂ)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, AddSubgroup.card_top]
  rw [h1, Fintype.card_congr Additive.toMul, AddChar.card_eq]

omit [Fintype E] [DecidableEq E] in

/-- A family generates the multiplicative character group exactly when its additive type synonym
generates the full additive group. -/
private theorem closure_top_iff_closure_top {L : ℕ}
    (ω : Fin L → Additive (AddChar E ℂ)) :
    Subgroup.closure (Set.range (Additive.toMul ∘ ω)) = ⊤ ↔
      AddSubgroup.closure (Set.range ω) = ⊤ := by
  constructor
  · intro h
    rw [AddSubgroup.eq_top_iff']
    intro x
    have key : ∀ y : AddChar E ℂ,
        y ∈ Subgroup.closure (Set.range (Additive.toMul ∘ ω)) →
          Additive.ofMul y ∈ AddSubgroup.closure (Set.range ω) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          exact AddSubgroup.subset_closure ⟨i, rfl⟩
      | one => exact AddSubgroup.zero_mem _
      | mul a b _ _ iha ihb => exact AddSubgroup.add_mem _ iha ihb
      | inv a _ iha => exact AddSubgroup.neg_mem _ iha
    exact key (Additive.toMul x) (by rw [h]; trivial)
  · intro h
    rw [Subgroup.eq_top_iff']
    intro y
    have key : ∀ x : Additive (AddChar E ℂ),
        x ∈ AddSubgroup.closure (Set.range ω) →
          Additive.toMul x ∈ Subgroup.closure (Set.range (Additive.toMul ∘ ω)) := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem z hz =>
          obtain ⟨i, rfl⟩ := hz
          exact Subgroup.subset_closure ⟨i, rfl⟩
      | zero => exact Subgroup.one_mem _
      | add a b _ _ iha ihb => exact Subgroup.mul_mem _ iha ihb
      | neg a _ iha => exact Subgroup.inv_mem _ iha
    exact key (Additive.ofMul y) (by rw [h]; trivial)

/-- The probability of failure to generate the character group is preserved when the Fourier
Born distribution and samples are transported to the additive character type. -/
private theorem probEvent_transport (L : ℕ) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := L) (fourierBornDist E)
        (fun hs => Subgroup.closure (Set.range hs) ≠ ⊤)
      = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := L) (additiveBornDist E)
        (fun ω => AddSubgroup.closure (Set.range ω) ≠ ⊤) := by
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.refl (Fin L)) (Additive.toMul)) _ _ fun ω => ?_
  have hf : ((Equiv.refl (Fin L)).arrowCongr Additive.toMul) ω = Additive.toMul ∘ ω := rfl
  rw [hf]
  by_cases h : AddSubgroup.closure (Set.range ω) = ⊤
  · rw [if_neg (not_not_intro h),
      if_neg (not_not_intro ((closure_top_iff_closure_top E ω).mpr h))]
  · rw [if_pos h, if_pos ((closure_top_iff_closure_top E ω).not.mpr h)]
    rfl

/-- For a finite abelian group of size at most `2 ^ n` with `n > 0`, ideal Fourier samples are
uniform on its characters, and `n + 4` independent samples fail to generate the full
character group with probability at most `1 / 3` [Kitaev1995]. -/
theorem orbitFourierIdealGenerationSubgoal : OrbitFourierIdealGenerationSubgoal := by
  intro n hn E _ _ _ hcard
  refine ⟨fourierBornDist_apply E, ?_⟩
  have htop : Fintype.card ↥(⊤ : AddSubgroup (Additive (AddChar E ℂ))) ≤ 2 ^ n := by
    rw [card_top_additive_addChar E]
    exact hcard
  have hnear : ∀ L : Finset ↥(⊤ : AddSubgroup (Additive (AddChar E ℂ))),
      |(∑ g ∈ L, (additiveBornDist E).prob (g : Additive (AddChar E ℂ))) -
          (L.card : ℝ) / (Fintype.card ↥(⊤ : AddSubgroup (Additive (AddChar E ℂ))) : ℝ)|
        ≤ 1 / ((6 : ℝ) * ↑(1 : ℕ) * ↑(n + 4)) := by
    intro L
    have hprob : ∀ g ∈ L, (additiveBornDist E).prob (g : Additive (AddChar E ℂ)) =
        (Fintype.card E : ℝ)⁻¹ := fun g _ => additiveBornDist_prob E _
    rw [Finset.sum_congr rfl hprob, Finset.sum_const, nsmul_eq_mul,
      card_top_additive_addChar E, div_eq_mul_inv, sub_self, abs_zero]
    positivity
  have hgen := abelianStabilizerGenerationSubgoal (n := n) (k := 1)
    (G := Additive (AddChar E ℂ)) (H := ⊤) (μ := additiveBornDist E)
    hn (by norm_num) htop hnear
  rwa [probEvent_transport E (n + 4)]

end Qatlib.Concepts.HspRecovery.AbelianSampling
