/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-! # Global character coefficients for implicit source moments

The source side of the half-support far expansion can be represented by
global character coefficients.  The finite-subset recurrence below is an
algebraic interface for an elementary-symmetric dynamic program; it does not
claim a target-side interval evaluator or a complete DCP algorithm.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteCounts.SubsetMoments
open scoped BigOperators Classical

/-- The sum of products of weights over the subsets of a prescribed cardinality. -/
def weightedSubsetSum {α R : Type*} [CommSemiring R]
    (s : Finset α) (k : ℕ) (a : α → R) : R :=
  ∑ T ∈ s.powersetCard k, ∏ i ∈ T, a i

/-- Inserting a fresh element splits the weighted subset sum into the subsets omitting and containing it. -/
theorem weightedSubsetSum_succ_insert {α R : Type*} [DecidableEq α] [CommSemiring R]
    {s : Finset α} {x : α} (hx : x ∉ s) (k : ℕ) (a : α → R) :
    weightedSubsetSum (insert x s) (k + 1) a =
      weightedSubsetSum s (k + 1) a + a x * weightedSubsetSum s k a := by
  unfold weightedSubsetSum
  rw [Finset.powersetCard_succ_insert hx k, Finset.sum_union]
  · rw [Finset.sum_image]
    · have hprod : ∀ t ∈ Finset.powersetCard k s,
          (∏ i ∈ insert x t, a i) = a x * ∏ i ∈ t, a i := by
        intro t ht
        have hxt : x ∉ t := by
          intro h
          exact hx ((Finset.mem_powersetCard.mp ht).1 h)
        rw [Finset.prod_insert hxt]
      have hsum : (∑ t ∈ Finset.powersetCard k s, ∏ i ∈ insert x t, a i) =
          ∑ t ∈ Finset.powersetCard k s, a x * ∏ i ∈ t, a i := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hprod t ht
      rw [hsum, ← Finset.mul_sum]
    · intro t ht u hu htu
      have hxt : x ∉ t := by
        intro h
        exact hx ((Finset.mem_powersetCard.mp ht).1 h)
      have hxu : x ∉ u := by
        intro h
        exact hx ((Finset.mem_powersetCard.mp hu).1 h)
      apply Finset.ext
      intro z
      by_cases hz : z = x
      · simp [hz, hxt, hxu]
      · simpa [hz] using Finset.ext_iff.mp htu z
  · rw [Finset.disjoint_left]
    intro t ht hti
    rcases Finset.mem_image.mp hti with ⟨u, hu, htu⟩
    have hsub := (Finset.mem_powersetCard.mp ht).1
    have hxt : x ∈ t := by rw [← htu]; simp
    exact hx (hsub hxt)

/-- The weighted coefficient of a residue among fixed-cardinality subset sums. -/
def sourceResidueCoefficient {m N : ℕ} (labels : Fin m → ZMod N)
    (phases : Fin m → ℂ) (degree : ℕ) (y : ZMod N) : ℂ :=
  ∑ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
    if (∑ i ∈ S, labels i) = y then ∏ i ∈ S, phases i else 0

/-- The additive-character moment of weighted fixed-cardinality subset sums. -/
def sourceCharacterSum {m N : ℕ} [NeZero N] (labels : Fin m → ZMod N)
    (phases : Fin m → ℂ) (degree frequency : ℕ) : ℂ :=
  ∑ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
    (∏ i ∈ S, phases i) *
      ZMod.stdAddChar ((frequency : ZMod N) * ∑ i ∈ S, labels i)

/-- Taking the Fourier coefficient of the residue table gives its subset-character moment. -/
theorem source_character_sum_eq {m N : ℕ} [NeZero N]
    (labels : Fin m → ZMod N) (phases : Fin m → ℂ)
    (degree frequency : ℕ) :
    (∑ y : ZMod N, sourceResidueCoefficient labels phases degree y *
      ZMod.stdAddChar ((frequency : ZMod N) * y)) =
      sourceCharacterSum labels phases degree frequency := by
  unfold sourceResidueCoefficient sourceCharacterSum
  calc
    (∑ y : ZMod N,
      (∑ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
        if (∑ i ∈ S, labels i) = y then ∏ i ∈ S, phases i else 0) *
        ZMod.stdAddChar ((frequency : ZMod N) * y)) =
      ∑ y : ZMod N, ∑ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
        (if (∑ i ∈ S, labels i) = y then ∏ i ∈ S, phases i else 0) *
          ZMod.stdAddChar ((frequency : ZMod N) * y) := by
        apply Fintype.sum_congr
        intro y
        rw [Finset.sum_mul]
    _ = ∑ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
        ∑ y : ZMod N,
          (if (∑ i ∈ S, labels i) = y then ∏ i ∈ S, phases i else 0) *
            ZMod.stdAddChar ((frequency : ZMod N) * y) := by
        rw [Finset.sum_comm]
    _ = ∑ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
        (∏ i ∈ S, phases i) *
          ZMod.stdAddChar ((frequency : ZMod N) * ∑ i ∈ S, labels i) := by
        apply Finset.sum_congr rfl
        intro S hS
        simp [Finset.mem_univ]

/-- A subset-character moment is the elementary symmetric sum of character-weighted entries. -/
theorem sourceCharacterSum_eq_weightedSubsetSum {m N : ℕ} [NeZero N]
    (labels : Fin m → ZMod N) (phases : Fin m → ℂ)
    (degree frequency : ℕ) :
    sourceCharacterSum labels phases degree frequency =
      weightedSubsetSum (Finset.univ : Finset (Fin m)) degree
        (fun i => phases i * ZMod.stdAddChar ((frequency : ZMod N) * labels i)) := by
  unfold sourceCharacterSum weightedSubsetSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_mul_distrib]
  have hchar : (∏ i ∈ S, ZMod.stdAddChar ((frequency : ZMod N) * labels i)) =
      ZMod.stdAddChar ((frequency : ZMod N) * ∑ i ∈ S, labels i) := by
    clear hS
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_add,
        AddChar.map_add_eq_mul, ih]
  rw [hchar]

end Qatlib.Foundations.FiniteCounts.SubsetMoments
