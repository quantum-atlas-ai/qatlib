/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Risk Grid

Risk Partition constructions for Decision Risk.
Defines `riskCell`.
Proves `riskCell_measurable`, `riskCell_disjoint`, `riskCell_cover`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.DecisionRisk.RiskPartition
open MeasureTheory

/-- Cells are indexed by all possible finite three-label floor bins, including
empty cells. No posterior weights enter the partition. -/
def riskCell {Y : Type*} (K : ℕ) (c : Y → Fin 3 → ℝ)
    (b : Fin 3 → Fin (K+1)) : Set Y :=
  {y | ∀ i, ⌊(K:ℝ)*c y i⌋₊=(b i).val}

/-- The stated finite risk construction satisfies `riskCell_measurable` with all displayed hypotheses retained. -/
lemma riskCell_measurable {Y : Type*} [MeasurableSpace Y] (K : ℕ)
    (c : Y → Fin 3 → ℝ) (hc : ∀ i, Measurable (fun y => c y i))
    (b : Fin 3 → Fin (K+1)) : MeasurableSet (riskCell K c b) := by
  simp only [riskCell, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_singleton ((b i).val)).preimage
    (Nat.measurable_floor.comp (measurable_const.mul (hc i)))

/-- The stated finite risk construction satisfies `riskCell_disjoint` with all displayed hypotheses retained. -/
lemma riskCell_disjoint {Y : Type*} (K : ℕ) (c : Y → Fin 3 → ℝ) :
    Pairwise (fun a b => Disjoint (riskCell K c a) (riskCell K c b)) := by
  intro a b hab
  apply Set.disjoint_left.2
  intro y ha hb
  apply hab
  funext i
  apply Fin.ext
  exact (ha i).symm.trans (hb i)

/-- The stated finite risk construction satisfies `riskCell_cover` with all displayed hypotheses retained. -/
lemma riskCell_cover {Y : Type*} (K : ℕ) (c : Y → Fin 3 → ℝ)
    (hc : ∀ y i, c y i ≤ 1) : ⋃ b, riskCell K c b=Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  refine Set.mem_iUnion.2 ⟨(fun i => ⟨⌊(K:ℝ)*c y i⌋₊, ?_⟩), ?_⟩
  · apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    exact mul_le_of_le_one_right (Nat.cast_nonneg K) (hc y i)
  · intro i
    rfl

/-- Coordinate diameter, including boundary values zero and one. -/
lemma riskCell_diameter {Y : Type*} {K : ℕ} (hK : 0 < K)
    (c : Y → Fin 3 → ℝ) (hc : ∀ y i, 0 ≤ c y i)
    {b : Fin 3 → Fin (K+1)} {y z : Y}
    (hy : y ∈ riskCell K c b) (hz : z ∈ riskCell K c b) (i : Fin 3) :
    |c y i-c z i| ≤ 1/(K:ℝ) := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  have heq : ⌊(K:ℝ)*c y i⌋₊=⌊(K:ℝ)*c z i⌋₊ := (hy i).trans (hz i).symm
  have hy0 := Nat.floor_le (mul_nonneg hKR.le (hc y i))
  have hz0 := Nat.floor_le (mul_nonneg hKR.le (hc z i))
  have hy1 := Nat.lt_floor_add_one ((K:ℝ)*c y i)
  have hz1 := Nat.lt_floor_add_one ((K:ℝ)*c z i)
  rw [heq] at hy0 hy1
  have hp : |(c y i-c z i)*(K:ℝ)| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith only [hy0, hz1], by nlinarith only [hy1, hz0]⟩
  apply (le_div_iff₀ hKR).2
  simpa only [abs_mul, abs_of_pos hKR] using hp

end Qatlib.Foundations.DecisionRisk.RiskPartition
