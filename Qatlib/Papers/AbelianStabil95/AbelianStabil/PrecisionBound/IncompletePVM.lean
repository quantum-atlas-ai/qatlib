/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound.Lemmas3To5

/-!
# Completing an incomplete projective measurement

`completedEffect` adds a complementary outcome to a finite family of projections, and
`completedPOVM` packages the completed family as a finite POVM. The complement identities
support `lemma4_incomplete_orthogonal`, which bounds the total probability difference on the
original outcomes by the trace norm of the difference of density operators. The development
follows [Kitaev1995].

## Main statements

* `completedPOVM`: constructs a POVM including the complementary outcome.
* `lemma4_incomplete_orthogonal`: bounds the original-outcome probability differences by trace
  norm.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound

open scoped BigOperators
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {d : ℕ}

/-- The effects indexed by `Option Ω`, using `P i` at `some i` and `1 - ∑ i, P i` at `none`. -/
def completedEffect (P : Ω → Operator d) : Option Ω → Operator d
  | some i => P i
  | none => 1 - ∑ i, P i

/-- The finite POVM obtained by adding the complementary effect, assuming the original effects
and their complement are Hermitian idempotents. -/
def completedPOVM (P : Ω → Operator d)
    (hproj : ∀ i, P i * P i = P i)
    (hherm : ∀ i, Matrix.conjTranspose (P i) = P i)
    (hcompP : (1 - ∑ i, P i) * (1 - ∑ i, P i) = (1 - ∑ i, P i))
    (hcompH : Matrix.conjTranspose (1 - ∑ i, P i) = 1 - ∑ i, P i) :
    FinitePOVM (Option Ω) d where
  effect := completedEffect P
  effect_sum := by
    rw [Fintype.sum_option]
    simp only [completedEffect]
    abel
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  factor := completedEffect P
  effect_eq_factor := by
    intro o
    cases o with
    | some i =>
      simp only [completedEffect]
      rw [hherm i, hproj i]
      simp
    | none =>
      simp only [completedEffect]
      rw [hcompH, hcompP]
      simp

omit [DecidableEq Ω] in

/-- The complement of a finite sum of pairwise orthogonal idempotents is idempotent, as used in
[Kitaev1995]. -/
theorem complement_mul_self (P : Ω → Operator d)
    (hproj : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ i, P i) * (1 - ∑ i, P i) = 1 - ∑ i, P i := by
  have hSS : (∑ i, P i) * (∑ i, P i) = ∑ i, P i := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [hproj i]
    · intro j _ hji
      exact horth i j (fun h => hji h.symm)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hSS]
  abel

omit [DecidableEq Ω] in

/-- The complement of a finite sum of Hermitian matrices is Hermitian, as used in [Kitaev1995]. -/
theorem complement_conjTranspose (P : Ω → Operator d)
    (hherm : ∀ i, Matrix.conjTranspose (P i) = P i) :
    Matrix.conjTranspose (1 - ∑ i, P i) = 1 - ∑ i, P i := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_sum]
  simp [hherm]

/-- For a finite pairwise orthogonal family of Hermitian projections, the sum of absolute
probability differences on the original outcomes is at most the trace norm of the
density-operator difference. This is the incomplete-measurement form of [Kitaev, 1995, Lemma
4][Kitaev1995]. -/
theorem lemma4_incomplete_orthogonal
    (P : Ω → Operator d)
    (hproj : ∀ i, P i * P i = P i)
    (hherm : ∀ i, Matrix.conjTranspose (P i) = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (A B : Operator d) (hA : IsDensityOperator A) (hB : IsDensityOperator B) :
    (∑ i, |(povmRecordLaw (completedPOVM P hproj hherm
            (complement_mul_self P hproj horth)
            (complement_conjTranspose P hherm)) A hA).prob (some i) -
          (povmRecordLaw (completedPOVM P hproj hherm
            (complement_mul_self P hproj horth)
            (complement_conjTranspose P hherm)) B hB).prob (some i)|)
      ≤ Matrix.traceNorm (A - B) := by
  let E := completedPOVM P hproj hherm
    (complement_mul_self P hproj horth) (complement_conjTranspose P hherm)
  have hfull := lemma4_measurement_distance E A B hA hB
  let f : Option Ω → ℝ := fun o =>
    |(povmRecordLaw E A hA).prob o - (povmRecordLaw E B hB).prob o|
  have hsplit : (∑ o : Option Ω, f o) = f none + ∑ i, f (some i) := by
    rw [Fintype.sum_option]
  have hnonneg : 0 ≤ f none := abs_nonneg _
  have hle : (∑ i, f (some i)) ≤ ∑ o : Option Ω, f o := by
    rw [hsplit]
    linarith
  exact hle.trans hfull

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound
