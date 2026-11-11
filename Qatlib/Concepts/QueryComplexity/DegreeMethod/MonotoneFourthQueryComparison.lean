/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DecisionTrees.Lemma53DetCertificateBlockBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MonotoneCertificateSensitivity
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.BooleanQueryMinimumBounds

/-!
# Fourth-power query comparisons for monotone functions

The deterministic query complexity of a Boolean function is bounded by the product of its
one-certificate complexity and block sensitivity. For monotone functions this gives a square
bound in block sensitivity and the explicit comparison `deterministicQueryComplexity f ≤ 256 *
boundedMinimum f ^ 4`.

The mathematical background is developed in [BealsEtAl2001].

## Main statements

* `deterministicQueryComplexity_le_oneCertificate_mul_blockSensitivity`: gives the
  certificate-times-sensitivity bound.
* `monotone_deterministicQueryComplexity_le_256_boundedMinimum_pow_four`: gives the fourth-power
  comparison.
* `frontier1`: collects the monotone certificate and query bounds.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.MonotoneFourthQueryComparison

open Qatlib
open Qatlib
open Qatlib.Concepts.QueryComplexity.DecisionTrees
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open scoped Classical

/-- The deterministic query complexity of a Boolean function is at most its one-certificate
complexity times its block sensitivity. -/
theorem deterministicQueryComplexity_le_oneCertificate_mul_blockSensitivity {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    deterministicQueryComplexity f ≤ oneCertificateComplexity f * blockSensitivity f := by
  obtain ⟨t, ht, hb⟩ := lemma53DeterministicCertificateBlock n f
  calc
    deterministicQueryComplexity f ≤ t.MaxQueries := by
      apply Nat.sInf_le
      exact Set.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩
    _ ≤ oneCertificateComplexity f * blockSensitivity f := hb

/-- The deterministic query complexity of a monotone Boolean function is at most the square of
its block sensitivity. -/
theorem monotone_deterministicQueryComplexity_le_blockSensitivity_sq {n : ℕ}
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) →
      f x = true → f y = true) :
    deterministicQueryComplexity f ≤ blockSensitivity f ^ 2 := by
  calc
    deterministicQueryComplexity f ≤ oneCertificateComplexity f * blockSensitivity f :=
      deterministicQueryComplexity_le_oneCertificate_mul_blockSensitivity f
    _ ≤ blockSensitivity f * blockSensitivity f :=
      Nat.mul_le_mul_right _ (monotone_oneCertificate_le_blockSensitivity hmono)
    _ = blockSensitivity f ^ 2 := by ring

/-- For a monotone Boolean function, deterministic query complexity is at most `256 *
boundedMinimum f ^ 4`. -/
theorem monotone_deterministicQueryComplexity_le_256_boundedMinimum_pow_four {n : ℕ}
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) →
      f x = true → f y = true) :
    deterministicQueryComplexity f ≤ 256 * boundedMinimum f ^ 4 := by
  have hb : blockSensitivity f ≤ 16 * boundedMinimum f ^ 2 := (frontier3 f).2.1
  calc
    deterministicQueryComplexity f ≤ blockSensitivity f ^ 2 :=
      monotone_deterministicQueryComplexity_le_blockSensitivity_sq f hmono
    _ ≤ (16 * boundedMinimum f ^ 2) ^ 2 := Nat.pow_le_pow_left hb 2
    _ = 256 * boundedMinimum f ^ 4 := by ring

/-- A monotone Boolean function has one-certificate complexity at most its block sensitivity and
deterministic query complexity at most `256 * boundedMinimum f ^ 4`. This gives the stated
monotone fourth-power comparison associated with [BealsEtAl2001]. -/
theorem frontier1 {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) →
      f x = true → f y = true) :
    oneCertificateComplexity f ≤ blockSensitivity f ∧
      deterministicQueryComplexity f ≤ 256 * boundedMinimum f ^ 4 :=
  ⟨monotone_oneCertificate_le_blockSensitivity hmono,
    monotone_deterministicQueryComplexity_le_256_boundedMinimum_pow_four f hmono⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod.MonotoneFourthQueryComparison
