/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.ShadowsDefs
import Qatlib.Concepts.AmplitudeSearch.Amplification.ExecutionDefs
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Finite-member sampling definitions

`MemberSampler` records a positive finite member count that fits within a prescribed number of
fair bits. The module defines the uniform bit law, member encoding and rejection decoding, and
scalar acceptance and rejection masses. It also defines signed coordinate states, separation
parameters, dyadic approximation, and resource data.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `memberDecode`: accepts bit indices below the member count.
* `acceptanceMass`: gives the accepted fraction of bit strings.
* `roundedDyadic`: truncates the magnitude to the dyadic grid and restores its sign.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.ClassShadows20.LowerBound
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.ClassShadows20.MainTheorem

open Matrix
open scoped Classical BigOperators ComplexOrder

variable {n : ℕ}

/-- The number `2^k` of `k`-bit strings, cast to the reals. -/
noncomputable def fairBitMass (k : ℕ) : ℝ :=
  (Nat.pow 2 k : ℝ)

/-- The real-valued count `fairBitMass k` is strictly positive. -/
theorem fairBitMass_pos (k : ℕ) : 0 < fairBitMass k := by
  show 0 < (Nat.pow 2 k : ℝ)
  exact_mod_cast (show (0 : ℕ) < Nat.pow 2 k from Nat.pow_pos (by norm_num))

/-- The real cardinality of `Fin (2^k)` equals `fairBitMass k`. -/
theorem fairBitCount_cast (k : ℕ) :
    ((Finset.univ : Finset (Fin (2 ^ k))).card : ℝ) = fairBitMass k := by
  rw [Finset.card_univ, Fintype.card_fin]
  rfl

/-- The reciprocal of the real-valued count of `k`-bit strings. -/
noncomputable def fairBitProb (k : ℕ) : ℝ :=
  (fairBitMass k)⁻¹

/-- A positive member count and a fair-bit count, with a proof that the members fit within the
available bit strings. -/
structure MemberSampler where

  size : ℕ

  fairBits : ℕ

  size_pos : 0 < size

  size_le : size ≤ 2 ^ fairBits

/-- The uniform finite distribution on the `2^k` possible `k`-bit indices. -/
noncomputable def fairBitLaw (k : ℕ) : FinDist (Fin (2 ^ k)) where
  prob j := fairBitProb k
  nonneg j := by
    show 0 ≤ fairBitProb k
    have h : 0 < fairBitMass k := fairBitMass_pos k
    unfold fairBitProb
    exact inv_nonneg.mpr (le_of_lt h)
  sum_one := by
    classical
    calc (∑ j : Fin (2 ^ k), fairBitProb k)
        = ((Finset.univ : Finset (Fin (2 ^ k))).card : ℝ) * fairBitProb k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = fairBitMass k * fairBitProb k := by
          rw [fairBitCount_cast]
      _ = 1 := by
          show fairBitMass k * fairBitProb k = 1
          unfold fairBitProb
          rw [mul_inv_cancel₀]
          exact ne_of_gt (fairBitMass_pos k)

/-- Encodes a member index as the bit-string index with the same natural value. -/
noncomputable def memberBitString (S : MemberSampler) (i : Fin S.size) :
    Fin (2 ^ S.fairBits) :=
  ⟨i.val, lt_of_lt_of_le i.isLt S.size_le⟩

/-- Returns the member with the given index when that index is below the member count, and
rejects it otherwise. -/
noncomputable def memberDecode (S : MemberSampler) (j : Fin (2 ^ S.fairBits)) :
    Option (Fin S.size) :=
  if h : j.val < S.size then some ⟨j.val, h⟩ else none

/-- The fair-bit probability of the bit-string encoding of a specified member. -/
noncomputable def acceptedMemberProb (S : MemberSampler) (i : Fin S.size) : ℝ :=
  (fairBitLaw S.fairBits).prob (memberBitString S i)

/-- The real member count divided by the number of available fair-bit strings. -/
noncomputable def acceptanceMass (S : MemberSampler) : ℝ :=
  (S.size : ℝ) * (fairBitMass S.fairBits)⁻¹

/-- One minus the sampler's acceptance mass. -/
noncomputable def rejectionTail (S : MemberSampler) : ℝ :=
  1 - acceptanceMass S

/-- The dimension-`d` state with coordinate `1 / sqrt d` for a true sign bit and `-1 / sqrt d`
otherwise. -/
noncomputable def signPoint {d : ℕ} (hd : 0 < d) (s : Fin d → Bool) : QState (Fin d) :=
  fun i => if s i then 1 / Real.sqrt d else -1 / Real.sqrt d

/-- The real separation parameter `2 / sqrt d`. -/
noncomputable def signPackingSep (d : ℕ) : ℝ :=
  2 / Real.sqrt d

/-- The real sign equal to one on nonnegative inputs and minus one on negative inputs. -/
noncomputable def quantSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

/-- The signed dyadic value obtained by flooring `2^k * |x|`, dividing by `2^k`, and restoring
the sign of `x`. -/
noncomputable def roundedDyadic (k : ℕ) (x : ℝ) : ℝ :=
  quantSign x * ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k

/-- The complex approximation obtained by applying signed dyadic rounding separately to the real
and imaginary parts. -/
noncomputable def roundedDyadicComplex (k : ℕ) (z : ℂ) : ℂ :=
  roundedDyadic k z.re + (roundedDyadic k z.im) * Complex.I

/-- A resource record containing the fair-bit count, gate count, and peak qubit count. -/
structure MemberCost where

  fairBits : ℕ

  gateCount : ℕ

  peakQubits : ℕ

end Qatlib.Papers.ClassShadows20.MainTheorem
