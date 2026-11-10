/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.ShadowsDefs
import Qatlib.Concepts.AmplitudeSearch.Amplification.ExecutionDefs
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
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

noncomputable def fairBitMass (k : ℕ) : ℝ :=
  (Nat.pow 2 k : ℝ)

theorem fairBitMass_pos (k : ℕ) : 0 < fairBitMass k := by
  show 0 < (Nat.pow 2 k : ℝ)
  exact_mod_cast (show (0 : ℕ) < Nat.pow 2 k from Nat.pow_pos (by norm_num))

theorem fairBitCount_cast (k : ℕ) :
    ((Finset.univ : Finset (Fin (2 ^ k))).card : ℝ) = fairBitMass k := by
  rw [Finset.card_univ, Fintype.card_fin]
  rfl

noncomputable def fairBitProb (k : ℕ) : ℝ :=
  (fairBitMass k)⁻¹

structure MemberSampler where

  size : ℕ

  fairBits : ℕ

  size_pos : 0 < size

  size_le : size ≤ 2 ^ fairBits

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

noncomputable def memberBitString (S : MemberSampler) (i : Fin S.size) :
    Fin (2 ^ S.fairBits) :=
  ⟨i.val, lt_of_lt_of_le i.isLt S.size_le⟩

noncomputable def memberDecode (S : MemberSampler) (j : Fin (2 ^ S.fairBits)) :
    Option (Fin S.size) :=
  if h : j.val < S.size then some ⟨j.val, h⟩ else none

noncomputable def acceptedMemberProb (S : MemberSampler) (i : Fin S.size) : ℝ :=
  (fairBitLaw S.fairBits).prob (memberBitString S i)

noncomputable def acceptanceMass (S : MemberSampler) : ℝ :=
  (S.size : ℝ) * (fairBitMass S.fairBits)⁻¹

noncomputable def rejectionTail (S : MemberSampler) : ℝ :=
  1 - acceptanceMass S

noncomputable def signPoint {d : ℕ} (hd : 0 < d) (s : Fin d → Bool) : QState (Fin d) :=
  fun i => if s i then 1 / Real.sqrt d else -1 / Real.sqrt d

noncomputable def signPackingSep (d : ℕ) : ℝ :=
  2 / Real.sqrt d

noncomputable def quantSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

noncomputable def roundedDyadic (k : ℕ) (x : ℝ) : ℝ :=
  quantSign x * ((Nat.floor (fairBitMass k * |x|) : ℕ) : ℝ) / fairBitMass k

noncomputable def roundedDyadicComplex (k : ℕ) (z : ℂ) : ℂ :=
  roundedDyadic k z.re + (roundedDyadic k z.im) * Complex.I

structure MemberCost where

  fairBits : ℕ

  gateCount : ℕ

  peakQubits : ℕ

end Qatlib.Papers.ClassShadows20.MainTheorem
