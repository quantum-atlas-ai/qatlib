/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointCore
import Qatlib.Papers.FixedPtSearch14.FixedPoint.YlcWordAuxiliary
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix
open Qatlib.Papers.FixedPtSearch14.FixedPoint

noncomputable def wordPhase (L j : ℕ) (gamma : ℝ) : ℝ := ylcAlpha L j gamma

noncomputable def wordPhaseTable (l : ℕ) (delta : ℝ) : List ℝ :=
  (List.range l).map fun i => wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta)

noncomputable def wordBetaTable (l : ℕ) (delta : ℝ) : List ℝ :=
  (List.range l).map fun i => -wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta)

noncomputable def wordPhaseSequence (l : ℕ) (delta : ℝ) : List ℝ :=
  (List.range l).flatMap fun i =>
    [wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta),
      -wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta)]

theorem wordPhaseSequence_length (l : ℕ) (delta : ℝ) :
    (wordPhaseSequence l delta).length = 2 * l := by
  have h := wordPhaseList_length l (2 * l + 1) (ylcGamma (2 * l + 1) delta)
  simpa [wordPhaseSequence, wordPhase] using h

noncomputable def publicIterate (l : ℕ) (delta lam : ℝ) (i : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  groverIterate lam (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta))
    (-wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))

noncomputable def publicWord (l : ℕ) (delta lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((List.range l).map (publicIterate l delta lam)).reverse.prod

noncomputable def publicIterateList (l : ℕ) (delta lam : ℝ) :
    List (Matrix (Fin 2) (Fin 2) ℂ) :=
  (List.range l).map (publicIterate l delta lam)

theorem publicWord_eq (l : ℕ) (delta lam : ℝ) :
    publicWord l delta lam = ylcWordMatrix l delta lam := by
  rfl

theorem publicWord_unitary (l : ℕ) (delta lam : ℝ) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicWord l delta lam ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [publicWord_eq]
  exact ylcWordMatrix_unitary l delta lam hl hl'

noncomputable def publicLength (lam0 delta : ℝ) : ℕ := ylcLength lam0 delta

noncomputable def publicIterateCount (lam0 delta : ℝ) : ℕ := (publicLength lam0 delta - 1) / 2

theorem publicLength_odd {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    Odd (publicLength lam0 delta) := by
  rw [publicLength]
  exact ylcLength_odd hl0 hl0'

theorem publicLength_one_le {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    1 ≤ publicLength lam0 delta := by
  rw [publicLength]
  exact ylcLength_one_le hl0 hl0'

theorem publicLength_eq (lam0 delta : ℝ) (h : lam0 ≠ 1) :
    publicLength lam0 delta =
      2 * Nat.ceil (Real.arcosh (1 / delta) /
        Real.arcosh (1 / Real.sqrt (1 - lam0))) + 1 := by
  rw [publicLength]
  exact ylcLength_eq lam0 delta h

def publicQueryCost (l : ℕ) : ℕ := wordQueryCount l

def publicPreparationCost (l : ℕ) : ℕ := wordPreparationCount l

def publicAccessCost (l : ℕ) : ℕ := publicQueryCost l + publicPreparationCost l

theorem publicQueryCost_eq (l : ℕ) : publicQueryCost l = 2 * l := rfl

theorem publicPreparationCost_eq (l : ℕ) : publicPreparationCost l = 2 * l := rfl

theorem publicAccessCost_eq (l : ℕ) : publicAccessCost l = 4 * l := by
  rw [publicAccessCost, publicQueryCost_eq, publicPreparationCost_eq]
  ring

theorem publicLedger_complete (l : ℕ) (delta : ℝ) :
    publicPreparationCost l = l + l ∧ publicQueryCost l = 2 * l ∧
      publicQueryCost l + 1 = 2 * l + 1 ∧
        (wordPhaseSequence l delta).length = 2 * l := by
  refine ⟨?_, rfl, rfl, ?_⟩
  rw [publicPreparationCost_eq]
  ring
  exact wordPhaseSequence_length l delta

private theorem two_pow_succ_le (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc n + 2 ≤ 2 * (n + 1) := by omega
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

def phaseCompileCost (l b : ℕ) : ℕ := 2 * l * b

theorem phaseCompilation_surrogate (b : ℕ) (hb : 0 < b) (theta : ℝ) :
    ∃ q : ℤ, |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ Real.pi / (2:ℝ) ^ b :=
  exists_dyadic_phase b hb theta

theorem phaseCompilation_attain (theta : ℝ) (eps : ℝ) (epspos : 0 < eps) :
    ∃ b : ℕ, 0 < b ∧ ∃ q : ℤ,
      |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ eps := by
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos epspos hpi)
  have hmesh : Real.pi / (2:ℝ) ^ (n + 1) < eps := by
    have h1 : Real.pi / (2:ℝ) ^ (n + 1) ≤ Real.pi / (n + 1 : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < (2:ℝ) ^ (n + 1))]
      have h2 : (n + 1 : ℝ) ≤ (2:ℝ) ^ (n + 1) := by
        have h := two_pow_succ_le n
        have h' : n + 1 ≤ 2 ^ (n + 1) := by
          have h'' : 2 ^ n ≤ 2 ^ (n + 1) := by
            rw [pow_succ]
            nlinarith
          exact le_trans h h''
        exact_mod_cast h'
      have h3 : Real.pi * (n + 1 : ℝ) ≤ Real.pi * (2:ℝ) ^ (n + 1) := by
        nlinarith [h2]
      have h4 : Real.pi ≤ (Real.pi / (n + 1 : ℝ)) * (2:ℝ) ^ (n + 1) := by
        field_simp
        nlinarith [h3]
      nlinarith [h4]
    have h2 : Real.pi / (n + 1 : ℝ) < eps := by
      have h5 : Real.pi * (1 / (n + 1 : ℝ)) < Real.pi * (eps / Real.pi) :=
        mul_lt_mul_of_pos_left hn hpi
      have h6 : Real.pi / (n + 1 : ℝ) = Real.pi * (1 / (n + 1 : ℝ)) := by ring
      have h7 : Real.pi * (eps / Real.pi) = eps := by field_simp
      rwa [← h6, h7] at h5
    exact h1.trans_lt h2
  obtain ⟨q, hq⟩ := exists_dyadic_phase (n + 1) (by omega) theta
  exact ⟨n + 1, by omega, q, hq.trans (le_of_lt hmesh)⟩

noncomputable def publicSuccessAmplitude (l : ℕ) (delta lam : ℝ) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner ylcTargetVec (publicWord l delta lam *ᵥ ampState lam)

noncomputable def publicFailureAmplitude (l : ℕ) (delta lam : ℝ) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner ylcFailVec (publicWord l delta lam *ᵥ ampState lam)

noncomputable def publicSuccessProb (l : ℕ) (delta lam : ℝ) : ℝ :=
  ‖publicSuccessAmplitude l delta lam‖ ^ 2

noncomputable def publicFailureProb (l : ℕ) (delta lam : ℝ) : ℝ :=
  ‖publicFailureAmplitude l delta lam‖ ^ 2

noncomputable def publicConditionalOutput (l : ℕ) (delta lam : ℝ) : Qatlib.Foundations.PureStateMath.QState (Fin 2) :=
  conditionalOutput ylcTargetVec (publicWord l delta lam *ᵥ ampState lam)

theorem publicConditionalOutput_onTargetRay (l : ℕ) (delta lam : ℝ) :
    publicConditionalOutput l delta lam =
      (publicSuccessAmplitude l delta lam / (‖publicSuccessAmplitude l delta lam‖ : ℂ)) •
        ylcTargetVec := by
  rfl

noncomputable def publicWordFiber {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : Matrix (J × Fin 2) (J × Fin 2) ℂ :=
  Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀ (publicWord l delta lam)

theorem publicWordFiber_apply {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) (ψ : Qatlib.Foundations.PureStateMath.QState (Fin 2)) :
    publicWordFiber j₀ l delta lam *ᵥ Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) ψ =
      Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (publicWord l delta lam *ᵥ ψ) := by
  show Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀
      (publicWord l delta lam) *ᵥ Qatlib.Foundations.PureStateMath.TensorState
      (Qatlib.Foundations.PureStateMath.Ket j₀) ψ = _
  exact Qatlib.Concepts.BlockEncoding.StateBlockEncoding.fiberEmbed_mulVec_tensorState_ket j₀
      (publicWord l delta lam) ψ

theorem publicWordFiber_mul {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l₁ l₂ : ℕ) (delta lam : ℝ) :
    publicWordFiber j₀ l₁ delta lam * publicWordFiber j₀ l₂ delta lam =
      Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀ (publicWord l₁ delta lam * publicWord l₂ delta lam) := by
  show Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀
      (publicWord l₁ delta lam) * Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀
      (publicWord l₂ delta lam) = _
  rw [Qatlib.Concepts.BlockEncoding.StateBlockEncoding.fiberEmbed_mul]

theorem publicWordFiber_corner {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    Qatlib.Concepts.BlockEncoding.StateBlockEncoding.BlockCorner (publicWordFiber j₀ l delta lam) j₀ = publicWord l delta lam := by
  ext i i'
  rw [Qatlib.Concepts.BlockEncoding.StateBlockEncoding.blockCorner_apply, publicWordFiber,
      fiberEmbed_apply]
  simp

end Qatlib.Papers.FixedPtSearch14.FixedPoint
