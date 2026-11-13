/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointCore
import Qatlib.Papers.FixedPtSearch14.FixedPoint.YlcWordAuxiliary
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# Public fixed-point search words

This module exposes the phase tables and ordered matrix products for the fixed-point search
construction of [YoderLowChuang2014]. The public interface includes the chosen odd length,
access counts, success and failure amplitudes, and embedding into a selected ancillary fiber.

`phaseCompilation_surrogate` and `phaseCompilation_attain` provide dyadic phase approximations;
`publicLedger_complete` collects the exact resource identities.

## Main statements

* `publicWord`: The reversed product of the prescribed Grover iterates.
* `publicWord_unitary`: Unitarity for a marked mass in the unit interval.
* `publicLedger_complete`: Preparation, query, and phase-sequence counts.
* `publicWordFiber_corner`: Recovery of the word from its selected block corner.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix
open Qatlib.Papers.FixedPtSearch14.FixedPoint

/-- The Yoder–Low–Chuang phase `ylcAlpha L j gamma` at index `j`. -/
noncomputable def wordPhase (L j : ℕ) (gamma : ℝ) : ℝ := ylcAlpha L j gamma

/-- The list of `l` source phases for the odd length `2 * l + 1` and tolerance parameter
`delta`. -/
noncomputable def wordPhaseTable (l : ℕ) (delta : ℝ) : List ℝ :=
  (List.range l).map fun i => wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta)

/-- The list of target phases obtained by negating the source phases in reverse index order. -/
noncomputable def wordBetaTable (l : ℕ) (delta : ℝ) : List ℝ :=
  (List.range l).map fun i => -wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta)

/-- The interleaved list of source and target phases for the `l` Grover iterates. -/
noncomputable def wordPhaseSequence (l : ℕ) (delta : ℝ) : List ℝ :=
  (List.range l).flatMap fun i =>
    [wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta),
      -wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta)]

/-- The interleaved phase sequence has length `2 * l`. -/
theorem wordPhaseSequence_length (l : ℕ) (delta : ℝ) :
    (wordPhaseSequence l delta).length = 2 * l := by
  have h := wordPhaseList_length l (2 * l + 1) (ylcGamma (2 * l + 1) delta)
  simpa [wordPhaseSequence, wordPhase] using h

/-- The Grover iterate at index `i` with the paired phases prescribed by `l` and `delta`. -/
noncomputable def publicIterate (l : ℕ) (delta lam : ℝ) (i : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  groverIterate lam (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta))
    (-wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))

/-- The matrix product of the `l` prescribed Grover iterates, with later iterates acting on the
left. -/
noncomputable def publicWord (l : ℕ) (delta lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((List.range l).map (publicIterate l delta lam)).reverse.prod

/-- The list of prescribed Grover iterates in increasing index order. -/
noncomputable def publicIterateList (l : ℕ) (delta lam : ℝ) :
    List (Matrix (Fin 2) (Fin 2) ℂ) :=
  (List.range l).map (publicIterate l delta lam)

/-- The public word agrees with `ylcWordMatrix`. -/
theorem publicWord_eq (l : ℕ) (delta lam : ℝ) :
    publicWord l delta lam = ylcWordMatrix l delta lam := by
  rfl

/-- The public word is unitary when `lam` lies in the unit interval. -/
theorem publicWord_unitary (l : ℕ) (delta lam : ℝ) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicWord l delta lam ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [publicWord_eq]
  exact ylcWordMatrix_unitary l delta lam hl hl'

/-- The odd word length selected by `ylcLength` from the marked-mass bound and tolerance. -/
noncomputable def publicLength (lam0 delta : ℝ) : ℕ := ylcLength lam0 delta

/-- The number of paired iterates computed as `(publicLength lam0 delta - 1) / 2`. -/
noncomputable def publicIterateCount (lam0 delta : ℝ) : ℕ := (publicLength lam0 delta - 1) / 2

/-- The selected public length is odd when `0 < lam0 < 1`. -/
theorem publicLength_odd {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    Odd (publicLength lam0 delta) := by
  rw [publicLength]
  exact ylcLength_odd hl0 hl0'

/-- The selected public length is at least one when `0 < lam0 < 1`. -/
theorem publicLength_one_le {lam0 delta : ℝ} (hl0 : 0 < lam0) (hl0' : lam0 < 1) :
    1 ≤ publicLength lam0 delta := by
  rw [publicLength]
  exact ylcLength_one_le hl0 hl0'

/-- For `lam0 ≠ 1`, the public length is twice the natural ceiling of the specified
inverse-hyperbolic-cosine ratio, plus one. -/
theorem publicLength_eq (lam0 delta : ℝ) (h : lam0 ≠ 1) :
    publicLength lam0 delta =
      2 * Nat.ceil (Real.arcosh (1 / delta) /
        Real.arcosh (1 / Real.sqrt (1 - lam0))) + 1 := by
  rw [publicLength]
  exact ylcLength_eq lam0 delta h

/-- The query count `wordQueryCount l` assigned to a word of `l` paired iterates. -/
def publicQueryCost (l : ℕ) : ℕ := wordQueryCount l

/-- The preparation-access count `wordPreparationCount l` assigned to a word of `l` paired
iterates. -/
def publicPreparationCost (l : ℕ) : ℕ := wordPreparationCount l

/-- The sum of the public query and preparation-access counts. -/
def publicAccessCost (l : ℕ) : ℕ := publicQueryCost l + publicPreparationCost l

/-- A word of `l` paired iterates has public query cost `2 * l`. -/
theorem publicQueryCost_eq (l : ℕ) : publicQueryCost l = 2 * l := rfl

/-- A word of `l` paired iterates has public preparation cost `2 * l`. -/
theorem publicPreparationCost_eq (l : ℕ) : publicPreparationCost l = 2 * l := rfl

/-- The total public access cost is `4 * l`. -/
theorem publicAccessCost_eq (l : ℕ) : publicAccessCost l = 4 * l := by
  rw [publicAccessCost, publicQueryCost_eq, publicPreparationCost_eq]
  ring

/-- The preparation and query costs are both `2 * l`, the query cost plus one is `2 * l + 1`,
and the phase sequence has length `2 * l`. -/
theorem publicLedger_complete (l : ℕ) (delta : ℝ) :
    publicPreparationCost l = l + l ∧ publicQueryCost l = 2 * l ∧
      publicQueryCost l + 1 = 2 * l + 1 ∧
        (wordPhaseSequence l delta).length = 2 * l := by
  refine ⟨?_, rfl, rfl, ?_⟩
  rw [publicPreparationCost_eq]
  ring
  exact wordPhaseSequence_length l delta

/-- For every natural number `n`, one has `n + 1 ≤ 2 ^ n`. -/
private theorem two_pow_succ_le (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc n + 2 ≤ 2 * (n + 1) := by omega
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- The phase-compilation cost surrogate `2 * l * b` for `2 * l` phases at precision `b`. -/
def phaseCompileCost (l b : ℕ) : ℕ := 2 * l * b

/-- For positive precision `b`, every real phase is within `π / 2^b` of an integer multiple of
`2π / 2^b`. -/
theorem phaseCompilation_surrogate (b : ℕ) (hb : 0 < b) (theta : ℝ) :
    ∃ q : ℤ, |theta - (2 * Real.pi * (q : ℝ)) / (2:ℝ) ^ b| ≤ Real.pi / (2:ℝ) ^ b :=
  exists_dyadic_phase b hb theta

/-- Every real phase can be approximated to any positive tolerance by an integer multiple of `2π
/ 2^b` for some positive `b`. -/
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

/-- The target component of the state obtained by applying `publicWord` to `ampState lam`. -/
noncomputable def publicSuccessAmplitude (l : ℕ) (delta lam : ℝ) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner ylcTargetVec (publicWord l delta lam *ᵥ ampState lam)

/-- The failure component of the state obtained by applying `publicWord` to `ampState lam`. -/
noncomputable def publicFailureAmplitude (l : ℕ) (delta lam : ℝ) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner ylcFailVec (publicWord l delta lam *ᵥ ampState lam)

/-- The squared norm of the public success amplitude. -/
noncomputable def publicSuccessProb (l : ℕ) (delta lam : ℝ) : ℝ :=
  ‖publicSuccessAmplitude l delta lam‖ ^ 2

/-- The squared norm of the public failure amplitude. -/
noncomputable def publicFailureProb (l : ℕ) (delta lam : ℝ) : ℝ :=
  ‖publicFailureAmplitude l delta lam‖ ^ 2

/-- The output obtained by applying `conditionalOutput` along `ylcTargetVec` to the evolved
amplitude state. -/
noncomputable def publicConditionalOutput (l : ℕ) (delta lam : ℝ) : Qatlib.Foundations.PureStateMath.QState (Fin 2) :=
  conditionalOutput ylcTargetVec (publicWord l delta lam *ᵥ ampState lam)

/-- The conditional output equals the target vector scaled by the success amplitude divided by
its norm. -/
theorem publicConditionalOutput_onTargetRay (l : ℕ) (delta lam : ℝ) :
    publicConditionalOutput l delta lam =
      (publicSuccessAmplitude l delta lam / (‖publicSuccessAmplitude l delta lam‖ : ℂ)) •
        ylcTargetVec := by
  rfl

/-- The embedding of the public word into the ancillary fiber indexed by `j₀`. -/
noncomputable def publicWordFiber {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : Matrix (J × Fin 2) (J × Fin 2) ℂ :=
  Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀ (publicWord l delta lam)

/-- On a tensor state with ancillary basis vector `Ket j₀`, the fiber embedding applies the
public word to the second factor. -/
theorem publicWordFiber_apply {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) (ψ : Qatlib.Foundations.PureStateMath.QState (Fin 2)) :
    publicWordFiber j₀ l delta lam *ᵥ Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) ψ =
      Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (publicWord l delta lam *ᵥ ψ) := by
  show Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀
      (publicWord l delta lam) *ᵥ Qatlib.Foundations.PureStateMath.TensorState
      (Qatlib.Foundations.PureStateMath.Ket j₀) ψ = _
  exact Qatlib.Concepts.BlockEncoding.StateBlockEncoding.fiberEmbed_mulVec_tensorState_ket j₀
      (publicWord l delta lam) ψ

/-- Multiplying two public words embedded in the same fiber equals embedding their matrix
product. -/
theorem publicWordFiber_mul {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l₁ l₂ : ℕ) (delta lam : ℝ) :
    publicWordFiber j₀ l₁ delta lam * publicWordFiber j₀ l₂ delta lam =
      Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀ (publicWord l₁ delta lam * publicWord l₂ delta lam) := by
  show Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀
      (publicWord l₁ delta lam) * Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberEmbed j₀
      (publicWord l₂ delta lam) = _
  rw [Qatlib.Concepts.BlockEncoding.StateBlockEncoding.fiberEmbed_mul]

/-- The block corner at `j₀` of the embedded public word is the original public word. -/
theorem publicWordFiber_corner {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    Qatlib.Concepts.BlockEncoding.StateBlockEncoding.BlockCorner (publicWordFiber j₀ l delta lam) j₀ = publicWord l delta lam := by
  ext i i'
  rw [Qatlib.Concepts.BlockEncoding.StateBlockEncoding.blockCorner_apply, publicWordFiber,
      fiberEmbed_apply]
  simp

end Qatlib.Papers.FixedPtSearch14.FixedPoint
