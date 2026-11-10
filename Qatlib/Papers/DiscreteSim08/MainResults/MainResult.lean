/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.Defs
import Qatlib.Papers.DiscreteSim08.MainResults.Theorem1
import Qatlib.Papers.DiscreteSim08.MainResults.Budget
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiscreteSim08.MainResults

def sourceWordAchieves {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    {n q : ℕ} (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H)
    {r : ℕ} (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)) (f : ℝ) : Prop :=
  ∀ x, f ≤ (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re

theorem sourceCoherentQ_le_of_sourceWordAchieves {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) {ε : ℝ}
    {r : ℕ} (hr : 0 < r) (C : SourceWord (SourceSpace n q H r))
    (hlegal : sourceWordLegal C)
    (hach : sourceWordAchieves input ρ σ hr C (Real.sqrt (1 - ε))) :
    sourceCoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞) := by
  unfold sourceCoherentQ
  exact sInf_le ⟨r, hr, C, rfl, hlegal, hach⟩

theorem sourceKnownUnitaryCount_le_length {S : Type} (C : SourceWord S) :
    sourceKnownUnitaryCount C ≤ C.length := by
  unfold sourceKnownUnitaryCount
  exact List.countP_le_length

theorem sourceKnownUnitaryCount_add_calls {S : Type} (C : SourceWord S) :
    sourceKnownUnitaryCount C + sourceWordCalls C = C.length := by
  induction C with
  | nil => simp [sourceKnownUnitaryCount, sourceWordCalls]
  | cons s C ih =>
      cases s with
      | inl U =>
          have hc : sourceWordCalls (Sum.inl U :: C) = sourceWordCalls C := by
            simp [sourceWordCalls]
          have hk : sourceKnownUnitaryCount (Sum.inl U :: C) = sourceKnownUnitaryCount C + 1 :=
            sourceKnownUnitaryCount_add_call C U
          rw [hk, hc, List.length_cons]
          omega
      | inr b =>
          have hc : sourceWordCalls (Sum.inr b :: C) = sourceWordCalls C + 1 := by
            simp [sourceWordCalls]
          have hk : sourceKnownUnitaryCount (Sum.inr b :: C) = sourceKnownUnitaryCount C :=
            sourceKnownUnitaryCount_add_query C b
          rw [hk, hc, List.length_cons]
          omega

theorem source_theorem1_query_reduction_quantum {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) {ε T : ℝ}
    (hT : 0 < T) (hε : 0 < ε)
    {r : ℕ} (hr : 0 < r) (C : SourceWord (SourceSpace n q H r))
    (hlegal : sourceWordLegal C)
    (hach : sourceWordAchieves input ρ σ hr C (Real.sqrt (1 - ε)))
    (k : ℝ) (hcalls : (sourceWordCalls C : ℝ) ≤ 8 * T * k / ε)
    (hlog : 1 < Real.log (T / ε))
    (hk : k ≤ 2 * Real.log (T / ε) / Real.log (Real.log (T / ε))) :
    sourceCoherentQ input ρ σ ε ≤
      ENNReal.ofReal (16 * (T * Real.log (T / ε)) / (ε * Real.log (Real.log (T / ε)))) := by
  refine le_trans (sourceCoherentQ_le_of_sourceWordAchieves input ρ σ hr C hlegal hach) ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (le_trans hcalls (theorem1_query_budget T ε k hT hε hlog hk))

theorem source_theorem1_query_reduction_classical {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ0 : QState H) (σ : X → QState H) {ε T : ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {r : ℕ} (hr : 0 < r) (C : SourceWord (SourceSpace n q H r))
    (hlegal : sourceWordLegal C)
    (hach : sourceWordAchieves input (fun _ => ρ0) σ hr C (Real.sqrt (1 - ε)))
    (k : ℝ) (hcalls : (sourceWordCalls C : ℝ) ≤ 8 * T * k * Real.log (1 / ε))
    (hlog : 1 < Real.log (T / ε))
    (hk : k ≤ 2 * Real.log (T / ε) / Real.log (Real.log (T / ε))) :
    sourceCoherentQ input (fun _ => ρ0) σ ε ≤
      ENNReal.ofReal
        (16 * (T * Real.log (T / ε) * Real.log (1 / ε)) / Real.log (Real.log (T / ε))) := by
  refine le_trans
    (sourceCoherentQ_le_of_sourceWordAchieves input (fun _ => ρ0) σ hr C hlegal hach) ?_
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hfac : 0 ≤ 8 * T * Real.log (1 / ε) := by
    have hA : 0 ≤ Real.log (1 / ε) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hε]
      linarith
    positivity
  have hLL : Real.log (Real.log (T / ε)) ≠ 0 := ne_of_gt (Real.log_pos hlog)
  calc (sourceWordCalls C : ℝ)
      ≤ 8 * T * k * Real.log (1 / ε) := hcalls
    _ = (8 * T * Real.log (1 / ε)) * k := by ring
    _ ≤ (8 * T * Real.log (1 / ε)) *
          (2 * Real.log (T / ε) / Real.log (Real.log (T / ε))) :=
        mul_le_mul_of_nonneg_left hk hfac
    _ = 16 * (T * Real.log (T / ε) * Real.log (1 / ε)) /
          Real.log (Real.log (T / ε)) := by
        field_simp
        ring

theorem source_main_result_known_unitaries {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) {T p Kq Ku : ℝ}
    (hp0 : 0 < p)
    {r : ℕ} (hr : 0 < r) (C : SourceWord (SourceSpace n q H r))
    (hlegal : sourceWordLegal C)
    (hach : sourceWordAchieves input ρ σ hr C p)
    (hcalls : (sourceWordCalls C : ℝ) ≤ Kq * (T * Real.log T) / Real.log (Real.log T))
    (hknown : (sourceKnownUnitaryCount C : ℝ) ≤ Ku * (T ^ 2 * Real.log T)) :
    sourceCoherentQ input ρ σ (1 - p ^ 2) ≤
        ENNReal.ofReal (Kq * (T * Real.log T) / Real.log (Real.log T)) ∧
      (sourceKnownUnitaryCount C : ℝ) ≤ Ku * (T ^ 2 * Real.log T) := by
  constructor
  · have hsqrt : Real.sqrt (1 - (1 - p ^ 2)) = p := by
      rw [show 1 - (1 - p ^ 2) = p ^ 2 by ring, Real.sqrt_sq hp0.le]
    have hach' : sourceWordAchieves input ρ σ hr C (Real.sqrt (1 - (1 - p ^ 2))) := by
      rw [hsqrt]
      exact hach
    refine le_trans (sourceCoherentQ_le_of_sourceWordAchieves input ρ σ hr C hlegal hach') ?_
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcalls
  · exact hknown

end Qatlib.Papers.DiscreteSim08.MainResults
