/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan

set_option backward.isDefEq.respectTransparency false

/-!
# StateConvert — Theorem 4.1 in the printed ε-range

Lee--Mittal--Reichardt--Spalek--Szegedy, fixed arXiv:1011.3020v2.
PDF SHA-256 edb6a9db14e47b34a18a5b54610041c680bbe090084e81ca1822eddd990228f1.

Printed Theorem 4.1 (pp. 6–7) asks for the bound `Q_ε(ρ,σ) = O(γ₂(ρ−σ|Δ) log(1/ε)/ε²)`
for any `ε ∈ (0, γ₂(ρ−σ|Δ))`, and printed Proposition 4.6 (p. 8) is the `W ≥ ε`
specialisation whose output error is below `4ε`.  The shared algorithm is proved
for the standard bounded-error window `0 < ε ≤ 1/3`; this module closes the
range to the printed `0 < ε < min(1, γ₂(ρ−σ|Δ))` by running the same algorithm
at the clamped error `min ε (1/3)`.

The clamp is faithful to the printed contract: the output condition
`Re ≥ √(1−ε)` weakens as `ε` grows and the printed budget `log(1/ε)/ε²` is
bounded below on `[1/3,1)`, so the clamped run still meets the printed bound
with a larger (still absolute) constant.  The end point `ε ≥ 1` is excluded:
`√(1−ε)` is not a meaningful success threshold there and the printed budget
`log(1/ε)/ε²` has become nonpositive.  No change is made to the shared
algorithm; only the paper-level statement and the constant accounting are new.

Boundary: the query model, oracle semantics and known unitary primitives are the
source ones; nothing is added about numerical SDP solving or gate synthesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.StateConversion
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

namespace Qatlib.Papers.StateConvLee10.StateConvert

/-- The printed budget at the clamped error `1/3` costs at most a fixed factor
`24` of the printed budget at any error in `(1/3, 1)`. -/
private theorem source_clamped_budget {W ε : ℝ} (hW : 0 ≤ W) (hε : 1/3 < ε)
    (hε1 : ε < 1) :
    W * Real.log (2 / (1 / 3 : ℝ)) / (1 / 3 : ℝ) ^ 2 ≤
      24 * (W * Real.log (2 / ε) / ε ^ 2) := by
  have hεpos : 0 < ε := by linarith
  have hlog6 : (3 : ℝ) * Real.log 6 ≤ 8 * Real.log 2 := by
    have h216 : (3 : ℝ) * Real.log 6 = Real.log 216 := by
      rw [show (216 : ℝ) = 6 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    have h256 : (8 : ℝ) * Real.log 2 = Real.log 256 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h216, h256]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogge : Real.log 2 ≤ Real.log (2 / ε) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hεpos]
    linarith
  have hlarge2 : Real.log 2 ≤ Real.log (2 / ε) / ε ^ 2 := by
    rw [div_eq_mul_inv]
    have hinv : (1 : ℝ) ≤ (ε ^ 2)⁻¹ :=
      (one_le_inv₀ (by positivity : (0 : ℝ) < ε ^ 2)).mpr (by nlinarith)
    calc Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
      _ ≤ Real.log (2 / ε) * (ε ^ 2)⁻¹ :=
          mul_le_mul hlogge hinv (by norm_num)
            (le_trans (le_of_lt hlog2pos) hlogge)
  have hkey : 9 * Real.log 6 ≤ 24 * (Real.log (2 / ε) / ε ^ 2) := by
    nlinarith [hlog6, hlarge2]
  have hleft : W * Real.log (2 / (1 / 3 : ℝ)) / (1 / 3 : ℝ) ^ 2 =
      W * (9 * Real.log 6) := by
    have h1 : (2 : ℝ) / (1 / 3) = 6 := by norm_num
    rw [h1, div_eq_mul_inv, show ((1 / 3 : ℝ) ^ 2)⁻¹ = 9 by norm_num]
    ring
  rw [hleft, mul_div_assoc]
  calc W * (9 * Real.log 6) ≤ W * (24 * (Real.log (2 / ε) / ε ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey hW
    _ = 24 * (W * (Real.log (2 / ε) / ε ^ 2)) := by ring

/-- Fixed arXiv:1011.3020v2. Theorem4.1 and Proposition4.6 in the printed ε-range: for 0<ε<min(1,W), a real filtered-Gram budget W yields one legal source-query word with at most c·ceil(W log(2/ε)/ε²) calls, pointwise clean real overlap at least sqrt(1−ε), and, because ε<W, clean output L2 error below4ε. -/
theorem source_state_conversion_printed_range :
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ W →
    sourceRectValue (gramStateMatrix ρ-gramStateMatrix σ) (sourceAlphabetDelta input) ≤
      ENNReal.ofReal W → 0 < ε → ε < 1 → ε < W →
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
      sourceWordLegal C ∧
      sourceWordCalls C ≤ c*Nat.ceil (W*Real.log (2/ε)/ε^2) ∧
      (∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥
          Real.sqrt (1-ε)) ∧
      (∀ x, ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖ < 4*ε) := by
  obtain ⟨c₀, hc₀, hmain⟩ := realBudgetConversionAlgorithm
  refine ⟨24*c₀, by positivity, ?_⟩
  intro X H _ _ _ _ _ n q input ρ σ W ε hn hW hval hε hε1 hεW
  rcases le_or_gt ε (1/3) with hsmall | hlarge
  · obtain ⟨r, hr, C, hlegal, hcalls, -, hoverlap, hfour⟩ :=
      hmain X H n q input ρ σ W ε hn hW hval hε hsmall
    refine ⟨r, hr, C, hlegal, ?_, hoverlap, fun x => hfour hεW.le x⟩
    exact hcalls.trans (Nat.mul_le_mul_right _
      (Nat.le_mul_of_pos_left c₀ (by norm_num)))
  · have hε3 : (0 : ℝ) < 1 / 3 := by norm_num
    obtain ⟨r, hr, C, hlegal, hcalls, -, hoverlap, hfour⟩ :=
      hmain X H n q input ρ σ W (1/3) hn hW hval hε3 (le_refl _)
    have hW3 : (1 / 3 : ℝ) ≤ W := by linarith
    have hceil : Nat.ceil (W*Real.log (2/(1/3:ℝ))/(1/3:ℝ)^2) ≤
        24*Nat.ceil (W*Real.log (2/ε)/ε^2) := by
      rw [Nat.ceil_le, Nat.cast_mul, Nat.cast_ofNat]
      refine (source_clamped_budget hW hlarge hε1).trans ?_
      exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
    refine ⟨r, hr, C, hlegal, ?_, ?_, fun x => ?_⟩
    · calc sourceWordCalls C
          ≤ c₀*Nat.ceil (W*Real.log (2/(1/3:ℝ))/(1/3:ℝ)^2) := hcalls
        _ ≤ c₀*(24*Nat.ceil (W*Real.log (2/ε)/ε^2)) :=
            Nat.mul_le_mul_left _ hceil
        _ = (24*c₀)*Nat.ceil (W*Real.log (2/ε)/ε^2) := by
            ring
    · intro x
      exact (Real.sqrt_le_sqrt (by linarith : 1-ε ≤ 1-(1/3:ℝ))).trans (hoverlap x)
    · have h4' := hfour hW3 x
      calc ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
            sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖
          < 4*(1/3:ℝ) := h4'
        _ ≤ 4*ε := by linarith

end Qatlib.Papers.StateConvLee10.StateConvert
