/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.LowRankHHL.LowRankOffGridHHL
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm

/-!
# Rational rotations and the counted HHL program

`rationalHHLDecode` and `rationalHHLGamma` define signed rational phase decoding and clipped
reciprocal amplitudes. `rationalHHLCS` computes exact rational unit-circle parameters, which
define the flag gate, lookup table, and counted program `rationalHHLWord` for the linear-systems
method of [HarrowHassidimLloyd2009].

The module proves unitarity, table correctness, exact circuit counts, and full-workspace error
bounds for replacing the ideal rotations by their rational approximations.

## Main statements

* `rationalHHLRotation_error`: the rotation error is at most `32 / 2^k`.
* `rational_hhl_table_and_actual_forward_inverse`: table correctness, well-formedness, and exact
  query and gate counts.
* `rational_hhl_low_rank_full_program_error`: the signed low-rank workspace error is at most
  `eta + 32 / 2^k`.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The signed rational phase label, equal to `y / M` on the lower half of the grid and `y / M -
1` on the upper half. -/
def rationalHHLDecode (M : ℕ) (y : Fin M) : ℚ :=
  if 2*y.val ≤ M then (y.val:ℚ)/M else (y.val:ℚ)/M-1

/-- The rational signed clipped reciprocal amplitude, set to zero when `d ≤ 0` or the decoded
value is zero. -/
def rationalHHLGamma (d x : ℚ) : ℚ :=
  if d ≤ 0 ∨ x=0 then 0 else (d/4)*(if 0 < x then 1 else -1)/max (d/2) |x|

/-- The rational cosine-sine pair computed from the squared clipped amplitude, with its sign
restored in the sine component. -/
def rationalHHLCS (d x : ℚ) (k : ℕ) : ℚ × ℚ :=
  let g := rationalHHLGamma d x
  let p := rationalPayoffCS (g^2) k
  (p.1,(if 0 ≤ g then 1 else -1)*p.2)

/-- The two-dimensional rotation matrix determined by the computed rational cosine-sine pair. -/
def rationalHHLRotation (d x : ℚ) (k : ℕ) : Matrix Bool Bool ℂ :=
  fun a b => if a=b then (rationalHHLCS d x k).1
    else if a then (rationalHHLCS d x k).2 else -(rationalHHLCS d x k).2

/-- The phase-controlled rational rotation on the success flag, tensored with the identity on
the data register. -/
noncomputable def rationalHHLFlag {D M : ℕ} (d : ℚ) (k : ℕ) :
  Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (gridHHLFlagData (D:=D) (M:=M))
    (TensorGate (BlockDiag (fun y : Fin M => rationalHHLRotation d (rationalHHLDecode M y) k)) (1 : Operator D))

/-- The counted adjoint-circuit word combining input preparation, QPE, the rational flag
rotation, and inverse QPE. -/
noncomputable def rationalHHLWord {D : ℕ} (M : ℕ) (d : ℚ) (k : ℕ) (B : Operator D) :
    List (AdjointStep (Fin M × (Bool × (Bool × Fin D)))) :=
  adjointCircuit (countedQPEWord D M) ++ [.gate (countedHHLLiftGate (rationalHHLFlag d k))] ++
    countedQPEWord D M ++ [.gate (countedHHLLiftGate (countedHHLPrepMain B))]

/-- The full-workspace output obtained by evaluating the rational HHL word on zero ancillas and
the input basis state. -/
noncomputable def rationalHHLRun {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D)
    (d : ℚ) (k : ℕ) (B : Operator D) (j : Fin D) : QState (Fin M × (Bool × (Bool × Fin D))) :=
  evaluate (countedHHLOracleLift U) (rationalHHLWord M d k B) *ᵥ
    TensorState (Ket (⟨0,by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (Ket j)))

/-- The array of rational rotation parameters computed for every decoded phase label. -/
def rationalHHLTable (M : ℕ) (d : ℚ) (k : ℕ) : Array (ℚ × ℚ) :=
  (List.ofFn (fun y : Fin M => rationalHHLCS d (rationalHHLDecode M y) k)).toArray

/-- For positive `d`, the rational clipped amplitude agrees with `uniformHHLGamma` after casting
to the reals. -/
theorem rationalHHLGamma_cast (d x : ℚ) (hd : 0 < d) :
    (rationalHHLGamma d x : ℝ) = uniformHHLGamma d x := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  by_cases hx : x = 0
  · subst x; simp [rationalHHLGamma, uniformHHLGamma]
  · have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    by_cases hp : 0 < x
    · have hp' : 0 < (x : ℝ) := by exact_mod_cast hp
      simp [rationalHHLGamma, not_le.mpr hd, hx, hp, uniformHHLGamma,
        Real.sign_of_pos hp', Rat.cast_max, Rat.cast_abs]
    · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
      have hn' : (x : ℝ) < 0 := by exact_mod_cast hn
      simp [rationalHHLGamma, not_le.mpr hd, hx, hp, uniformHHLGamma,
        Real.sign_of_neg hn', Rat.cast_max, Rat.cast_abs]

/-- For positive `d`, the squared rational clipped amplitude lies in `[0, 1]`. -/
theorem rationalHHLGamma_sq_range (d x : ℚ) (hd : 0 < d) :
    0 ≤ (rationalHHLGamma d x)^2 ∧ (rationalHHLGamma d x)^2 ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h := uniformHHLGamma_abs_le (d : ℝ) (x : ℝ) (by exact_mod_cast hd)
  rw [← rationalHHLGamma_cast d x hd] at h
  have hh : ((rationalHHLGamma d x : ℚ) : ℝ)^2 ≤ 1 := by
    have hh := (abs_le.mp h)
    nlinarith [hh.1, hh.2]
  exact_mod_cast hh

/-- The computed rational cosine-sine pair lies exactly on the unit circle. -/
theorem rationalHHLCS_circle (d x : ℚ) (k : ℕ) :
    (rationalHHLCS d x k).1^2 + (rationalHHLCS d x k).2^2 = 1 := by
  have h := rationalPayoffCS_circle ((rationalHHLGamma d x)^2) k
  by_cases hg : 0 ≤ rationalHHLGamma d x <;> simp [rationalHHLCS, hg] <;> nlinarith [h]

/-- The computed rational HHL rotation is unitary. -/
theorem rationalHHLRotation_unitary (d x : ℚ) (k : ℕ) :
    rationalHHLRotation d x k ∈ Matrix.unitaryGroup Bool ℂ := by
  have hc : ((rationalHHLCS d x k).1 : ℂ)^2 + ((rationalHHLCS d x k).2 : ℂ)^2 = 1 := by
    exact_mod_cast rationalHHLCS_circle d x k
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, rationalHHLRotation, pow_two] at *
  all_goals first | (simpa only [pow_two, add_comm] using! hc) | ring

/-- For positive `d`, each computed rotation parameter differs from its ideal value by at most
`16 / 2^k`. -/
theorem rationalHHLCS_error (d x : ℚ) (k : ℕ) (hd : 0 < d) :
    |((rationalHHLCS d x k).1 : ℝ) - Real.sqrt (1-uniformHHLGamma d x^2)| ≤ 16/2^k ∧
    |((rationalHHLCS d x k).2 : ℝ) - uniformHHLGamma d x| ≤ 16/2^k := by
  obtain ⟨hq, hq1⟩ := rationalHHLGamma_sq_range d x hd
  have h := rationalPayoffCS_sqrt_error ((rationalHHLGamma d x)^2) k hq hq1
  have hc := rationalHHLGamma_cast d x hd
  refine ⟨?_, ?_⟩
  · simpa [rationalHHLCS, Rat.cast_pow, hc] using! h.1
  · by_cases hg : 0 ≤ rationalHHLGamma d x
    · have hg' : 0 ≤ ((rationalHHLGamma d x : ℚ) : ℝ) := by exact_mod_cast hg
      have hs := h.2
      rw [Rat.cast_pow, Real.sqrt_sq hg'] at hs
      simpa only [rationalHHLCS, hg, if_true, Rat.cast_mul, Rat.cast_one, one_mul, hc] using! hs
    · have hg' : ((rationalHHLGamma d x : ℚ) : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hg)
      have hs := h.2
      rw [Rat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonpos hg'] at hs
      have he : |(-((rationalPayoffCS ((rationalHHLGamma d x)^2) k).2 : ℝ)) -
          (rationalHHLGamma d x : ℝ)| =
          |((rationalPayoffCS ((rationalHHLGamma d x)^2) k).2 : ℝ) - -(rationalHHLGamma d x : ℝ)| := by
        rw [← abs_neg]; congr 1; ring
      simpa only [rationalHHLCS, hg, if_false, Rat.cast_mul, Rat.cast_neg, Rat.cast_one,
        neg_one_mul, ← hc, he] using! hs

/-- The operator-norm error of the computed rational rotation is at most `32 / 2^k` for positive
`d`. -/
theorem rationalHHLRotation_error (d x : ℚ) (k : ℕ) (hd : 0 < d) :
    ‖rationalHHLRotation d x k - uniformHHLRotation d x‖ ≤ 32/2^k := by
  let dc : ℝ := ((rationalHHLCS d x k).1 : ℝ) - Real.sqrt (1-uniformHHLGamma d x^2)
  let ds : ℝ := ((rationalHHLCS d x k).2 : ℝ) - uniformHHLGamma d x
  let C : Matrix Bool Bool ℂ := Matrix.diagonal (fun _ => (dc : ℂ))
  let S : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => ((if b then ds else -ds : ℝ) : ℂ))
  have heq : rationalHHLRotation d x k - uniformHHLRotation d x = C + S * PauliX := by
    ext a b
    cases a <;> cases b <;>
      simp [rationalHHLRotation, uniformHHLRotation, C, S, dc, ds,
        Matrix.diagonal_mul, PauliX, permMatrix, Complex.ofReal_ratCast]
    all_goals ring
  have hC : ‖C‖ ≤ 16/2^k := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (rationalHHLCS_error d x k hd).1
  have hS : ‖S‖ ≤ 16/2^k := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true, abs_neg]
    all_goals exact (rationalHHLCS_error d x k hd).2
  have hX : ‖PauliX‖ ≤ 1 := l2_norm_unitary_le_one pauliX_unitary
  rw [heq]
  calc
    _ ≤ ‖C‖ + ‖S*PauliX‖ := norm_add_le _ _
    _ ≤ 16/2^k + (16/2^k)*1 := add_le_add hC
      ((norm_mul_le _ _).trans (mul_le_mul hS hX (norm_nonneg _) (by positivity)))
    _ = _ := by ring

/-- The lower endpoint of the rational square-root bracket for zero is zero at every precision. -/
theorem rationalSqrtBracket_zero_lower (k : ℕ) : (rationalSqrtBracket 0 k).1 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rationalSqrtBracket]
    split_ifs with h
    · have hb := (rational_sqrt_bracket_actual_interval_and_comparisons 0 k (by norm_num) (by norm_num)).1
      have hlow : ((rationalSqrtBracket 0 k).2.1 : ℚ) = 0 := by
        nlinarith [sq_nonneg ((rationalSqrtBracket 0 k).2.1)]
      simp [ih, hlow]
    · exact ih

/-- The rational rotation at decoded value zero is the identity. -/
theorem rationalHHLRotation_zero (d : ℚ) (k : ℕ) : rationalHHLRotation d 0 k = 1 := by
  have hg : rationalHHLGamma d 0 = 0 := by simp [rationalHHLGamma]
  ext a b
  cases a <;> cases b <;>
    simp [rationalHHLRotation, rationalHHLCS, hg, rationalPayoffCS,
      rationalPayoffParameter, rationalSqrtBracket_zero_lower]

/-- For positive `d`, the computed clipped amplitude agrees with the real specification and its
rotation is unitary, has error at most `32 / 2^k`, and is the identity at zero. -/
theorem rational_hhl_computed_signed_clip_and_rotation :
    ∀ (d x : ℚ) (k : ℕ), 0 < d →
      (rationalHHLGamma d x : ℝ) = uniformHHLGamma d x ∧
      rationalHHLRotation d x k ∈ Matrix.unitaryGroup Bool ℂ ∧
      ‖rationalHHLRotation d x k-uniformHHLRotation d x‖ ≤ 32/2^k ∧
      rationalHHLRotation d 0 k = 1 := by
  intro d x k hd
  exact ⟨rationalHHLGamma_cast d x hd, rationalHHLRotation_unitary d x k,
    rationalHHLRotation_error d x k hd, rationalHHLRotation_zero d k⟩

/-- The rational HHL table contains exactly `M` entries. -/
theorem rationalHHLTable_size (M : ℕ) (d : ℚ) (k : ℕ) :
    (rationalHHLTable M d k).size = M := by simp [rationalHHLTable]

/-- A valid lookup in the rational HHL table returns the computed parameters for that decoded
phase label. -/
theorem rationalHHLTable_get (M : ℕ) (d : ℚ) (k : ℕ) (y : Fin M) :
    (rationalHHLTable M d k)[y.val]? = some (rationalHHLCS d (rationalHHLDecode M y) k) := by
  simp [rationalHHLTable, y.isLt]

/-- Casting the rational phase decoder to the reals gives `uniformHHLDecode`. -/
theorem rationalHHLDecode_cast (M : ℕ) (y : Fin M) :
    (rationalHHLDecode M y : ℝ) = uniformHHLDecode M y := by
  simp only [rationalHHLDecode, uniformHHLDecode]
  split_ifs <;> push_cast <;> rfl

/-- The rational HHL flag gate is unitary. -/
theorem rationalHHLFlag_unitary {D M : ℕ} (d : ℚ) (k : ℕ) :
    rationalHHLFlag (D := D) (M := M) d k ∈ Matrix.unitaryGroup _ ℂ := by
  apply (relabelGate_mem_unitaryGroup _ _).2
  exact tensorGate_unitary (blockDiag_unitary _ fun y => rationalHHLRotation_unitary d _ k)
    (Submonoid.one_mem _)

/-- For unitary input preparation and a grid of size at least two, the rational table has the
specified entries and the HHL word is well formed. The word uses `2 * (M - 1)` queries and
`4 * (M - 1) + 6` fixed gates. -/
theorem rational_hhl_table_and_actual_forward_inverse :
    ∀ (D M k : ℕ) (d : ℚ) (B : Operator D), 2 ≤ M → 0 < d →
      B ∈ Matrix.unitaryGroup (Fin D) ℂ →
      (rationalHHLTable M d k).size = M ∧
      (∀ y : Fin M, (rationalHHLTable M d k)[y.val]? =
        some (rationalHHLCS d (rationalHHLDecode M y) k)) ∧
      WellFormedAdjointCircuit (rationalHHLWord M d k B) ∧
      adjointQueryCount (rationalHHLWord M d k B) = 2*(M-1) ∧
      adjointGateCount (rationalHHLWord M d k B) = 4*(M-1)+6 := by
  intro D M k d B hM _hd hB
  have hm : 0 < M := by omega
  have hwf := countedQPEWord_wellFormed D M hm
  refine ⟨rationalHHLTable_size M d k, rationalHHLTable_get M d k, ?_, ?_, ?_⟩
  · simp only [rationalHHLWord, WellFormedAdjointCircuit.append_iff,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨⟨hwf.adjointCircuit, countedHHLLiftGate_unitary (rationalHHLFlag_unitary d k)⟩,
      hwf⟩, countedHHLLiftGate_unitary (countedHHLPrepMain_unitary hB)⟩
  · rw [rationalHHLWord, adjointQueryCount_append, adjointQueryCount_append,
      adjointQueryCount_append, adjointQueryCount_adjointCircuit,
      (countedQPEWord_counts D M hm).1]
    simp only [adjointQueryCount]; omega
  · rw [rationalHHLWord, adjointGateCount_append, adjointGateCount_append,
      adjointGateCount_append, adjointGateCount_adjointCircuit,
      (countedQPEWord_counts D M hm).2]
    simp only [adjointGateCount]; omega

/-- The block-diagonal matrix of rational rotations differs from its ideal counterpart by at
most `32 / 2^k` in operator norm. -/
theorem rationalHHLBlock_error (M k : ℕ) (d : ℚ) (hd : 0 < d) :
    ‖BlockDiag (fun y : Fin M => rationalHHLRotation d (rationalHHLDecode M y) k) -
      BlockDiag (fun y : Fin M => uniformHHLRotation d (uniformHHLDecode M y))‖ ≤ 32/2^k := by
  let dc : Fin M → ℝ := fun y => ((rationalHHLCS d (rationalHHLDecode M y) k).1 : ℝ) -
    Real.sqrt (1-uniformHHLGamma d (uniformHHLDecode M y)^2)
  let ds : Fin M → ℝ := fun y => ((rationalHHLCS d (rationalHHLDecode M y) k).2 : ℝ) -
    uniformHHLGamma d (uniformHHLDecode M y)
  let C : Matrix (Fin M × Bool) (Fin M × Bool) ℂ := Matrix.diagonal (fun p => (dc p.1 : ℂ))
  let S : Matrix (Fin M × Bool) (Fin M × Bool) ℂ :=
    Matrix.diagonal (fun p => ((if p.2 then ds p.1 else -ds p.1 : ℝ) : ℂ))
  let X : Matrix (Fin M × Bool) (Fin M × Bool) ℂ := TensorGate (1 : Operator M) PauliX
  have heq : BlockDiag (fun y : Fin M => rationalHHLRotation d (rationalHHLDecode M y) k) -
      BlockDiag (fun y : Fin M => uniformHHLRotation d (uniformHHLDecode M y)) = C + S*X := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i=j
    · subst j
      cases a <;> cases b <;>
        simp [BlockDiag, rationalHHLRotation, uniformHHLRotation, C, S, X, dc, ds,
          Matrix.diagonal_mul, TensorGate, PauliX, permMatrix, Complex.ofReal_ratCast]
      all_goals ring
    · cases a <;> cases b <;>
        simp [BlockDiag, C, S, X, Matrix.diagonal_mul, TensorGate, hij]
  have hC : ‖C‖ ≤ 16/2^k := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa only [dc, rationalHHLDecode_cast] using!
      (rationalHHLCS_error d (rationalHHLDecode M p.1) k hd).1
  have hS : ‖S‖ ≤ 16/2^k := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases p.2 <;> simp only [Bool.false_eq_true, if_false, if_true, abs_neg]
    all_goals simpa only [ds, rationalHHLDecode_cast] using!
        (rationalHHLCS_error d (rationalHHLDecode M p.1) k hd).2
  have hX : ‖X‖ ≤ 1 := l2_norm_unitary_le_one (tensorGate_unitary (by simp) pauliX_unitary)
  rw [heq]
  calc
    _ ≤ ‖C‖ + ‖S*X‖ := norm_add_le _ _
    _ ≤ 16/2^k + (16/2^k)*1 := add_le_add hC
      ((norm_mul_le _ _).trans (mul_le_mul hS hX (norm_nonneg _) (by positivity)))
    _ = _ := by ring

/-- The rational flag gate differs from the ideal uniform HHL flag gate by at most `32 / 2^k` in
operator norm. -/
theorem rationalHHLFlag_error {D M : ℕ} (d : ℚ) (k : ℕ) (hd : 0 < d) :
    ‖rationalHHLFlag (D := D) (M := M) d k - uniformHHLFlag d‖ ≤ 32/2^k := by
  rw [rationalHHLFlag, uniformHHLFlag, l2_norm_relabelGate_sub,
    tensorGate_sub_left, l2_norm_tensorGate]
  exact (mul_le_mul (rationalHHLBlock_error M k d hd) l2_norm_one_le
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

/-- Evaluation of the rational HHL word factors as adjoint QPE, flag rotation, QPE, and input
preparation. -/
theorem rationalHHLWord_evaluate {D M : ℕ} (U B : Operator D) (d : ℚ) (k : ℕ) :
    evaluate (countedHHLOracleLift (D := D) (M := M) U) (rationalHHLWord M d k B) =
    (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ *
      (countedHHLLiftGate (rationalHHLFlag d k) *
        (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M) *
          countedHHLLiftGate (countedHHLPrepMain B))) := by
  rw [rationalHHLWord, evaluate_append, evaluate_append, evaluate_append, evaluate_adjointCircuit]
  simp only [evaluate, instructionMatrix, mul_one]
  noncomm_ring

/-- For unitary oracle and preparation, replacing ideal flag rotations by rational rotations
changes the full-workspace output by at most `32 / 2^k`. -/
theorem rational_hhl_full_workspace_numerical_bias :
    ∀ (D M k : ℕ) (hM : 2 ≤ M) (U B : Operator D) (j : Fin D) (d : ℚ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d →
      ‖toEuclidean_fromVec (rationalHHLRun M hM U d k B j - uniformHHLRun M hM U d B j)‖ ≤ 32/2^k := by
  intro D M k hM U B j d hU hB hd
  let Q := evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)
  let P := countedHHLLiftGate (D := D) (M := M) (countedHHLPrepMain B)
  let R := countedHHLLiftGate (D := D) (M := M) (rationalHHLFlag d k)
  let S := countedHHLLiftGate (D := D) (M := M) (uniformHHLFlag d)
  have hQ : Q ∈ Matrix.unitaryGroup _ ℂ :=
    (countedQPEWord_wellFormed D M (by omega)).evaluate_unitary (countedHHLOracleLift_unitary hU)
  have hP : P ∈ Matrix.unitaryGroup _ ℂ :=
      countedHHLLiftGate_unitary (countedHHLPrepMain_unitary hB)
  have hQt : ‖Qᴴ‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact l2_norm_unitary_le_one hQ
  have hR : ‖R-S‖ ≤ 32/2^k := by
    dsimp [R,S]
    rw [countedHHLLiftGate, countedHHLLiftGate, l2_norm_relabelGate_sub,
      tensorGate_sub_right, l2_norm_tensorGate]
    exact (mul_le_mul l2_norm_one_le (rationalHHLFlag_error d k hd)
      (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
  have hE : ‖Qᴴ*(R*(Q*P))-Qᴴ*(S*(Q*P))‖ ≤ 32/2^k := by
    rw [← Matrix.mul_sub, ← Matrix.sub_mul]
    have hQP : ‖Q*P‖ ≤ 1 := (norm_mul_le _ _).trans
      ((mul_le_mul (l2_norm_unitary_le_one hQ) (l2_norm_unitary_le_one hP)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
    exact (norm_mul_le _ _).trans ((mul_le_mul hQt
      ((norm_mul_le _ _).trans ((mul_le_mul hR hQP (norm_nonneg _) (by positivity)).trans_eq (mul_one _)))
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hEval : evaluate (countedHHLOracleLift (D := D) (M := M) U) (uniformHHLWord M d B) = Qᴴ*(S*(Q*P)) := by
    rw [uniformHHLWord, evaluate_append, evaluate_append, evaluate_append, evaluate_adjointCircuit]
    simp only [evaluate, instructionMatrix, mul_one]
    dsimp [Q,S,P]; noncomm_ring
  unfold rationalHHLRun uniformHHLRun
  rw [rationalHHLWord_evaluate, hEval, ← Matrix.sub_mulVec]
  exact (l2_norm_mulVec_fromVec_le _ _).trans
    ((mul_le_mul_of_nonneg_right hE (norm_nonneg _)).trans_eq (by rw [norm_countedHHLBranchInput]; ring))

/-- Under the signed low-rank spectral promise and grid bound, the rational HHL output differs
from the ideal workspace state by at most `eta + 32 / 2^k`. -/
theorem rational_hhl_low_rank_full_program_error :
    ∀ (D M k : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℚ) (eta : ℝ),
      V ∈ Matrix.unitaryGroup (Fin D) ℂ → B ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < d →
      0 < eta → eta ≤ 1 → (∀ i, eig i=0 ∨ ((d:ℝ) ≤ |eig i| ∧ |eig i| ≤ 1/4)) →
      4096/((d:ℝ)^2*eta^4) ≤ (M:ℝ) →
      ‖toEuclidean_fromVec (rationalHHLRun M hM (continuousHHLOracle eig V) d k B j -
        uniformHHLIdeal M hM eig V d B j)‖ ≤ eta+32/2^k := by
  intro D M k hM eig V B j d eta hV hB hd heta heta1 heig hbudget
  have hn := rational_hhl_full_workspace_numerical_bias D M k hM _ B j d
    (continuous_hhl_oracle_unitary eig V hV) hB hd
  have hq := low_rank_uniform_hhl_full_workspace_error D M hM eig V B j d eta hV hB
    (by exact_mod_cast hd) heta heta1 heig hbudget
  exact (norm_sub_le_norm_sub_add_norm_sub (toEuclidean_fromVec (rationalHHLRun M hM (continuousHHLOracle eig V) d k B j))
    (toEuclidean_fromVec (uniformHHLRun M hM (continuousHHLOracle eig V) d B j))
    (toEuclidean_fromVec (uniformHHLIdeal M hM eig V d B j))).trans
      ((add_le_add hn hq).trans_eq (add_comm _ _))

/-- For a unitary oracle, the rational HHL run equals the phase-flag embedding of the QPE,
rational-rotation, and inverse-QPE circuit on the prepared input. -/
theorem rationalHHLRun_eq {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U : Operator D) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (d : ℚ) (k : ℕ) (B : Operator D) (j : Fin D) :
    rationalHHLRun M hM U d k B j = phaseFlagEmbed M
      (Run 1 (gridHHLQPEBlock (D := D) (M := M) U
        ++ [Step.gate (rationalHHLFlag (D := D) (M := M) d k)]
        ++ gridHHLQPEBlockInv (D := D) (M := M) U)
        (TensorState (Ket (⟨0, by omega⟩ : Fin M))
          (TensorState (Ket false) (ApplyGate B (Ket j))))) := by
  have hMpos : 0 < M := by omega
  have hEval : evaluate (countedHHLOracleLift (D := D) (M := M) U) (rationalHHLWord M d k B)
      = (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M))ᴴ *
        (countedHHLLiftGate (rationalHHLFlag (D := D) (M := M) d k) *
          (evaluate (countedHHLOracleLift (D := D) (M := M) U) (countedQPEWord D M)
            * countedHHLLiftGate (countedHHLPrepMain (D := D) (M := M) B))) := by
    rw [rationalHHLWord, evaluate_append, evaluate_append, evaluate_append,
      evaluate_adjointCircuit]
    simp only [evaluate, instructionMatrix, mul_one]
    noncomm_ring
  unfold rationalHHLRun
  rw [countedHHLBranchInput_eq D M hMpos j]
  change ApplyGate _ _ = _
  rw [hEval, ← applyGate_comp, ← applyGate_comp, ← applyGate_comp]
  rw [countedHHLLiftGate_apply (countedHHLPrepMain (D := D) (M := M) B),
    countedHHLPrepMain_apply hMpos B j, countedQPEWord_apply D M hMpos U _,
    countedHHLLiftGate_apply (rationalHHLFlag (D := D) (M := M) d k),
    countedQPEWord_apply_adjoint D M hMpos U hU _]
  rw [run_append, run_append, run_gate, run_nil]

end Qatlib.Concepts.HhlAlgorithms.RationalProgram
