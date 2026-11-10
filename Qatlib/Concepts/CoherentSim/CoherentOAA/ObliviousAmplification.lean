/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.Amplification
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
section CubicBlocks

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem oddCubic_dilationBlock (A : Matrix O I ℂ) (a b : ℂ) :
    (aeval (hermitianDilation A) (C a * X - C b * X ^ 3)).toBlocks₁₂ =
      a • A - b • (A * Aᴴ * A) := by
  have hp : C a * X - C b * X ^ 3 =
      oddSingularPolynomial (C a - C b * X) := by
    simp [oddSingularPolynomial, evenSingularPolynomial]
    ring
  rw [hp, aeval_oddSingularPolynomial]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_assoc]

theorem cubic_dilationBlock (A : Matrix O I ℂ) :
    (aeval (hermitianDilation A) (responseP (-Complex.I) cubicPhases)).toBlocks₁₂ =
      (3 : ℂ) • A - (4 : ℂ) • (A * Aᴴ * A) := by
  rw [responseP_cubic]
  simpa only [map_ofNat] using oddCubic_dilationBlock A 3 4

omit [DecidableEq O] in

theorem cubic_half_isometry {V : Matrix O I ℂ} (hV : IsIsometry V) :
    (3 : ℂ) • ((1 / 2 : ℂ) • V) -
      (4 : ℂ) • (((1 / 2 : ℂ) • V) * ((1 / 2 : ℂ) • V)ᴴ *
        ((1 / 2 : ℂ) • V)) = V := by
  have hv : Vᴴ * V = 1 := hV
  simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, hv, smul_smul, ← sub_smul]
  norm_num

end CubicBlocks

theorem responseQ_cubic :
    responseQ (-Complex.I) cubicPhases = 4 * X ^ 2 - 1 := by
  have hI4 : Complex.I ^ 4 = (1 : ℂ) := by
    calc
      _ = (Complex.I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  apply Polynomial.funext
  intro x
  simp [cubicPhases, responseP_cons, responseQ_cons]
  ring_nf
  simp only [Complex.I_sq, hI4]
  ring

section Oblivious

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

theorem cubic_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) :
    ProjectedUnitaryEncoding ((3 : ℂ) • A - (4 : ℂ) • (A * Aᴴ * A))
      (phasedAlternating U (rangeProjector R) (rangeProjector L)
        (-Complex.I) cubicPhases) L R := by
  have hb : IsPhase (-Complex.I) := by norm_num [IsPhase]
  have hz : ∀ z ∈ cubicPhases, IsPhase z := by
    simp [cubicPhases, IsPhase]
  simpa only [cubic_dilationBlock] using
    qsvt_odd_projectedEncoding h hb cubicPhases hz (by decide)

theorem cubic_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) :
    ∃ cs : List (AdjointStep H),
      ProjectedUnitaryEncoding ((3 : ℂ) • A - (4 : ℂ) • (A * Aᴴ * A))
        (evaluate U cs) L R ∧
      adjointQueryCount cs = 3 ∧ adjointGateCount cs = 4 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) (-Complex.I) cubicPhases,
    ?_, ?_, ?_⟩
  · rw [evaluate_compileQSVT]
    exact cubic_projectedEncoding h
  · rw [queryCount_compileQSVT]
    rfl
  · rw [gateCount_compileQSVT]
    rfl

theorem oblivious_half_isometry_projectedEncoding {V : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding ((1 / 2 : ℂ) • V) U L R) (hV : IsIsometry V) :
    ProjectedUnitaryEncoding V
      (phasedAlternating U (rangeProjector R) (rangeProjector L)
        (-Complex.I) cubicPhases) L R := by
  simpa only [cubic_half_isometry hV] using cubic_projectedEncoding h

theorem oblivious_half_isometry_action {V : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding ((1 / 2 : ℂ) • V) U L R) (hV : IsIsometry V) :
    phasedAlternating U (rangeProjector R) (rangeProjector L)
      (-Complex.I) cubicPhases * R = L * V := by
  have hv : Vᴴ * V = 1 := hV
  have hav : ((1 / 2 : ℂ) • V) * (1 : Matrix I I ℂ) = (1 / 2 : ℂ) • V := by
    simp
  have haw : ((1 / 2 : ℂ) • V)ᴴ * V = (1 / 2 : ℂ) • (1 : Matrix I I ℂ) := by
    simp [Matrix.conjTranspose_smul, Matrix.smul_mul, hv]
  have hs := (signalPair_of_encoding h hav haw).phased_response (-Complex.I) cubicPhases
  rw [responseP_cubic, responseQ_cubic] at hs
  norm_num [alternatingSource, cubicPhases] at hs
  exact hs

theorem oblivious_half_isometry_all_inputs {K : Type*} {V : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding ((1 / 2 : ℂ) • V) U L R) (hV : IsIsometry V)
    (ψ : Matrix I K ℂ) :
    phasedAlternating U (rangeProjector R) (rangeProjector L)
      (-Complex.I) cubicPhases * (R * ψ) = L * (V * ψ) := by
  rw [← Matrix.mul_assoc, oblivious_half_isometry_action h hV, Matrix.mul_assoc]

theorem oblivious_half_isometry_counted {V : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding ((1 / 2 : ℂ) • V) U L R) (hV : IsIsometry V) :
    ∃ cs : List (AdjointStep H),
      ProjectedUnitaryEncoding V (evaluate U cs) L R ∧
      evaluate U cs * R = L * V ∧
      adjointQueryCount cs = 3 ∧ adjointGateCount cs = 4 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) (-Complex.I) cubicPhases,
    ?_, ?_, ?_, ?_⟩
  · rw [evaluate_compileQSVT]
    exact oblivious_half_isometry_projectedEncoding h hV
  · rw [evaluate_compileQSVT]
    exact oblivious_half_isometry_action h hV
  · rw [queryCount_compileQSVT]
    rfl
  · rw [gateCount_compileQSVT]
    rfl

end Oblivious

noncomputable def fixedPointPhase : ℂ := ⟨Real.sqrt 3 / 2, 1 / 2⟩

noncomputable def fixedPointCoefficient : ℂ := ⟨3 / 2, Real.sqrt 3 / 2⟩

noncomputable def fixedPointPhases : List ℂ := [1, fixedPointPhase, fixedPointPhase]

theorem fixedPointPhase_isPhase : IsPhase fixedPointPhase := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [fixedPointPhase, Complex.mul_re]
    nlinarith
  · simp [fixedPointPhase, Complex.mul_im]
    ring

theorem fixedPointPhases_isPhase : ∀ z ∈ fixedPointPhases, IsPhase z := by
  intro z hz
  simp only [fixedPointPhases, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · simp [IsPhase]
  · exact fixedPointPhase_isPhase
  · exact fixedPointPhase_isPhase

theorem responseP_fixedPoint :
    responseP 1 fixedPointPhases = C fixedPointCoefficient * X - X ^ 3 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Polynomial.funext
  intro x
  simp [fixedPointPhases, responseP_cons, responseQ_cons]
  apply Complex.ext <;>
    simp [fixedPointPhase, fixedPointCoefficient, pow_succ, Complex.mul_re,
      Complex.mul_im] <;>
    ring_nf <;> norm_num [hs] <;> ring

theorem responseQ_fixedPoint : responseQ 1 fixedPointPhases = 1 - X ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Polynomial.funext
  intro x
  simp [fixedPointPhases, responseP_cons, responseQ_cons]
  apply Complex.ext <;>
    simp [fixedPointPhase, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring_nf
  all_goals norm_num [hs]

theorem fixedPoint_failure (x : ℝ) :
    1 - Complex.normSq ((responseP 1 fixedPointPhases).eval (x : ℂ)) =
      (1 - x ^ 2) ^ 3 := by
  have hn := response_normalization (base := 1) (by simp [IsPhase])
    fixedPointPhases fixedPointPhases_isPhase x
  rw [responseQ_fixedPoint] at hn
  simp [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im] at hn ⊢
  nlinarith [hn]

theorem fixedPoint_polynomial_failure (x : ℝ) :
    1 - Complex.normSq (fixedPointCoefficient * (x : ℂ) - (x : ℂ) ^ 3) =
      (1 - x ^ 2) ^ 3 := by
  simpa [responseP_fixedPoint] using fixedPoint_failure x

theorem fixedPoint_failure_le {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    1 - Complex.normSq ((responseP 1 fixedPointPhases).eval (x : ℂ)) ≤ 1 - x ^ 2 := by
  rw [fixedPoint_failure]
  have h0 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have h2 := mul_le_mul_of_nonneg_left h1 h0
  have h3 := mul_le_mul_of_nonneg_left h2 h0
  nlinarith

theorem fixedPoint_weighted_failure {J : Type*} [Fintype J]
    (p σ : J → ℝ) (hp : ∑ j, p j = 1) :
    1 - ∑ j, p j * Complex.normSq ((responseP 1 fixedPointPhases).eval (σ j : ℂ)) =
      ∑ j, p j * (1 - σ j ^ 2) ^ 3 := by
  simp only [← fixedPoint_failure]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp]

section FixedPointRealization

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

theorem fixedPoint_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) :
    ProjectedUnitaryEncoding (fixedPointCoefficient • A - A * Aᴴ * A)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) 1 fixedPointPhases) L R := by
  have hb : IsPhase (1 : ℂ) := by simp [IsPhase]
  have he := qsvt_odd_projectedEncoding h hb fixedPointPhases
    fixedPointPhases_isPhase (by decide)
  have hm : (aeval (hermitianDilation A) (responseP 1 fixedPointPhases)).toBlocks₁₂ =
      fixedPointCoefficient • A - A * Aᴴ * A := by
    rw [responseP_fixedPoint]
    simpa using oddCubic_dilationBlock A fixedPointCoefficient 1
  simpa only [hm] using he

theorem fixedPoint_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) :
    ∃ cs : List (AdjointStep H),
      ProjectedUnitaryEncoding (fixedPointCoefficient • A - A * Aᴴ * A)
        (evaluate U cs) L R ∧
      adjointQueryCount cs = 3 ∧ adjointGateCount cs = 4 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) 1 fixedPointPhases,
    ?_, ?_, ?_⟩
  · rw [evaluate_compileQSVT]
    exact fixedPoint_projectedEncoding h
  · rw [queryCount_compileQSVT]
    rfl
  · rw [gateCount_compileQSVT]
    rfl

theorem fixedPoint_singularPair {K : Type*} {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℝ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = (σ : ℂ) • w) (haw : Aᴴ * w = (σ : ℂ) • v) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L)
      1 fixedPointPhases) R * v =
        (fixedPointCoefficient * (σ : ℂ) - (σ : ℂ) ^ 3) • w := by
  simpa [responseP_fixedPoint] using
    qsvt_odd h hav haw 1 fixedPointPhases (by decide)

theorem fixedPoint_singularSector {K : Type*} {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℝ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = (σ : ℂ) • w) (haw : Aᴴ * w = (σ : ℂ) • v) :
    phasedAlternating U (rangeProjector R) (rangeProjector L) 1 fixedPointPhases * (R * v) =
      (fixedPointCoefficient * (σ : ℂ) - (σ : ℂ) ^ 3) • (L * w) +
      (1 - (σ : ℂ) ^ 2) • leftResidual U (σ : ℂ) (R * v) (L * w) := by
  have he := (signalPair_of_encoding h hav haw).phased_response 1 fixedPointPhases
  rw [responseP_fixedPoint, responseQ_fixedPoint] at he
  simpa [alternatingSource, fixedPointPhases] using he

end FixedPointRealization

end Qatlib.Concepts.CoherentSim.CoherentOAA
