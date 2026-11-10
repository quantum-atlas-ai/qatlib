/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
set_option warningAsError false


open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

section SameFrame
variable {H I : Type*} [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]

theorem hermitian_qsvt_compress {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {F : Matrix H I ℂ} (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (base : ℂ) (zs : List ℂ) :
    compress F (phasedAlternating U (rangeProjector F) (rangeProjector F) base zs) F =
      aeval A (responseP base zs) := by
  have ha : Aᴴ = A := hA
  have he := qsvt_operator_intertwiner h (S := A) (v := (1 : Matrix I I ℂ))
    (w := (1 : Matrix I I ℂ)) (by simp) (by simp [ha]) base zs
  simpa [compress, Matrix.mul_assoc, alternatingSource_eq] using he

theorem hermitian_qsvt_projectedEncoding {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {F : Matrix H I ℂ} (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ProjectedUnitaryEncoding (aeval A (responseP base zs))
      (phasedAlternating U (rangeProjector F) (rangeProjector F) base zs) F F := by
  exact ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.left_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.left_isometry, hermitian_qsvt_compress hA h base zs⟩

theorem hermitian_realPart_projectedEncoding {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {F : Matrix H I ℂ} (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ProjectedUnitaryEncoding (aeval A (realPartPolynomial (responseP base zs)))
      (realPartQSVT U (rangeProjector F) (rangeProjector F) base zs)
      (averageFrame F) (averageFrame F) := by
  have hc := average_projectedEncoding (hermitian_qsvt_projectedEncoding hA h hb zs hzs)
    (hermitian_qsvt_projectedEncoding hA h (Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate hb) (zs.map star)
      (phases_conjugate zs hzs))
  simpa only [realPartQSVT, realPartPolynomial_responseP, map_smul, map_add] using hc

omit [Fintype I] in

theorem hamiltonian_phase_projectedEncoding {B : Matrix I I ℂ} {V : Matrix H H ℂ}
    {F : Matrix H I ℂ} (h : ProjectedUnitaryEncoding B V F F)
    {z : ℂ} (hz : IsPhase z) : ProjectedUnitaryEncoding (z • B) (z • V) F F := by
  have hu : z ∈ unitary ℂ := ⟨hz, by simpa only [IsPhase, mul_comm] using hz⟩
  refine ⟨Unitary.smul_mem_of_mem hu h.unitary, h.left_isometry, h.right_isometry, ?_⟩
  rw [compress_smul, h.encoded]

end SameFrame

theorem hamiltonian_realPart_of_completion {p : Polynomial ℝ} {base : ℂ} {zs : List ℂ}
    (hp : responseP base zs + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs) =
      C (2 : ℂ) * p.map Complex.ofRealHom) :
    realPartPolynomial (responseP base zs) = p.map Complex.ofRealHom := by
  change (2 : ℂ)⁻¹ • (responseP base zs +
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs)) = _
  rw [hp, Polynomial.smul_eq_C_mul, ← mul_assoc, ← C_mul]
  norm_num

noncomputable def hamiltonianCosine (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  C (1 / 4) * cosineTaylorPolynomial t n

noncomputable def hamiltonianSine (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  C (1 / 4) * sineTaylorPolynomial t n

theorem hamiltonianTaylor_phases (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) (hE : exponentialTaylorError t n < 1) :
    ∃ (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ),
      IsPhase bc ∧ (∀ z ∈ zc, IsPhase z) ∧ zc.length = 2 * n ∧
      IsPhase bs ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = 2 * n + 1 ∧
      realPartPolynomial (responseP bc zc) = (hamiltonianCosine t n).map Complex.ofRealHom ∧
      realPartPolynomial (responseP bs zs) = (hamiltonianSine t n).map Complex.ofRealHom := by
  have hcd : (hamiltonianCosine t n).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    apply degree_le_of_natDegree_le
    exact (natDegree_C_mul_le _ _).trans ((cosineTaylorPolynomial_natDegree_le t n).trans
      (by omega))
  have hsd : (hamiltonianSine t n).degree ≤ ((2 * n + 1 : ℕ) : WithBot ℕ) := by
    apply degree_le_of_natDegree_le
    exact (natDegree_C_mul_le _ _).trans ((sineTaylorPolynomial_natDegree_le t n).trans
      (by omega))
  have hcp : HasRealParity (2 * n) (hamiltonianCosine t n) := by
    simp [HasRealParity, hamiltonianCosine, cosineTaylorPolynomial_comp_neg_X, pow_mul]
  have hsp : HasRealParity (2 * n + 1) (hamiltonianSine t n) := by
    simp [HasRealParity, hamiltonianSine, sineTaylorPolynomial_comp_neg_X, pow_add, pow_mul]
  obtain ⟨bc, zc, hbc, hzc, hlc, hpc, _⟩ := exists_phases_of_strict hcd hcp
    (fun x hx => (scaledCosineTaylorPolynomial_abs_lt_half t n hn hE hx).trans (by norm_num))
  obtain ⟨bs, zs, hbs, hzs, hls, hps, _⟩ := exists_phases_of_strict hsd hsp
    (fun x hx => (scaledSineTaylorPolynomial_abs_lt_half t n hn hE hx).trans (by norm_num))
  exact ⟨bc, zc, bs, zs, hbc, hzc, hlc, hbs, hzs, hls,
    hamiltonian_realPart_of_completion hpc, hamiltonian_realPart_of_completion hps⟩

theorem exponentialTaylorPolynomial_eq_trig (t : ℝ) (n : ℕ) :
    exponentialTaylorPolynomial t n =
      (cosineTaylorPolynomial t n).map Complex.ofRealHom -
        C Complex.I * (sineTaylorPolynomial t n).map Complex.ofRealHom := by
  simp only [exponentialTaylorPolynomial, cosineTaylorPolynomial, sineTaylorPolynomial,
    Polynomial.map_sum, Polynomial.map_monomial, Finset.mul_sum, ← Finset.sum_sub_distrib,
    C_mul_monomial, ← monomial_sub]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

section Construction
variable {H I : Type*} [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]

noncomputable def hamiltonianCircuit (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ) :
    Matrix (Bool × (Bool × H)) (Bool × (Bool × H)) ℂ :=
  averageCircuit (realPartQSVT U (rangeProjector F) (rangeProjector F) bc zc)
    ((-Complex.I) • realPartQSVT U (rangeProjector F) (rangeProjector F) bs zs)

noncomputable def hamiltonianFrame (F : Matrix H I ℂ) : Matrix (Bool × (Bool × H)) I ℂ :=
  averageFrame (averageFrame F)

private theorem hamiltonian_trig_matrix (A : Matrix I I ℂ) (t : ℝ) (n : ℕ) :
    (2 : ℂ)⁻¹ • (aeval A ((hamiltonianCosine t n).map Complex.ofRealHom) +
      (-Complex.I) • aeval A ((hamiltonianSine t n).map Complex.ofRealHom)) =
      (8 : ℂ)⁻¹ • aeval A (exponentialTaylorPolynomial t n) := by
  rw [exponentialTaylorPolynomial_eq_trig]
  simp only [hamiltonianCosine, hamiltonianSine, Polynomial.map_mul, Polynomial.map_C,
    map_mul, map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul]
  norm_num
  module

theorem hamiltonianTaylor_projectedEncoding
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ}
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (t : ℝ) (n : ℕ) (hn : 2 * |t| ≤ (n : ℝ) + 1) (hE : exponentialTaylorError t n < 1) :
    ∃ (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ),
      IsPhase bc ∧ (∀ z ∈ zc, IsPhase z) ∧ zc.length = 2 * n ∧
      IsPhase bs ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = 2 * n + 1 ∧
      ProjectedUnitaryEncoding ((8 : ℂ)⁻¹ • aeval A (exponentialTaylorPolynomial t n))
        (hamiltonianCircuit U F bc zc bs zs) (hamiltonianFrame F) (hamiltonianFrame F) := by
  obtain ⟨bc, zc, bs, zs, hbc, hzc, hlc, hbs, hzs, hls, hc, hs⟩ :=
    hamiltonianTaylor_phases t n hn hE
  have hcos := hermitian_realPart_projectedEncoding hA h hbc zc hzc
  have hsin := hermitian_realPart_projectedEncoding hA h hbs zs hzs
  rw [hc] at hcos
  rw [hs] at hsin
  have hout := average_projectedEncoding hcos
    (hamiltonian_phase_projectedEncoding hsin (z := -Complex.I) (by simp [IsPhase]))
  rw [hamiltonian_trig_matrix] at hout
  exact ⟨bc, zc, bs, zs, hbc, hzc, hlc, hbs, hzs, hls, hout⟩

theorem hamiltonianSimulation_exists
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ}
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ),
      IsPhase bc ∧ (∀ z ∈ zc, IsPhase z) ∧ zc.length = 2 * n ∧
      IsPhase bs ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = 2 * n + 1 ∧
      BlockEncoding (hamiltonianEvolution A t) (hamiltonianCircuit U F bc zc bs zs)
        (hamiltonianFrame F) (hamiltonianFrame F) 8 ε := by
  obtain ⟨N, hN⟩ := matrixTaylor_eventually_error_lt A t hε
  obtain ⟨M, hM⟩ := exponentialTaylor_eventually_error_lt t zero_lt_one
  let n := max N M
  have ha := hN n (le_max_left _ _)
  have hs := hM n (le_max_right _ _)
  obtain ⟨bc, zc, bs, zs, hbc, hzc, hlc, hbs, hzs, hls, hp⟩ :=
    hamiltonianTaylor_projectedEncoding hA h t n hs.1 hs.2.1
  refine ⟨n, bc, zc, bs, zs, hbc, hzc, hlc, hbs, hzs, hls,
    hp.unitary, hp.left_isometry, hp.right_isometry, by norm_num, hε.le, ?_⟩
  rw [hp.encoded]
  have hscale : (8 : ℝ) • ((8 : ℂ)⁻¹ • aeval A (exponentialTaylorPolynomial t n)) =
      aeval A (exponentialTaylorPolynomial t n) := by
    ext i j
    norm_num [Matrix.smul_apply, Complex.real_smul]
    ring
  rw [hscale, norm_sub_rev]
  exact ha.le

end Construction
end Qatlib.Concepts.QspSimulation.Achievability
