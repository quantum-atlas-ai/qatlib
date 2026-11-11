/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT

/-!
# Hamiltonian simulation from polynomial phases

This module constructs Hamiltonian simulation block encodings from a same-frame projected
unitary encoding of a Hermitian matrix. The polynomial transformation step uses
`phasedAlternating` and `responseP`, while `realPartQSVT` extracts real polynomial responses.
This connects the quantum signal processing approach to Hamiltonian simulation [LowChuang2017]
with the projected encoding viewpoint of quantum singular value transformation
[GilyenSuLowWiebe2019].

The scaled Taylor polynomials `hamiltonianCosine` and `hamiltonianSine` are synthesized
separately and combined in `hamiltonianCircuit`, with two applications of `averageFrame`. The
resulting exact Taylor encoding has scale one eighth; convergence of the matrix Taylor
approximation yields `hamiltonianSimulation_exists`, with normalization factor `8` and arbitrary
positive error.

## Main statements

* `hermitian_qsvt_compress` identifies the compressed phased circuit with polynomial evaluation
  at the Hermitian matrix.
* `hamiltonianTaylor_phases` produces cosine and sine phase lists of lengths `2 * n` and `2 * n
  + 1`.
* `hamiltonianTaylor_projectedEncoding` constructs an exact projected encoding of the scaled
  Taylor polynomial.
* `hamiltonianSimulation_exists` produces a block encoding of `hamiltonianEvolution` at any
  positive precision.

## References

* [Low and Chuang, 2017][LowChuang2017]
* [Gilyen, Su, Low, and Wiebe, 2019][GilyenSuLowWiebe2019]
-/

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

/-- For a same-frame projected unitary encoding of a Hermitian matrix `A`, compressing the
phased alternating circuit gives `responseP` evaluated at `A`. -/
theorem hermitian_qsvt_compress {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {F : Matrix H I ℂ} (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (base : ℂ) (zs : List ℂ) :
    compress F (phasedAlternating U (rangeProjector F) (rangeProjector F) base zs) F =
      aeval A (responseP base zs) := by
  have ha : Aᴴ = A := hA
  have he := qsvt_operator_intertwiner h (S := A) (v := (1 : Matrix I I ℂ))
    (w := (1 : Matrix I I ℂ)) (by simp) (by simp [ha]) base zs
  simpa [compress, Matrix.mul_assoc, alternatingSource_eq] using he

/-- Unit-modulus base and list phases turn the phased alternating circuit into a projected
unitary encoding of `aeval A (responseP base zs)` when `A` is Hermitian. -/
theorem hermitian_qsvt_projectedEncoding {A : Matrix I I ℂ} {U : Matrix H H ℂ}
    {F : Matrix H I ℂ} (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ProjectedUnitaryEncoding (aeval A (responseP base zs))
      (phasedAlternating U (rangeProjector F) (rangeProjector F) base zs) F F := by
  exact ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.left_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.left_isometry, hermitian_qsvt_compress hA h base zs⟩

/-- For a Hermitian encoded matrix, `realPartQSVT` encodes the real-part response polynomial
evaluated at that matrix, using `averageFrame F` on both sides. -/
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

/-- Multiplying both an encoded matrix and its encoding unitary by the same unit-modulus scalar
preserves the projected unitary encoding with its original frames. -/
theorem hamiltonian_phase_projectedEncoding {B : Matrix I I ℂ} {V : Matrix H H ℂ}
    {F : Matrix H I ℂ} (h : ProjectedUnitaryEncoding B V F F)
    {z : ℂ} (hz : IsPhase z) : ProjectedUnitaryEncoding (z • B) (z • V) F F := by
  have hu : z ∈ unitary ℂ := ⟨hz, by simpa only [IsPhase, mul_comm] using hz⟩
  refine ⟨Unitary.smul_mem_of_mem hu h.unitary, h.left_isometry, h.right_isometry, ?_⟩
  rw [compress_smul, h.encoded]

end SameFrame

/-- If a response polynomial plus its coefficientwise conjugate equals twice a mapped real
polynomial, its `realPartPolynomial` is that mapped polynomial. -/
theorem hamiltonian_realPart_of_completion {p : Polynomial ℝ} {base : ℂ} {zs : List ℂ}
    (hp : responseP base zs + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs) =
      C (2 : ℂ) * p.map Complex.ofRealHom) :
    realPartPolynomial (responseP base zs) = p.map Complex.ofRealHom := by
  change (2 : ℂ)⁻¹ • (responseP base zs +
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs)) = _
  rw [hp, Polynomial.smul_eq_C_mul, ← mul_assoc, ← C_mul]
  norm_num

/-- The cosine Taylor polynomial multiplied by the constant `1 / 4`, used as the real cosine
response in the Hamiltonian circuit. -/
noncomputable def hamiltonianCosine (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  C (1 / 4) * cosineTaylorPolynomial t n

/-- The sine Taylor polynomial multiplied by the constant `1 / 4`, used as the real sine
response in the Hamiltonian circuit. -/
noncomputable def hamiltonianSine (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  C (1 / 4) * sineTaylorPolynomial t n

/-- Under the stated time-degree and Taylor-error bounds, there are unit-modulus cosine and sine
phase lists of lengths `2 * n` and `2 * n + 1`. Their real-part responses are the mapped
polynomials `hamiltonianCosine t n` and `hamiltonianSine t n`. -/
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

/-- Decomposes the complex exponential Taylor polynomial as the mapped cosine Taylor polynomial
minus `Complex.I` times the mapped sine Taylor polynomial. -/
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

/-- The averaging circuit combining the cosine `realPartQSVT` circuit with `-Complex.I` times
the sine `realPartQSVT` circuit. -/
noncomputable def hamiltonianCircuit (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ) :
    Matrix (Bool × (Bool × H)) (Bool × (Bool × H)) ℂ :=
  averageCircuit (realPartQSVT U (rangeProjector F) (rangeProjector F) bc zc)
    ((-Complex.I) • realPartQSVT U (rangeProjector F) (rangeProjector F) bs zs)

/-- The frame obtained by applying `averageFrame` twice to `F`, matching the two Boolean
registers of `hamiltonianCircuit`. -/
noncomputable def hamiltonianFrame (F : Matrix H I ℂ) : Matrix (Bool × (Bool × H)) I ℂ :=
  averageFrame (averageFrame F)

/-- The average of the scaled cosine polynomial evaluated at `A` and `-Complex.I` times the
scaled sine polynomial evaluated at `A` equals one eighth of the exponential Taylor
polynomial evaluated at `A`. -/
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

/-- For a same-frame encoding of a Hermitian matrix and the stated Taylor bounds, suitable
cosine and sine phases make `hamiltonianCircuit` a projected unitary encoding of one eighth
of the matrix Taylor polynomial. The phase lists have lengths `2 * n` and `2 * n + 1`. -/
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

/-- For every positive `ε`, a same-frame projected unitary encoding of a Hermitian matrix yields
a `hamiltonianCircuit` block encoding of `hamiltonianEvolution A t` with normalization `8`
and error `ε`. The construction supplies unit-modulus cosine and sine phase lists of lengths
`2 * n` and `2 * n + 1` for some `n`. -/
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
