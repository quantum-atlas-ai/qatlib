/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 3 — Eigenvalue transformation

Source: arXiv:2105.02859v3, Sec. IV B, Theorem 3, Eqs. (29)--(32) (metadata
lines 337--363).  For a Hermitian block encoding `H = Π U Π` and a completed
response polynomial `P` of degree `d` (the printed conditions (i)--(iii) of
Theorem 1),

* `d` odd:  `Π_{φ₁} U ∏_{k} Π_{φ_{2k}} U† Π_{φ_{2k+1}} U = Π [P(H) ·; · ·]`, and
* `d` even: `∏_{k} Π_{φ_{2k-1}} U Π_{φ_{2k}} U† = Π [P(H) ·; · ·]`,

where `P(H) = Σ_λ P(λ) |λ⟩⟨λ|`.

The paper-layer statement below realizes the word as the library's alternating
phase product `phasedAlternating` with the range projector of the encoding
frame, and identifies the corner with `aeval H P`.  The two algebraic
ingredients are

* the whole-matrix QSVT dilation identity
  `qsvt_odd_eq_dilation` / `qsvt_even_left_eq_dilation`, and
* the parity block computation for the Hermitian dilation (`toBlocks₁₂` for odd
  `P`, `toBlocks₁₁` for even `P`), proved here over `ℂ` from the parity
  factorization `P(X) = X q(X²)` resp. `P(X) = q(X²)`.

Reused FQNs:
`QuantumAlgorithm.Concepts.CoherentSim.CoherentOAA.qsvt_odd_eq_dilation`,
`QuantumAlgorithm.Concepts.CoherentSim.CoherentOAA.qsvt_even_left_eq_dilation`,
`QuantumAlgorithm.Concepts.CoherentSim.CoherentOAA.aeval_oddSingularPolynomial`,
`aeval_evenSingularPolynomial`,
`QuantumAlgorithm.Papers.QSingValue19.PhaseExistence.PhaseSynthesis.completedPair_iff_response`.

Boundary: matrix-level corner identity; the paper's Π-controlled-NOT gate
assembly and the polynomial-degree/parity conditions are represented by
`CompletedPair`, not re-derived as a circuit.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Papers.GrandUnif21.MainResults.EigenvalueTransformation

/-! ### Polynomial parity factorization over `ℂ` -/

/-- An even complex polynomial has no odd-degree coefficients.  This is the
complex version of the real lemma used by the Hermitian dilation computation. -/
private theorem coeff_zero_of_odd_complex {f : Polynomial ℂ}
    (hf : f.comp (-X) = f) {k : ℕ} (hk : ¬ 2 ∣ k) : f.coeff k = 0 := by
  have he := congrArg (fun q : Polynomial ℂ => q.coeff k) hf
  have hx : (-X : Polynomial ℂ) = C (-1) * X := by simp
  have ho : Odd k := Nat.not_even_iff_odd.mp (fun h => hk h.two_dvd)
  simp only [hx, comp_C_mul_X_coeff, ho.neg_one_pow] at he
  have h2 : (2 : ℂ) * f.coeff k = 0 := by linear_combination -he
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Every even complex polynomial is recovered from its contraction by `X²`. -/
theorem comp_square_contract_of_even_complex {f : Polynomial ℂ}
    (hf : f.comp (-X) = f) : (contract 2 f).comp (X ^ 2) = f := by
  rw [← expand_eq_comp_X_pow (R := ℂ)]
  ext k
  rw [coeff_expand (by decide : 0 < 2), coeff_contract (by decide : 2 ≠ 0)]
  split_ifs with hk
  · rw [Nat.div_mul_cancel hk]
  · exact (coeff_zero_of_odd_complex hf hk).symm

/-- An even-degree coefficient of an odd complex polynomial vanishes. -/
private theorem coeff_zero_of_even_odd {p : Polynomial ℂ}
    (hp : p.comp (-X) = -p) {k : ℕ} (hk : 2 ∣ k) : p.coeff k = 0 := by
  have he := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  have hx : (-X : Polynomial ℂ) = C (-1) * X := by simp
  have hk1 : (-1 : ℂ) ^ k = 1 := by
    obtain ⟨m, rfl⟩ := hk
    simp [pow_mul]
  simp only [hx, comp_C_mul_X_coeff, hk1, coeff_neg] at he
  have h2 : (2 : ℂ) * p.coeff k = 0 := by linear_combination he
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- An odd complex polynomial factors as `X · q(X²)`. -/
theorem odd_polynomial_factor_complex {p : Polynomial ℂ}
    (hp : p.comp (-X) = -p) : ∃ q : Polynomial ℂ, p = X * q.comp (X ^ 2) := by
  have hc : p.coeff 0 = 0 := coeff_zero_of_even_odd hp (by norm_num)
  have hdiv : X * p.divX = p := by
    simpa only [hc, C_0, add_zero] using (Polynomial.X_mul_divX_add p)
  have heven : p.divX.comp (-X) = p.divX := by
    apply mul_left_cancel₀ (show (-X : Polynomial ℂ) ≠ 0 by simp)
    calc
      (-X) * p.divX.comp (-X) = (X * p.divX).comp (-X) := by
        simp only [mul_comp, X_comp]
      _ = p.comp (-X) := congrArg (fun q : Polynomial ℂ => q.comp (-X)) hdiv
      _ = -p := hp
      _ = (-X) * p.divX := by rw [neg_mul, hdiv]
  refine ⟨contract 2 p.divX, ?_⟩
  rw [comp_square_contract_of_even_complex heven]
  exact hdiv.symm

/-! ### Blocks of the Hermitian dilation -/

/-- Odd parity: the upper-right block of `P` evaluated on the Hermitian
dilation of a Hermitian `H` is ordinary evaluation `P(H)`. -/
theorem toBlocks₁₂_aeval_hermitianDilation_of_odd {I : Type*} [Fintype I]
    [DecidableEq I] (H : Matrix I I ℂ) (hH : Hᴴ = H) {p : Polynomial ℂ}
    (hp : p.comp (-X) = -p) :
    (aeval (hermitianDilation H) p).toBlocks₁₂ = aeval H p := by
  obtain ⟨q, hq⟩ := odd_polynomial_factor_complex hp
  have hm : p = oddSingularPolynomial q := by
    rw [hq, oddSingularPolynomial, evenSingularPolynomial]
  rw [hm, aeval_oddSingularPolynomial]
  simp only [Matrix.toBlocks_fromBlocks₁₂, hH]
  rw [oddSingularPolynomial, evenSingularPolynomial, Polynomial.aeval_mul,
    Polynomial.aeval_X, Polynomial.aeval_comp, Polynomial.aeval_X_pow, pow_two]

/-- Even parity: the upper-left block of `P` evaluated on the Hermitian
dilation of a Hermitian `H` is ordinary evaluation `P(H)`. -/
theorem toBlocks₁₁_aeval_hermitianDilation_of_even {I : Type*} [Fintype I]
    [DecidableEq I] (H : Matrix I I ℂ) (hH : Hᴴ = H) {p : Polynomial ℂ}
    (hp : p.comp (-X) = p) :
    (aeval (hermitianDilation H) p).toBlocks₁₁ = aeval H p := by
  let q := contract 2 p
  have hq : q.comp (X ^ 2) = p := comp_square_contract_of_even_complex hp
  have hm : p = evenSingularPolynomial q := by
    rw [← hq, evenSingularPolynomial]
  rw [hm, aeval_evenSingularPolynomial]
  simp only [Matrix.toBlocks_fromBlocks₁₁, hH]
  rw [evenSingularPolynomial, Polynomial.aeval_comp, Polynomial.aeval_X_pow, pow_two]

/-! ### Theorem 3 -/

/-- GrandUnif21 Theorem 3, odd-`d` case, Eq. (32): for a Hermitian projected
encoding `H = Π U Π` and a completed response pair `(P,Q)` of odd degree `d`,
there is a legal phase table of length `d` whose alternating word compresses to
`P(H) = aeval H P` on the encoded subspace. -/
theorem source_theorem3_eigenvalue_odd
    {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {Hm : Matrix I I ℂ} (hH : Hm.IsHermitian) {U : Matrix H H ℂ}
    {L : Matrix H I ℂ} (h : ProjectedUnitaryEncoding Hm U L L)
    {d : ℕ} {P Q : Polynomial ℂ} (hpair : CompletedPair d P Q)
    (hodd : d % 2 = 1) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
        compress L (phasedAlternating U (rangeProjector L) (rangeProjector L) base zs) L =
          aeval Hm P := by
  obtain ⟨base, zs, hb, hzs, hlen, hP, hQ⟩ := completedPair_iff_response.mp hpair
  have hpar : (responseP base zs).comp (-X) = -responseP base zs := by
    have hp := hpair.parityP
    change P.comp (-X) = C ((-1 : ℂ) ^ d) * P at hp
    have ho : Odd d := Nat.odd_iff.mpr hodd
    rw [ho.neg_one_pow, C_neg, C_1, neg_one_mul] at hp
    rw [hP]
    exact hp
  have hs : zs.length % 2 = 1 := by rw [hlen]; exact hodd
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  rw [qsvt_odd_eq_dilation h base zs hs, hP]
  exact toBlocks₁₂_aeval_hermitianDilation_of_odd (I := I) Hm hH.eq (hP ▸ hpar)

/-- GrandUnif21 Theorem 3, even-`d` case, Eq. (30): for a Hermitian projected
encoding `H = Π U Π` and a completed response pair `(P,Q)` of even degree `d`,
there is a legal phase table of length `d` whose alternating word compresses to
`P(H) = aeval H P` on the encoded subspace. -/
theorem source_theorem3_eigenvalue_even
    {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {Hm : Matrix I I ℂ} (hH : Hm.IsHermitian) {U : Matrix H H ℂ}
    {L : Matrix H I ℂ} (h : ProjectedUnitaryEncoding Hm U L L)
    {d : ℕ} {P Q : Polynomial ℂ} (hpair : CompletedPair d P Q)
    (heven : d % 2 = 0) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
        compress L (phasedAlternating U (rangeProjector L) (rangeProjector L) base zs) L =
          aeval Hm P := by
  obtain ⟨base, zs, hb, hzs, hlen, hP, hQ⟩ := completedPair_iff_response.mp hpair
  have hpar : (responseP base zs).comp (-X) = responseP base zs := by
    have hp := hpair.parityP
    change P.comp (-X) = C ((-1 : ℂ) ^ d) * P at hp
    have he : Even d := Nat.even_iff.mpr heven
    rw [he.neg_one_pow, C_1, one_mul] at hp
    rw [hP]
    exact hp
  have hs : zs.length % 2 = 0 := by rw [hlen]; exact heven
  refine ⟨base, zs, hb, hzs, hlen, ?_⟩
  rw [qsvt_even_left_eq_dilation h base zs hs, hP]
  exact toBlocks₁₁_aeval_hermitianDilation_of_even (I := I) Hm hH.eq (hP ▸ hpar)

end Qatlib.Papers.GrandUnif21.MainResults.EigenvalueTransformation
