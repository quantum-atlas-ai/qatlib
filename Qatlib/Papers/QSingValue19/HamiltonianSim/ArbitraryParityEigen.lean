/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.Phase
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Qatlib.Concepts.QsvtCore.PhaseExistence.QsvtCore
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceModulusTransport

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 56 — polynomial eigenvalue transformation of arbitrary parity

Source: Gilyén–Su–Low–Wiebe, *Quantum singular value transformation and
beyond*, arXiv:1806.01838v1, Theorem 56, printed p. 48.

The printed theorem removes the parity constraint of Corollary 18 at the price
of a factor `1/2` in the target.  Its proof splits an arbitrary real polynomial
`P` into the even and odd parts

```
P_even(x) := P(x) + P(-x),      P_odd(x) := P(x) - P(-x),
```

which satisfy `P_even + P_odd = 2P` and, when `|P| ≤ 1/2` on `[-1,1]`, are both
bounded by one there.  Corollary 18 (source-length real phase synthesis)
compiles each part into a projected unitary encoding, and an equal-weight
linear combination of the two circuits encodes their average, which is `P`.

This module formalizes the mathematical core of that argument:

* the even/odd split, its degree, parity, boundedness and the factorization
  `P_even = Q(X²)`, `P_odd = X · R(X²)` used by the real QSVT responses;
* the identification of the even and odd singular transforms of a Hermitian
  matrix with the ordinary polynomial functional calculus;
* a concrete equal-weight direct-sum combination of two projected unitary
  encodings.

It does **not** assert the printed gate/query count, the ancilla accounting, or
the error propagation `4d√(ε/α) + δ` of an approximate `(α,a,ε)`-encoding; those
are recorded as open obligations in the PR description.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.HamiltonianSim

open Qatlib.Concepts.PhaseGeometry.Phase
open Matrix Polynomial
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CoherentSim.CoherentOAA
open scoped Matrix.Norms.L2Operator

/-! ## The even/odd split of a real polynomial -/

/-- `P_even(x) = P(x) + P(-x)`; the complementary even part of `P`.  The
printed theorem uses this unnormalized split so that the half-weight linear
combination of the two compiled responses is exactly `P`. -/
def evenPart (P : Polynomial ℝ) : Polynomial ℝ := P + P.comp (-X)

/-- `P_odd(x) = P(x) - P(-x)`; the complementary odd part of `P`. -/
def oddPart (P : Polynomial ℝ) : Polynomial ℝ := P - P.comp (-X)

/-- `P_even + P_odd = P + P`; this is the polynomial identity behind the final
factor `1/2` of Theorem 56. -/
theorem evenPart_add_oddPart (P : Polynomial ℝ) :
    evenPart P + oddPart P = P + P := by
  simp only [evenPart, oddPart]
  abel

/-- The even part is invariant under `x ↦ -x`. -/
theorem evenPart_comp_neg (P : Polynomial ℝ) :
    (evenPart P).comp (-X) = evenPart P := by
  simp only [evenPart, add_comp]
  rw [comp_neg_X_comp_neg_X]
  abel

/-- The odd part changes sign under `x ↦ -x`. -/
theorem oddPart_comp_neg (P : Polynomial ℝ) :
    (oddPart P).comp (-X) = -oddPart P := by
  simp only [oddPart, sub_comp]
  rw [comp_neg_X_comp_neg_X]
  abel

/-- The even part evaluated at `x` is the symmetrization of `P`. -/
@[simp] theorem eval_evenPart (P : Polynomial ℝ) (x : ℝ) :
    (evenPart P).eval x = P.eval x + P.eval (-x) := by
  simp [evenPart]

/-- The odd part evaluated at `x` is the antisymmetrization of `P`. -/
@[simp] theorem eval_oddPart (P : Polynomial ℝ) (x : ℝ) :
    (oddPart P).eval x = P.eval x - P.eval (-x) := by
  simp [oddPart]

/-- On `[-1,1]`, the even part of a `1/2`-bounded polynomial is bounded by one. -/
theorem abs_eval_evenPart_le {P : Polynomial ℝ}
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ (1 / 2 : ℝ)) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |(evenPart P).eval x| ≤ 1 := by
  have hnx : -x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [eval_evenPart]
  calc
    |P.eval x + P.eval (-x)| ≤ |P.eval x| + |P.eval (-x)| := abs_add_le _ _
    _ ≤ 1 / 2 + 1 / 2 := add_le_add (hP x hx) (hP (-x) hnx)
    _ = 1 := by norm_num

/-- On `[-1,1]`, the odd part of a `1/2`-bounded polynomial is bounded by one. -/
theorem abs_eval_oddPart_le {P : Polynomial ℝ}
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ (1 / 2 : ℝ)) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |(oddPart P).eval x| ≤ 1 := by
  have hnx : -x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [eval_oddPart]
  calc
    |P.eval x - P.eval (-x)| ≤ |P.eval x| + |P.eval (-x)| := abs_sub _ _
    _ ≤ 1 / 2 + 1 / 2 := add_le_add (hP x hx) (hP (-x) hnx)
    _ = 1 := by norm_num

/-- The even part of a degree-`d` polynomial still has degree at most `d`. -/
theorem degree_evenPart_le {P : Polynomial ℝ} {d : ℕ} (h : P.degree ≤ (d : WithBot ℕ)) :
    (evenPart P).degree ≤ (d : WithBot ℕ) := by
  refine (degree_add_le _ _).trans (max_le h ?_)
  simpa using h

/-- The odd part of a degree-`d` polynomial still has degree at most `d`. -/
theorem degree_oddPart_le {P : Polynomial ℝ} {d : ℕ} (h : P.degree ≤ (d : WithBot ℕ)) :
    (oddPart P).degree ≤ (d : WithBot ℕ) := by
  refine (degree_sub_le _ _).trans (max_le h ?_)
  simpa using h

/-- For even `d`, `(-1)^d = 1`. -/
theorem neg_one_pow_eq_one_of_even {d : ℕ} (hd : d % 2 = 0) : ((-1 : ℝ) ^ d) = 1 := by
  have h : d = 2 * (d / 2) := by omega
  rw [h, pow_mul]
  norm_num

/-- For odd `d`, `(-1)^d = -1`. -/
theorem neg_one_pow_eq_neg_one_of_odd {d : ℕ} (hd : d % 2 = 1) : ((-1 : ℝ) ^ d) = -1 := by
  have h : d = 2 * (d / 2) + 1 := by omega
  rw [h, pow_succ, pow_mul]
  norm_num

/-- The even part satisfies the real parity condition at every even degree. -/
theorem hasRealParity_evenPart {P : Polynomial ℝ} {d : ℕ} (hd : d % 2 = 0) :
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (evenPart P) := by
  unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
  rw [evenPart_comp_neg, neg_one_pow_eq_one_of_even hd, map_one, one_mul]

/-- The odd part satisfies the real parity condition at every odd degree. -/
theorem hasRealParity_oddPart {P : Polynomial ℝ} {d : ℕ} (hd : d % 2 = 1) :
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (oddPart P) := by
  unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
  rw [oddPart_comp_neg, neg_one_pow_eq_neg_one_of_odd hd, map_neg, map_one, neg_one_mul]

/-- The even part is a polynomial in `X²`. -/
theorem evenPart_eq_contract_comp (P : Polynomial ℝ) :
    (contract 2 (evenPart P)).comp (X ^ 2) = evenPart P :=
  comp_square_contract_of_even (evenPart_comp_neg P)

/-- The odd part has zero constant coefficient. -/
theorem coeff_zero_oddPart (P : Polynomial ℝ) : (oddPart P).coeff 0 = 0 := by
  have hconst : (P.comp (-X)).coeff 0 = P.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
    simp
  rw [oddPart, coeff_sub, hconst, sub_self]

/-- The odd part is `X` times its quotient by `X`. -/
theorem oddPart_eq_X_mul_divX (P : Polynomial ℝ) :
    oddPart P = X * (oddPart P).divX := by
  have h := X_mul_divX_add (oddPart P)
  rw [coeff_zero_oddPart, map_zero, add_zero] at h
  exact h.symm

/-- The quotient `P_odd / X` is even. -/
theorem divX_oddPart_comp_neg (P : Polynomial ℝ) :
    ((oddPart P).divX).comp (-X) = (oddPart P).divX := by
  have hX : (X : Polynomial ℝ) ≠ 0 := X_ne_zero
  have hq : X * (oddPart P).divX = oddPart P := (oddPart_eq_X_mul_divX P).symm
  have h1 : (X * (oddPart P).divX).comp (-X) =
      -(X * ((oddPart P).divX).comp (-X)) := by
    rw [mul_comp, X_comp]
    simp
  have h2 : (X * (oddPart P).divX).comp (-X) = -(X * (oddPart P).divX) := by
    rw [hq, oddPart_comp_neg]
  rw [h1] at h2
  exact mul_left_cancel₀ hX (neg_injective h2)

/-- The odd part is `X` times an even polynomial in `X²`. -/
theorem oddPart_eq_X_mul_contract_comp (P : Polynomial ℝ) :
    oddPart P = X * ((contract 2 ((oddPart P).divX)).comp (X ^ 2)) := by
  calc oddPart P = X * (oddPart P).divX := oddPart_eq_X_mul_divX P
    _ = X * ((contract 2 ((oddPart P).divX)).comp (X ^ 2)) := by
        rw [comp_square_contract_of_even (divX_oddPart_comp_neg P)]

end Qatlib.Papers.QSingValue19.HamiltonianSim

/-! ## Eigenvalue transformation for Hermitian matrices

For a Hermitian matrix the even and odd singular transforms are the ordinary
polynomial functional calculus.  These bridges are what let the two compiled
real responses of Theorem 56 be combined into `P(A)`. -/

namespace Qatlib.Papers.QSingValue19.HamiltonianSim
namespace SpectralBridge

open Qatlib.Concepts.PhaseGeometry.Phase
open Matrix Polynomial
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CoherentSim.CoherentOAA

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Substituting `X²` then applying the polynomial functional calculus is the
functional calculus of `A * A`. -/
theorem aeval_comp_sq (A : Matrix I I ℂ) (q : Polynomial ℂ) :
    (aeval A) (q.comp (X ^ 2)) = aeval (A * A) q := by
  rw [Polynomial.aeval_comp]
  congr 1
  simp [pow_two]

/-- The even singular transform of a Hermitian matrix is its polynomial
functional calculus. -/
theorem rightSingularTransform_evenPart_eq_aeval
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (P : Polynomial ℝ) :
    rightSingularTransform A (fun x => (((evenPart P).eval x : ℝ) : ℂ)) =
      aeval A ((evenPart P).map Complex.ofRealHom) := by
  let q : Polynomial ℝ := contract 2 (evenPart P)
  have hq : q.comp (X ^ 2) = evenPart P := evenPart_eq_contract_comp P
  have hqC : (q.map Complex.ofRealHom).comp (X ^ 2) =
      (evenPart P).map Complex.ofRealHom := by
    have h : Polynomial.map Complex.ofRealHom (q.comp (X ^ 2)) =
        Polynomial.map Complex.ofRealHom (evenPart P) := by rw [hq]
    simpa only [Polynomial.map_comp, Polynomial.map_X, Polynomial.map_pow] using h
  have hfun : (fun x : ℝ => Polynomial.eval ((x : ℂ) ^ 2)
      (q.map Complex.ofRealHom)) =
      (fun x : ℝ => (((evenPart P).eval x : ℝ) : ℂ)) := by
    funext x
    have hx : ((x : ℂ) ^ 2) = Complex.ofRealHom (x ^ 2) := by
      simp [pow_two]
    rw [hx, Polynomial.eval_map_apply]
    have hqeval : q.eval (x ^ 2) = (evenPart P).eval x := by
      have h : (q.comp (X ^ 2)).eval x = q.eval (x ^ 2) := by
        simp [Polynomial.eval_comp]
      rw [← h, hq]
    rw [hqeval]
    rfl
  have hgram := gram_aeval_eq_rightSingularTransform A (q.map Complex.ofRealHom)
  rw [show (fun x : ℝ => (((evenPart P).eval x : ℝ) : ℂ)) =
      (fun x : ℝ => Polynomial.eval ((x : ℂ) ^ 2)
        (q.map Complex.ofRealHom)) from hfun.symm]
  rw [← hgram]
  have hAA : Aᴴ * A = A * A := by rw [hA]
  rw [hAA, ← aeval_comp_sq A (q.map Complex.ofRealHom), hqC]

/-- The odd singular transform of a Hermitian matrix is its polynomial
functional calculus. -/
theorem oddSingularTransform_oddPart_eq_aeval
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (P : Polynomial ℝ) :
    oddSingularTransform A (fun x => (((oddPart P).eval x : ℝ) : ℂ)) =
      aeval A ((oddPart P).map Complex.ofRealHom) := by
  let q : Polynomial ℝ := contract 2 ((oddPart P).divX)
  have hq : oddPart P = X * (q.comp (X ^ 2)) := oddPart_eq_X_mul_contract_comp P
  have hqC : (oddPart P).map Complex.ofRealHom =
      X * (q.map Complex.ofRealHom).comp (X ^ 2) := by
    rw [hq, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp]
    simp
  have hfun : (fun x : ℝ => (x : ℂ) * Polynomial.eval ((x : ℂ) ^ 2)
      (q.map Complex.ofRealHom)) =
      (fun x : ℝ => (((oddPart P).eval x : ℝ) : ℂ)) := by
    funext x
    have hx : ((x : ℂ) ^ 2) = Complex.ofRealHom (x ^ 2) := by
      simp [pow_two]
    rw [hx, Polynomial.eval_map_apply]
    have hqeval : ((x : ℂ) * (((q.eval (x ^ 2) : ℝ)) : ℂ)) =
        (((oddPart P).eval x : ℝ) : ℂ) := by
      rw [hq, Polynomial.eval_mul, Polynomial.eval_X]
      simp
    exact hqeval
  have hgram := mul_gram_aeval_eq_oddSingularTransform A (q.map Complex.ofRealHom)
  rw [show (fun x : ℝ => (((oddPart P).eval x : ℝ) : ℂ)) =
      (fun x : ℝ => (x : ℂ) * Polynomial.eval ((x : ℂ) ^ 2)
        (q.map Complex.ofRealHom)) from hfun.symm]
  rw [← hgram]
  have hAA : Aᴴ * A = A * A := by rw [hA]
  rw [hAA, ← aeval_comp_sq A (q.map Complex.ofRealHom)]
  calc A * (aeval A) ((q.map Complex.ofRealHom).comp (X ^ 2))
      = (aeval A) (X : Polynomial ℂ) *
          (aeval A) ((q.map Complex.ofRealHom).comp (X ^ 2)) := by
          rw [Polynomial.aeval_X]
    _ = (aeval A) ((X : Polynomial ℂ) *
          (q.map Complex.ofRealHom).comp (X ^ 2)) := (Polynomial.aeval_mul A).symm
    _ = (aeval A) ((oddPart P).map Complex.ofRealHom) := by rw [hqC]

end SpectralBridge

end Qatlib.Papers.QSingValue19.HamiltonianSim

/-! ## Equal-weight direct-sum combination of two encodings -/

namespace Qatlib.Papers.QSingValue19.HamiltonianSim
namespace SumEncoding

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP

variable {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The positive weight `1/√2` used by the equal-weight linear combination. -/
def halfCoeff : ℂ := (Real.sqrt (1 / 2) : ℂ)

/-- The squared weight is `1/2`. -/
theorem halfCoeff_mul_self : halfCoeff * halfCoeff = (2 : ℂ)⁻¹ := by
  unfold halfCoeff
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The weight is real, hence self-adjoint. -/
theorem halfCoeff_star : star halfCoeff = halfCoeff := by
  unfold halfCoeff
  rw [Complex.star_def, Complex.conj_ofReal]

/-- A frame for a direct sum of two workspaces, with equal positive weights. -/
noncomputable def sumFrame (A B : Matrix H I ℂ) : Matrix (H ⊕ H) I ℂ :=
  Matrix.of (Sum.elim (fun h i => halfCoeff * A h i) (fun h i => halfCoeff * B h i))

omit [DecidableEq H] [Fintype I] in
/-- The direct-sum frame is isometric when both summands are. -/
theorem sumFrame_isIsometry {A B : Matrix H I ℂ}
    (hA : IsIsometry A) (hB : IsIsometry B) : IsIsometry (sumFrame A B) := by
  unfold IsIsometry
  ext i j
  have hAe : (∑ h, star (A h i) * A h j) = if i = j then 1 else 0 := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  have hBe : (∑ h, star (B h i) * B h j) = if i = j then 1 else 0 := by
    have := congrFun (congrFun hB i) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [sumFrame, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.conjTranspose_apply, star_mul, halfCoeff_star]
  rw [show (∑ h : H, star (A h i) * halfCoeff * (halfCoeff * A h j)) =
      halfCoeff * halfCoeff * (∑ h : H, star (A h i) * A h j) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => by ring)]
  rw [show (∑ h : H, star (B h i) * halfCoeff * (halfCoeff * B h j)) =
      halfCoeff * halfCoeff * (∑ h : H, star (B h i) * B h j) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => by ring)]
  rw [hAe, hBe, halfCoeff_mul_self]
  by_cases hij : i = j
  · subst hij; norm_num
  · simp [hij]

/-- The direct sum of two workspace unitaries. -/
noncomputable def sumCircuit (U V : Matrix H H ℂ) : Matrix (H ⊕ H) (H ⊕ H) ℂ :=
  Matrix.fromBlocks U 0 0 V

/-- A direct sum of unitaries is unitary. -/
theorem sumCircuit_unitary {U V : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) :
    sumCircuit U V ∈ Matrix.unitaryGroup (H ⊕ H) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU hV ⊢
  have hU' : (Uᴴ) * U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using hU
  have hV' : (Vᴴ) * V = 1 := by simpa only [Matrix.star_eq_conjTranspose] using hV
  show (Matrix.fromBlocks U 0 0 V)ᴴ * Matrix.fromBlocks U 0 0 V = 1
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [hU', hV']
  simp only [zero_add]
  rw [Matrix.fromBlocks_one]

omit [DecidableEq H] [Fintype I] [DecidableEq I] in
/-- Compression of a direct sum is the equal-weight average of the two
compressions. -/
theorem sumCircuit_compress {L₁ R₁ L₂ R₂ : Matrix H I ℂ} {U V : Matrix H H ℂ} :
    compress (sumFrame L₁ L₂) (sumCircuit U V) (sumFrame R₁ R₂) =
      (halfCoeff * halfCoeff) • (compress L₁ U R₁ + compress L₂ V R₂) := by
  ext o i
  simp only [compress, sumCircuit, sumFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    Matrix.smul_apply, Matrix.add_apply]
  simp only [mul_zero, zero_add, Finset.sum_const_zero, add_zero]
  have hS₁ : (∑ x : H, (∑ y : H, star (halfCoeff * L₁ y o) * U y x) *
      (halfCoeff * R₁ x i)) =
      halfCoeff * halfCoeff * (∑ x : H, (∑ y : H, star (L₁ y o) * U y x) * R₁ x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hinner : (∑ y : H, star (halfCoeff * L₁ y o) * U y x) =
        halfCoeff * (∑ y : H, star (L₁ y o) * U y x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [star_mul, halfCoeff_star]
      ring
    rw [hinner]
    ring
  have hS₂ : (∑ x : H, (∑ y : H, star (halfCoeff * L₂ y o) * V y x) *
      (halfCoeff * R₂ x i)) =
      halfCoeff * halfCoeff * (∑ x : H, (∑ y : H, star (L₂ y o) * V y x) * R₂ x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hinner : (∑ y : H, star (halfCoeff * L₂ y o) * V y x) =
        halfCoeff * (∑ y : H, star (L₂ y o) * V y x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [star_mul, halfCoeff_star]
      ring
    rw [hinner]
    ring
  rw [hS₁, hS₂, smul_eq_mul]
  ring

omit [Fintype I] in
/-- Two exact projected unitary encodings with possibly different frames admit
a concrete equal-weight direct-sum encoding of the half-sum target. -/
theorem sum_projectedEncoding {A₁ A₂ : Matrix I I ℂ} {U₁ U₂ : Matrix H H ℂ}
    {L₁ R₁ L₂ R₂ : Matrix H I ℂ}
    (h₁ : ProjectedUnitaryEncoding A₁ U₁ L₁ R₁)
    (h₂ : ProjectedUnitaryEncoding A₂ U₂ L₂ R₂) :
    ProjectedUnitaryEncoding ((halfCoeff * halfCoeff) • (A₁ + A₂))
      (sumCircuit U₁ U₂) (sumFrame L₁ L₂) (sumFrame R₁ R₂) := by
  refine ⟨sumCircuit_unitary h₁.unitary h₂.unitary,
    sumFrame_isIsometry h₁.left_isometry h₂.left_isometry,
    sumFrame_isIsometry h₁.right_isometry h₂.right_isometry, ?_⟩
  rw [sumCircuit_compress, h₁.encoded, h₂.encoded]

end SumEncoding

end Qatlib.Papers.QSingValue19.HamiltonianSim

/-! ## Theorem 56 -/

namespace Qatlib.Papers.QSingValue19.HamiltonianSim
namespace Theorem56

open Qatlib.Concepts.PhaseGeometry.Phase
open Matrix Polynomial
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.QsVtMain
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CoherentSim.CoherentOAA

variable {H I : Type*} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- **Theorem 56 (exact normalized core).**  Let `U` be an exact `(α,0)` block
encoding of a Hermitian matrix `A` with frames `L,R`, and let `P` be a real
polynomial of degree at most `d ≥ 2` with `|P| ≤ 1/2` on `[-1,1]`.  Then the
even/odd split of `P`, the source-length real phase synthesis applied to each
part, and the equal-weight direct-sum combination produce an explicit projected
unitary encoding of `P(A/α)`.

The circuit is built from the two real-part QSVT words
`realPartQSVT U ...` and `realPartQSVT Uᴴ ...`; no gate count, ancilla count or
approximate-encoding error propagation is asserted here. -/
theorem theorem56_arbitraryParity
    (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (U : Matrix H H ℂ) (L R : Matrix H I ℂ) (α : ℝ) (hα : 0 < α)
    (henc : BlockEncoding A U L R α 0)
    (P : Polynomial ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hdeg : P.degree ≤ (d : WithBot ℕ))
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ (1 / 2 : ℝ)) :
    ∃ (U' : Matrix ((Bool × H) ⊕ (Bool × H)) ((Bool × H) ⊕ (Bool × H)) ℂ)
      (L' R' : Matrix ((Bool × H) ⊕ (Bool × H)) I ℂ),
      ProjectedUnitaryEncoding
        (aeval ((α⁻¹ : ℝ) • A) (P.map Complex.ofRealHom)) U' L' R' := by
  let B : Matrix I I ℂ := (α⁻¹ : ℝ) • A
  have hαne : α ≠ 0 := ne_of_gt hα
  have hB : B.IsHermitian := by
    dsimp only [B]
    rw [Matrix.IsHermitian]
    rw [Matrix.conjTranspose_smul, hA]
    simp
  have hcomp : compress L U R = B := by
    have h0 : A = α • compress L U R := by
      have hn : ‖A - α • compress L U R‖ = 0 :=
        le_antisymm henc.error_le (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp hn)
    calc compress L U R = (α⁻¹ : ℝ) • (α • compress L U R) := by
          rw [smul_smul, inv_mul_cancel₀ hαne, one_smul]
      _ = (α⁻¹ : ℝ) • A := by rw [← h0]
  have hBenc : ProjectedUnitaryEncoding B U L R :=
    ⟨henc.unitary, henc.left_isometry, henc.right_isometry, hcomp⟩
  let dE : ℕ := if d % 2 = 0 then d else d + 1
  let dO : ℕ := if d % 2 = 0 then d + 1 else d
  have hdEpos : 0 < dE := by
    dsimp only [dE]
    split <;> omega
  have hdOpos : 0 < dO := by
    dsimp only [dO]
    split <;> omega
  have hdEeven : dE % 2 = 0 := by
    dsimp only [dE]
    split <;> omega
  have hdOodd : dO % 2 = 1 := by
    dsimp only [dO]
    split <;> omega
  have hdEd : d ≤ dE := by
    dsimp only [dE]
    split <;> omega
  have hdOd : d ≤ dO := by
    dsimp only [dO]
    split <;> omega
  have hdegE : (evenPart P).degree ≤ (dE : WithBot ℕ) := by
    refine le_trans (degree_evenPart_le hdeg) ?_
    exact_mod_cast hdEd
  have hdegO : (oddPart P).degree ≤ (dO : WithBot ℕ) := by
    refine le_trans (degree_oddPart_le hdeg) ?_
    exact_mod_cast hdOd
  obtain ⟨ΦE, hlenE, hreE⟩ :=
    source_length_real_phase_existence (evenPart P) dE hdEpos hdegE
      (hasRealParity_evenPart hdEeven)
      (fun x hx => abs_eval_evenPart_le hbound hx)
  obtain ⟨ΦO, hlenO, hreO⟩ :=
    source_length_real_phase_existence (oddPart P) dO hdOpos hdegO
      (hasRealParity_oddPart hdOodd)
      (fun x hx => abs_eval_oddPart_le hbound hx)
  have hone : IsPhase (1 : ℂ) := by simp [IsPhase]
  have hzE : ∀ z ∈ ΦE.map anglePhase, IsPhase z := by
    intro z hz
    obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hz
    exact anglePhase_isPhase φ
  have hzO : ∀ z ∈ ΦO.map anglePhase, IsPhase z := by
    intro z hz
    obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hz
    exact anglePhase_isPhase φ
  have hEven := realPartQSVT_even_right_singularEncoding hBenc (base := (1 : ℂ)) hone
    (ΦE.map anglePhase) hzE (by simpa [hlenE] using hdEeven)
  have hEven' : ProjectedUnitaryEncoding
      (aeval B ((evenPart P).map Complex.ofRealHom))
      (realPartQSVT Uᴴ (rangeProjector L) (rangeProjector R) (1 : ℂ) (ΦE.map anglePhase))
      (averageFrame R) (averageFrame R) := by
    have hfunE : (fun x : ℝ =>
        (((responseP (1 : ℂ) (ΦE.map anglePhase)).eval (x : ℂ)).re : ℂ)) =
        (fun x : ℝ => (((evenPart P).eval x : ℝ) : ℂ)) := by
      funext x
      exact congrArg (fun y : ℝ => (y : ℂ)) (hreE x)
    rw [hfunE] at hEven
    rw [SpectralBridge.rightSingularTransform_evenPart_eq_aeval B hB P] at hEven
    exact hEven
  have hOdd := realPartQSVT_odd_singularEncoding hBenc (base := (1 : ℂ)) hone
    (ΦO.map anglePhase) hzO (by simpa [hlenO] using hdOodd)
  have hOdd' : ProjectedUnitaryEncoding
      (aeval B ((oddPart P).map Complex.ofRealHom))
      (realPartQSVT U (rangeProjector R) (rangeProjector L) (1 : ℂ) (ΦO.map anglePhase))
      (averageFrame L) (averageFrame R) := by
    have hfunO : (fun x : ℝ =>
        (((responseP (1 : ℂ) (ΦO.map anglePhase)).eval (x : ℂ)).re : ℂ)) =
        (fun x : ℝ => (((oddPart P).eval x : ℝ) : ℂ)) := by
      funext x
      exact congrArg (fun y : ℝ => (y : ℂ)) (hreO x)
    rw [hfunO] at hOdd
    rw [SpectralBridge.oddSingularTransform_oddPart_eq_aeval B hB P] at hOdd
    exact hOdd
  have hsum := SumEncoding.sum_projectedEncoding hOdd' hEven'
  refine ⟨SumEncoding.sumCircuit
      (realPartQSVT U (rangeProjector R) (rangeProjector L) (1 : ℂ) (ΦO.map anglePhase))
      (realPartQSVT Uᴴ (rangeProjector L) (rangeProjector R) (1 : ℂ) (ΦE.map anglePhase)),
    SumEncoding.sumFrame (averageFrame L) (averageFrame R),
    SumEncoding.sumFrame (averageFrame R) (averageFrame R), ?_⟩
  have hhalf : SumEncoding.halfCoeff * SumEncoding.halfCoeff = (2 : ℂ)⁻¹ :=
    SumEncoding.halfCoeff_mul_self
  have hgoal : (2 : ℂ)⁻¹ •
      (aeval B ((evenPart P).map Complex.ofRealHom) +
        aeval B ((oddPart P).map Complex.ofRealHom)) =
      aeval B (P.map Complex.ofRealHom) := by
    rw [← Polynomial.aeval_add]
    have hp : (evenPart P).map Complex.ofRealHom + (oddPart P).map Complex.ofRealHom =
        P.map Complex.ofRealHom + P.map Complex.ofRealHom := by
      rw [← Polynomial.map_add, evenPart_add_oddPart, Polynomial.map_add]
    rw [hp, Polynomial.aeval_add, smul_add, ← add_smul]
    norm_num
  rw [hhalf] at hsum
  rw [add_comm (aeval B ((oddPart P).map Complex.ofRealHom))] at hsum
  simpa only [hgoal] using hsum

end Theorem56

end Qatlib.Papers.QSingValue19.HamiltonianSim
