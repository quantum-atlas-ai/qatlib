/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Defs
public import Qatlib.Concepts.BosonFock.BosonOperators.CoeffPoly
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-! # The actual fixed-source coefficient and polynomial presentations

Aaronson--Arkhipov, arXiv:1011.3245v1, Section 3.2. The historical concrete
polynomial definitions are retained with the current coefficient API. The
occupation-to-polynomial map and commutation with actual linear substitution
are proved. Gaussian invariance and the physical-unitary bridge are separate.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockModel
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
open Qatlib.Concepts.BosonFock.BosonOperators
open MvPolynomial ComplexConjugate
open scoped ComplexConjugate

/-! ## Polynomial evaluation and the coefficient vector -/

/-- Evaluation of the degree-`n` polynomial with coefficient vector `a` at the
point `x`: `p(x) = Σ_S a_S x^S`, `x^S = ∏_i x_i^{s_i}` (p. 21). -/
noncomputable def polyEval {m n : ℕ} (a : FockCoeff m n) (x : Fin m → ℂ) : ℂ :=
  ∑ S : FockOccupation m n, a S * ∏ i : Fin m, (x i) ^ ((S.1 i : ℕ))

/-- The occupation vector of `S` as a finitely supported exponent function. -/
noncomputable def occFinsupp {m n : ℕ} (S : FockOccupation m n) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (S.1 i : ℕ))

/-- The occupation count `occFinsupp S` evaluates at mode `i` to the exponent
`s_i` stored in `S` (definitional unfolding of `occFinsupp`). -/
@[simp] theorem occApply {m n : ℕ} (S : FockOccupation m n) (i : Fin m) :
    occFinsupp S i = (S.1 i : ℕ) := rfl

/-- The polynomial with coefficient vector `a`, as an `MvPolynomial`. -/
noncomputable def polyOfCoeff {m n : ℕ} (a : FockCoeff m n) : MvPolynomial (Fin m) ℂ :=
  ∑ S : FockOccupation m n, monomial (occFinsupp S) (a S)

/-- Coefficient vector of an `MvPolynomial`, restricted to degree-`n` occupations. -/
noncomputable def coeffVec {m n : ℕ} (p : MvPolynomial (Fin m) ℂ) : FockCoeff m n :=
  fun S => p.coeff (occFinsupp S)

/-- The linear substitution `U[p]`: each variable `x_i` is replaced by the
linear form `Σ_j U_{i,j} x_j` (p. 23). -/
noncomputable def substPoly {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (p : MvPolynomial (Fin m) ℂ) : MvPolynomial (Fin m) ℂ :=
  aeval (fun i => ∑ j : Fin m, C (U i j) * X j) p

/-- The paper's operator `φ(U)` on the coefficient picture: substitute `U`
into the polynomial and read off the degree-`n` coefficients (p. 24). -/
noncomputable def phi {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (a : FockCoeff m n) : FockCoeff m n :=
  coeffVec (substPoly U (polyOfCoeff a))

/-- The (unnormalized) basis state `|S⟩` as a coefficient vector: `1` at `S`. -/
noncomputable def basisCoeff {m n : ℕ} (S : FockOccupation m n) : FockCoeff m n :=
  fun X => if X = S then 1 else 0

/-- The normalized physical state `|S⟩ = x^S/√(s₁!⋯s_m!)` in the coefficient
picture (p. 24). -/
noncomputable def stateVec {m n : ℕ} (S : FockOccupation m n) : FockCoeff m n :=
  fun X =>
    if X = S then (((Real.sqrt (((occFactorial S : ℕ) : ℝ)) : ℝ)) : ℂ)⁻¹ else 0

/-- The quantum amplitude `⟨S| φ(U) |T⟩` (p. 27), in the coefficient picture. -/
noncomputable def fockAmplitude {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) : ℂ :=
  fockInner (stateVec S) (phi U (stateVec T))


/-- Diagonal action `diag(λ)[p]`: multiply the coefficient of `x^S` by
`λ^S = ∏_i λ_i^{s_i}` (p. 23). -/
noncomputable def diagAct {m n : ℕ} (lam : Fin m → ℂ) (a : FockCoeff m n) :
    FockCoeff m n :=
  fun S => a S * ∏ i : Fin m, (lam i) ^ ((S.1 i : ℕ))

/-- The diagonal case of Theorem 17 (p. 23):
`⟨p, diag(λ)[q]⟩ = ⟨diag(conj λ)[p], q⟩`.  This is the paper's first step. -/
theorem diagAdjoint {m n : ℕ} (lam : Fin m → ℂ) (a b : FockCoeff m n) :
    fockInner a (diagAct lam b) = fockInner (diagAct (fun i => conj (lam i)) a) b := by
  unfold fockInner diagAct
  refine Finset.sum_congr rfl ?_
  intro S _
  rw [map_mul, map_prod]
  simp only [map_pow, Complex.conj_conj]
  ring

/-- The Fock norm squared is nonnegative (p. 23): `‖p‖²_Fock ≥ 0`. -/
theorem normNonneg {m n : ℕ} (a : FockCoeff m n) :
    0 ≤ fockNormSq a := by
  unfold fockNormSq
  refine Finset.sum_nonneg ?_
  intro S _
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

/-- The Fock norm squared equals the real part of the Fock inner product
`⟨p,p⟩` (p. 23). -/
theorem normEqReInner {m n : ℕ} (a : FockCoeff m n) :
    fockNormSq a = (fockInner a a).re := by
  unfold fockNormSq fockInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro S _
  rw [Complex.mul_re, Complex.mul_re]
  simp [Complex.normSq]

/-- The row multiset of `S`, as a list of mode indices (the paper's ordering of
the `s_i` copies of row `i`). -/
noncomputable def occRows {m n : ℕ} (S : FockOccupation m n) : List (Fin m) :=
  bosonRows (fun i : Fin m => (S.1 i : ℕ))

/-- The row multiset of an `n`-photon occupation pattern has exactly `n`
entries (the total photon number is `n`). -/
theorem occRows_length {m n : ℕ} (S : FockOccupation m n) : (occRows S).length = n :=
  (bosonRows_length (fun i : Fin m => (S.1 i : ℕ))).trans S.2

/-- The `k`-th element of the row multiset of `S`. -/
noncomputable def occPick {m n : ℕ} (S : FockOccupation m n) (k : Fin n) : Fin m :=
  (occRows S).get ⟨k.val, by rw [occRows_length]; exact k.isLt⟩

/-- The paper's `U_{S,T}` (p. 26): the `n × n` matrix obtained from `U` by
taking `s_i` copies of row `i` (for `S`) and `t_j` copies of column `j`
(for `T`). -/
noncomputable def fockSubmatrix {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (S T : FockOccupation m n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => U (occPick S i) (occPick T j)

/-- Coefficients of the substituted monomial `U[x^T]`: the coefficient of
`x^S` is the sum over all functions `f : Fin n → Fin m` with fibre
multiplicities `S` of `∏_k U_{t_k, f(k)}`. -/
noncomputable def polyActGenCoeff {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (T : FockOccupation m n) (S : FockOccupation m n) : ℂ :=
  ∑ f : Fin n → Fin m,
    if (∀ i : Fin m,
        (Finset.univ.filter (fun k : Fin n => f k = i)).card = (S.1 i).val)
      then ∏ k : Fin n, U (occPick T k) (f k) else 0

/-- The actual coefficient-vector polynomial map is injective (Theorem 19, first part). -/
theorem polyInjective {m n : ℕ} : Function.Injective (polyOfCoeff (m := m) (n := n)) :=
  Qatlib.Concepts.BosonFock.BosonOperators.CoeffPoly.polyInjective

/-- Actual mode substitution stays in the homogeneous sector, so coefficient readback is exact. -/
theorem substCommutes {m n : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (a : FockCoeff m n) :
    polyOfCoeff (phi U a) = substPoly U (polyOfCoeff a) := by
  exact Qatlib.Concepts.BosonFock.BosonOperators.CoeffPoly.reconstruct _
    (Qatlib.Concepts.BosonFock.BosonOperators.CoeffPoly.substDegree U a)

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.FockModel
