/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Matrix.Basic

/-!
# Rational Hamiltonian data and spectral predicates

`QMatrix`, `SELData`, and `LHData` encode rational matrices and the threshold or term data used
in the paper's promise problems. The file defines real eigenvalue predicates, norm bounds,
promised local-Hamiltonian instances, and the ratio `ExpectedMu`, and proves trace identities
and spectral bounds for matrix powers. See [BravyiEtAl2008Stoquastic].

## Main statements

* `SELData.InLambda`: the entry and threshold conditions for the largest-eigenvalue problem.
* `LHData.InOmega`: the bundled Hamiltonian promise conditions.
* `ExpectedMu`: the ratio of total masses of successive matrix powers.
* `trace_pow_eq_sum_eigenvalues`: the spectral formula for the trace of a power.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

/-- Rational matrix entries indexed by pairs of Boolean strings of length `n`. -/
abbrev QMatrix (n : ℕ) := Sigma n → Sigma n → ℚ

namespace QMatrix

/-- The real matrix obtained by casting every rational entry of `A`. -/
def toReal {n : ℕ} (A : QMatrix n) : Matrix (Sigma n) (Sigma n) ℝ :=
  fun x y => (A x y : ℝ)

end QMatrix

/-- The existence of a nonzero real vector on which `G` acts by multiplication by `μ`. -/
def HasEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  ∃ v : ι → ℝ, v ≠ 0 ∧ G.mulVec v = μ • v

/-- The condition that `μ` is an eigenvalue and every real eigenvalue of `G` is at most `μ`. -/
def IsLargestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  HasEigenvalue G μ ∧ ∀ ν, HasEigenvalue G ν → ν ≤ μ

/-- The condition that `μ1` is an eigenvalue no greater than a largest eigenvalue and bounds
every eigenvalue unequal to that largest value. -/
def IsSecondLargestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ1 : ℝ) : Prop :=
  ∃ μ0, IsLargestEigenvalue G μ0 ∧ HasEigenvalue G μ1 ∧ μ1 ≤ μ0 ∧
    ∀ ν, HasEigenvalue G ν → ν = μ0 ∨ ν ≤ μ1

/-- The condition that `μ` is an eigenvalue and is at most every real eigenvalue of `G`. -/
def IsSmallestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  HasEigenvalue G μ ∧ ∀ ν, HasEigenvalue G ν → μ ≤ ν

/-- The condition that `μ1` is an eigenvalue no smaller than a smallest eigenvalue and is a
lower bound for every eigenvalue unequal to that smallest value. -/
def IsSecondSmallestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ1 : ℝ) : Prop :=
  ∃ μ0, IsSmallestEigenvalue G μ0 ∧ HasEigenvalue G μ1 ∧ μ0 ≤ μ1 ∧
    ∀ ν, HasEigenvalue G ν → ν = μ0 ∨ μ1 ≤ ν

/-- The bound `‖A *ᵥ v‖ ≤ C * ‖v‖` for every real-valued function `v`, using its function-space
norm. -/
def OperatorNormLE {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (C : ℝ) : Prop :=
  ∀ v : ι → ℝ, ‖A.mulVec v‖ ≤ C * ‖v‖

/-- Data for a largest-eigenvalue threshold problem: a bit length, a rational matrix, and upper
and lower rational thresholds. -/
structure SELData where

  n : ℕ

  G : QMatrix n

  muPlus : ℚ

  muMinus : ℚ

namespace SELData

/-- The real matrix associated with the rational matrix stored in `SELData`. -/
def toRealG (d : SELData) : Matrix (Sigma d.n) (Sigma d.n) ℝ :=
  QMatrix.toReal d.G

/-- The equivalence between `SELData` and its dependent tuple of bit length, rational matrix,
and two thresholds. -/
def equiv : SELData ≃ (Σ n : ℕ, QMatrix n × ℚ × ℚ) where
  toFun d := ⟨d.n, d.G, d.muPlus, d.muMinus⟩
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩
  left_inv d := by
    rcases d with ⟨n, G, p, m⟩
    rfl
  right_inv s := by
    rcases s with ⟨n, G, p, m⟩
    rfl

instance encodable : Encodable SELData :=
  Encodable.ofEquiv (Σ n : ℕ, QMatrix n × ℚ × ℚ) equiv

end SELData

/-- The promise of positive separated thresholds with logarithmic gap at least `1 / p n`,
entries in `[0, 1]`, and a largest eigenvalue above the upper threshold or below the lower
threshold. -/
def SELData.InLambda (p : ℕ → ℕ) (d : SELData) : Prop :=
  0 < p d.n ∧ 0 < (d.muMinus : ℝ) ∧ (d.muMinus : ℝ) < (d.muPlus : ℝ) ∧
  Real.log (d.muPlus : ℝ) - Real.log (d.muMinus : ℝ) ≥ 1 / (p d.n) ∧
  (∀ x y : Sigma d.n, 0 ≤ d.toRealG x y ∧ d.toRealG x y ≤ 1) ∧
  ((∃ μ : ℝ, IsLargestEigenvalue d.toRealG μ ∧ (d.muPlus : ℝ) ≤ μ) ∨
   (∃ μ : ℝ, IsLargestEigenvalue d.toRealG μ ∧ μ ≤ (d.muMinus : ℝ)))

/-- The promise problem distinguishing a largest eigenvalue at least `muPlus` from one at most
`muMinus` on data satisfying `InLambda`. -/
def selProblem (p : ℕ → ℕ) : PromiseProblem {d : SELData // d.InLambda p} where
  yes d := ∃ μ : ℝ, IsLargestEigenvalue d.1.toRealG μ ∧ (d.1.muPlus : ℝ) ≤ μ
  no d := ∃ μ : ℝ, IsLargestEigenvalue d.1.toRealG μ ∧ μ ≤ (d.1.muMinus : ℝ)

/-- The Boolean encoding of the underlying `SELData` natural-number code for a promised
instance. -/
def selEncoding (p : ℕ → ℕ) : Encoding {d : SELData // d.InLambda p} :=
  ⟨fun d => Nat.bits (Encodable.encode d.1)⟩

/-- Hamiltonian data consisting of bit length, locality parameter, finitely many rational terms,
and a specified support for each term. -/
structure LHData where

  n : ℕ

  k : ℕ

  m : ℕ

  term : Fin m → QMatrix n

  support : Fin m → Finset (Fin n)

namespace LHData

/-- The rational Hamiltonian obtained by summing all stored terms. -/
def H (d : LHData) : QMatrix d.n :=
  ∑ a : Fin d.m, d.term a

/-- The real matrix obtained by casting the summed rational Hamiltonian. -/
def toRealH (d : LHData) : Matrix (Sigma d.n) (Sigma d.n) ℝ :=
  QMatrix.toReal d.H

/-- The support condition that a term entry vanishes whenever its two Boolean indices differ at
some coordinate in that term's specified support. -/
def IsKLocal (d : LHData) : Prop :=
  ∀ (a : Fin d.m) (x y : Sigma d.n),
    (∃ i ∈ d.support a, x i ≠ y i) → d.term a x y = 0

/-- The condition that every off-diagonal entry of the total real Hamiltonian is nonpositive. -/
def IsStoquastic (d : LHData) : Prop :=
  ∀ x y : Sigma d.n, x ≠ y → d.toRealH x y ≤ 0

/-- The condition that every off-diagonal real entry of each individual Hamiltonian term is
nonpositive. -/
def IsTermwiseStoquastic (d : LHData) : Prop :=
  ∀ (a : Fin d.m) (x y : Sigma d.n), x ≠ y → QMatrix.toReal (d.term a) x y ≤ 0

/-- The conditional requirement of termwise stoquasticity when `termwise` is true. -/
def TermwiseCondition (termwise : Bool) (d : LHData) : Prop :=
  termwise = true → d.IsTermwiseStoquastic

/-- The equivalence between `LHData` and the dependent tuple of its bit length, locality
parameter, term count, terms, and supports. -/
def equiv : LHData ≃ (Σ n : ℕ, Σ k : ℕ, Σ m : ℕ,
    (Fin m → QMatrix n) × (Fin m → Finset (Fin n))) where
  toFun d := ⟨d.n, d.k, d.m, d.term, d.support⟩
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2⟩
  left_inv d := by
    rcases d with ⟨n, k, m, term, support⟩
    rfl
  right_inv s := by
    rcases s with ⟨n, k, m, term, support⟩
    rfl

instance encodable : Encodable LHData :=
  Encodable.ofEquiv
    (Σ n : ℕ, Σ k : ℕ, Σ m : ℕ, (Fin m → QMatrix n) × (Fin m → Finset (Fin n)))
    equiv

/-- The bundled conditions fixing the locality parameter, requiring `IsKLocal` and
stoquasticity, bounding term norms by positive `p1 n`, and placing a smallest eigenvalue at
most zero or at least `1 / p2 n`. -/
def InOmega (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) (d : LHData) : Prop :=
  d.k = k ∧ d.IsKLocal ∧ d.TermwiseCondition termwise ∧ d.IsStoquastic ∧
  0 < p1 d.n ∧ 0 < p2 d.n ∧
  (∀ a : Fin d.m, OperatorNormLE (QMatrix.toReal (d.term a)) (p1 d.n)) ∧
  (∃ lam : ℝ, IsSmallestEigenvalue d.toRealH lam ∧ (lam ≤ 0 ∨ (1 : ℝ) / (p2 d.n) ≤ lam))

end LHData

/-- The subtype of Hamiltonian data satisfying the specified `InOmega` conditions. -/
def LHInstance (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) : Type :=
  {d : LHData // d.InOmega k termwise p1 p2}

/-- The Boolean encoding of the underlying Hamiltonian-data natural-number code for an
`LHInstance`. -/
def lhEncoding (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) :
    Encoding (LHInstance k termwise p1 p2) :=
  ⟨fun I => Nat.bits (Encodable.encode I.1)⟩

/-- The promise problem distinguishing a smallest eigenvalue at most zero from one at least `1 /
p2 n` on `LHInstance` data. -/
def lhProblem (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) :
    PromiseProblem (LHInstance k termwise p1 p2) where
  yes I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ lam ≤ 0
  no I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ (1 : ℝ) / (p2 I.1.n) ≤ lam

/-- The existence of smallest and second-smallest eigenvalues whose difference is at least `1 /
p n`. -/
def HasSpectralGap (p : ℕ → ℕ) (d : LHData) : Prop :=
  ∃ mu0 mu1 : ℝ, IsSmallestEigenvalue d.toRealH mu0 ∧
    IsSecondSmallestEigenvalue d.toRealH mu1 ∧ (1 : ℝ) / (p d.n) ≤ mu1 - mu0

/-- The subtype of Hamiltonian data satisfying both the specified `InOmega` conditions and
`HasSpectralGap`. -/
def GappedLHInstance (k : ℕ) (termwise : Bool) (p1 p2 gapP : ℕ → ℕ) : Type :=
  {d : LHData // d.InOmega k termwise p1 p2 ∧ HasSpectralGap gapP d}

/-- The Boolean encoding of the underlying Hamiltonian-data natural-number code for a gapped
instance. -/
def gappedLHEncoding (k : ℕ) (termwise : Bool) (p1 p2 gapP : ℕ → ℕ) :
    Encoding (GappedLHInstance k termwise p1 p2 gapP) :=
  ⟨fun I => Nat.bits (Encodable.encode I.1)⟩

/-- The smallest-eigenvalue promise problem restricted to data satisfying the additional
spectral-gap condition. -/
def gappedLHProblem (k : ℕ) (termwise : Bool) (p1 p2 gapP : ℕ → ℕ) :
    PromiseProblem (GappedLHInstance k termwise p1 p2 gapP) where
  yes I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ lam ≤ 0
  no I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ (1 : ℝ) / (p2 I.1.n) ≤ lam

/-- The sum of all entries of `G ^ (L + 1)` divided by the sum of all entries of `G ^ L`. -/
def ExpectedMu {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (L : ℕ) : ℝ :=
  ((∑ x, ∑ y, (G ^ (L + 1)) x y)) / (∑ x, ∑ y, (G ^ L) x y)

open Matrix

/-- Conjugation by a real unitary matrix preserves the trace. -/
theorem trace_conj_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (Matrix ι ι ℝ)) (M : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) u M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

/-- The trace of the `k`th power of a real Hermitian matrix is the sum of the `k`th powers of
its eigenvalues. See [BravyiEtAl2008Stoquastic]. -/
theorem trace_pow_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [trace_conj_unitary, diagonal_pow, trace_diagonal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

/-- For a real Hermitian matrix with nonnegative eigenvalues, the `k`th power of a specified
largest eigenvalue is at most the trace of `G ^ k`. -/
theorem trace_pow_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (k : ℕ)
    (mu : ℝ) (hmu : ∃ i, hG.eigenvalues i = mu) (_hmax : ∀ i, hG.eigenvalues i ≤ mu)
    (hnonneg : ∀ i, 0 ≤ hG.eigenvalues i) :
    mu ^ k ≤ (G ^ k).trace := by
  rw [trace_pow_eq_sum_eigenvalues G hG k]
  obtain ⟨i0, hi0⟩ := hmu
  calc mu ^ k = (hG.eigenvalues i0) ^ k := by rw [hi0]
    _ ≤ ∑ i, (hG.eigenvalues i) ^ k :=
      Finset.single_le_sum (f := fun i => (hG.eigenvalues i) ^ k)
        (fun i _ => pow_nonneg (hnonneg i) k) (Finset.mem_univ i0)

/-- If every eigenvalue of a real Hermitian matrix has absolute value at most nonnegative `mu`,
then the trace of `G ^ k` is at most the matrix dimension times `mu ^ k`. -/
theorem trace_pow_upper_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (k : ℕ)
    (mu : ℝ) (_hmu : 0 ≤ mu) (hbound : ∀ i, |hG.eigenvalues i| ≤ mu) :
    (G ^ k).trace ≤ (Fintype.card ι : ℝ) * mu ^ k := by
  rw [trace_pow_eq_sum_eigenvalues G hG k]
  calc ∑ i, (hG.eigenvalues i) ^ k
      ≤ ∑ _i : ι, mu ^ k := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        calc (hG.eigenvalues i) ^ k ≤ |hG.eigenvalues i| ^ k := by
              have h := le_abs_self ((hG.eigenvalues i) ^ k)
              rwa [abs_pow] at h
          _ ≤ mu ^ k := pow_le_pow_left₀ (abs_nonneg _) (hbound i) k
    _ = (Fintype.card ι : ℝ) * mu ^ k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
