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
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

abbrev QMatrix (n : ℕ) := Sigma n → Sigma n → ℚ

namespace QMatrix

def toReal {n : ℕ} (A : QMatrix n) : Matrix (Sigma n) (Sigma n) ℝ :=
  fun x y => (A x y : ℝ)

end QMatrix

def HasEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  ∃ v : ι → ℝ, v ≠ 0 ∧ G.mulVec v = μ • v

def IsLargestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  HasEigenvalue G μ ∧ ∀ ν, HasEigenvalue G ν → ν ≤ μ

def IsSecondLargestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ1 : ℝ) : Prop :=
  ∃ μ0, IsLargestEigenvalue G μ0 ∧ HasEigenvalue G μ1 ∧ μ1 ≤ μ0 ∧
    ∀ ν, HasEigenvalue G ν → ν = μ0 ∨ ν ≤ μ1

def IsSmallestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  HasEigenvalue G μ ∧ ∀ ν, HasEigenvalue G ν → μ ≤ ν

def IsSecondSmallestEigenvalue {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (μ1 : ℝ) : Prop :=
  ∃ μ0, IsSmallestEigenvalue G μ0 ∧ HasEigenvalue G μ1 ∧ μ0 ≤ μ1 ∧
    ∀ ν, HasEigenvalue G ν → ν = μ0 ∨ μ1 ≤ ν

def OperatorNormLE {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (C : ℝ) : Prop :=
  ∀ v : ι → ℝ, ‖A.mulVec v‖ ≤ C * ‖v‖

structure SELData where

  n : ℕ

  G : QMatrix n

  muPlus : ℚ

  muMinus : ℚ

namespace SELData

def toRealG (d : SELData) : Matrix (Sigma d.n) (Sigma d.n) ℝ :=
  QMatrix.toReal d.G

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

def SELData.InLambda (p : ℕ → ℕ) (d : SELData) : Prop :=
  0 < p d.n ∧ 0 < (d.muMinus : ℝ) ∧ (d.muMinus : ℝ) < (d.muPlus : ℝ) ∧
  Real.log (d.muPlus : ℝ) - Real.log (d.muMinus : ℝ) ≥ 1 / (p d.n) ∧
  (∀ x y : Sigma d.n, 0 ≤ d.toRealG x y ∧ d.toRealG x y ≤ 1) ∧
  ((∃ μ : ℝ, IsLargestEigenvalue d.toRealG μ ∧ (d.muPlus : ℝ) ≤ μ) ∨
   (∃ μ : ℝ, IsLargestEigenvalue d.toRealG μ ∧ μ ≤ (d.muMinus : ℝ)))

def selProblem (p : ℕ → ℕ) : PromiseProblem {d : SELData // d.InLambda p} where
  yes d := ∃ μ : ℝ, IsLargestEigenvalue d.1.toRealG μ ∧ (d.1.muPlus : ℝ) ≤ μ
  no d := ∃ μ : ℝ, IsLargestEigenvalue d.1.toRealG μ ∧ μ ≤ (d.1.muMinus : ℝ)

def selEncoding (p : ℕ → ℕ) : Encoding {d : SELData // d.InLambda p} :=
  ⟨fun d => Nat.bits (Encodable.encode d.1)⟩

structure LHData where

  n : ℕ

  k : ℕ

  m : ℕ

  term : Fin m → QMatrix n

  support : Fin m → Finset (Fin n)

namespace LHData

def H (d : LHData) : QMatrix d.n :=
  ∑ a : Fin d.m, d.term a

def toRealH (d : LHData) : Matrix (Sigma d.n) (Sigma d.n) ℝ :=
  QMatrix.toReal d.H

def IsKLocal (d : LHData) : Prop :=
  ∀ (a : Fin d.m) (x y : Sigma d.n),
    (∃ i ∈ d.support a, x i ≠ y i) → d.term a x y = 0

def IsStoquastic (d : LHData) : Prop :=
  ∀ x y : Sigma d.n, x ≠ y → d.toRealH x y ≤ 0

def IsTermwiseStoquastic (d : LHData) : Prop :=
  ∀ (a : Fin d.m) (x y : Sigma d.n), x ≠ y → QMatrix.toReal (d.term a) x y ≤ 0

def TermwiseCondition (termwise : Bool) (d : LHData) : Prop :=
  termwise = true → d.IsTermwiseStoquastic

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

def InOmega (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) (d : LHData) : Prop :=
  d.k = k ∧ d.IsKLocal ∧ d.TermwiseCondition termwise ∧ d.IsStoquastic ∧
  0 < p1 d.n ∧ 0 < p2 d.n ∧
  (∀ a : Fin d.m, OperatorNormLE (QMatrix.toReal (d.term a)) (p1 d.n)) ∧
  (∃ lam : ℝ, IsSmallestEigenvalue d.toRealH lam ∧ (lam ≤ 0 ∨ (1 : ℝ) / (p2 d.n) ≤ lam))

end LHData

def LHInstance (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) : Type :=
  {d : LHData // d.InOmega k termwise p1 p2}

def lhEncoding (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) :
    Encoding (LHInstance k termwise p1 p2) :=
  ⟨fun I => Nat.bits (Encodable.encode I.1)⟩

def lhProblem (k : ℕ) (termwise : Bool) (p1 p2 : ℕ → ℕ) :
    PromiseProblem (LHInstance k termwise p1 p2) where
  yes I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ lam ≤ 0
  no I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ (1 : ℝ) / (p2 I.1.n) ≤ lam

def HasSpectralGap (p : ℕ → ℕ) (d : LHData) : Prop :=
  ∃ mu0 mu1 : ℝ, IsSmallestEigenvalue d.toRealH mu0 ∧
    IsSecondSmallestEigenvalue d.toRealH mu1 ∧ (1 : ℝ) / (p d.n) ≤ mu1 - mu0

def GappedLHInstance (k : ℕ) (termwise : Bool) (p1 p2 gapP : ℕ → ℕ) : Type :=
  {d : LHData // d.InOmega k termwise p1 p2 ∧ HasSpectralGap gapP d}

def gappedLHEncoding (k : ℕ) (termwise : Bool) (p1 p2 gapP : ℕ → ℕ) :
    Encoding (GappedLHInstance k termwise p1 p2 gapP) :=
  ⟨fun I => Nat.bits (Encodable.encode I.1)⟩

def gappedLHProblem (k : ℕ) (termwise : Bool) (p1 p2 gapP : ℕ → ℕ) :
    PromiseProblem (GappedLHInstance k termwise p1 p2 gapP) where
  yes I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ lam ≤ 0
  no I := ∃ lam : ℝ, IsSmallestEigenvalue I.1.toRealH lam ∧ (1 : ℝ) / (p2 I.1.n) ≤ lam

def ExpectedMu {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (L : ℕ) : ℝ :=
  ((∑ x, ∑ y, (G ^ (L + 1)) x y)) / (∑ x, ∑ y, (G ^ L) x y)

open Matrix

theorem trace_conj_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (Matrix ι ι ℝ)) (M : Matrix ι ι ℝ) :
    (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) u M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

theorem trace_pow_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [trace_conj_unitary, diagonal_pow, trace_diagonal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

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
