/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.ShadowsDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Papers.ClassShadows20.LowerBound.LocalProductRecordInformation

/-!
# Finite shadow lower bound ingredients

The module supplies a twenty-four-member qubit moment ensemble and constructs a rank-`r`
coordinate projector capturing at least `r/d` of a density operator. It proves positivity and
trace identities for projector codes and combines assumed rotation moments with successful
decoding to obtain a finite measurement lower bound. It also refutes a universal one-sided error
claim for `dyadicRat`.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `clause7_conjunct5`: constructs a projector with the required trace overlap.
* `clause7_conjunct6`: derives a demand-versus-allowance inequality from decoding and moment
  hypotheses.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.ClassShadows20.LowerBound
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.ClassShadows20.LowerBound.Shadows

open Qatlib.Papers.ClassShadows20.LowerBound.Shadows Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020
open Qatlib
open Matrix

/-- The claim that every real input has `dyadicRat` error in the half-open interval from zero to
`2^(-k)` is false. -/
theorem clause6_quantization_conjunct_refutable :
    ¬ (∀ (k : ℕ) (t : ℝ),
        0 ≤ (t : ℝ) - ((Qatlib.Concepts.RiskEstimation.PopulationGap.dyadicRat k t : ℚ) : ℝ) ∧
          (t : ℝ) - ((Qatlib.Concepts.RiskEstimation.PopulationGap.dyadicRat k t : ℚ) : ℝ) <
            (1 / 2 : ℝ) ^ k) := by
  intro hall
  have hs : (-1 : ℝ) - ((Qatlib.Concepts.RiskEstimation.PopulationGap.dyadicRat 0 (-1) : ℚ) : ℝ) = -1 := by
    rw [dyadicRat]
    have hle : (2 : ℝ) ^ 0 * (-1 : ℝ) ≤ 0 := by norm_num
    rw [Nat.floor_of_nonpos hle]
    norm_num
  have h := (hall 0 (-1)).1
  rw [hs] at h
  norm_num at h

open scoped BigOperators ComplexOrder
set_option warningAsError false

/-- There exists a family of twenty-four qubit unitaries whose uniform average has the stated
first moment and second moment for Hermitian test operators. -/
theorem clause7_conjunct2 :
    ∃ f : Fin 24 → Operator 2,
      (∀ i, f i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
        (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A : Operator 2,
          (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
            (Matrix.trace A).re / 2) ∧
        (∀ Pp : Operator 2, IsPureDensityOperator Pp → ∀ A B : Operator 2,
          A.IsHermitian → B.IsHermitian →
          (∑ i, (Matrix.trace (A * Matrix.conjTranspose (f i) * Pp * f i)).re *
              (Matrix.trace (B * Matrix.conjTranspose (f i) * Pp * f i)).re) / 24 =
            ((Matrix.trace A).re * (Matrix.trace B).re +
              (Matrix.trace (A * B)).re) / 6) :=
  qubit_conjugation_two_design_exists

/-- The real trace of a product of positive semidefinite operators is nonnegative. -/
private theorem trace_mul_re_nonneg {D : ℕ} (A B : Operator D)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  have hA' : (0 : HermitianMat (Fin D) ℂ) ≤ ⟨A, hA.1⟩ := HermitianMat.zero_le_iff.mpr hA
  have hB' : (0 : HermitianMat (Fin D) ℂ) ≤ ⟨B, hB.1⟩ := HermitianMat.zero_le_iff.mpr hB
  have h := HermitianMat.inner_ge_zero hA' hB'
  rw [HermitianMat.inner_eq_re_trace] at h
  exact h

/-- A positive semidefinite operator has real trace of its square at most the square of its real
trace. -/
private theorem trace_sq_le_trace_sq' {D : ℕ} (A : Operator D) (hA : A.PosSemidef) :
    (Matrix.trace (A * A)).re ≤ (Matrix.trace A).re ^ 2 := by
  have hA' : (0 : HermitianMat (Fin D) ℂ) ≤ ⟨A, hA.1⟩ := HermitianMat.zero_le_iff.mpr hA
  have h := HermitianMat.inner_le_mul_trace hA' hA'
  rw [HermitianMat.inner_eq_re_trace] at h
  exact h.trans_eq (pow_two _).symm

/-- For `r > 0`, the number of `r`-element subsets of `Fin d` containing a fixed index is `(d -
1).choose (r - 1)`. -/
private lemma powersetCard_mem_card (d r : ℕ) (i : Fin d) (hr : 0 < r) :
    (((Finset.univ : Finset (Fin d)).powersetCard r).filter (fun S => i ∈ S)).card =
      (d - 1).choose (r - 1) := by
  classical
  have h : ((Finset.univ : Finset (Fin d)).powersetCard r).filter (fun S => i ∈ S)
      = ((Finset.univ : Finset (Fin d)).powersetCard r).filter
          (fun S => ({i} : Finset (Fin d)) ⊆ S) := by
    apply Finset.filter_congr
    intro S _
    simp [Finset.singleton_subset_iff]
  rw [h, Finset.card_filter_powersetCard_subset _ _ _
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
      (by rw [Finset.card_singleton]; omega),
    Finset.card_univ, Fintype.card_fin, Finset.card_singleton]

/-- Summing coordinate sums over all `r`-element subsets counts each coordinate `(d - 1).choose
(r - 1)` times when `r > 0`. -/
private lemma powersetCard_sum_eq (d r : ℕ) (x : Fin d → ℝ) (hr : 0 < r) :
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, ∑ i ∈ S, x i)
      = ((d - 1).choose (r - 1) : ℝ) * ∑ i, x i := by
  classical
  have hsum : (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, ∑ i ∈ S, x i)
      = ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
          ∑ i : Fin d, if i ∈ S then x i else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    rw [← Finset.sum_filter (s := Finset.univ) (p := fun i : Fin d => i ∈ S)]
    rw [show (Finset.univ.filter (fun i : Fin d => i ∈ S)) = S from by ext i; simp]
  rw [hsum, Finset.sum_comm]
  have hcount : ∀ i : Fin d,
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, if i ∈ S then x i else 0)
        = x i * (((Finset.univ : Finset (Fin d)).powersetCard r).filter (fun S => i ∈ S)).card := by
    intro i
    rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin d)).powersetCard r)
        (p := fun S => i ∈ S) (f := fun _ => x i)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [hcount, fun i => powersetCard_mem_card d r i hr]
  rw [← Finset.sum_mul]
  ring

/-- The diagonal coordinate projector associated with a finite set of indices. -/
private def coordProj {d : ℕ} (S : Finset (Fin d)) : Operator d :=
  Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0)

/-- A coordinate projector is Hermitian. -/
private lemma coordProj_isHermitian {d : ℕ} (S : Finset (Fin d)) :
    (coordProj S).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext i
  by_cases hi : i ∈ S <;> simp [hi]

/-- A coordinate projector is idempotent. -/
private lemma coordProj_mul_self {d : ℕ} (S : Finset (Fin d)) :
    coordProj S * coordProj S = coordProj S := by
  have hmul := Matrix.diagonal_mul_diagonal
    (fun i => if i ∈ S then (1 : ℂ) else 0) (fun i => if i ∈ S then (1 : ℂ) else 0)
  show Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) *
      Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) = _
  rw [hmul]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  by_cases hi : i ∈ S <;> simp [hi]

/-- The trace of a coordinate projector is the cardinality of its index set, cast to the complex
numbers. -/
private lemma coordProj_trace {d : ℕ} (S : Finset (Fin d)) :
    Matrix.trace (coordProj S) = ((S.card : ℕ) : ℂ) := by
  show Matrix.trace (Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0)) = _
  rw [Matrix.trace_diagonal]
  have h : (∑ i : Fin d, (if i ∈ S then (1 : ℂ) else 0)) = (S.card : ℂ) := by
    rw [← Finset.sum_filter (s := Finset.univ) (p := fun i : Fin d => i ∈ S)]
    rw [show (Finset.univ.filter (fun i : Fin d => i ∈ S)) = S from by ext i; simp]
    rw [Finset.sum_const, nsmul_one]
  exact h

/-- The real trace pairing with a coordinate projector equals the sum of the selected real
diagonal entries. -/
private lemma coordProj_trace_mul {d : ℕ} (S : Finset (Fin d)) (ρ : Operator d) :
    (Matrix.trace (coordProj S * ρ)).re = ∑ i ∈ S, (ρ i i).re := by
  have hkey : ∀ i : Fin d,
      Matrix.diag (Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0) * ρ) i
        = (if i ∈ S then (1 : ℂ) else 0) * ρ i i := by
    intro i
    show (Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0) * ρ) i i = _
    rw [Matrix.diagonal_mul]
  show (Matrix.trace (Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0) * ρ)).re = _
  rw [Matrix.trace, Complex.re_sum]
  simp only [hkey]
  have h : (∑ i : Fin d, ((if i ∈ S then (1 : ℂ) else 0) * ρ i i).re) = ∑ i ∈ S, (ρ i i).re := by
    have hterm : ∀ i : Fin d, ((if i ∈ S then (1 : ℂ) else 0) * ρ i i).re
        = if i ∈ S then (ρ i i).re else 0 := by
      intro i
      by_cases hi : i ∈ S <;> simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rw [← Finset.sum_filter (s := Finset.univ) (p := fun i : Fin d => i ∈ S)]
    rw [show (Finset.univ.filter (fun i : Fin d => i ∈ S)) = S from by ext i; simp]
  exact h

/-- For a density operator and `0 < r ≤ d`, there exists a Hermitian idempotent of trace `r`
whose real trace pairing with the state is at least `r / d`. -/
theorem clause7_conjunct5 (d r : ℕ) (ρ : Operator d)
    (hr : 0 < r) (hrd : r ≤ d) (hρ : IsDensityOperator ρ) :
    ∃ P : Operator d,
      P.IsHermitian ∧ P * P = P ∧
        Matrix.trace P = ((r : ℕ) : ℂ) ∧
        (r : ℝ) / d ≤ (Matrix.trace (P * ρ)).re := by
  classical
  have htr : (Matrix.trace ρ).re = 1 := by
    rw [hρ.2, Complex.one_re]
  have hxsum : (∑ i : Fin d, (ρ i i).re) = 1 := by
    rw [← htr]
    show (∑ i : Fin d, (ρ i i).re) = (Matrix.trace ρ).re
    rw [Matrix.trace, Complex.re_sum]
    simp
  set Q : Finset (Fin d) → Operator d := fun S => coordProj S
  have hQprop : ∀ S : Finset (Fin d),
      (Q S).IsHermitian ∧ Q S * Q S = Q S ∧
        Matrix.trace (Q S) = ((S.card : ℕ) : ℂ) ∧
        (Matrix.trace (Q S * ρ)).re = ∑ i ∈ S, (ρ i i).re := by
    intro S
    exact ⟨coordProj_isHermitian S, coordProj_mul_self S, coordProj_trace S,
      coordProj_trace_mul S ρ⟩
  have havg0 : (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      (Matrix.trace (Q S * ρ)).re)
      = ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r, ∑ i ∈ S, (ρ i i).re :=
    Finset.sum_congr rfl (fun S _ => (hQprop S).2.2.2)
  have havg : (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      (Matrix.trace (Q S * ρ)).re)
      = (((Finset.univ : Finset (Fin d)).powersetCard r).card : ℝ) * ((r : ℝ) / d) := by
    rw [havg0, powersetCard_sum_eq _ _ _ hr, hxsum, mul_one,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hdpos : 0 < d := by omega
    have hnat : d * (d - 1).choose (r - 1) = d.choose r * r := by
      have h := Nat.add_one_mul_choose_eq (d - 1) (r - 1)
      have hd : d - 1 + 1 = d := by omega
      have hrr : r - 1 + 1 = r := by omega
      rw [hd, hrr] at h
      exact h
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at hcast
    have hne : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    field_simp
    nlinarith
  have hnonempty : ((Finset.univ : Finset (Fin d)).powersetCard r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact Nat.choose_pos hrd
  obtain ⟨S, hSmem, hS⟩ : ∃ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      (r : ℝ) / d ≤ (Matrix.trace (Q S * ρ)).re := by
    by_contra! hex
    obtain ⟨S₀, hS₀⟩ := hnonempty
    have hlt : (∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        (Matrix.trace (Q S * ρ)).re) <
        (((Finset.univ : Finset (Fin d)).powersetCard r).card : ℝ) * ((r : ℝ) / d) := by
      have h := Finset.sum_lt_sum (fun S h => (hex S h).le) ⟨S₀, hS₀, hex S₀ hS₀⟩
      rwa [Finset.sum_const, nsmul_eq_mul] at h
    linarith
  simp only [Finset.mem_powersetCard] at hSmem
  refine ⟨Q S, (hQprop S).1, (hQprop S).2.1, ?_, hS⟩
  rw [← hSmem.2]
  exact (hQprop S).2.2.1

/-- Taking the trace commutes with real scalar multiplication after casting the scalar to the
complex numbers. -/
private lemma trace_real_smul {D : ℕ} (c : ℝ) (A : Operator D) :
    Matrix.trace (c • A) = (c : ℂ) * Matrix.trace A := by
  rw [Matrix.trace_smul]
  exact Complex.real_smul

/-- A Hermitian idempotent operator is positive semidefinite. -/
private lemma idem_hermitian_posSemidef {D : ℕ} (Q : Operator D)
    (hherm : Q.IsHermitian) (hsq : Q * Q = Q) : Q.PosSemidef := by
  have hEq : Q = Q.conjTranspose * Q := by rw [hherm, hsq]
  rw [hEq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A code operator formed from a positive semidefinite operator is positive semidefinite when
`0 ≤ α ≤ 1`. -/
private lemma lemma8CodeState_posSemidef {d r : ℕ} (Q : Operator d)
    (hQpsd : Q.PosSemidef) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (lemma8CodeState d r α Q).PosSemidef := by
  rw [lemma8CodeState]
  exact Matrix.PosSemidef.add
    (Matrix.PosSemidef.smul Matrix.PosSemidef.one
      (div_nonneg (by linarith) (by positivity)))
    (Matrix.PosSemidef.smul hQpsd (by positivity))

/-- For positive `d` and `r`, an operator of trace `r` yields a code operator of trace one. -/
private lemma lemma8CodeState_trace_one {d r : ℕ} (Q : Operator d)
    (hQtr : Matrix.trace Q = ((r : ℕ) : ℂ)) (α : ℝ) (hd : 0 < d) (hr : 0 < r) :
    Matrix.trace (lemma8CodeState d r α Q) = 1 := by
  have hc : ∀ (c : ℝ) (n : ℕ), 0 < n → (c / (n : ℝ)) • ((n : ℂ)) = ((c : ℝ) : ℂ) := by
    intro c n hn
    have hn' : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn.ne'
    have hkey : Complex.ofReal (c / (n : ℝ)) * Complex.ofReal ((n : ℝ)) = Complex.ofReal c := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hn']
    rw [Algebra.smul_def]
    exact hkey
  rw [lemma8CodeState, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    hQtr, Matrix.trace_one, Fintype.card_fin, hc (1 - α) d hd, hc α r hr]
  push_cast
  ring

/-- Conjugates the state by `Uf i` when `μ.prob i` is positive and otherwise returns the input
state. -/
private noncomputable def gatedState {d : ℕ} {I : Type} [Fintype I]
    (μ : FinDist I) (Uf : I → Operator d) (ρ : Operator d) (i : I) : Operator d :=
  if 0 < μ.prob i then (Uf i * ρ * (Uf i)ᴴ) else ρ

/-- Under the stated dimension, rank, and purity-parameter relation, replacing `t2 ≤ t²` bounds
the second-moment expression by `(t/d)² * (1 + α²(d-r)/(r(d+1)))`. -/
private theorem theorem5_second_moment_bound (d r : ℕ) (α s t t2 : ℝ)
    (hd : 2 ≤ d) (hr : 0 < r) (hrd : r ≤ d) (hα : 0 < α)
    (hs : s = (1 - α ^ 2) / (d : ℝ) + α ^ 2 / (r : ℝ))
    (hT2 : t2 ≤ t ^ 2) :
    (((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1))) * t ^ 2 +
      (((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1))) * t2 ≤
      (t / (d : ℝ)) ^ 2 *
        (1 + α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1))) := by
  have h2d : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : (0 : ℝ) < d := by linarith
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  have hRD : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hD2 : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith [h2d]
  have hneD : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hneR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hneD2 : (d : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [hD2]
  have hneD1 : (d : ℝ) + 1 ≠ 0 := by nlinarith [hD]
  have hβ : (d : ℝ) * s - 1 = α ^ 2 * ((d : ℝ) - (r : ℝ)) / (r : ℝ) := by
    rw [hs]
    field_simp
    ring
  have hβ0 : 0 ≤ (d : ℝ) * s - 1 := by
    rw [hβ]
    exact div_nonneg (mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hRD)) (le_of_lt hR)
  have hv : α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1))
      = ((d : ℝ) * s - 1) / ((d : ℝ) + 1) := by
    rw [hβ]
    field_simp
  rw [hv]

  have hDP : 0 ≤ ((d : ℝ) + 1) * ((d : ℝ) * s - 1) * (t ^ 2 - t2) := by
    have h1 : 0 ≤ ((d : ℝ) + 1) * ((d : ℝ) * s - 1) :=
      mul_nonneg (by positivity) hβ0
    exact mul_nonneg h1 (sub_nonneg.mpr hT2)
  have hDP2 : 0 ≤ (d : ℝ) * (((d : ℝ) + 1) * ((d : ℝ) * s - 1) * (t ^ 2 - t2)) :=
    mul_nonneg (le_of_lt hD) hDP

  have hpoly : ((d : ℝ) ^ 2 - 1) * ((d : ℝ) * s + (d : ℝ)) * t ^ 2
      - (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) - s) * t ^ 2
      - (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) * s - 1) * t2
      = (d : ℝ) * (((d : ℝ) + 1) * ((d : ℝ) * s - 1) * (t ^ 2 - t2)) := by
    ring
  have hcleared : (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) - s) * t ^ 2
      + (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) * s - 1) * t2
      ≤ ((d : ℝ) ^ 2 - 1) * ((d : ℝ) * s + (d : ℝ)) * t ^ 2 := by
    nlinarith [hpoly, hDP2]
  field_simp
  nlinarith [hpoly, hDP2, hT2]

/-- For the specified finite POVM, projector codes, rotation moments, and uniformly successful
decoder, `theorem5WrapperDemand M δ` is at most `N * theorem5WrapperAllowance d r α`. This
is the finite decoding implication associated with [Huang et al., Theorem
5][HuangKuengPreskill2020]. -/
theorem clause7_conjunct6 :
    ∀ (d r M N : ℕ) (O I : Type) [Fintype O] [DecidableEq O]
      [Fintype I] [DecidableEq I]
      (F : O → Operator d) (hFpsd : ∀ o, (F o).PosSemidef) (hFsum : (∑ o, F o) = 1)
      (P : Fin M → Operator d)
      (hP : ∀ x, (P x).IsHermitian ∧ P x * P x = P x ∧
        Matrix.trace (P x) = ((r : ℕ) : ℂ))
      (μ : FinDist I) (Uf : I → Operator d)
      (hμU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
      (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
      (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
      (hd : 2 ≤ d) (hr : 0 < r) (hrd : r ≤ d) (hM : 0 < M)
      (s : ℝ) (hs : s = (1 - α ^ 2) / (d : ℝ) + α ^ 2 / (r : ℝ))
      (h1 : ∀ x : Fin M,
        (∑ i, μ.prob i • (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ)) =
          (1 / (d : ℝ)) • 1)
      (h2 : ∀ x : Fin M, ∀ A B : Operator d,
        A.IsHermitian → B.IsHermitian →
        (∑ i, μ.prob i *
            (Matrix.trace (A * (Uf i * lemma8CodeState d r α (P x) *
              (Uf i)ᴴ))).re *
            (Matrix.trace (B * (Uf i * lemma8CodeState d r α (P x) *
              (Uf i)ᴴ))).re) =
          ((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
              (Matrix.trace A).re * (Matrix.trace B).re +
          ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (A * B)).re)
      (g : (Fin N → I) → (Fin N → O) → Fin M)
      (hg : ∀ (x : Fin M) (u : Fin N → I),
        1 - δ ≤ ∑ ω ∈ Finset.univ.filter
            (fun ω : Fin N → O => g u ω = x),
          ∏ j : Fin N,
            (Matrix.trace (F (ω j) *
              (Uf (u j) * lemma8CodeState d r α (P x) * (Uf (u j))ᴴ))).re),
    theorem5WrapperDemand M δ ≤ (N : ℝ) * theorem5WrapperAllowance d r α := by
  intro d r M N O I _ _ _ _ F hFpsd hFsum P hP μ Uf hμU α hα0 hα1 δ hδ0 hδ1
    hd hr hrd hM s hs h1 h2 g hg
  classical

  have hD : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  have hRD : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)

  have hPpsd : ∀ x : Fin M, (P x).PosSemidef := by
    intro x
    exact idem_hermitian_posSemidef (P x) (hP x).1 (hP x).2.1
  have hρpsd : ∀ x : Fin M, (lemma8CodeState d r α (P x)).PosSemidef := by
    intro x
    exact lemma8CodeState_posSemidef (P x) (hPpsd x) α (le_of_lt hα0) hα1
  have hρtr : ∀ x : Fin M, Matrix.trace (lemma8CodeState d r α (P x)) = 1 := by
    intro x
    exact lemma8CodeState_trace_one (P x) (hP x).2.2 α (by omega) hr

  have hu : ∀ i, 0 < μ.prob i →
      (Uf i * (Uf i)ᴴ = 1 ∧ (Uf i)ᴴ * Uf i = 1) := by
    intro i hi
    have h := hμU i hi
    have ha := Matrix.mem_unitaryGroup_iff.mp h
    rw [Matrix.star_eq_conjTranspose] at ha
    have hb := Matrix.mem_unitaryGroup_iff'.mp h
    rw [Matrix.star_eq_conjTranspose] at hb
    exact ⟨ha, hb⟩
  have hconjpsd : ∀ x i, 0 < μ.prob i →
      (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ).PosSemidef := by
    intro x i hi
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same (hρpsd x) (Uf i)

  have hgated_psd : ∀ x i, (gatedState μ Uf (lemma8CodeState d r α (P x)) i).PosSemidef := by
    intro x i
    by_cases hi : 0 < μ.prob i
    · rw [gatedState, if_pos hi]
      exact hconjpsd x i hi
    · rw [gatedState, if_neg hi]
      exact hρpsd x
  have hgated_tr : ∀ x i, Matrix.trace (gatedState μ Uf (lemma8CodeState d r α (P x)) i) = 1 := by
    intro x i
    by_cases hi : 0 < μ.prob i
    · rw [gatedState, if_pos hi]
      obtain ⟨_, hb⟩ := hu i hi
      rw [Matrix.trace_mul_cycle, hb, Matrix.one_mul]
      exact hρtr x
    · rw [gatedState, if_neg hi]
      exact hρtr x
  have hgated_pos : ∀ x i, 0 < μ.prob i →
      gatedState μ Uf (lemma8CodeState d r α (P x)) i
        = Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ := by
    intro x i hi
    rw [gatedState, if_pos hi]

  have hw_nonneg : ∀ o : O, 0 ≤ (Matrix.trace (F o)).re / (d : ℝ) := by
    intro o
    have h := trace_mul_re_nonneg (F o) 1 (hFpsd o) Matrix.PosSemidef.one
    rw [Matrix.mul_one] at h
    exact div_nonneg h (le_of_lt hD)
  have hw_sum : (∑ o : O, (Matrix.trace (F o)).re / (d : ℝ)) = 1 := by
    have h : (∑ o : O, (Matrix.trace (F o)).re) = (d : ℝ) := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, hFsum, Matrix.trace_one,
        Fintype.card_fin, Complex.natCast_re]
    rw [← Finset.sum_div, h]
    exact div_self hD.ne'

  have hq_nonneg : ∀ (x : Fin M) (i : I) (o : O),
      0 ≤ (Matrix.trace (F o * gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re := by
    intro x i o
    exact trace_mul_re_nonneg (F o) _ (hFpsd o) (hgated_psd x i)
  have hq_sum : ∀ (x : Fin M) (i : I),
      (∑ o : O, (Matrix.trace (F o * gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re) = 1 := by
    intro x i
    have h : (∑ o : O, (Matrix.trace (F o * gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re)
        = (Matrix.trace (gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hFsum, Matrix.one_mul]
    rw [h, hgated_tr, Complex.one_re]

  set w : FinDist O := ⟨fun o => (Matrix.trace (F o)).re / (d : ℝ), hw_nonneg, hw_sum⟩
  set q : Fin M → (Fin N → I) → Fin N → FinDist O :=
    fun x u j => ⟨fun o => (Matrix.trace (F o * gatedState μ Uf (lemma8CodeState d r α (P x)) (u j))).re,
      fun o => hq_nonneg x (u j) o, hq_sum x (u j)⟩
  set π : FinDist (Fin N → I) :=
    ⟨fun u => μ.probOf u,
      fun u => Finset.prod_nonneg (fun i _ => μ.nonneg (u i)), μ.sum_probOf N⟩
  have hπ_apply : ∀ u : Fin N → I, π.prob u = ∏ j : Fin N, μ.prob (u j) := fun _ => rfl
  have hq_apply : ∀ (x : Fin M) (u : Fin N → I) (j : Fin N) (o : O),
      (q x u j).prob o =
        (Matrix.trace (F o * gatedState μ Uf (lemma8CodeState d r α (P x)) (u j))).re := by
    intro x u j o
    rfl

  have hmean : ∀ j o, (1 / (M : ℝ)) * ∑ x, ∑ u, π.prob u * (q x u j).prob o = (w).prob o := by
    intro j o
    have hstep : ∀ x : Fin M,
        (∑ u : Fin N → I, π.prob u * (q x u j).prob o)
          = ∑ i, μ.prob i * (Matrix.trace (F o *
              gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re := by
      intro x
      simpa [hπ_apply, hq_apply] using!
        μ.expect_coord j (fun i => (Matrix.trace (F o *
          gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re)
    have hmass : ∀ x : Fin M,
        (∑ i, μ.prob i * (Matrix.trace (F o *
            gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re)
          = (Matrix.trace (F o * ((1 / (d : ℝ)) • (1 : Operator d)))).re := by
      intro x
      have hkey : (∑ i : I, μ.prob i • gatedState μ Uf (lemma8CodeState d r α (P x)) i)
          = (1 / (d : ℝ)) • (1 : Operator d) := by
        have hterm : ∀ i : I,
            μ.prob i • gatedState μ Uf (lemma8CodeState d r α (P x)) i
              = μ.prob i • (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ) := by
          intro i
          by_cases hi : 0 < μ.prob i
          · rw [hgated_pos x i hi]
          · have hz : μ.prob i = 0 := by linarith [μ.nonneg i]
            rw [hz, zero_smul, zero_smul]
        rw [Finset.sum_congr rfl (fun i _ => hterm i)]
        exact h1 x
      have hre : (Matrix.trace (F o * (∑ i : I, μ.prob i •
          gatedState μ Uf (lemma8CodeState d r α (P x)) i))).re
          = ∑ i, μ.prob i * (Matrix.trace (F o *
              gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re := by
        rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
        try rw [smul_eq_mul]
      rw [← hre, hkey]
    have hval : (Matrix.trace (F o * ((1 / (d : ℝ)) • (1 : Operator d)))).re
        = (Matrix.trace (F o)).re / (d : ℝ) := by
      have hsmul : F o * ((1 / (d : ℝ)) • (1 : Operator d)) = (1 / (d : ℝ)) • F o := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply]
        rw [Finset.sum_eq_single j]
        · by_cases hj : j = i <;> simp [hj] <;> ring
        · intro b _ hb
          rw [if_neg hb]
          simp
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      rw [hsmul, trace_real_smul]
      have hre : ((((1 / (d : ℝ) : ℝ) : ℂ)) * Matrix.trace (F o)).re
          = (1 / (d : ℝ)) * (Matrix.trace (F o)).re := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hre]
      ring
    have hsumx : (∑ x : Fin M, ∑ u : Fin N → I, π.prob u * (q x u j).prob o)
        = ∑ x : Fin M, (Matrix.trace (F o)).re / (d : ℝ) :=
      Finset.sum_congr rfl (fun x _ => (hstep x).trans ((hmass x).trans hval))
    rw [hsumx]
    have h : (∑ x : Fin M, (Matrix.trace (F o)).re / (d : ℝ))
        = (M : ℝ) * ((Matrix.trace (F o)).re / (d : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hwo : (w).prob o = (Matrix.trace (F o)).re / (d : ℝ) := rfl
    rw [h, hwo]
    field_simp

  have hsecond : ∀ j o, (1 / (M : ℝ)) * ∑ x, ∑ u, π.prob u * ((q x u j).prob o)^2
      ≤ ((w).prob o)^2 * (1 + theorem5WrapperAllowance d r α) := by
    intro j o
    have hstep : ∀ x : Fin M,
        (∑ u : Fin N → I, π.prob u * ((q x u j).prob o)^2)
          = ∑ i, μ.prob i * (Matrix.trace (F o * (Uf i *
              lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re ^ 2 := by
      intro x
      have h1' : (∑ u : Fin N → I, π.prob u * ((q x u j).prob o)^2)
          = ∑ u : Fin N → I, μ.probOf u *
              (Matrix.trace (F o *
                gatedState μ Uf (lemma8CodeState d r α (P x)) (u j))).re ^ 2 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [hπ_apply, hq_apply, FinDist.probOf]
      have h2' : (∑ u : Fin N → I, μ.probOf u *
            (Matrix.trace (F o *
              gatedState μ Uf (lemma8CodeState d r α (P x)) (u j))).re ^ 2)
          = ∑ i, μ.prob i *
              (Matrix.trace (F o *
                gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re ^ 2 :=
        μ.expect_coord j (fun i => (Matrix.trace (F o *
          gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re ^ 2)
      have hterm : ∀ i : I,
          μ.prob i * (Matrix.trace (F o *
              gatedState μ Uf (lemma8CodeState d r α (P x)) i)).re ^ 2
            = μ.prob i * (Matrix.trace (F o * (Uf i *
                lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re ^ 2 := by
        intro i
        by_cases hi : 0 < μ.prob i
        · rw [hgated_pos x i hi]
        · have hz : μ.prob i = 0 := by linarith [μ.nonneg i]
          rw [hz, zero_mul, zero_mul]
      rw [h1', h2']
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    have hmom : ∀ x : Fin M,
        (∑ i, μ.prob i * (Matrix.trace (F o * (Uf i *
            lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re ^ 2)
          = ((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
              (Matrix.trace (F o)).re * (Matrix.trace (F o)).re +
            ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
              (Matrix.trace (F o * F o)).re := by
      intro x
      have hA : (F o).IsHermitian := (hFpsd o).isHermitian
      have h := h2 x (F o) (F o) hA hA
      have hLHS : (∑ i, μ.prob i * (Matrix.trace (F o * (Uf i *
            lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re ^ 2)
          = (∑ i, μ.prob i * (Matrix.trace (F o * (Uf i *
              lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re *
              (Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) *
                (Uf i)ᴴ))).re) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_two]
        ring
      rw [hLHS, h]
    have hxs : (∑ x : Fin M,
          (((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o)).re * (Matrix.trace (F o)).re +
            ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
              (Matrix.trace (F o * F o)).re))
        = (M : ℝ) * (((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
          (Matrix.trace (F o)).re * (Matrix.trace (F o)).re +
          ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o * F o)).re) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hall : (∑ x : Fin M, ∑ u : Fin N → I, π.prob u * ((q x u j).prob o)^2)
        = ∑ x : Fin M,
          (((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o)).re * (Matrix.trace (F o)).re +
            ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
              (Matrix.trace (F o * F o)).re) :=
      Finset.sum_congr rfl (fun x _ => (hstep x).trans (hmom x))
    rw [hall, hxs]
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hkey := theorem5_second_moment_bound d r α s (Matrix.trace (F o)).re
      (Matrix.trace (F o * F o)).re hd hr hrd hα0 hs
      (trace_sq_le_trace_sq' (F o) (hFpsd o))
    have hwo : (w).prob o = (Matrix.trace (F o)).re / (d : ℝ) := rfl
    have hcancel : (1 / (M : ℝ)) * ((M : ℝ) *
        (((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
          (Matrix.trace (F o)).re * (Matrix.trace (F o)).re +
          ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o * F o)).re)) =
        (((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
          (Matrix.trace (F o)).re * (Matrix.trace (F o)).re +
          ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o * F o)).re) := by
      field_simp
    rw [hcancel, hwo]
    simpa only [mul_assoc, pow_two, theorem5WrapperAllowance] using! hkey

  have hv : 0 ≤ theorem5WrapperAllowance d r α := by
    unfold theorem5WrapperAllowance
    exact div_nonneg
      (mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hRD))
      (mul_nonneg (le_of_lt hR) (by positivity))

  have hgood : ∀ x u, 0 < π.prob u →
      1 - δ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin N → O => g u ω = x),
        ∏ j : Fin N, (q x u j).prob (ω j) := by
    intro x u hpu
    have hall : ∀ j : Fin N, 0 < μ.prob (u j) := by
      intro j
      by_contra hn
      have hz : μ.prob (u j) = 0 := by linarith [μ.nonneg (u j)]
      have hzero : π.prob u = 0 := by
        rw [hπ_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ j) hz
      linarith
    have hq' : ∀ (j : Fin N) (o : O), (q x u j).prob o =
        (Matrix.trace (F o *
          (Uf (u j) * lemma8CodeState d r α (P x) * (Uf (u j))ᴴ))).re := by
      intro j o
      rw [hq_apply, hgated_pos x (u j) (hall j)]
    have hsum : (∑ ω ∈ Finset.univ.filter (fun ω : Fin N → O => g u ω = x),
        ∏ j : Fin N, (q x u j).prob (ω j))
        = ∑ ω ∈ Finset.univ.filter (fun ω : Fin N → O => g u ω = x),
          ∏ j : Fin N, (Matrix.trace (F (ω j) *
            (Uf (u j) * lemma8CodeState d r α (P x) * (Uf (u j))ᴴ))).re := by
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.prod_congr rfl
      intro j _
      exact hq' j (ω j)
    rw [hsum]
    exact hg x u
  have hfano := local_product_record_moment_fano_supported M N (Fin N → I) O
    π (fun _ => w) q (theorem5WrapperAllowance d r α) δ hv hmean hsecond g hgood
  simpa [theorem5WrapperDemand] using! hfano

end Qatlib.Papers.ClassShadows20.LowerBound.Shadows
