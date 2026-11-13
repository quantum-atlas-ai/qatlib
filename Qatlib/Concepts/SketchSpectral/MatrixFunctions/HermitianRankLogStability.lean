/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Mathlib.LinearAlgebra.Matrix.Rank
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic rank bounds for Hermitian matrix functions

This module proves operator norm perturbation and quasicommutator estimates for Hermitian
functional calculus under a scalar Lipschitz condition on the union of two spectra. The factor
`hermitianRankLogWeight` depends logarithmically on rank; finite-dimensional spectral calculus
and singular value estimates provide the background [Bhatia1997].

The estimates support the matrix-function stability analysis of [ChiaEtAl2022]. The proof
constructs low-rank approximations to weighted divided difference matrices, bounds their
residuals in Frobenius norm, and derives a logarithmic Schur multiplier estimate from reciprocal
singular value decay.

## Main statements

* `hermitianFunction_operator_rank_quasicommutator`: a universal quasicommutator bound with a
  logarithmic left-rank factor.
* `hermitianFunction_operator_min_rank_stability`: an operator perturbation bound using the
  smaller rank.
* `ddMat_hadamard_vecMulVec_sv_bound`: reciprocal singular value decay for weighted divided
  differences.

## References

* [Bhatia, 1997][Bhatia1997]
* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The logarithmic rank weight 1 + log(1 + n). -/
def hermitianRankLogWeight (n : ℕ) : ℝ := 1 + Real.log (1 + (n : ℝ))

/-- The function `f` satisfies the scalar Lipschitz bound with constant `L` on the union of the
spectra of `A` and `B`. -/
def hermitianPairScalarLipschitz {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (B : Matrix J J ℂ) (hB : B.IsHermitian) (f : ℝ → ℂ) (L : ℝ) : Prop :=
  ∀ x ∈ Set.range (orderedHermitianValues hA) ∪ Set.range (orderedHermitianValues hB),
    ∀ y ∈ Set.range (orderedHermitianValues hA) ∪ Set.range (orderedHermitianValues hB),
      ‖f x - f y‖ ≤ L * |x - y|

/-- The logarithmic rank weight is at least one. -/
theorem hermitianRankLogWeight_ge_one (n : ℕ) : 1 ≤ hermitianRankLogWeight n := by
  have h :=
      Real.log_nonneg (show (1 : ℝ) ≤ 1+(n : ℝ) by exact le_add_of_nonneg_right (Nat.cast_nonneg n))
  unfold hermitianRankLogWeight
  linarith

/-- The logarithmic rank weight is monotone in the rank parameter. -/
theorem hermitianRankLogWeight_mono : Monotone hermitianRankLogWeight := by
  intro m n hmn
  unfold hermitianRankLogWeight
  have hR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlog : Real.log (1+(m : ℝ)) ≤ Real.log (1+(n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- The spectral Lipschitz condition bounds the difference of function values at any eigenvalue
of `A` and any eigenvalue of `B`. -/
theorem hermitianPairScalarLipschitz_cross {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {A : Matrix I I ℂ} {hA : A.IsHermitian}
    {B : Matrix J J ℂ} {hB : B.IsHermitian} {f : ℝ → ℂ} {L : ℝ}
    (hf : hermitianPairScalarLipschitz A hA B hB f L)
    (i : Fin (Fintype.card I)) (j : Fin (Fintype.card J)) :
    ‖f (orderedHermitianValues hA i)-f (orderedHermitianValues hB j)‖ ≤
      L*|orderedHermitianValues hA i-orderedHermitianValues hB j| :=
  hf _ (Or.inl ⟨i,rfl⟩) _ (Or.inr ⟨j,rfl⟩)

/-- The spectral Lipschitz condition is invariant under exchanging the two Hermitian matrices. -/
theorem hermitianPairScalarLipschitz_swap {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {A : Matrix I I ℂ} {hA : A.IsHermitian}
    {B : Matrix J J ℂ} {hB : B.IsHermitian} {f : ℝ → ℂ} {L : ℝ}
    (hf : hermitianPairScalarLipschitz A hA B hB f L) :
    hermitianPairScalarLipschitz B hB A hA f L := by
  simpa only [hermitianPairScalarLipschitz, Set.union_comm] using hf

/-- In the ordered eigenbases of `A` and `B`, each entry of f(A)S - Sf(B) is the corresponding
entry of `S` multiplied by the difference of function values. -/
theorem hermitianFunction_quasicommutator_coordinates {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
    (S : Matrix I J ℂ) (f : ℝ → ℂ)
    (i : Fin (Fintype.card I)) (j : Fin (Fintype.card J)) :
    ((basisColumns (orderedHermitianBasis hA))ᴴ *
      (hermitianFunction A hA f*S-S*hermitianFunction B hB f) *
      basisColumns (orderedHermitianBasis hB)) i j =
    (f (orderedHermitianValues hA i)-f (orderedHermitianValues hB j)) *
      ((basisColumns (orderedHermitianBasis hA))ᴴ*S*basisColumns (orderedHermitianBasis hB)) i j := by
  have hleft := basis_adjoint_mul_spectralDiagonal (orderedHermitianBasis hA)
    (fun i => f (orderedHermitianValues hA i))
  have hright := spectralDiagonal_mul_basis (orderedHermitianBasis hB)
    (fun j => f (orderedHermitianValues hB j))
  have he : (basisColumns (orderedHermitianBasis hA))ᴴ *
      (hermitianFunction A hA f*S-S*hermitianFunction B hB f) *
      basisColumns (orderedHermitianBasis hB) =
      diagonal (fun i => f (orderedHermitianValues hA i)) *
        ((basisColumns (orderedHermitianBasis hA))ᴴ*S*basisColumns (orderedHermitianBasis hB)) -
      ((basisColumns (orderedHermitianBasis hA))ᴴ*S*basisColumns (orderedHermitianBasis hB)) *
        diagonal (fun j => f (orderedHermitianValues hB j)) := by
    calc
      _ = ((basisColumns (orderedHermitianBasis hA))ᴴ*hermitianFunction A hA f) *
          (S*basisColumns (orderedHermitianBasis hB)) -
        ((basisColumns (orderedHermitianBasis hA))ᴴ*S) *
          (hermitianFunction B hB f*basisColumns (orderedHermitianBasis hB)) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = _ := by
        change ((basisColumns (orderedHermitianBasis hA))ᴴ*spectralDiagonal _ _) * _ -
          _ * (spectralDiagonal _ _*basisColumns (orderedHermitianBasis hB)) = _
        rw [hleft,hright]
        simp only [Matrix.mul_assoc]
  rw [he, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- In the ordered eigenbases, each entry of AS - SB is the corresponding entry of `S`
multiplied by the eigenvalue difference. -/
theorem hermitian_quasicommutator_coordinates {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
    (S : Matrix I J ℂ) (i : Fin (Fintype.card I)) (j : Fin (Fintype.card J)) :
    ((basisColumns (orderedHermitianBasis hA))ᴴ * (A*S-S*B) *
      basisColumns (orderedHermitianBasis hB)) i j =
    ((orderedHermitianValues hA i-orderedHermitianValues hB j : ℝ) : ℂ) *
      ((basisColumns (orderedHermitianBasis hA))ᴴ*S*basisColumns (orderedHermitianBasis hB)) i j := by
  have h := hermitianFunction_quasicommutator_coordinates A hA B hB S (fun x => (x : ℂ)) i j
  have ha : hermitianFunction A hA (fun x => (x : ℂ)) = A := (orderedHermitian_diagonal hA).symm
  have hb : hermitianFunction B hB (fun x => (x : ℂ)) = B := (orderedHermitian_diagonal hB).symm
  simpa only [ha,hb,Complex.ofReal_sub] using h

/-- Passing to the ordered eigenbases of the two Hermitian matrices preserves the operator norm
of a rectangular matrix. -/
theorem hermitian_pair_coordinates_norm {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
    (S : Matrix I J ℂ) :
    ‖(basisColumns (orderedHermitianBasis hA))ᴴ*S*basisColumns (orderedHermitianBasis hB)‖ = ‖S‖ := by
  let U := basisColumns (orderedHermitianBasis hA)
  let V := basisColumns (orderedHermitianBasis hB)
  have hu : ‖U‖ ≤ 1 := basisColumns_norm_le _
  have hv : ‖V‖ ≤ 1 := basisColumns_norm_le _
  have huc : ‖Uᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hu
  have hvc : ‖Vᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hv
  have hbound {K O P Q : Type} [Fintype K] [DecidableEq K]
      [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
      (X : Matrix O K ℂ) (M : Matrix K P ℂ) (Y : Matrix P Q ℂ)
      (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) : ‖X*M*Y‖ ≤ ‖M‖ := by
    calc
      _ ≤ (‖X‖*‖M‖)*‖Y‖ := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1*‖M‖)*1 := by gcongr
      _ = _ := by ring
  apply le_antisymm (hbound Uᴴ S V huc hv)
  have he : U*(Uᴴ*S*V)*Vᴴ = S := by
    dsimp [U,V]
    simp only [← Matrix.mul_assoc, basisColumns_mul_adjoint, Matrix.one_mul]
    simp only [Matrix.mul_assoc, basisColumns_mul_adjoint, Matrix.mul_one]
  calc
    ‖S‖ = ‖U*(Uᴴ*S*V)*Vᴴ‖ := congrArg norm he.symm
    _ ≤ ‖Uᴴ*S*V‖ := hbound U (Uᴴ*S*V) Vᴴ hu hvc

/-- The diagonal matrix of ordered eigenvalues of a Hermitian matrix has the same rank as the
original matrix. -/
theorem orderedHermitian_diagonal_rank {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (diagonal (fun i => (orderedHermitianValues hA i : ℂ))).rank = A.rank := by
  let U := basisColumns (orderedHermitianBasis hA)
  let D := diagonal (fun i => (orderedHermitianValues hA i : ℂ))
  have ha : A = U*D*Uᴴ := orderedHermitian_diagonal hA
  have hd : D = Uᴴ*A*U := by
    rw [ha]
    dsimp [U]
    simp only [← Matrix.mul_assoc, basisColumns_adjoint_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc, basisColumns_adjoint_mul, Matrix.mul_one]
  change D.rank = A.rank
  apply Nat.le_antisymm
  · rw [hd]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [ha]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- The number of nonzero ordered eigenvalues, counted with multiplicity, equals the rank. -/
theorem orderedHermitian_nonzero_card {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    Fintype.card {i // orderedHermitianValues hA i ≠ 0} = A.rank := by
  have h := orderedHermitian_diagonal_rank A hA
  simpa only [Matrix.rank_diagonal, ne_eq, Complex.ofReal_eq_zero] using h

/-- Every ordered eigenvalue of a Hermitian matrix of rank zero is zero. -/
theorem orderedHermitianValues_eq_zero_of_rank_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (hr : A.rank = 0)
    (i : Fin (Fintype.card I)) : orderedHermitianValues hA i = 0 := by
  have hc : Fintype.card {j // orderedHermitianValues hA j ≠ 0} = 0 :=
    (orderedHermitian_nonzero_card A hA).trans hr
  have hi : IsEmpty {j // orderedHermitianValues hA j ≠ 0} := Fintype.card_eq_zero_iff.mp hc
  by_contra hn
  exact hi.false ⟨i, hn⟩

/-- Functional calculus on a Hermitian matrix of rank zero gives `f 0` times the identity. -/
theorem hermitianFunction_of_rank_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (hr : A.rank = 0) (f : ℝ → ℂ) :
    hermitianFunction A hA f = f 0 • (1 : Matrix I I ℂ) := by
  unfold hermitianFunction
  have hv : (fun i => f (orderedHermitianValues hA i)) = fun _ => f 0 := by
    funext i
    rw [orderedHermitianValues_eq_zero_of_rank_zero A hA hr i]
  rw [hv]
  exact spectralDiagonal_const _ _

/-- The number of distinct eigenvalues of a Hermitian matrix is at most its rank plus one. -/
theorem orderedHermitian_spectrum_card_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (Finset.univ.image (orderedHermitianValues hA)).card ≤ A.rank+1 := by
  classical
  let t := Finset.univ.filter (fun i => orderedHermitianValues hA i ≠ 0)
  have ht : t.card = A.rank := by
    rw [← orderedHermitian_nonzero_card A hA]
    exact (Fintype.card_subtype (fun i => orderedHermitianValues hA i ≠ 0)).symm
  have hs : Finset.univ.image (orderedHermitianValues hA) ⊆
      insert 0 (t.image (orderedHermitianValues hA)) := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases hi : orderedHermitianValues hA i = 0
    · simp [hi]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i, by simp [t,hi], rfl⟩
  calc
    _ ≤ (insert 0 (t.image (orderedHermitianValues hA))).card := Finset.card_le_card hs
    _ ≤ (t.image (orderedHermitianValues hA)).card+1 := Finset.card_insert_le _ _
    _ ≤ t.card+1 := Nat.add_le_add_right (Finset.card_image_le) 1
    _ = _ := by rw [ht]

/-- One plus the logarithm of the number of distinct eigenvalues is bounded by the logarithmic
rank weight. -/
theorem orderedHermitian_log_spectrum_card_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    1+Real.log ((Finset.univ.image (orderedHermitianValues hA)).card : ℝ) ≤
      hermitianRankLogWeight A.rank := by
  let n := (Finset.univ.image (orderedHermitianValues hA)).card
  change 1+Real.log (n : ℝ) ≤ hermitianRankLogWeight A.rank
  by_cases hn : n = 0
  · simpa only [hn, Nat.cast_zero, Real.log_zero, add_zero] using
      hermitianRankLogWeight_ge_one A.rank
  · have hp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hc : n ≤ A.rank+1 := orderedHermitian_spectrum_card_le A hA
    have hc' : (n : ℝ) ≤ (A.rank : ℝ)+1 := by exact_mod_cast hc
    have hl : Real.log (n : ℝ) ≤ Real.log (1+(A.rank : ℝ)) :=
      Real.log_le_log hp (by linarith)
    unfold hermitianRankLogWeight
    linarith

/-- The divided difference between eigenvalues of the two matrices has norm at most `L`, with
value zero at coincident eigenvalues. -/
theorem hermitianPairScalarLipschitz_divided_difference_norm_le {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {A : Matrix I I ℂ} {hA : A.IsHermitian} {B : Matrix J J ℂ} {hB : B.IsHermitian}
    {f : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hf : hermitianPairScalarLipschitz A hA B hB f L)
    (i : Fin (Fintype.card I)) (j : Fin (Fintype.card J)) :
    ‖if orderedHermitianValues hA i = orderedHermitianValues hB j then (0 : ℂ) else
      (f (orderedHermitianValues hA i)-f (orderedHermitianValues hB j)) /
        ((orderedHermitianValues hA i-orderedHermitianValues hB j : ℝ) : ℂ)‖ ≤ L := by
  by_cases he : orderedHermitianValues hA i = orderedHermitianValues hB j
  · simpa only [if_pos he, norm_zero] using hL
  · rw [if_neg he, norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr he))).mpr
    exact hermitianPairScalarLipschitz_cross hf i j

/-- Each spectral coordinate of f(A)S - Sf(B) is the divided difference times the corresponding
coordinate of AS - SB. -/
theorem hermitianFunction_quasicommutator_divided_difference {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
    (S : Matrix I J ℂ) (f : ℝ → ℂ)
    (i : Fin (Fintype.card I)) (j : Fin (Fintype.card J)) :
    ((basisColumns (orderedHermitianBasis hA))ᴴ *
      (hermitianFunction A hA f*S-S*hermitianFunction B hB f) *
      basisColumns (orderedHermitianBasis hB)) i j =
    (if orderedHermitianValues hA i = orderedHermitianValues hB j then 0 else
      (f (orderedHermitianValues hA i)-f (orderedHermitianValues hB j)) /
        ((orderedHermitianValues hA i-orderedHermitianValues hB j : ℝ) : ℂ)) *
      ((basisColumns (orderedHermitianBasis hA))ᴴ*(A*S-S*B)*
        basisColumns (orderedHermitianBasis hB)) i j := by
  rw [hermitianFunction_quasicommutator_coordinates, hermitian_quasicommutator_coordinates]
  by_cases he : orderedHermitianValues hA i = orderedHermitianValues hB j
  · simp [he]
  · have hn : ((orderedHermitianValues hA i-orderedHermitianValues hB j : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr he)
    simp only [if_neg he]
    field_simp

/-- A uniform quasicommutator bound depending on the left rank implies a functional calculus
perturbation bound depending on the smaller rank. -/
theorem hermitianFunction_min_rank_stability_of_quasicommutator_bound (c₀ : ℝ)
    (hq : ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix I I ℂ) (hB : B.IsHermitian)
      (S : Matrix I I ℂ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
      hermitianPairScalarLipschitz A hA B hB f L →
      ‖hermitianFunction A hA f*S-S*hermitianFunction B hB f‖ ≤
        c₀*hermitianRankLogWeight A.rank*L*‖A*S-S*B‖) :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
      (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
      hermitianPairScalarLipschitz A hA B hB f L →
      ‖hermitianFunction A hA f-hermitianFunction B hB f‖ ≤
        c₀*hermitianRankLogWeight (min A.rank B.rank)*L*‖A-B‖ := by
  intro I _ _ A B hA hB f L hL hf
  by_cases hr : A.rank ≤ B.rank
  · simpa only [Nat.min_eq_left hr, Matrix.mul_one, Matrix.one_mul] using
      hq I A hA B hB 1 f L hL hf
  · have hr' := le_of_not_ge hr
    simpa only [Nat.min_eq_right hr', Matrix.mul_one, Matrix.one_mul, norm_sub_rev] using
      hq I B hB A hA 1 f L hL (hermitianPairScalarLipschitz_swap hf)

/-- If `A` has rank zero, the spectral Lipschitz condition bounds the operator norm of f(A) -
f(B) by L times the norm of A - B. -/
theorem hermitianFunction_operator_stability_rank_zero {I : Type}
    [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hr : A.rank = 0)
    (f : ℝ → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hf : hermitianPairScalarLipschitz A hA B hB f L) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤ L * ‖A - B‖ := by
  rw [hermitianFunction_of_rank_zero A hA hr f]
  change ‖f 0 • (1 : Matrix I I ℂ) - spectralDiagonal (orderedHermitianBasis hB)
    (fun i => f (orderedHermitianValues hB i))‖ ≤ _
  rw [← spectralDiagonal_const (orderedHermitianBasis hB) (f 0)]
  apply spectralDiagonal_error_le _ _ _ (mul_nonneg hL (norm_nonneg _))
  intro i
  have hzero := orderedHermitianValues_eq_zero_of_rank_zero A hA hr i
  have hl := orderedHermitian_sub_le_norm A B hA hB i
  have hu := orderedHermitian_sub_le_norm B A hB hA i
  rw [hzero, zero_sub] at hl
  rw [hzero, sub_zero, norm_sub_rev] at hu
  have hab : |0 - orderedHermitianValues hB i| ≤ ‖A - B‖ := by
    rw [zero_sub, abs_neg]
    exact abs_le.mpr ⟨by linarith, hu⟩
  have hc := hermitianPairScalarLipschitz_cross hf i i
  rw [hzero] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hab hL)

/-- When the smaller rank is zero, the functional calculus perturbation bound holds with the
logarithmic weight of that rank. -/
theorem hermitianFunction_operator_stability_min_rank_zero {I : Type}
    [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hr : min A.rank B.rank = 0)
    (f : ℝ → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hf : hermitianPairScalarLipschitz A hA B hB f L) :
    ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
      hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ := by
  have hbase : ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤ L * ‖A - B‖ := by
    by_cases h : A.rank = 0
    · exact hermitianFunction_operator_stability_rank_zero A B hA hB h f L hL hf
    · have h' : B.rank = 0 := by omega
      simpa only [norm_sub_rev] using
        hermitianFunction_operator_stability_rank_zero B A hB hA h' f L hL
          (hermitianPairScalarLipschitz_swap hf)
  simpa [hr, hermitianRankLogWeight] using hbase

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open WithLp (toLp ofLp)
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- The matrix of divided differences of `f` on two real eigenvalue families, taking value zero
when the arguments coincide. -/
def ddMat {I J : Type} (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) : Matrix I J ℂ :=
  Matrix.of fun i j => if eigL i = eigR j then 0
    else (f (eigL i) - f (eigR j)) / ((eigL i - eigR j : ℝ) : ℂ)

/-- The scalar Lipschitz condition for `f` on the union of the ranges of two real eigenvalue
families. -/
def lipUnion {I J : Type} (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) (L : ℝ) : Prop :=
  ∀ x ∈ Set.range eigL ∪ Set.range eigR, ∀ y ∈ Set.range eigL ∪ Set.range eigR,
    ‖f x - f y‖ ≤ L * |x - y|

/-- Exchanging the two arguments leaves a divided difference unchanged. -/
theorem ddMat_apply_swap {I J : Type} (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ)
    (i : I) (j : J) :
    ddMat eigL eigR f i j = ddMat eigR eigL f j i := by
  unfold ddMat
  simp only [Matrix.of_apply]
  by_cases h : eigL i = eigR j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
    have hne : ((eigL i - eigR j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr h
    have hd : ((eigR j - eigL i : ℝ) : ℂ) = -((eigL i - eigR j : ℝ) : ℂ) := by
      push_cast; ring
    rw [hd]
    field_simp
    ring

/-- Transposing the divided difference matrix exchanges its two eigenvalue families. -/
theorem ddMat_transpose {I J : Type} [DecidableEq I] (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) :
    (ddMat eigL eigR f)ᵀ = ddMat eigR eigL f := by
  ext i j
  simp only [Matrix.transpose_apply]
  exact ddMat_apply_swap eigL eigR f j i

/-- The Lipschitz condition on the union of the ranges is invariant under exchanging the
families. -/
theorem lipUnion_swap {I J : Type} (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) (L : ℝ)
    (h : lipUnion eigL eigR f L) : lipUnion eigR eigL f L := by
  simpa only [lipUnion, Set.union_comm] using h
omit [Fintype O] [DecidableEq O] in

/-- The dimension of the range of the Euclidean linear map associated with a matrix equals its
matrix rank. -/
theorem finrank_range_toEuclideanLin_eq_rank (A : Matrix O I ℂ) :
    Module.finrank ℂ A.toEuclideanLin.range = A.rank := by
  have hcomp : (A.toEuclideanLin : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ O) =
      (WithLp.linearEquiv 2 ℂ (O → ℂ)).symm.toLinearMap.comp
        (A.mulVecLin.comp (WithLp.linearEquiv 2 ℂ (I → ℂ)).toLinearMap) := by
    ext1 x
    apply (WithLp.linearEquiv 2 ℂ (O → ℂ)).injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv,
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply', Matrix.mulVecLin_apply]
  rw [Matrix.rank, hcomp, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (WithLp.linearEquiv 2 ℂ (I → ℂ)).range,
    LinearEquiv.finrank_map_eq]

/-- A matrix whose rows factor through selected eigenvalue labels has rank at most the number of
selected distinct labels. -/
theorem rank_of_row_factor_restrict {I J V : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] [DecidableEq V] (eigL : I → V) (P : V → Prop) [DecidablePred P]
    (R : V → J → ℂ) (u : I → ℂ) :
    (Matrix.of fun i j => (if P (eigL i) then u i else 0) * R (eigL i) j).rank ≤
      ((Finset.univ.image eigL).filter P).card := by
  set F := (Finset.univ.image eigL).filter P with hF
  have hdecomp :
      Matrix.of (fun i j => (if P (eigL i) then u i else 0) * R (eigL i) j) =
        Matrix.of (fun i (t : { t // t ∈ F }) =>
            (if P (eigL i) then u i else 0) * (if eigL i = t.val then 1 else 0)) *
          Matrix.of (fun (t : { t // t ∈ F }) j => R t.val j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    by_cases h : P (eigL i)
    · have hmem : eigL i ∈ F := by
        rw [hF, Finset.mem_filter]
        exact ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩, h⟩
      rw [Finset.sum_eq_single ⟨eigL i, hmem⟩]
      · simp [h]
      · intro b _ hb
        by_cases hbv : eigL i = b.val
        · exact absurd (Subtype.ext hbv.symm) hb
        · simp [hbv]
      · intro hcontra
        exact absurd (Finset.mem_univ _) hcontra
    · simp [h]
  rw [hdecomp]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_coe F))

/-- A matrix whose columns factor through selected eigenvalue labels has rank at most the number
of selected distinct labels. -/
theorem rank_of_col_factor_restrict {I J V : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] [DecidableEq V] (eigR : J → V) (P : V → Prop) [DecidablePred P]
    (R : V → I → ℂ) (w : J → ℂ) :
    (Matrix.of fun i j => R (eigR j) i * (if P (eigR j) then w j else 0)).rank ≤
      ((Finset.univ.image eigR).filter P).card := by
  have hT : (Matrix.of fun i j => R (eigR j) i * (if P (eigR j) then w j else 0))ᵀ =
      Matrix.of fun j i => (if P (eigR j) then w j else 0) * R (eigR j) i := by
    ext j i
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact mul_comm _ _
  rw [← Matrix.rank_transpose (Matrix.of fun i j => R (eigR j) i * (if P (eigR j) then w j else 0)),
    hT]
  exact rank_of_row_factor_restrict eigR P R w

/-- The sum of the first `n` reciprocal positive integers is at most 1 + log n. -/
theorem sum_range_one_div_le_one_add_log (n : ℕ) :
    ∑ q ∈ Finset.range n, (1 : ℝ)/((q : ℝ)+1) ≤ 1 + Real.log n := by
  have hsum : ∀ m : ℕ,
      ∑ q ∈ Finset.range m, (1 : ℝ)/((q : ℝ)+1) = (harmonic m : ℝ) := by
    intro m
    induction m with
    | zero => simp [harmonic_zero]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      push_cast
      rw [one_div]
  rw [hsum n]
  exact harmonic_le_one_add_log n

/-- The sum of the squared singular values equals the squared spectral Frobenius norm. -/
theorem sum_sq_matrixSingularValues_eq_spectralFrobenius_sq {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (X : Matrix O I ℂ) :
    ∑ i : Fin (Fintype.card I), (matrixSingularValues X i)^2 = spectralFrobenius X ^ 2 :=
  (spectralFrobenius_sq_singular X).symm

/-- The square of singular value `q`, multiplied by q + 1, is at most the squared spectral
Frobenius norm. -/
theorem matrixSingularValues_sq_mul_le_spectralFrobenius_sq {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (X : Matrix O I ℂ) (q : ℕ) :
    ((q+1 : ℕ) : ℝ) * (matrixSingularValues X q)^2 ≤ spectralFrobenius X ^ 2 := by
  by_cases h : Fintype.card I ≤ q
  · rw [matrixSingularValues_of_card_le X h]
    simp
  · have hq : q < Fintype.card I := not_le.mp h
    have hn : q + 1 ≤ Fintype.card I := hq
    have h1 : ((q+1 : ℕ) : ℝ) * (matrixSingularValues X q)^2 =
        ∑ _i ∈ Finset.range (q+1), (matrixSingularValues X q)^2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : ∑ i ∈ Finset.range (q+1), (matrixSingularValues X q)^2 ≤
        ∑ i ∈ Finset.range (q+1), (matrixSingularValues X i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hord : matrixSingularValues X q ≤ matrixSingularValues X i := by
        simp only [matrixSingularValues_apply]
        exact X.toEuclideanLin.singularValues_antitone hiq
      exact (sq_le_sq₀ (matrixSingularValues_nonneg X q)
        (matrixSingularValues_nonneg X i)).mpr hord
    have h3 : ∑ i ∈ Finset.range (q+1), (matrixSingularValues X i)^2 ≤
        ∑ i ∈ Finset.range (Fintype.card I), (matrixSingularValues X i)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn)
        (fun i _ _ => sq_nonneg _)
    have h4 : ∑ i ∈ Finset.range (Fintype.card I), (matrixSingularValues X i)^2 =
        spectralFrobenius X ^ 2 := by
      rw [← sum_sq_matrixSingularValues_eq_spectralFrobenius_sq X]
      exact (Fin.sum_univ_eq_sum_range
        (fun i => (matrixSingularValues X i)^2) (Fintype.card I)).symm
    calc ((q+1 : ℕ) : ℝ) * (matrixSingularValues X q)^2
        = ∑ _i ∈ Finset.range (q+1), (matrixSingularValues X q)^2 := h1
      _ ≤ ∑ i ∈ Finset.range (q+1), (matrixSingularValues X i)^2 := h2
      _ ≤ ∑ i ∈ Finset.range (Fintype.card I), (matrixSingularValues X i)^2 := h3
      _ = spectralFrobenius X ^ 2 := h4

/-- The trace norm of a finite matrix, defined as the sum of its singular values. -/
noncomputable def matrixTraceNorm {O I : Type} [Fintype O] [Fintype I] (X : Matrix O I ℂ) : ℝ :=
  ∑ q : Fin (Fintype.card I), matrixSingularValues X q

/-- A nonnegative bound on all matrix coefficients between unit Euclidean vectors bounds the
matrix operator norm. -/
theorem l2_opNorm_le_of_inner_le {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J), ‖u‖ = 1 → ‖v‖ = 1 →
      ‖inner ℂ u (M.toEuclideanLin v)‖ ≤ C) :
    ‖M‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  show ‖M.toEuclideanLin v‖ ≤ C * ‖v‖
  by_cases hv : v = 0
  · simp [hv]
  · by_cases hMv : M.toEuclideanLin v = 0
    · rw [hMv, norm_zero]
      exact mul_nonneg hC (norm_nonneg v)
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hnMv : ‖M.toEuclideanLin v‖ ≠ 0 := norm_ne_zero_iff.mpr hMv
      have hw : ‖(‖v‖ : ℂ)⁻¹ • v‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v),
          inv_mul_cancel₀ hnv]
      have hu : ‖(‖M.toEuclideanLin v‖ : ℂ)⁻¹ • M.toEuclideanLin v‖ = 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg (M.toEuclideanLin v)), inv_mul_cancel₀ hnMv]
      have hbound := h _ _ hu hw
      have hnorm : ‖inner ℂ ((‖M.toEuclideanLin v‖ : ℂ)⁻¹ • M.toEuclideanLin v)
            (M.toEuclideanLin ((‖v‖ : ℂ)⁻¹ • v))‖ = ‖M.toEuclideanLin v‖ * ‖v‖⁻¹ := by
        rw [map_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
        simp only [starRingEnd_apply, norm_star, norm_mul, norm_inv, norm_pow, Complex.norm_real,
          RCLike.norm_ofReal, Real.norm_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
        calc ‖M.toEuclideanLin v‖⁻¹ * (‖v‖⁻¹ * ‖M.toEuclideanLin v‖ ^ 2)
            = (‖M.toEuclideanLin v‖⁻¹ * ‖M.toEuclideanLin v‖ * ‖M.toEuclideanLin v‖) * ‖v‖⁻¹ := by
              ring
          _ = ‖M.toEuclideanLin v‖ * ‖v‖⁻¹ := by rw [inv_mul_cancel₀ hnMv, one_mul]
      rw [hnorm] at hbound
      have hvv := mul_le_mul_of_nonneg_right hbound (norm_nonneg v)
      rw [mul_assoc, inv_mul_cancel₀ hnv, mul_one] at hvv
      exact hvv

/-- A matrix coefficient of a Hadamard product is expressed as a trace pairing with an outer
product. -/
theorem inner_toEuclideanLin_hadamard_eq_trace {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (D K : Matrix I J ℂ) (u : I → ℂ) (v : J → ℂ) :
    inner ℂ (toEuclidean_fromVec u) ((D ⊙ K).toEuclideanLin (toEuclidean_fromVec v)) =
      Matrix.trace (K * ((Dᵀ) ⊙ Matrix.vecMulVec v (star u))) := by
  have hmul : ∀ (M : Matrix I J ℂ) (w : EuclideanSpace ℂ J) (i : I),
      (M.toEuclideanLin w) i = ∑ j, M i j * w j := fun M w i => rfl
  have hstar : ∀ (c : I → ℂ) (i : I), (star c) i = star (c i) := fun c i => rfl
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply, toEuclidean_fromVec_apply]
  rw [show Matrix.trace (K * (Dᵀ ⊙ Matrix.vecMulVec v (star u)))
      = ∑ i, (K * (Dᵀ ⊙ Matrix.vecMulVec v (star u))) i i from rfl]
  simp_rw [Matrix.mul_apply, Matrix.hadamard_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply,
    hstar]
  apply Finset.sum_congr rfl; intro i _
  rw [hmul]
  simp_rw [Matrix.hadamard_apply, toEuclidean_fromVec_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  rw [starRingEnd_apply]
  ring

/-- The trace pairing of a matrix with an outer product equals the associated Euclidean inner
product. -/
private theorem trace_mul_vecMulVec_eq_inner {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (K : Matrix I J ℂ) (a : EuclideanSpace ℂ J) (b : EuclideanSpace ℂ I) :
    Matrix.trace (K * Matrix.vecMulVec a (star b)) = inner ℂ b (K.toEuclideanLin a) := by
  have hmul : ∀ (M : Matrix I J ℂ) (w : EuclideanSpace ℂ J) (i : I),
      (M.toEuclideanLin w) i = ∑ j, M i j * w j := fun M w i => rfl
  have hstar : ∀ (c : I → ℂ) (i : I), (star c) i = star (c i) := fun c i => rfl
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  rw [show Matrix.trace (K * Matrix.vecMulVec a (star b))
      = ∑ i, (K * Matrix.vecMulVec a (star b)) i i from rfl]
  simp_rw [Matrix.mul_apply, Matrix.vecMulVec_apply, hstar]
  apply Finset.sum_congr rfl; intro i _
  rw [hmul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  rw [starRingEnd_apply]
  ring

/-- The absolute value of a trace pairing is bounded by the operator norm of the first matrix
times the trace norm of the second. -/
theorem norm_trace_mul_le_traceNorm {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (K : Matrix I J ℂ) (X : Matrix J I ℂ) :
    ‖Matrix.trace (K * X)‖ ≤ ‖K‖ * matrixTraceNorm X := by
  have ha : ∀ q : Fin (Fintype.card I), ‖leftSingularVector X q‖ ≤ 1 := by
    intro q
    by_cases hσ : matrixSingularValues X q = 0
    · rw [leftSingularVector_eq_zero X q hσ, norm_zero]
      exact zero_le_one
    · exact (norm_leftSingularVector X q ((matrixSingularValues_pos_iff_lt_finrank_range X).1
        (lt_of_le_of_ne' (matrixSingularValues_nonneg X q) hσ))).le
  have hterm : ∀ q : Fin (Fintype.card I),
      ‖inner ℂ (rightSingularBasis X q) (K.toEuclideanLin (leftSingularVector X q))‖ ≤ ‖K‖ := by
    intro q
    calc ‖inner ℂ (rightSingularBasis X q) (K.toEuclideanLin (leftSingularVector X q))‖
        ≤ ‖rightSingularBasis X q‖ * ‖K.toEuclideanLin (leftSingularVector X q)‖ :=
          norm_inner_le_norm _ _
      _ = 1 * ‖K.toEuclideanLin (leftSingularVector X q)‖ := by rw [norm_rightSingularBasis]
      _ ≤ 1 * (‖K‖ * ‖leftSingularVector X q‖) :=
          mul_le_mul le_rfl (Matrix.l2_opNorm_mulVec K (leftSingularVector X q)) (norm_nonneg _)
            zero_le_one
      _ ≤ 1 * (‖K‖ * 1) :=
          mul_le_mul le_rfl (mul_le_mul_of_nonneg_left (ha q) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
      _ = ‖K‖ := by rw [mul_one, one_mul]
  have key : ∀ q : Fin (Fintype.card I),
      ‖(matrixSingularValues X q : ℂ) * inner ℂ (rightSingularBasis X q)
          (K.toEuclideanLin (leftSingularVector X q))‖ ≤ matrixSingularValues X q * ‖K‖ := by
    intro q
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (matrixSingularValues_nonneg X q)]
    exact mul_le_mul_of_nonneg_left (hterm q) (matrixSingularValues_nonneg X q)
  conv_lhs => rw [matrix_eq_sum_singularVectors X]
  rw [Matrix.mul_sum]
  simp_rw [Matrix.mul_smul]
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, smul_eq_mul, trace_mul_vecMulVec_eq_inner K]
  calc ‖∑ q : Fin (Fintype.card I), (matrixSingularValues X q : ℂ) * inner ℂ (rightSingularBasis X q)
          (K.toEuclideanLin (leftSingularVector X q))‖
      ≤ ∑ q : Fin (Fintype.card I), ‖(matrixSingularValues X q : ℂ) * inner ℂ
          (rightSingularBasis X q) (K.toEuclideanLin (leftSingularVector X q))‖ := norm_sum_le _ _
    _ ≤ ∑ q : Fin (Fintype.card I), matrixSingularValues X q * ‖K‖ :=
        Finset.sum_le_sum fun q _ => key q
    _ = ‖K‖ * matrixTraceNorm X := by
        rw [show matrixTraceNorm X = ∑ q : Fin (Fintype.card I), matrixSingularValues X q from rfl,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- The singular value of a sum at index a + b is bounded by the sum of the singular values at
indices `a` and `b`. -/
theorem matrixSingularValues_add_le (X Y : Matrix O I ℂ) (a b : ℕ) :
    matrixSingularValues (X + Y) (a + b) ≤
      matrixSingularValues X a + matrixSingularValues Y b := by
  by_cases hab : a + b < Fintype.card I
  · have ha : a < Fintype.card I := by omega
    have hb : b < Fintype.card I := by omega
    let S1 := spectralSpan (rightSingularBasis (X+Y)) (Finset.Iic ⟨a+b, hab⟩)
    let S2 := spectralSpan (rightSingularBasis X) (Finset.Ici ⟨a, ha⟩)
    let S3 := spectralSpan (rightSingularBasis Y) (Finset.Ici ⟨b, hb⟩)
    have hS1 : Module.finrank ℂ S1 = a+b+1 := by
      rw [spectralSpan_finrank, Fin.card_Iic]
    have hS2 : Module.finrank ℂ S2 = Fintype.card I - a := by
      rw [spectralSpan_finrank, Fin.card_Ici]
    have hS3 : Module.finrank ℂ S3 = Fintype.card I - b := by
      rw [spectralSpan_finrank, Fin.card_Ici]
    have hdim12 := Submodule.finrank_sup_add_finrank_inf_eq S1 S2
    have hdim123 := Submodule.finrank_sup_add_finrank_inf_eq (S1 ⊓ S2) S3
    have hsup12 : Module.finrank ℂ ↥(S1 ⊔ S2) ≤ Fintype.card I := by
      simpa only [finrank_euclideanSpace] using Submodule.finrank_le (S1 ⊔ S2)
    have hsup123 : Module.finrank ℂ ↥((S1 ⊓ S2) ⊔ S3) ≤ Fintype.card I := by
      simpa only [finrank_euclideanSpace] using Submodule.finrank_le ((S1 ⊓ S2) ⊔ S3)
    have hinf : S1 ⊓ S2 ⊓ S3 ≠ ⊥ := by
      intro hz
      rw [hz, finrank_bot] at hdim123
      omega
    obtain ⟨v, hv, hv0⟩ := (S1 ⊓ S2 ⊓ S3).ne_bot_iff.mp hinf
    rw [Submodule.mem_inf, Submodule.mem_inf] at hv
    have hv1 : v ∈ spectralSpan (rightSingularBasis (X+Y)) (Finset.Iic ⟨a+b, hab⟩) := hv.1.1
    have hv2 : v ∈ spectralSpan (rightSingularBasis X) (Finset.Ici ⟨a, ha⟩) := hv.1.2
    have hv3 : v ∈ spectralSpan (rightSingularBasis Y) (Finset.Ici ⟨b, hb⟩) := hv.2
    have hlow2 : (matrixSingularValues (X+Y) (a+b))^2*‖v‖^2 ≤
        ‖(X+Y).toEuclideanLin v‖^2 := by
      rw [singular_norm_image_sq, spectral_norm_sq_basis (rightSingularBasis (X+Y)),
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ≤ ⟨a+b, hab⟩
      · have horder := (X+Y).toEuclideanLin.singularValues_antitone
          (Fin.le_iff_val_le_val.mp hj)
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (matrixSingularValues_nonneg _ _) (matrixSingularValues_nonneg _ _)).mpr
            horder) (Complex.normSq_nonneg _)
      · rw [spectralSpan_repr_zero _ _ hv1 (by simpa using hj)]
        simp
    have hupX2 : ‖X.toEuclideanLin v‖^2 ≤ (matrixSingularValues X a)^2*‖v‖^2 := by
      rw [singular_norm_image_sq, spectral_norm_sq_basis (rightSingularBasis X), Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : ⟨a, ha⟩ ≤ j
      · have horder := X.toEuclideanLin.singularValues_antitone (Fin.le_iff_val_le_val.mp hj)
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (matrixSingularValues_nonneg _ _) (matrixSingularValues_nonneg _ _)).mpr
            horder) (Complex.normSq_nonneg _)
      · rw [spectralSpan_repr_zero _ _ hv2 (by simpa using hj)]
        simp
    have hupY2 : ‖Y.toEuclideanLin v‖^2 ≤ (matrixSingularValues Y b)^2*‖v‖^2 := by
      rw [singular_norm_image_sq, spectral_norm_sq_basis (rightSingularBasis Y), Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : ⟨b, hb⟩ ≤ j
      · have horder := Y.toEuclideanLin.singularValues_antitone (Fin.le_iff_val_le_val.mp hj)
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (matrixSingularValues_nonneg _ _) (matrixSingularValues_nonneg _ _)).mpr
            horder) (Complex.normSq_nonneg _)
      · rw [spectralSpan_repr_zero _ _ hv3 (by simpa using hj)]
        simp
    have hlowNorm : matrixSingularValues (X+Y) (a+b)*‖v‖ ≤ ‖(X+Y).toEuclideanLin v‖ :=
      (sq_le_sq₀ (mul_nonneg (matrixSingularValues_nonneg _ _) (norm_nonneg _))
        (norm_nonneg _)).mp (by simpa only [mul_pow] using hlow2)
    have hupX : ‖X.toEuclideanLin v‖ ≤ matrixSingularValues X a*‖v‖ :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (matrixSingularValues_nonneg _ _) (norm_nonneg _))).mp
        (by simpa only [mul_pow] using hupX2)
    have hupY : ‖Y.toEuclideanLin v‖ ≤ matrixSingularValues Y b*‖v‖ :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (matrixSingularValues_nonneg _ _) (norm_nonneg _))).mp
        (by simpa only [mul_pow] using hupY2)
    have hsum : ‖(X+Y).toEuclideanLin v‖ ≤
        (matrixSingularValues X a + matrixSingularValues Y b)*‖v‖ := by
      have hadd : (X+Y).toEuclideanLin v = X.toEuclideanLin v + Y.toEuclideanLin v := by
        simp only [map_add, LinearMap.add_apply]
      rw [hadd, add_mul]
      exact (norm_add_le _ _).trans (add_le_add hupX hupY)
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hfin : matrixSingularValues (X+Y) (a+b) * ‖v‖ ≤
        (matrixSingularValues X a + matrixSingularValues Y b) * ‖v‖ := hlowNorm.trans hsum
    exact le_of_mul_le_mul_right hfin hpos
  · rw [matrixSingularValues_of_card_le _ (Nat.le_of_not_lt hab)]
    exact add_nonneg (matrixSingularValues_nonneg _ _) (matrixSingularValues_nonneg _ _)

/-- A uniform reciprocal singular value bound for divided differences applied to outer products
implies a logarithmic operator norm bound for the corresponding Schur multiplier. -/
theorem schurBound_of_weakSchatten {c₁ : ℝ} (hc₁ : 0 < c₁)
    (H1 : ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (μ : J → ℝ) (ν : I → ℝ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L → lipUnion μ ν f L →
      ∀ (a : J → ℂ) (b : I → ℂ) (q : ℕ),
        matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q ≤
          c₁ * L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) /
            ((q : ℝ) + 1)) :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
      lipUnion eigL eigR f L → ∀ K : Matrix I J ℂ,
        ‖ddMat eigL eigR f ⊙ K‖ ≤
          c₁ * (1 + Real.log ((Finset.univ.image eigL).card : ℝ)) * L * ‖K‖ := by
  intro I J _ _ _ _ eigL eigR f L hL hf K
  set nA := (Finset.univ.image eigL).card with hnA
  have hlog : 0 ≤ 1 + Real.log (nA : ℝ) := by
    rcases Nat.eq_zero_or_pos nA with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; norm_num
    · have h1 : (1 : ℝ) ≤ (nA : ℝ) := by exact_mod_cast h
      linarith [Real.log_nonneg h1]
  have hC : 0 ≤ c₁ * (1 + Real.log (nA : ℝ)) * L * ‖K‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hc₁.le hlog) hL) (norm_nonneg K)
  refine l2_opNorm_le_of_inner_le _ hC fun u v hu hv => ?_
  have hpair := inner_toEuclideanLin_hadamard_eq_trace (ddMat eigL eigR f) K
    (WithLp.ofLp u) (WithLp.ofLp v)
  rw [show toEuclidean_fromVec (WithLp.ofLp u) = u from rfl,
    show toEuclidean_fromVec (WithLp.ofLp v) = v from rfl] at hpair
  rw [hpair, ddMat_transpose eigL eigR f]
  set X := ddMat eigR eigL f ⊙ Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp u)) with hXd
  refine (norm_trace_mul_le_traceNorm K X).trans ?_
  rw [show c₁ * (1 + Real.log (nA : ℝ)) * L * ‖K‖ =
      ‖K‖ * (c₁ * L * (1 + Real.log (nA : ℝ))) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg K)

  have hXeq : X = Matrix.of fun j i =>
      (if eigR j = eigL i then (0 : ℂ)
        else (f (eigR j) - f (eigL i)) / ((eigR j - eigL i : ℝ) : ℂ)) * (WithLp.ofLp v) j *
          star (WithLp.ofLp u) i := by
    ext j i
    simp only [hXd, Matrix.hadamard_apply, ddMat, Matrix.of_apply, Matrix.vecMulVec_apply,
      Pi.star_apply]
    ring
  have hXrank : X.rank ≤ nA := by
    have hle := rank_of_col_factor_restrict (I := J) (J := I) (V := ℝ) eigL (fun _ => True)
      (fun t j => (if eigR j = t then (0 : ℂ)
        else (f (eigR j) - f t) / ((eigR j - t : ℝ) : ℂ)) * (WithLp.ofLp v) j)
      (fun i => star (WithLp.ofLp u) i)
    rw [hXeq, hnA]
    refine hle.trans_eq ?_
    congr 1
    exact Finset.filter_true_of_mem fun _ _ => trivial
  have hfinrank : Module.finrank ℂ X.toEuclideanLin.range ≤ nA := by
    rw [finrank_range_toEuclideanLin_eq_rank]; exact hXrank
  have hs0 : ∀ q : ℕ, nA ≤ q → matrixSingularValues X q = 0 := by
    intro q hq
    rcases eq_or_lt_of_le (matrixSingularValues_nonneg X q) with h0 | hpos
    · exact h0.symm
    · rw [matrixSingularValues_pos_iff_lt_finrank_range] at hpos
      exact absurd (hpos.trans_le hfinrank) (not_lt_of_ge hq)
  have hnAle : nA ≤ Fintype.card I := by
    rw [hnA]
    exact Finset.card_image_le.trans_eq Finset.card_univ
  have hsum : matrixTraceNorm X = ∑ q ∈ Finset.range nA, matrixSingularValues X q := by
    rw [show matrixTraceNorm X = ∑ q : Fin (Fintype.card I), matrixSingularValues X q from rfl,
      Fin.sum_univ_eq_sum_range]
    exact (Finset.sum_subset (Finset.range_subset.2 fun x hx =>
      Finset.mem_range.2 (lt_of_lt_of_le hx hnAle)) fun q _ hq =>
      hs0 q (by simpa only [Finset.mem_range, not_lt] using hq)).symm
  have hnv : Real.sqrt (∑ j, ‖WithLp.ofLp v j‖ ^ 2) = 1 := by
    have hsumv : (∑ j, ‖WithLp.ofLp v j‖ ^ 2) = ∑ j, ‖v j‖ ^ 2 := rfl
    rw [hsumv, ← EuclideanSpace.norm_eq, hv]
  have hnu : Real.sqrt (∑ i, ‖star (WithLp.ofLp u) i‖ ^ 2) = 1 := by
    have he : (∑ i, ‖star (WithLp.ofLp u) i‖ ^ 2) = ∑ i, ‖u i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (star (WithLp.ofLp u)) i = star (u i) from rfl, norm_star]
    rw [he, ← EuclideanSpace.norm_eq, hu]
  have hterm : ∀ q : ℕ, matrixSingularValues X q ≤ c₁ * L / ((q : ℝ) + 1) := by
    intro q
    have h1 := H1 J I eigR eigL f L hL (lipUnion_swap eigL eigR f L hf)
      (WithLp.ofLp v) (star (WithLp.ofLp u)) q
    rw [hnv, hnu] at h1
    rw [hXd]
    simpa using h1
  calc matrixTraceNorm X = ∑ q ∈ Finset.range nA, matrixSingularValues X q := hsum
    _ ≤ ∑ q ∈ Finset.range nA, c₁ * L / ((q : ℝ) + 1) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = c₁ * L * ∑ q ∈ Finset.range nA, (1 : ℝ) / ((q : ℝ) + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => div_eq_mul_one_div _ _
    _ ≤ c₁ * L * (1 + Real.log (nA : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_range_one_div_le_one_add_log nA) (mul_nonneg hc₁.le hL)

end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators

variable {J I : Type} [Fintype J] [Fintype I]
  (a : J → ℂ) (μ : J → ℝ) (b : I → ℂ) (ν : I → ℝ) (m : ℕ)

/-- The sum of the squared magnitudes of the left coefficients over the eigenvalue fiber at `t`. -/
def fibα (t : ℝ) : ℝ := ∑ j ∈ Finset.univ.filter (fun j => μ j = t), ‖a j‖ ^ 2

/-- The sum of the squared magnitudes of the right coefficients over the eigenvalue fiber at
`t`. -/
def fibβ (t : ℝ) : ℝ := ∑ i ∈ Finset.univ.filter (fun i => ν i = t), ‖b i‖ ^ 2

/-- The combined fiber mass obtained by normalizing the left and right squared coefficient
masses. -/
def γmass (t : ℝ) : ℝ :=
  fibα a μ t / (∑ j, ‖a j‖ ^ 2) + fibβ b ν t / (∑ i, ‖b i‖ ^ 2)

/-- The eigenvalues whose left and right fiber masses are each below one `m`th of the
corresponding total mass. -/
def lightSet : Finset ℝ :=
  (Finset.univ.image μ ∪ Finset.univ.image ν).filter
    (fun t => fibα a μ t < (∑ j, ‖a j‖ ^ 2) / m ∧ fibβ b ν t < (∑ i, ‖b i‖ ^ 2) / m)

/-- The combined mass of light eigenvalues strictly below `t`. -/
def Γcum (t : ℝ) : ℝ := ∑ s ∈ (lightSet a μ b ν m).filter (· < t), γmass a μ b ν s

/-- The natural number group index obtained by taking the floor of m / 2 times the cumulative
light mass. -/
def grp (t : ℝ) : ℕ := ⌊(m : ℝ) / 2 * Γcum a μ b ν m t⌋₊

/-- The light eigenvalues assigned to group `k`. -/
def groupVals (k : ℕ) : Finset ℝ := (lightSet a μ b ν m).filter (fun t => grp a μ b ν m t = k)

/-- The minimum eigenvalue in group `k`, or zero if the group is empty. -/
def glo (k : ℕ) : ℝ :=
    if h : (groupVals a μ b ν m k).Nonempty then (groupVals a μ b ν m k).min' h else 0

/-- The maximum eigenvalue in group `k`, or zero if the group is empty. -/
def ghi (k : ℕ) : ℝ :=
    if h : (groupVals a μ b ν m k).Nonempty then (groupVals a μ b ν m k).max' h else 0

/-- The difference between the upper and lower endpoints of group `k`. -/
def glen (k : ℕ) : ℝ := ghi a μ b ν m k - glo a μ b ν m k

/-- The midpoint of the interval spanned by group `k`. -/
def gctr (k : ℕ) : ℝ := (glo a μ b ν m k + ghi a μ b ν m k) / 2

/-- Half the length of the interval spanned by group `k`. -/
def gρ (k : ℕ) : ℝ := glen a μ b ν m k / 2

section basics

variable (hm : 0 < m)

/-- Every left fiber mass is nonnegative. -/
theorem fibα_nonneg (t : ℝ) : 0 ≤ fibα a μ t :=
  Finset.sum_nonneg fun _j _ => sq_nonneg _

/-- Every right fiber mass is nonnegative. -/
theorem fibβ_nonneg (t : ℝ) : 0 ≤ fibβ b ν t :=
  Finset.sum_nonneg fun _i _ => sq_nonneg _

/-- A finite sum of squared complex magnitudes is nonnegative. -/
private theorem normSqSum_nonneg {α : Type*} [Fintype α] (c : α → ℂ) :
    0 ≤ ∑ j, ‖c j‖ ^ 2 :=
  Finset.sum_nonneg fun _j _ => sq_nonneg _

/-- The combined normalized fiber mass is nonnegative. -/
private theorem γmass_nonneg_of (t : ℝ) : 0 ≤ γmass a μ b ν t :=
  add_nonneg (div_nonneg (fibα_nonneg a μ t) (normSqSum_nonneg a))
    (div_nonneg (fibβ_nonneg b ν t) (normSqSum_nonneg b))

/-- The combined fiber mass is nonnegative when both total coefficient masses are positive. -/
theorem γmass_nonneg (_hA : 0 < ∑ j, ‖a j‖ ^ 2) (_hB : 0 < ∑ i, ‖b i‖ ^ 2) (t : ℝ) :
    0 ≤ γmass a μ b ν t :=
  γmass_nonneg_of a μ b ν t

/-- Summing the left fiber masses over distinct left eigenvalues recovers the total squared
coefficient mass. -/
theorem sum_fibα_image : ∑ t ∈ Finset.univ.image μ, fibα a μ t = ∑ j, ‖a j‖ ^ 2 :=
  Finset.sum_fiberwise_of_maps_to
    (fun j _ => Finset.mem_image_of_mem μ (Finset.mem_univ j)) (fun j => ‖a j‖ ^ 2)

/-- Summing the right fiber masses over distinct right eigenvalues recovers the total squared
coefficient mass. -/
theorem sum_fibβ_image : ∑ t ∈ Finset.univ.image ν, fibβ b ν t = ∑ i, ‖b i‖ ^ 2 :=
  Finset.sum_fiberwise_of_maps_to
    (fun i _ => Finset.mem_image_of_mem ν (Finset.mem_univ i)) (fun i => ‖b i‖ ^ 2)

/-- The left fiber mass vanishes outside the range of the left eigenvalue family. -/
private theorem fibα_eq_zero_of_not_mem_image {s : ℝ} (hs : s ∉ Finset.univ.image μ) :
    fibα a μ s = 0 := by
  unfold fibα
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [← hj.2] at hs
  exact absurd (Finset.mem_image_of_mem μ (Finset.mem_univ j)) hs

/-- The right fiber mass vanishes outside the range of the right eigenvalue family. -/
private theorem fibβ_eq_zero_of_not_mem_image {s : ℝ} (hs : s ∉ Finset.univ.image ν) :
    fibβ b ν s = 0 := by
  unfold fibβ
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [← hi.2] at hs
  exact absurd (Finset.mem_image_of_mem ν (Finset.mem_univ i)) hs

/-- With positive total masses, the combined mass at a light eigenvalue is less than 2 / m. -/
theorem γmass_lt_of_mem_lightSet
    (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2)
    {t : ℝ} (ht : t ∈ lightSet a μ b ν m) : γmass a μ b ν t < 2 / m := by
  obtain ⟨_, hα, hβ⟩ := Finset.mem_filter.mp ht
  have hα' : fibα a μ t / (∑ j, ‖a j‖ ^ 2) < 1 / (m : ℝ) := by
    calc fibα a μ t / (∑ j, ‖a j‖ ^ 2)
        < ((∑ j, ‖a j‖ ^ 2) / m) / (∑ j, ‖a j‖ ^ 2) := div_lt_div_of_pos_right hα hA
      _ = 1 / (m : ℝ) := by
        rw [div_div, mul_comm, div_mul_eq_div_div, div_self (ne_of_gt hA)]
  have hβ' : fibβ b ν t / (∑ i, ‖b i‖ ^ 2) < 1 / (m : ℝ) := by
    calc fibβ b ν t / (∑ i, ‖b i‖ ^ 2)
        < ((∑ i, ‖b i‖ ^ 2) / m) / (∑ i, ‖b i‖ ^ 2) := div_lt_div_of_pos_right hβ hB
      _ = 1 / (m : ℝ) := by
        rw [div_div, mul_comm, div_mul_eq_div_div, div_self (ne_of_gt hB)]
  have h2 : (2 : ℝ) / m = 1 / m + 1 / m := by
    rw [← add_div, one_add_one_eq_two]
  show fibα a μ t / (∑ j, ‖a j‖ ^ 2) + fibβ b ν t / (∑ i, ‖b i‖ ^ 2) < 2 / (m : ℝ)
  linarith

/-- The cumulative light mass is at most two when both total coefficient masses are positive. -/
theorem Γcum_le_two (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2) (t : ℝ) :
    Γcum a μ b ν m t ≤ 2 := by
  have hα1 : ∑ s ∈ lightSet a μ b ν m, fibα a μ s / (∑ j, ‖a j‖ ^ 2) ≤ 1 := by
    have hle : ∑ s ∈ lightSet a μ b ν m, fibα a μ s / (∑ j, ‖a j‖ ^ 2)
        ≤ ∑ s ∈ Finset.univ.image μ ∪ Finset.univ.image ν, fibα a μ s / (∑ j, ‖a j‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun s _ _ => div_nonneg (fibα_nonneg a μ s) hA.le
    have heq : (∑ s ∈ Finset.univ.image μ ∪ Finset.univ.image ν,
          fibα a μ s / (∑ j, ‖a j‖ ^ 2))
        = ∑ s ∈ Finset.univ.image μ, fibα a μ s / (∑ j, ‖a j‖ ^ 2) :=
      (Finset.sum_subset Finset.subset_union_left fun s _ hsμ => by
        rw [fibα_eq_zero_of_not_mem_image a μ hsμ, zero_div]).symm
    calc ∑ s ∈ lightSet a μ b ν m, fibα a μ s / (∑ j, ‖a j‖ ^ 2)
        ≤ ∑ s ∈ Finset.univ.image μ ∪ Finset.univ.image ν, fibα a μ s / (∑ j, ‖a j‖ ^ 2) := hle
      _ = ∑ s ∈ Finset.univ.image μ, fibα a μ s / (∑ j, ‖a j‖ ^ 2) := heq
      _ = (∑ s ∈ Finset.univ.image μ, fibα a μ s) / (∑ j, ‖a j‖ ^ 2) :=
          (Finset.sum_div _ _ _).symm
      _ = (∑ j, ‖a j‖ ^ 2) / (∑ j, ‖a j‖ ^ 2) := by rw [sum_fibα_image a μ]
      _ = 1 := div_self (ne_of_gt hA)
  have hβ1 : ∑ s ∈ lightSet a μ b ν m, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) ≤ 1 := by
    have hle : ∑ s ∈ lightSet a μ b ν m, fibβ b ν s / (∑ i, ‖b i‖ ^ 2)
        ≤ ∑ s ∈ Finset.univ.image μ ∪ Finset.univ.image ν, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun s _ _ => div_nonneg (fibβ_nonneg b ν s) hB.le
    have heq : (∑ s ∈ Finset.univ.image μ ∪ Finset.univ.image ν,
          fibβ b ν s / (∑ i, ‖b i‖ ^ 2))
        = ∑ s ∈ Finset.univ.image ν, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) :=
      (Finset.sum_subset Finset.subset_union_right fun s _ hsν => by
        rw [fibβ_eq_zero_of_not_mem_image b ν hsν, zero_div]).symm
    calc ∑ s ∈ lightSet a μ b ν m, fibβ b ν s / (∑ i, ‖b i‖ ^ 2)
        ≤ ∑ s ∈ Finset.univ.image μ ∪ Finset.univ.image ν, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) := hle
      _ = ∑ s ∈ Finset.univ.image ν, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) := heq
      _ = (∑ s ∈ Finset.univ.image ν, fibβ b ν s) / (∑ i, ‖b i‖ ^ 2) :=
          (Finset.sum_div _ _ _).symm
      _ = (∑ i, ‖b i‖ ^ 2) / (∑ i, ‖b i‖ ^ 2) := by rw [sum_fibβ_image b ν]
      _ = 1 := div_self (ne_of_gt hB)
  have hsplit : ∑ s ∈ lightSet a μ b ν m, γmass a μ b ν s
      = ∑ s ∈ lightSet a μ b ν m, fibα a μ s / (∑ j, ‖a j‖ ^ 2)
        + ∑ s ∈ lightSet a μ b ν m, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) := by
    simp only [γmass]
    exact Finset.sum_add_distrib
  calc Γcum a μ b ν m t
      ≤ ∑ s ∈ lightSet a μ b ν m, γmass a μ b ν s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun s _ _ => γmass_nonneg_of a μ b ν s
    _ = ∑ s ∈ lightSet a μ b ν m, fibα a μ s / (∑ j, ‖a j‖ ^ 2)
          + ∑ s ∈ lightSet a μ b ν m, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) := hsplit
    _ ≤ 1 + 1 := add_le_add hα1 hβ1
    _ = 2 := one_add_one_eq_two

/-- The group index is monotone in the eigenvalue. -/
theorem grp_mono : Monotone (grp a μ b ν m) := by
  intro t₁ t₂ ht
  have hΓ : Γcum a μ b ν m t₁ ≤ Γcum a μ b ν m t₂ := by
    show ∑ s ∈ (lightSet a μ b ν m).filter (· < t₁), γmass a μ b ν s
        ≤ ∑ s ∈ (lightSet a μ b ν m).filter (· < t₂), γmass a μ b ν s
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      rw [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, lt_of_lt_of_le hs.2 ht⟩
    · intro s _ _
      exact γmass_nonneg_of a μ b ν s
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hΓ (div_nonneg (Nat.cast_nonneg m) two_pos.le))

/-- The group index of a light eigenvalue is at most `m` under the positive mass assumptions. -/
theorem grp_le_m (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2)
    {t : ℝ} (_ht : t ∈ lightSet a μ b ν m) : grp a μ b ν m t ≤ m := by
  have h2 : Γcum a μ b ν m t ≤ 2 := Γcum_le_two a μ b ν m hA hB t
  have hmul : (m : ℝ) / 2 * Γcum a μ b ν m t ≤ (m : ℝ) := by
    calc (m : ℝ) / 2 * Γcum a μ b ν m t
        ≤ (m : ℝ) / 2 * 2 :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (Nat.cast_nonneg m) two_pos.le)
      _ = (m : ℝ) := by ring
  have hfl : ⌊(m : ℝ) / 2 * Γcum a μ b ν m t⌋₊ ≤ ⌊(m : ℝ)⌋₊ := Nat.floor_mono hmul
  rw [Nat.floor_natCast] at hfl
  exact hfl

/-- The combined mass of each group is at most 4 / m under the positive parameter and mass
assumptions. -/
theorem group_mass_le (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2) (k : ℕ) :
    ∑ s ∈ groupVals a μ b ν m k, γmass a μ b ν s ≤ 4 / m := by
  rcases Finset.eq_empty_or_nonempty (groupVals a μ b ν m k) with hG | hG
  · rw [hG, Finset.sum_empty]
    exact div_nonneg (by norm_num) (Nat.cast_nonneg m)
  · obtain ⟨ht₀L, hgrp₀⟩ := Finset.mem_filter.mp ((groupVals a μ b ν m k).min'_mem hG)
    obtain ⟨ht₁L, hgrp₁⟩ := Finset.mem_filter.mp ((groupVals a μ b ν m k).max'_mem hG)
    have ht₀t₁ : (groupVals a μ b ν m k).min' hG ≤ (groupVals a μ b ν m k).max' hG :=
      Finset.min'_le_max' _ hG
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      by_contra h
      have hm0 : (m : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg m)
      have hα := (Finset.mem_filter.mp ht₀L).2.1
      rw [hm0, div_zero] at hα
      exact absurd hα (not_lt_of_ge (fibα_nonneg a μ _))
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hΓnn : 0 ≤ Γcum a μ b ν m ((groupVals a μ b ν m k).min' hG) :=
      Finset.sum_nonneg fun s _ => γmass_nonneg_of a μ b ν s
    have h0' : (k : ℝ) ≤ (m : ℝ) / 2 * Γcum a μ b ν m ((groupVals a μ b ν m k).min' hG) := by
      have hx0 : 0 ≤ (m : ℝ) / 2 * Γcum a μ b ν m ((groupVals a μ b ν m k).min' hG) :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg m) two_pos.le) hΓnn
      have hfl := Nat.floor_le hx0
      have hgrp₀' : ⌊(m : ℝ) / 2 * Γcum a μ b ν m ((groupVals a μ b ν m k).min' hG)⌋₊ = k :=
        hgrp₀
      rw [hgrp₀'] at hfl
      exact hfl
    have h1' : (m : ℝ) / 2 * Γcum a μ b ν m ((groupVals a μ b ν m k).max' hG) < (k : ℝ) + 1 := by
      have hfl := Nat.lt_floor_add_one
        ((m : ℝ) / 2 * Γcum a μ b ν m ((groupVals a μ b ν m k).max' hG))
      have hgrp₁' : ⌊(m : ℝ) / 2 * Γcum a μ b ν m ((groupVals a μ b ν m k).max' hG)⌋₊ = k :=
        hgrp₁
      rw [hgrp₁'] at hfl
      exact hfl
    have hγ' : (m : ℝ) / 2 * γmass a μ b ν ((groupVals a μ b ν m k).max' hG) < 1 := by
      have hγ := γmass_lt_of_mem_lightSet a μ b ν m hA hB ht₁L
      calc (m : ℝ) / 2 * γmass a μ b ν ((groupVals a μ b ν m k).max' hG)
          < (m : ℝ) / 2 * (2 / (m : ℝ)) :=
            mul_lt_mul_of_pos_left hγ (div_pos hmpos two_pos)
        _ = 1 := by field_simp
    have hG2 : groupVals a μ b ν m k
        = (lightSet a μ b ν m).filter
            (fun s => (groupVals a μ b ν m k).min' hG ≤ s
              ∧ s ≤ (groupVals a μ b ν m k).max' hG) := by
      ext s
      constructor
      · intro hs
        obtain ⟨hsL, hsk⟩ := Finset.mem_filter.mp hs
        have hsmem : s ∈ groupVals a μ b ν m k := Finset.mem_filter.mpr ⟨hsL, hsk⟩
        exact Finset.mem_filter.mpr ⟨hsL, (groupVals a μ b ν m k).min'_le _ hsmem,
          (groupVals a μ b ν m k).le_max' _ hsmem⟩
      · intro hs
        obtain ⟨hsL, h0, h1⟩ := Finset.mem_filter.mp hs
        have e1 := grp_mono a μ b ν m h0
        have e2 := grp_mono a μ b ν m h1
        rw [hgrp₀] at e1
        rw [hgrp₁] at e2
        exact Finset.mem_filter.mpr ⟨hsL, le_antisymm e2 e1⟩
    have hdec : (lightSet a μ b ν m).filter
          (fun s => (groupVals a μ b ν m k).min' hG ≤ s
            ∧ s ≤ (groupVals a μ b ν m k).max' hG)
        = (lightSet a μ b ν m).filter (· ≤ (groupVals a μ b ν m k).max' hG)
            \ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).min' hG) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · intro ⟨hsL, h0, h1⟩
        exact ⟨⟨hsL, h1⟩, fun h => absurd h.2 (not_lt_of_ge h0)⟩
      · intro ⟨⟨hsL, h1⟩, hnot⟩
        exact ⟨hsL, not_lt.mp fun hlt => hnot ⟨hsL, hlt⟩, h1⟩
    have hsub : (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).min' hG)
        ⊆ (lightSet a μ b ν m).filter (· ≤ (groupVals a μ b ν m k).max' hG) := by
      intro s hs
      rw [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, (hs.2.trans_le ht₀t₁).le⟩
    have hS1 : (lightSet a μ b ν m).filter (· ≤ (groupVals a μ b ν m k).max' hG)
        = insert ((groupVals a μ b ν m k).max' hG)
            ((lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).max' hG)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro ⟨hsL, hsle⟩
        rcases lt_or_eq_of_le hsle with h | h
        · exact Or.inr ⟨hsL, h⟩
        · exact Or.inl h
      · intro h
        rcases h with rfl | h
        · exact ⟨ht₁L, le_refl _⟩
        · exact ⟨h.1, h.2.le⟩
    have hnotmem : (groupVals a μ b ν m k).max' hG
        ∉ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).max' hG) := by
      rw [Finset.mem_filter]
      exact fun h => absurd h.2 (lt_irrefl _)
    have hsum1 : ∑ s ∈ (lightSet a μ b ν m).filter (· ≤ (groupVals a μ b ν m k).max' hG),
          γmass a μ b ν s
        = γmass a μ b ν ((groupVals a μ b ν m k).max' hG)
          + ∑ s ∈ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).max' hG),
              γmass a μ b ν s := by
      rw [hS1, Finset.sum_insert hnotmem]
    have hsumG : ∑ s ∈ groupVals a μ b ν m k, γmass a μ b ν s
        = γmass a μ b ν ((groupVals a μ b ν m k).max' hG)
          + ∑ s ∈ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).max' hG),
              γmass a μ b ν s
          - ∑ s ∈ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).min' hG),
              γmass a μ b ν s := by
      have hsumG0 : ∑ s ∈ groupVals a μ b ν m k, γmass a μ b ν s
          = ∑ s ∈ (lightSet a μ b ν m).filter
              (fun s => (groupVals a μ b ν m k).min' hG ≤ s
                ∧ s ≤ (groupVals a μ b ν m k).max' hG), γmass a μ b ν s :=
        Finset.sum_congr hG2 fun _ _ => rfl
      rw [hsumG0, hdec, Finset.sum_sdiff_eq_sub hsub, hsum1]
    have h0'' : (k : ℝ) ≤ (m : ℝ) / 2 *
        ∑ s ∈ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).min' hG),
          γmass a μ b ν s := h0'
    have h1'' : (m : ℝ) / 2 *
        ∑ s ∈ (lightSet a μ b ν m).filter (· < (groupVals a μ b ν m k).max' hG),
          γmass a μ b ν s < (k : ℝ) + 1 := h1'
    rw [le_div_iff₀ hmpos, hsumG]
    linarith

/-- The left fiber mass of each group is at most 4 / m times the total left coefficient mass. -/
theorem group_fibα_le (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2) (k : ℕ) :
    ∑ s ∈ groupVals a μ b ν m k, fibα a μ s ≤ 4 / m * (∑ j, ‖a j‖ ^ 2) := by
  have h1 : ∑ s ∈ groupVals a μ b ν m k, fibα a μ s / (∑ j, ‖a j‖ ^ 2) ≤ 4 / (m : ℝ) := by
    refine le_trans ?_ (group_mass_le a μ b ν m hA hB k)
    exact Finset.sum_le_sum fun s _ =>
      le_add_of_nonneg_right (div_nonneg (fibβ_nonneg b ν s) (normSqSum_nonneg b))
  rw [← Finset.sum_div, div_le_iff₀ hA] at h1
  exact h1

/-- The right fiber mass of each group is at most 4 / m times the total right coefficient mass. -/
theorem group_fibβ_le (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2) (k : ℕ) :
    ∑ s ∈ groupVals a μ b ν m k, fibβ b ν s ≤ 4 / m * (∑ i, ‖b i‖ ^ 2) := by
  have h1 : ∑ s ∈ groupVals a μ b ν m k, fibβ b ν s / (∑ i, ‖b i‖ ^ 2) ≤ 4 / (m : ℝ) := by
    refine le_trans ?_ (group_mass_le a μ b ν m hA hB k)
    exact Finset.sum_le_sum fun s _ =>
      le_add_of_nonneg_left (div_nonneg (fibα_nonneg a μ s) (normSqSum_nonneg a))
  rw [← Finset.sum_div, div_le_iff₀ hB] at h1
  exact h1

end basics

section intervals

/-- The lower endpoint of a nonempty group belongs to that group. -/
theorem glo_mem {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) :
    glo a μ b ν m k ∈ groupVals a μ b ν m k := by
  simp only [glo, dif_pos hk]
  exact Finset.min'_mem _ _

/-- The upper endpoint of a nonempty group belongs to that group. -/
theorem ghi_mem {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) :
    ghi a μ b ν m k ∈ groupVals a μ b ν m k := by
  simp only [ghi, dif_pos hk]
  exact Finset.max'_mem _ _

/-- The lower endpoint of a nonempty group does not exceed its upper endpoint. -/
theorem glo_le_ghi {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) :
    glo a μ b ν m k ≤ ghi a μ b ν m k := by
  simp only [glo, ghi, dif_pos hk]
  exact Finset.min'_le _ _ (Finset.max'_mem _ _)

/-- The radius of a nonempty group is nonnegative. -/
theorem gρ_nonneg {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) :
    0 ≤ gρ a μ b ν m k := by
  have hle : glo a μ b ν m k ≤ ghi a μ b ν m k := glo_le_ghi a μ b ν m hk
  have hρ : gρ a μ b ν m k = (ghi a μ b ν m k - glo a μ b ν m k) / 2 := rfl
  rw [hρ]
  exact div_nonneg (sub_nonneg.mpr hle) (by norm_num)

/-- Each eigenvalue in a nonempty group lies between its lower and upper endpoints. -/
theorem mem_bounds_of_grp_eq {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) {t : ℝ}
    (ht : t ∈ groupVals a μ b ν m k) :
    glo a μ b ν m k ≤ t ∧ t ≤ ghi a μ b ν m k := by
  simp only [glo, ghi, dif_pos hk]
  exact ⟨Finset.min'_le _ _ ht, Finset.le_max' _ _ ht⟩

/-- The distance of a group member from the group midpoint is at most the group radius. -/
theorem abs_sub_ctr_le {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) {t : ℝ}
    (ht : t ∈ groupVals a μ b ν m k) : |t - gctr a μ b ν m k| ≤ gρ a μ b ν m k := by
  obtain ⟨hlo, hhi⟩ := mem_bounds_of_grp_eq a μ b ν m hk ht
  have hρ : gρ a μ b ν m k = (ghi a μ b ν m k - glo a μ b ν m k) / 2 := rfl
  have hctr : gctr a μ b ν m k = (glo a μ b ν m k + ghi a μ b ν m k) / 2 := rfl
  rw [hρ, hctr, abs_le]
  constructor <;> linarith

/-- A light eigenvalue in a different group is at least the group radius away from the midpoint. -/
theorem ge_ρ_of_grp_ne {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) {t : ℝ}
    (ht : t ∈ lightSet a μ b ν m) (htk : grp a μ b ν m t ≠ k) :
    gρ a μ b ν m k ≤ |t - gctr a μ b ν m k| := by
  have hlo_mem : glo a μ b ν m k ∈ groupVals a μ b ν m k := glo_mem a μ b ν m hk
  have hhi_mem : ghi a μ b ν m k ∈ groupVals a μ b ν m k := ghi_mem a μ b ν m hk
  have hlo_grp : grp a μ b ν m (glo a μ b ν m k) = k := (Finset.mem_filter.mp hlo_mem).2
  have hhi_grp : grp a μ b ν m (ghi a μ b ν m k) = k := (Finset.mem_filter.mp hhi_mem).2
  have hgh : glo a μ b ν m k ≤ ghi a μ b ν m k := glo_le_ghi a μ b ν m hk
  have hnot : ¬(glo a μ b ν m k ≤ t ∧ t ≤ ghi a μ b ν m k) := by
    rintro ⟨h1, h2⟩
    apply htk
    have g1 : grp a μ b ν m (glo a μ b ν m k) ≤ grp a μ b ν m t := grp_mono a μ b ν m h1
    have g2 : grp a μ b ν m t ≤ grp a μ b ν m (ghi a μ b ν m k) := grp_mono a μ b ν m h2
    rw [hlo_grp] at g1
    rw [hhi_grp] at g2
    exact le_antisymm g2 g1
  have hcases : t < glo a μ b ν m k ∨ ghi a μ b ν m k < t := by
    rcases le_total t (glo a μ b ν m k) with h | h
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq
        exact absurd ⟨le_refl _, hgh⟩ hnot
      · exact Or.inl hlt
    · exact Or.inr (not_le.mp fun hle => hnot ⟨h, hle⟩)
  have hρ : gρ a μ b ν m k = (ghi a μ b ν m k - glo a μ b ν m k) / 2 := rfl
  have hctr : gctr a μ b ν m k = (glo a μ b ν m k + ghi a μ b ν m k) / 2 := rfl
  rw [hρ, hctr]
  rcases hcases with h | h
  · rw [abs_of_neg (show t - (glo a μ b ν m k + ghi a μ b ν m k) / 2 < 0 by linarith)]
    linarith
  · rw [abs_of_pos (show 0 < t - (glo a μ b ν m k + ghi a μ b ν m k) / 2 by linarith)]
    linarith

/-- The upper endpoint of an earlier nonempty group is strictly below the lower endpoint of a
later nonempty group. -/
theorem hi_lt_lo_of_lt {k₁ k₂ : ℕ} (hk₁ : (groupVals a μ b ν m k₁).Nonempty)
    (hk₂ : (groupVals a μ b ν m k₂).Nonempty) (h : k₁ < k₂) :
    ghi a μ b ν m k₁ < glo a μ b ν m k₂ := by
  have hhi_mem : ghi a μ b ν m k₁ ∈ groupVals a μ b ν m k₁ := ghi_mem a μ b ν m hk₁
  have hlo_mem : glo a μ b ν m k₂ ∈ groupVals a μ b ν m k₂ := glo_mem a μ b ν m hk₂
  have hhi_grp : grp a μ b ν m (ghi a μ b ν m k₁) = k₁ := (Finset.mem_filter.mp hhi_mem).2
  have hlo_grp : grp a μ b ν m (glo a μ b ν m k₂) = k₂ := (Finset.mem_filter.mp hlo_mem).2
  by_contra hcon
  push Not at hcon
  have hle := grp_mono a μ b ν m hcon
  rw [hlo_grp, hhi_grp] at hle
  exact (not_le.mpr h) hle

end intervals

section covering

variable (hm : 0 < m) (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2)

/-- The total length of finitely many ordered, nonoverlapping intervals is at most the span of
their extreme endpoints, with value zero for an empty index set. -/
theorem sum_sub_le_of_pairwise_ordered {S : Finset ℕ} {lo' hi' : ℕ → ℝ}
    (hord : ∀ x ∈ S, ∀ y ∈ S, x < y → hi' x ≤ lo' y)
    (hnonneg : ∀ x ∈ S, lo' x ≤ hi' x) :
    ∑ k ∈ S, (hi' k - lo' k) ≤
      (if h : S.Nonempty then hi' (S.max' h) - lo' (S.min' h) else 0) := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert M S' hlt ih =>
    rw [dif_pos (Finset.insert_nonempty M S')]
    have hMnotin : M ∉ S' := fun h => (lt_irrefl M (hlt M h)).elim
    rw [Finset.sum_insert hMnotin]
    have hmax : (insert M S').max' (Finset.insert_nonempty M S') = M := by
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact le_rfl
        · exact le_of_lt (hlt y hy)
      · exact Finset.le_max' _ _ (Finset.mem_insert_self M S')
    rw [hmax]
    by_cases hS' : S'.Nonempty
    · have hmin : (insert M S').min' (Finset.insert_nonempty M S') = S'.min' hS' := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem S' hS'))
        · apply Finset.le_min'
          intro y hy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · exact le_of_lt (hlt _ (Finset.min'_mem S' hS'))
          · exact Finset.min'_le _ _ hy
      rw [hmin]
      have hord' : ∀ x ∈ S', ∀ y ∈ S', x < y → hi' x ≤ lo' y :=
        fun x hx y hy hxy => hord x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have hnonneg' : ∀ x ∈ S', lo' x ≤ hi' x :=
        fun x hx => hnonneg x (Finset.mem_insert_of_mem hx)
      have ih' := ih hord' hnonneg'
      rw [dif_pos hS'] at ih'
      have hle : hi' (S'.max' hS') ≤ lo' M :=
        hord _ (Finset.mem_insert_of_mem (Finset.max'_mem S' hS')) _ (Finset.mem_insert_self M S')
          (hlt _ (Finset.max'_mem S' hS'))
      linarith [ih']
    · rw [Finset.not_nonempty_iff_eq_empty] at hS'
      subst hS'
      rw [Finset.sum_empty, add_zero]
      have hm1 : (insert M (∅ : Finset ℕ)).min' (Finset.insert_nonempty M ∅) = M := by
        simp
      rw [hm1]

/-- The number of groups at least as long as a fixed positive-radius group and meeting the
radius-`R` neighborhood of its center is at most R / radius + 2. -/
theorem card_groups_meeting_le (k : ℕ) (_hk : (groupVals a μ b ν m k).Nonempty)
    (hρ : 0 < gρ a μ b ν m k) (R : ℝ) (hR : 0 ≤ R) :
    ((((lightSet a μ b ν m).image (grp a μ b ν m)).filter (fun k' =>
        glen a μ b ν m k ≤ glen a μ b ν m k' ∧
          ∃ t ∈ groupVals a μ b ν m k', |t - gctr a μ b ν m k| ≤ R)).card : ℝ) ≤
      R / gρ a μ b ν m k + 2 := by
  classical
  set S : Finset ℕ := ((lightSet a μ b ν m).image (grp a μ b ν m)).filter (fun k' =>
      glen a μ b ν m k ≤ glen a μ b ν m k' ∧
        ∃ t ∈ groupVals a μ b ν m k', |t - gctr a μ b ν m k| ≤ R) with hSdef
  set lo' : ℕ → ℝ := fun k' => max (glo a μ b ν m k') (gctr a μ b ν m k - R - 2 * gρ a μ b ν m k)
    with hlo'def
  set hi' : ℕ → ℝ := fun k' => min (ghi a μ b ν m k') (gctr a μ b ν m k + R + 2 * gρ a μ b ν m k)
    with hhi'def
  have hgl : ∀ k'' : ℕ, glen a μ b ν m k'' = ghi a μ b ν m k'' - glo a μ b ν m k'' :=
    fun k'' => rfl
  have hρ2 : gρ a μ b ν m k = glen a μ b ν m k / 2 := rfl
  have hmem : ∀ k' ∈ S, (groupVals a μ b ν m k').Nonempty ∧
      (glen a μ b ν m k ≤ glen a μ b ν m k' ∧
        ∃ t ∈ groupVals a μ b ν m k', |t - gctr a μ b ν m k| ≤ R) := by
    intro k' hk'
    rw [hSdef, Finset.mem_filter] at hk'
    obtain ⟨himg, hcond⟩ := hk'
    rw [Finset.mem_image] at himg
    obtain ⟨t₀, ht₀, hgrp⟩ := himg
    exact ⟨⟨t₀, Finset.mem_filter.mpr ⟨ht₀, hgrp⟩⟩, hcond⟩
  have hstrong : ∀ k' ∈ S, 2 * gρ a μ b ν m k ≤ hi' k' - lo' k' := by
    intro k' hk'
    obtain ⟨hne', hlen', t, ht, hdist⟩ := hmem k' hk'
    obtain ⟨hgt, hgt2⟩ := mem_bounds_of_grp_eq a μ b ν m hne' ht
    have hdist1 : gctr a μ b ν m k - R ≤ t := by
      have h := (abs_le.mp hdist).1
      linarith
    have hdist2 : t ≤ gctr a μ b ν m k + R := by
      have h := (abs_le.mp hdist).2
      linarith
    have hlen : 2 * gρ a μ b ν m k ≤ ghi a μ b ν m k' - glo a μ b ν m k' := by
      have e1 := hgl k
      have e2 := hgl k'
      linarith [hlen']
    have hhi : min (ghi a μ b ν m k') (t + 2 * gρ a μ b ν m k) ≤ hi' k' := by
      simp only [hhi'def]
      exact min_le_min le_rfl (by linarith)
    have hlo : lo' k' ≤ max (glo a μ b ν m k') (t - 2 * gρ a μ b ν m k) := by
      simp only [hlo'def]
      exact max_le_max le_rfl (by linarith)
    rcases le_total (ghi a μ b ν m k') (t + 2 * gρ a μ b ν m k) with hmin | hmin <;>
    rcases le_total (glo a μ b ν m k') (t - 2 * gρ a μ b ν m k) with hmax | hmax
    · rw [min_eq_left hmin] at hhi; rw [max_eq_right hmax] at hlo; linarith
    · rw [min_eq_left hmin] at hhi; rw [max_eq_left hmax] at hlo; linarith [hlen]
    · rw [min_eq_right hmin] at hhi; rw [max_eq_right hmax] at hlo; linarith [hρ]
    · rw [min_eq_right hmin] at hhi; rw [max_eq_left hmax] at hlo; linarith
  have hord : ∀ x ∈ S, ∀ y ∈ S, x < y → hi' x ≤ lo' y := by
    intro x hx y hy hxy
    obtain ⟨hnex, -, -⟩ := hmem x hx
    obtain ⟨hney, -, -⟩ := hmem y hy
    have h1 : hi' x ≤ ghi a μ b ν m x := by simp only [hhi'def]; exact min_le_left _ _
    have h2 : glo a μ b ν m y ≤ lo' y := by simp only [hlo'def]; exact le_max_left _ _
    exact (h1.trans (le_of_lt (hi_lt_lo_of_lt a μ b ν m hnex hney hxy))).trans h2
  by_cases hS : S.Nonempty
  · have h1 := sum_sub_le_of_pairwise_ordered hord (fun k' hk' => sub_nonneg.mp
      ((mul_pos two_pos hρ).le.trans (hstrong k' hk')))
    rw [dif_pos hS] at h1
    have hmax_hi : hi' (S.max' hS) ≤ gctr a μ b ν m k + R + 2 * gρ a μ b ν m k := by
      simp only [hhi'def]; exact min_le_right _ _
    have hmin_lo : gctr a μ b ν m k - R - 2 * gρ a μ b ν m k ≤ lo' (S.min' hS) := by
      simp only [hlo'def]; exact le_max_right _ _
    have h2 : ∑ k' ∈ S, (hi' k' - lo' k') ≤ 2 * R + 4 * gρ a μ b ν m k := by
      linarith [h1, hmax_hi, hmin_lo]
    have h3 : (S.card : ℝ) * (2 * gρ a μ b ν m k) ≤ ∑ k' ∈ S, (hi' k' - lo' k') := by
      have h := Finset.sum_le_sum hstrong
      rwa [Finset.sum_const, nsmul_eq_mul] at h
    have h4 : (S.card : ℝ) ≤ (2 * R + 4 * gρ a μ b ν m k) / (2 * gρ a μ b ν m k) := by
      rw [le_div_iff₀ (mul_pos two_pos hρ)]
      linarith [h3, h2]
    have h5 : (2 * R + 4 * gρ a μ b ν m k) / (2 * gρ a μ b ν m k) = R / gρ a μ b ν m k + 2 := by
      have hρne : gρ a μ b ν m k ≠ 0 := ne_of_gt hρ
      field_simp
      ring
    linarith [h4, h5]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h6 : (0:ℝ) ≤ R / gρ a μ b ν m k := div_nonneg hR hρ.le
    linarith

/-- For a nonempty group of positive radius, the weighted inverse-square decay sum over other
groups of at least its length is at most 80 / (3m) times the total left mass. -/
theorem decay_sum_le (k : ℕ) (hk : (groupVals a μ b ν m k).Nonempty)
    (hρ : 0 < gρ a μ b ν m k) :
    ∑ t ∈ (lightSet a μ b ν m).filter
        (fun t => grp a μ b ν m t ≠ k ∧ glen a μ b ν m k ≤ glen a μ b ν m (grp a μ b ν m t)),
      fibα a μ t * min 1 ((gρ a μ b ν m k) ^ 2 / (t - gctr a μ b ν m k) ^ 2) ≤
      (80 / 3) * (∑ j, ‖a j‖ ^ 2) / m := by
  classical
  have hA0' : (0:ℝ) ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB0' : (0:ℝ) ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases eq_or_ne m 0 with rfl | hm0
  · have hgrp0 : ∀ t : ℝ, grp a μ b ν 0 t = 0 := by
      intro t
      simp [grp]
    obtain ⟨s₀, hs₀⟩ := hk
    have hk0 : k = 0 := (Finset.mem_filter.mp hs₀).2.symm.trans (hgrp0 s₀)
    have hS0 : (lightSet a μ b ν 0).filter
        (fun t => grp a μ b ν 0 t ≠ k ∧ glen a μ b ν 0 k ≤ glen a μ b ν 0 (grp a μ b ν 0 t))
        = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro t ht
      rw [Finset.mem_filter] at ht
      exact ht.2.1 (by rw [hgrp0 t, hk0])
    rw [hS0, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) hA0') (Nat.cast_nonneg _)
  rcases eq_or_ne (∑ i, ‖b i‖ ^ 2) 0 with hB0 | hB0
  · have hlight : lightSet a μ b ν m = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro t ht
      obtain ⟨-, hcond⟩ := Finset.mem_filter.mp ht
      have hfb : 0 ≤ fibβ b ν t := fibβ_nonneg b ν t
      rw [hB0] at hcond
      have h2 : fibβ b ν t < 0 := by
        have h3 := hcond.2
        rwa [zero_div] at h3
      linarith
    have hS0 : (lightSet a μ b ν m).filter
        (fun t => grp a μ b ν m t ≠ k ∧ glen a μ b ν m k ≤ glen a μ b ν m (grp a μ b ν m t))
        = ∅ := by
      rw [hlight, Finset.filter_empty]
    rw [hS0, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) hA0') (Nat.cast_nonneg _)
  rcases eq_or_ne (∑ j, ‖a j‖ ^ 2) 0 with hA0e | hA0e
  · have haj : ∀ j : J, ‖a j‖ ^ 2 = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (‖a j‖))).mp hA0e
      intro j
      exact h j (Finset.mem_univ j)
    have hfib0 : ∀ t : ℝ, fibα a μ t = 0 := fun t => Finset.sum_eq_zero (fun j _ => haj j)
    have hsum0 : ∑ t ∈ (lightSet a μ b ν m).filter
        (fun t => grp a μ b ν m t ≠ k ∧ glen a μ b ν m k ≤ glen a μ b ν m (grp a μ b ν m t)),
        fibα a μ t * min 1 ((gρ a μ b ν m k) ^ 2 / (t - gctr a μ b ν m k) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [hfib0 t, zero_mul]
    rw [hsum0, hA0e]
    positivity
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have hB : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hB0' (Ne.symm hB0)
  have hA : 0 < ∑ j, ‖a j‖ ^ 2 := lt_of_le_of_ne hA0' (Ne.symm hA0e)

  set S : Finset ℝ := (lightSet a μ b ν m).filter
      (fun t => grp a μ b ν m t ≠ k ∧ glen a μ b ν m k ≤ glen a μ b ν m (grp a μ b ν m t))
    with hSdef
  set ρ : ℝ := gρ a μ b ν m k with hρdef
  set c : ℝ := gctr a μ b ν m k with hcdef
  set A : ℝ := ∑ j, ‖a j‖ ^ 2 with hAdef
  set C : ℝ := 4 / (m : ℝ) * A with hCdef
  have hmℝ : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmℝ
  have hA0 : 0 ≤ A := hA.le
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (div_nonneg (by norm_num) hmℝ.le) hA0
  have htS : ∀ t ∈ S, t ∈ lightSet a μ b ν m ∧ grp a μ b ν m t ≠ k ∧
      glen a μ b ν m k ≤ glen a μ b ν m (grp a μ b ν m t) := by
    intro t ht
    rw [hSdef] at ht
    exact Finset.mem_filter.mp ht
  have hdist : ∀ t ∈ S, ρ ≤ |t - c| := by
    intro t ht
    obtain ⟨htl, htne, -⟩ := htS t ht
    have h := ge_ρ_of_grp_ne a μ b ν m hk htl htne
    rwa [← hρdef, ← hcdef] at h
  have hnfloor : ∀ t ∈ S, 1 ≤ ⌊|t - c| / ρ⌋₊ := by
    intro t ht
    rw [Nat.one_le_floor_iff, le_div_iff₀ hρ, one_mul]
    exact hdist t ht
  have hlow : ∀ t ∈ S, (2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊ * ρ ≤ |t - c| := by
    intro t ht
    have h1 : (2 : ℕ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊ ≤ ⌊|t - c| / ρ⌋₊ :=
      Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp (hnfloor t ht))
    have h2 : (⌊|t - c| / ρ⌋₊ : ℝ) ≤ |t - c| / ρ := Nat.floor_le (div_nonneg (abs_nonneg _) hρ.le)
    rw [le_div_iff₀ hρ] at h2
    have h3 : ((2 ^ Nat.log 2 ⌊|t - c| / ρ⌋₊ : ℕ) : ℝ) ≤ (⌊|t - c| / ρ⌋₊ : ℝ) :=
      Nat.cast_le.mpr h1
    push_cast at h3
    exact le_trans (mul_le_mul_of_nonneg_right h3 hρ.le) h2
  have hup : ∀ t ∈ S, |t - c| < (2:ℝ) ^ (Nat.log 2 ⌊|t - c| / ρ⌋₊ + 1) * ρ := by
    intro t ht
    have h1 : ⌊|t - c| / ρ⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊|t - c| / ρ⌋₊ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
    have h2 : |t - c| / ρ < ⌊|t - c| / ρ⌋₊ + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hρ] at h2
    have h3 : (⌊|t - c| / ρ⌋₊ : ℝ) + 1 ≤ (2:ℝ) ^ (Nat.log 2 ⌊|t - c| / ρ⌋₊ + 1) := by
      have h : ((⌊|t - c| / ρ⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊|t - c| / ρ⌋₊ + 1) : ℕ) : ℝ) :=
        Nat.cast_le.mpr h1
      push_cast at h
      exact h
    exact lt_of_lt_of_le h2 (mul_le_mul_of_nonneg_right h3 hρ.le)
  have hdecay : ∀ t ∈ S, ρ ^ 2 / (t - c) ^ 2 ≤ ((4:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊)⁻¹ := by
    intro t ht
    have hlow' := hlow t ht
    have hpos1 : (0:ℝ) < (2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊ * ρ :=
      mul_pos (pow_pos two_pos _) hρ
    calc ρ ^ 2 / (t - c) ^ 2 = ρ ^ 2 / |t - c| ^ 2 := by rw [sq_abs]
      _ ≤ ρ ^ 2 / ((2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊ * ρ) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg ρ) (pow_pos hpos1 2)
            (pow_le_pow_left₀ hpos1.le hlow' 2)
      _ = ((4:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊)⁻¹ := by
          have h4 : (4:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊ =
              ((2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊) ^ 2 := by
            rw [pow_two, ← mul_pow, show (2:ℝ) * 2 = 4 by norm_num]
          have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ.ne'
          have h2s : ((2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊) ^ 2 ≠ 0 :=
            pow_ne_zero 2 (pow_ne_zero _ two_ne_zero)
          rw [h4, mul_pow,
            mul_comm (((2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊) ^ 2) (ρ ^ 2),
            div_eq_iff (mul_ne_zero hρ2 h2s),
            mul_comm (ρ ^ 2) (((2:ℝ) ^ Nat.log 2 ⌊|t - c| / ρ⌋₊) ^ 2),
            inv_mul_cancel_left₀ h2s]
  have hmin : ∀ t ∈ S,
      fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2) = fibα a μ t * (ρ ^ 2 / (t - c) ^ 2) := by
    intro t ht
    have hsq : ρ ^ 2 ≤ (t - c) ^ 2 := by
      have h := pow_le_pow_left₀ hρ.le (hdist t ht) 2
      rwa [sq_abs] at h
    rw [min_eq_right (div_le_one_of_le₀ hsq (sq_nonneg _))]
  have hkey : ∀ s : ℕ, ((4:ℝ) ^ s)⁻¹ * (2 ^ (s + 1) + 2) = 2 * (1/2) ^ s + 2 * (1/4) ^ s := by
    intro s
    have h4 : (4:ℝ) ^ s = 2 ^ s * 2 ^ s := by
      rw [← mul_pow, show (2:ℝ) * 2 = 4 by norm_num]
    have hu : (2:ℝ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [h4, pow_succ, inv_eq_one_div,
      mul_comm (1 / (2 ^ s * 2 ^ s)) (2 ^ s * 2 + 2), ← div_eq_mul_one_div,
      add_div, mul_div_mul_left 2 (2 ^ s) hu, div_pow, div_pow, one_pow, h4,
      mul_one_div, mul_one_div]
  have hgeo2 : ∀ N : ℕ, ∑ s ∈ Finset.range N, (1/2:ℝ) ^ s ≤ 2 := by
    intro N
    rw [geom_sum_eq (by norm_num : (1/2:ℝ) ≠ 1) N]
    have h1 : ((1/2:ℝ) ^ N - 1) / ((1/2:ℝ) - 1) = 2 * (1 - (1/2) ^ N) := by
      rw [show (1/2:ℝ) - 1 = -(1/2) by norm_num, div_eq_mul_inv,
        show (-(1/2:ℝ))⁻¹ = -2 by norm_num]
      ring
    rw [h1]
    have h2 : (0:ℝ) ≤ (1/2:ℝ) ^ N := pow_nonneg (by norm_num) N
    linarith
  have hgeo4 : ∀ N : ℕ, ∑ s ∈ Finset.range N, (1/4:ℝ) ^ s ≤ 4 / 3 := by
    intro N
    rw [geom_sum_eq (by norm_num : (1/4:ℝ) ≠ 1) N]
    have h1 : ((1/4:ℝ) ^ N - 1) / ((1/4:ℝ) - 1) = (4/3) * (1 - (1/4) ^ N) := by
      rw [show (1/4:ℝ) - 1 = -(3/4) by norm_num, div_eq_mul_inv,
        show (-(3/4:ℝ))⁻¹ = -(4/3) by norm_num]
      ring
    rw [h1]
    have h2 : (0:ℝ) ≤ (1/4:ℝ) ^ N := pow_nonneg (by norm_num) N
    linarith
  have hfiber : ∀ s : ℕ, ∑ t ∈ S.filter (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊ = s),
      fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2) ≤ ((4:ℝ) ^ s)⁻¹ * ((2 ^ (s + 1) + 2) * C) := by
    intro s
    set T : Finset ℝ := S.filter (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊ = s) with hTdef
    have step1 : ∑ t ∈ T, fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2) ≤
        ∑ t ∈ T, fibα a μ t * ((4:ℝ) ^ s)⁻¹ := by
      apply Finset.sum_le_sum
      intro t ht
      rw [hTdef] at ht
      obtain ⟨htS', hts⟩ := Finset.mem_filter.mp ht
      rw [hmin t htS']
      have hdec := hdecay t htS'
      rw [hts] at hdec
      exact mul_le_mul_of_nonneg_left hdec (fibα_nonneg a μ t)
    have step2 : ∑ t ∈ T, fibα a μ t * ((4:ℝ) ^ s)⁻¹ = ((4:ℝ) ^ s)⁻¹ * ∑ t ∈ T, fibα a μ t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_comm]
    have step3 : ∑ t ∈ T, fibα a μ t ≤ (2 ^ (s + 1) + 2) * C := by
      set G : Finset ℕ := ((lightSet a μ b ν m).image (grp a μ b ν m)).filter (fun k' =>
        glen a μ b ν m k ≤ glen a μ b ν m k' ∧
          ∃ t ∈ groupVals a μ b ν m k', |t - gctr a μ b ν m k| ≤ (2:ℝ) ^ (s + 1) * ρ) with hGdef
      have hR' : (0:ℝ) ≤ (2:ℝ) ^ (s + 1) * ρ := mul_nonneg (pow_nonneg (by norm_num) _) hρ.le
      have hρg : (0:ℝ) < gρ a μ b ν m k := hρdef ▸ hρ
      have hGcard : (G.card : ℝ) ≤ (2:ℝ) ^ (s + 1) + 2 := by
        have h := card_groups_meeting_le a μ b ν m k hk hρg ((2:ℝ) ^ (s + 1) * ρ) hR'
        rw [mul_div_cancel_right₀ _ hρg.ne'] at h
        rwa [← hGdef] at h
      have hsub : T ⊆ G.biUnion (groupVals a μ b ν m) := by
        intro t ht
        rw [hTdef] at ht
        obtain ⟨htS', hts⟩ := Finset.mem_filter.mp ht
        obtain ⟨htl, htne, hlen⟩ := htS t htS'
        rw [Finset.mem_biUnion]
        refine ⟨grp a μ b ν m t, ?_, Finset.mem_filter.mpr ⟨htl, rfl⟩⟩
        rw [hGdef, Finset.mem_filter]
        refine ⟨Finset.mem_image.mpr ⟨t, htl, rfl⟩, hlen, t, Finset.mem_filter.mpr ⟨htl, rfl⟩, ?_⟩
        have hup' := hup t htS'
        rw [hts] at hup'
        rw [hcdef] at hup'
        exact le_of_lt hup'
      have hsum1 : ∑ t ∈ T, fibα a μ t ≤ ∑ t ∈ G.biUnion (groupVals a μ b ν m), fibα a μ t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => fibα_nonneg a μ i)
      have hdisj : (G : Set ℕ).PairwiseDisjoint (groupVals a μ b ν m) := by
        intro k₁ _ k₂ _ hne
        apply Finset.disjoint_left.mpr
        intro t ht₁ ht₂
        obtain ⟨-, hg1⟩ := Finset.mem_filter.mp ht₁
        obtain ⟨-, hg2⟩ := Finset.mem_filter.mp ht₂
        exact hne (hg1.symm.trans hg2)
      have hsum2 : ∑ t ∈ G.biUnion (groupVals a μ b ν m), fibα a μ t =
          ∑ k' ∈ G, ∑ t ∈ groupVals a μ b ν m k', fibα a μ t := Finset.sum_biUnion hdisj
      have hg : ∀ k' ∈ G, ∑ t ∈ groupVals a μ b ν m k', fibα a μ t ≤ C := by
        intro k' _
        have h := group_fibα_le a μ b ν m hA hB k'
        rwa [← hAdef, ← hCdef] at h
      have hsum3 : ∑ k' ∈ G, ∑ t ∈ groupVals a μ b ν m k', fibα a μ t ≤ (G.card : ℝ) * C := by
        have h := Finset.sum_le_sum hg
        rwa [Finset.sum_const, nsmul_eq_mul] at h
      calc ∑ t ∈ T, fibα a μ t ≤ ∑ t ∈ G.biUnion (groupVals a μ b ν m), fibα a μ t := hsum1
        _ = ∑ k' ∈ G, ∑ t ∈ groupVals a μ b ν m k', fibα a μ t := hsum2
        _ ≤ (G.card : ℝ) * C := hsum3
        _ ≤ (2 ^ (s + 1) + 2) * C := mul_le_mul_of_nonneg_right hGcard hC0
    calc ∑ t ∈ T, fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2)
        ≤ ∑ t ∈ T, fibα a μ t * ((4:ℝ) ^ s)⁻¹ := step1
      _ = ((4:ℝ) ^ s)⁻¹ * ∑ t ∈ T, fibα a μ t := step2
      _ ≤ ((4:ℝ) ^ s)⁻¹ * ((2 ^ (s + 1) + 2) * C) :=
          mul_le_mul_of_nonneg_left step3 (inv_nonneg.mpr (pow_nonneg (by norm_num) s))
  set img : Finset ℕ := S.image (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊) with himg
  have hfinal : ∑ s ∈ img, ((4:ℝ) ^ s)⁻¹ * ((2 ^ (s + 1) + 2) * C) ≤ (80 / 3) * A / m := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s ∈ img, s < N := by
      by_cases hne : img.Nonempty
      · exact ⟨img.max' hne + 1, fun s hs => Nat.lt_succ_of_le (Finset.le_max' _ _ hs)⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        exact ⟨0, fun s hs => by rw [hne] at hs; exact (Finset.notMem_empty s hs).elim⟩
    have hsub : img ⊆ Finset.range N := fun s hs => Finset.mem_range.mpr (hN s hs)
    have hterm : ∀ s : ℕ, ((4:ℝ) ^ s)⁻¹ * ((2 ^ (s + 1) + 2) * C) =
        C * (2 * (1/2) ^ s + 2 * (1/4) ^ s) := by
      intro s
      rw [← hkey s]
      ring
    calc ∑ s ∈ img, ((4:ℝ) ^ s)⁻¹ * ((2 ^ (s + 1) + 2) * C)
        = ∑ s ∈ img, C * (2 * (1/2) ^ s + 2 * (1/4) ^ s) :=
          Finset.sum_congr rfl (fun s _ => hterm s)
      _ = C * ∑ s ∈ img, (2 * (1/2) ^ s + 2 * (1/4) ^ s) := by rw [← Finset.mul_sum]
      _ ≤ C * ∑ s ∈ Finset.range N, (2 * (1/2) ^ s + 2 * (1/4) ^ s) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)) hC0
      _ = C * (2 * ∑ s ∈ Finset.range N, (1/2:ℝ) ^ s + 2 * ∑ s ∈ Finset.range N, (1/4:ℝ) ^ s) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ C * (2 * 2 + 2 * (4/3)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hgeo2 N) (by norm_num))
              (mul_le_mul_of_nonneg_left (hgeo4 N) (by norm_num))) hC0
      _ = (80 / 3) * A / m := by
          have hnum : (2:ℝ) * 2 + 2 * (4/3) = 20 / 3 := by norm_num
          rw [hCdef, hnum, div_eq_mul_inv (4:ℝ) (m:ℝ), div_eq_mul_inv ((80/3) * A) (m:ℝ)]
          ring
  have hfib : (∑ t ∈ S, fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2)) =
      ∑ s ∈ img, ∑ t ∈ S.filter (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊ = s),
        fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2) := by
    have hmap : ∀ t ∈ S, (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊) t ∈
        S.image (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊) :=
      fun t ht => Finset.mem_image.mpr ⟨t, ht, rfl⟩
    rw [himg]
    exact (Finset.sum_fiberwise_of_maps_to hmap _).symm
  calc ∑ t ∈ S, fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2)
      = ∑ s ∈ img, ∑ t ∈ S.filter (fun t => Nat.log 2 ⌊|t - c| / ρ⌋₊ = s),
          fibα a μ t * min 1 (ρ ^ 2 / (t - c) ^ 2) := hfib
    _ ≤ ∑ s ∈ img, ((4:ℝ) ^ s)⁻¹ * ((2 ^ (s + 1) + 2) * C) :=
        Finset.sum_le_sum (fun s _ => hfiber s)
    _ ≤ (80 / 3) * A / m := hfinal

end covering

end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

/-- The rank of a sum of two matrices is at most the sum of their ranks. -/
theorem rank_add_le' {m' n : Type} [Fintype m'] [Fintype n] [DecidableEq n]
    (A B : Matrix m' n ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  have hle : Module.finrank ℂ ↥(A.mulVecLin + B.mulVecLin).range ≤
      Module.finrank ℂ ↥(A.mulVecLin.range ⊔ B.mulVecLin.range) :=
    Submodule.finrank_mono (LinearMap.range_add_le _ _)
  have hsum : Module.finrank ℂ ↥(A.mulVecLin.range ⊔ B.mulVecLin.range) ≤
      Module.finrank ℂ ↥A.mulVecLin.range + Module.finrank ℂ ↥B.mulVecLin.range := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A.mulVecLin.range B.mulVecLin.range
    omega
  have hun : (A + B).rank = Module.finrank ℂ ↥(A.mulVecLin + B.mulVecLin).range := by
    unfold Matrix.rank
    rw [Matrix.mulVecLin_add]
  calc (A + B).rank = Module.finrank ℂ ↥(A.mulVecLin + B.mulVecLin).range := hun
    _ ≤ _ := hle
    _ ≤ _ := hsum

/-- The rank of a finite matrix sum is at most the sum of the ranks. -/
theorem rank_sum_le {m' n : Type} [Fintype m'] [Fintype n] [DecidableEq n]
    {S : Finset ℕ} (M : ℕ → Matrix m' n ℂ) :
    (∑ k ∈ S, M k).rank ≤ ∑ k ∈ S, (M k).rank := by
  refine S.induction_on ?_ ?_
  · simp [Matrix.rank_zero]
  · intro k S hk ih
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (rank_add_le' _ _).trans (Nat.add_le_add_left ih _)

omit [DecidableEq O] in

/-- Matrix singular values decrease as the index increases. -/
theorem matrixSingularValues_anti {X : Matrix O I ℂ} {q q' : ℕ} (h : q ≤ q') :
    matrixSingularValues X q' ≤ matrixSingularValues X q := by
  simp only [matrixSingularValues_apply]
  exact X.toEuclideanLin.singularValues_antitone h

omit [DecidableEq O] in

/-- A singular value vanishes when its index is at least the matrix rank. -/
theorem matrixSingularValues_eq_zero_of_rank_le {X : Matrix O I ℂ} {q : ℕ}
    (hq : X.rank ≤ q) : matrixSingularValues X q = 0 := by
  rcases eq_or_lt_of_le (matrixSingularValues_nonneg X q) with h0 | hpos
  · exact h0.symm
  · rw [matrixSingularValues_pos_iff_lt_finrank_range,
      finrank_range_toEuclideanLin_eq_rank] at hpos
    omega

/-- The Lipschitz condition bounds every divided difference entry in norm by the nonnegative
constant `L`. -/
theorem ddMat_entry_norm_le {J I : Type} [Fintype J] [Fintype I] {μ : J → ℝ} {ν : I → ℝ}
    {f : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hf : lipUnion μ ν f L) (j : J) (i : I) :
    ‖ddMat μ ν f j i‖ ≤ L := by
  unfold ddMat
  simp only [Matrix.of_apply]
  by_cases h : μ j = ν i
  · rw [if_pos h]; simpa using hL
  · rw [if_neg h]
    have hpos : (0 : ℝ) < ‖((μ j - ν i : ℝ) : ℂ)‖ := by
      rw [norm_pos_iff]
      exact_mod_cast sub_ne_zero.mpr h
    rw [norm_div, div_le_iff₀ hpos]
    have hcast : ‖((μ j - ν i : ℝ) : ℂ)‖ = |μ j - ν i| := by norm_cast
    rw [hcast]
    exact hf (μ j) (Set.mem_union_left _ (Set.mem_range_self j))
      (ν i) (Set.mem_union_right _ (Set.mem_range_self i))

/-- If nonnegative weights have total mass at most `W`, at most `m` distinct labels can carry
fiber mass at least W / m, assuming `m` and `W` are positive. -/
theorem card_filter_image_le_of_mass' {I V : Type} [Fintype I] [DecidableEq V] (eigL : I → V)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) {m : ℕ} (hm : 0 < m) {W : ℝ} (hW : 0 < W)
    (hsum : ∑ i, w i ≤ W) :
    ((Finset.univ.image eigL).filter
      (fun t => W / m ≤ ∑ i ∈ Finset.univ.filter (fun i' => eigL i' = t), w i)).card ≤ m := by
  set S := (Finset.univ.image eigL).filter
    (fun t => W / m ≤ ∑ i ∈ Finset.univ.filter (fun i' => eigL i' = t), w i) with hS
  have hfiber_nn : ∀ t : V, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i' => eigL i' = t), w i :=
    fun t => Finset.sum_nonneg fun i _ => hw i
  have htot : ∑ t ∈ Finset.univ.image eigL,
      ∑ i ∈ Finset.univ.filter (fun i' => eigL i' = t), w i ≤ W := by
    rw [Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem eigL (Finset.mem_univ i)) w]
    exact hsum
  have h1 : (S.card : ℝ) * (W / (m : ℝ)) ≤ W := by
    calc (S.card : ℝ) * (W / (m : ℝ)) = ∑ t ∈ S, W / (m : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ S, ∑ i ∈ Finset.univ.filter (fun i' => eigL i' = t), w i := by
          apply Finset.sum_le_sum
          intro t ht
          exact (Finset.mem_filter.1 ht).2
      _ ≤ ∑ t ∈ Finset.univ.image eigL, ∑ i ∈ Finset.univ.filter (fun i' => eigL i' = t), w i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun t _ _ => hfiber_nn t
      _ ≤ W := htot
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkey : (S.card : ℝ) * W ≤ W * (m : ℝ) := by
    have h2 : (S.card : ℝ) * (W / (m : ℝ)) = (S.card : ℝ) * W / m := by ring
    rw [h2, div_le_iff₀ hmR] at h1
    linarith [h1]
  have hkey' : (S.card : ℝ) ≤ (m : ℝ) := by
    rw [mul_comm (S.card : ℝ) W] at hkey
    exact le_of_mul_le_mul_left hkey hW
  exact_mod_cast hkey'

end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators Matrix.Norms.L2Operator

section decomposition

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  (μ : J → ℝ) (ν : I → ℝ) (f : ℝ → ℂ) (a : J → ℂ) (b : I → ℂ) (m : ℕ)

/-- The scalar divided difference of `f`, set to zero when its two arguments coincide. -/
def ddVal (x y : ℝ) : ℂ := if x = y then 0 else (f x - f y) / ((x - y : ℝ) : ℂ)

omit [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] in

/-- An entry of the divided difference matrix equals `ddVal` at the corresponding eigenvalues. -/
theorem ddMat_apply_eq_ddVal (j : J) (i : I) :
    ddMat μ ν f j i = ddVal f (μ j) (ν i) := rfl

/-- The part of the weighted divided difference matrix supported on rows whose eigenvalues are
not light. -/
def Hrows : Matrix J I ℂ :=
  Matrix.of fun j i => if μ j ∈ lightSet a μ b ν m then 0
    else ddVal f (μ j) (ν i) * a j * b i

/-- The part of the weighted divided difference matrix supported on light rows and columns whose
eigenvalues are not light. -/
def Hcols : Matrix J I ℂ :=
  Matrix.of fun j i => if μ j ∈ lightSet a μ b ν m ∧ ν i ∉ lightSet a μ b ν m
    then ddVal f (μ j) (ν i) * a j * b i else 0

/-- The light eigenvalues in other groups whose lengths are at least the length of group `k`. -/
def farJset (k : ℕ) : Finset ℝ :=
  (lightSet a μ b ν m).filter (fun t =>
    grp a μ b ν m t ≠ k ∧ glen a μ b ν m k ≤ glen a μ b ν m (grp a μ b ν m t))

/-- The light eigenvalues in other groups whose lengths strictly exceed the length of group `k`. -/
def farIset (k : ℕ) : Finset ℝ :=
  (lightSet a μ b ν m).filter (fun t =>
    grp a μ b ν m t ≠ k ∧ glen a μ b ν m k < glen a μ b ν m (grp a μ b ν m t))

/-- The outer product forming the left function-value contribution for far rows paired with
columns in group `k`. -/
def P1 (k : ℕ) : Matrix J I ℂ := Matrix.vecMulVec
  (fun j => if μ j ∈ farJset μ ν a b m k then f (μ j) * a j / ((μ j - gctr a μ b ν m k : ℝ) : ℂ) else 0)
  (fun i => if ν i ∈ groupVals a μ b ν m k then b i else 0)

/-- The outer product forming the negative right function-value contribution for far rows paired
with columns in group `k`. -/
def P2 (k : ℕ) : Matrix J I ℂ := Matrix.vecMulVec
  (fun j => if μ j ∈ farJset μ ν a b m k then a j / ((μ j - gctr a μ b ν m k : ℝ) : ℂ) else 0)
  (fun i => if ν i ∈ groupVals a μ b ν m k then -(f (ν i) * b i) else 0)

/-- The outer product forming the negative left function-value contribution for rows in group
`k` paired with far columns. -/
def Q1 (k : ℕ) : Matrix J I ℂ := Matrix.vecMulVec
  (fun j => if μ j ∈ groupVals a μ b ν m k then -(f (μ j) * a j) else 0)
  (fun i => if ν i ∈ farIset μ ν a b m k then b i / ((ν i - gctr a μ b ν m k : ℝ) : ℂ) else 0)

/-- The outer product forming the right function-value contribution for rows in group `k` paired
with far columns. -/
def Q2 (k : ℕ) : Matrix J I ℂ := Matrix.vecMulVec
  (fun j => if μ j ∈ groupVals a μ b ν m k then a j else 0)
  (fun i => if ν i ∈ farIset μ ν a b m k then
    f (ν i) * b i / ((ν i - gctr a μ b ν m k : ℝ) : ℂ) else 0)

/-- The finite set of group indices represented among the light eigenvalues. -/
def groupIdx : Finset ℕ := (lightSet a μ b ν m).image (grp a μ b ν m)

/-- The sum over represented groups of the four outer products approximating interactions
between different light groups. -/
def Lfar : Matrix J I ℂ := ∑ k ∈ groupIdx μ ν a b m, (P1 μ ν f a b m k + P2 μ ν f a b m k +
  Q1 μ ν f a b m k + Q2 μ ν f a b m k)

/-- The approximation obtained by adding the heavy-row, heavy-column, and far-group
contributions. -/
def Hmat : Matrix J I ℂ := Hrows μ ν f a b m + Hcols μ ν f a b m + Lfar μ ν f a b m

/-- The residual after subtracting `Hmat` from the weighted divided difference matrix. -/
def Rmat : Matrix J I ℂ := (ddMat μ ν f ⊙ Matrix.vecMulVec a b) - Hmat μ ν f a b m

end decomposition

end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators Matrix.Norms.L2Operator

section rankbounds

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {μ : J → ℝ} {ν : I → ℝ} {f : ℝ → ℂ} (a : J → ℂ) (b : I → ℂ) (m : ℕ)
  (hm : 0 < m) (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2)

include hm hA hB

omit [DecidableEq J] [DecidableEq I] in

/-- Under positive parameter and total mass assumptions, at most 2m distinct left eigenvalues
lie outside the light set. -/
theorem card_heavy_rows_le :
    ((Finset.univ.image μ).filter (fun t => t ∉ lightSet a μ b ν m)).card ≤ 2 * m := by
  have hβm : (0 : ℝ) < (∑ i, ‖b i‖ ^ 2) / m := div_pos hB (by exact_mod_cast hm)
  have hunion : (Finset.univ.image μ).filter (fun t => t ∉ lightSet a μ b ν m) ⊆
      ((Finset.univ.image μ).filter (fun t => (∑ j, ‖a j‖ ^ 2) / m ≤ fibα a μ t)) ∪
      ((Finset.univ.image ν).filter (fun t => (∑ i, ‖b i‖ ^ 2) / m ≤ fibβ b ν t)) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htim, htNL⟩ := ht
    have hφ : ¬ (fibα a μ t < (∑ j, ‖a j‖ ^ 2) / m ∧ fibβ b ν t < (∑ i, ‖b i‖ ^ 2) / m) := by
      intro hφ
      apply htNL
      rw [lightSet, Finset.mem_filter]
      exact ⟨Finset.mem_union_left _ htim, hφ⟩
    rw [not_and_or, not_lt, not_lt] at hφ
    rcases hφ with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htim, h⟩)
    · have htν : t ∈ Finset.univ.image ν := by
        have hpos : 0 < fibβ b ν t := lt_of_lt_of_le hβm h
        have hne : (Finset.univ.filter (fun i => ν i = t)).Nonempty := by
          by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          have : fibβ b ν t = 0 := by
            rw [fibβ, hne, Finset.sum_empty]
          rw [this] at hpos
          exact lt_irrefl _ hpos
        obtain ⟨i, hi⟩ := hne
        rw [Finset.mem_filter] at hi
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.2⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htν, h⟩)
  calc ((Finset.univ.image μ).filter (fun t => t ∉ lightSet a μ b ν m)).card
      ≤ (((Finset.univ.image μ).filter (fun t => (∑ j, ‖a j‖ ^ 2) / m ≤ fibα a μ t)) ∪
        ((Finset.univ.image ν).filter (fun t => (∑ i, ‖b i‖ ^ 2) / m ≤ fibβ b ν t))).card :=
        Finset.card_le_card hunion
    _ ≤ ((Finset.univ.image μ).filter (fun t => (∑ j, ‖a j‖ ^ 2) / m ≤ fibα a μ t)).card +
        ((Finset.univ.image ν).filter (fun t => (∑ i, ‖b i‖ ^ 2) / m ≤ fibβ b ν t)).card :=
        Finset.card_union_le _ _
    _ ≤ m + m :=
        Nat.add_le_add
          (by simpa only [RankLogStability.Partition.fibα] using
            card_filter_image_le_of_mass' μ (fun j => ‖a j‖ ^ 2) (fun j => sq_nonneg _) hm hA le_rfl)
          (by simpa only [RankLogStability.Partition.fibβ] using
            card_filter_image_le_of_mass' ν (fun i => ‖b i‖ ^ 2) (fun i => sq_nonneg _) hm hB le_rfl)
    _ = 2 * m := (two_mul m).symm

omit [DecidableEq J] [DecidableEq I] in

/-- Under positive parameter and total mass assumptions, at most 2m distinct right eigenvalues
lie outside the light set. -/
theorem card_heavy_cols_le :
    ((Finset.univ.image ν).filter (fun t => t ∉ lightSet a μ b ν m)).card ≤ 2 * m := by
  have hαm : (0 : ℝ) < (∑ j, ‖a j‖ ^ 2) / m := div_pos hA (by exact_mod_cast hm)
  have hunion : (Finset.univ.image ν).filter (fun t => t ∉ lightSet a μ b ν m) ⊆
      ((Finset.univ.image μ).filter (fun t => (∑ j, ‖a j‖ ^ 2) / m ≤ fibα a μ t)) ∪
      ((Finset.univ.image ν).filter (fun t => (∑ i, ‖b i‖ ^ 2) / m ≤ fibβ b ν t)) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htim, htNL⟩ := ht
    have hφ : ¬ (fibα a μ t < (∑ j, ‖a j‖ ^ 2) / m ∧ fibβ b ν t < (∑ i, ‖b i‖ ^ 2) / m) := by
      intro hφ
      apply htNL
      rw [lightSet, Finset.mem_filter]
      exact ⟨Finset.mem_union_right _ htim, hφ⟩
    rw [not_and_or, not_lt, not_lt] at hφ
    rcases hφ with h | h
    · have htμ : t ∈ Finset.univ.image μ := by
        have hpos : 0 < fibα a μ t := lt_of_lt_of_le hαm h
        have hne : (Finset.univ.filter (fun j => μ j = t)).Nonempty := by
          by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          have : fibα a μ t = 0 := by
            rw [fibα, hne, Finset.sum_empty]
          rw [this] at hpos
          exact lt_irrefl _ hpos
        obtain ⟨j, hj⟩ := hne
        rw [Finset.mem_filter] at hj
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.2⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htμ, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htim, h⟩)
  calc ((Finset.univ.image ν).filter (fun t => t ∉ lightSet a μ b ν m)).card
      ≤ (((Finset.univ.image μ).filter (fun t => (∑ j, ‖a j‖ ^ 2) / m ≤ fibα a μ t)) ∪
        ((Finset.univ.image ν).filter (fun t => (∑ i, ‖b i‖ ^ 2) / m ≤ fibβ b ν t))).card :=
        Finset.card_le_card hunion
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ m + m :=
        Nat.add_le_add
          (by simpa only [RankLogStability.Partition.fibα] using
            card_filter_image_le_of_mass' μ (fun j => ‖a j‖ ^ 2) (fun j => sq_nonneg _) hm hA le_rfl)
          (by simpa only [RankLogStability.Partition.fibβ] using
            card_filter_image_le_of_mass' ν (fun i => ‖b i‖ ^ 2) (fun i => sq_nonneg _) hm hB le_rfl)
    _ = 2 * m := (two_mul m).symm

/-- The heavy-row contribution has rank at most 2m under the positive parameter and mass
assumptions. -/
theorem Hrows_rank_le : (Hrows μ ν f a b m).rank ≤ 2 * m := by
  have hrewrite : Hrows μ ν f a b m = Matrix.of fun j i =>
      (if μ j ∉ lightSet a μ b ν m then a j else 0) * (ddVal f (μ j) (ν i) * b i) := by
    ext j i
    simp only [Hrows, Matrix.of_apply]
    by_cases h : μ j ∈ lightSet a μ b ν m
    · simp [h]
    · simp [h]; ring
  rw [hrewrite]
  exact (rank_of_row_factor_restrict μ (fun t => t ∉ lightSet a μ b ν m)
    (fun t i => ddVal f t (ν i) * b i) a).trans (card_heavy_rows_le (μ := μ) (ν := ν) a b m hm hA hB)

/-- The heavy-column contribution has rank at most 2m under the positive parameter and mass
assumptions. -/
theorem Hcols_rank_le : (Hcols μ ν f a b m).rank ≤ 2 * m := by
  have hrewrite : Hcols μ ν f a b m = Matrix.of fun j i =>
      (if μ j ∈ lightSet a μ b ν m then ddVal f (μ j) (ν i) * a j else 0) *
        (if ν i ∉ lightSet a μ b ν m then b i else 0) := by
    ext j i
    simp only [Hcols, Matrix.of_apply]
    by_cases hj : μ j ∈ lightSet a μ b ν m
    · by_cases hi : ν i ∉ lightSet a μ b ν m
      · simp [hj, hi]
      · simp [hj, hi]
    · simp [hj]
  rw [hrewrite]
  exact (rank_of_col_factor_restrict ν (fun t => t ∉ lightSet a μ b ν m)
    (fun s j => if μ j ∈ lightSet a μ b ν m then ddVal f (μ j) s * a j else 0) b).trans
    (card_heavy_cols_le (μ := μ) (ν := ν) a b m hm hA hB)

omit [DecidableEq J] hm in

/-- The far-group approximation has rank at most 4(m + 1) under the positive parameter and mass
assumptions. -/
theorem Lfar_rank_le : (Lfar μ ν f a b m).rank ≤ 4 * (m + 1) := by
  rw [Lfar]
  refine (rank_sum_le _).trans ?_
  calc ∑ k ∈ groupIdx μ ν a b m, (P1 μ ν f a b m k + P2 μ ν f a b m k + Q1 μ ν f a b m k +
          Q2 μ ν f a b m k).rank
      ≤ ∑ k ∈ groupIdx μ ν a b m, 4 := by
        apply Finset.sum_le_sum
        intro k _
        have h1 : (P1 μ ν f a b m k).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
        have h2 : (P2 μ ν f a b m k).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
        have h3 : (Q1 μ ν f a b m k).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
        have h4 : (Q2 μ ν f a b m k).rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
        have h12 := rank_add_le' (P1 μ ν f a b m k) (P2 μ ν f a b m k)
        have h123 := rank_add_le' (P1 μ ν f a b m k + P2 μ ν f a b m k) (Q1 μ ν f a b m k)
        have h1234 := rank_add_le' (P1 μ ν f a b m k + P2 μ ν f a b m k + Q1 μ ν f a b m k)
          (Q2 μ ν f a b m k)
        omega
    _ = 4 * (groupIdx μ ν a b m).card := by
        simp [Finset.sum_const, mul_comm]
    _ ≤ 4 * (m + 1) := by
        apply Nat.mul_le_mul_left
        have hsub : groupIdx μ ν a b m ⊆ Finset.range (m + 1) := by
          intro k hk
          simp only [groupIdx, Finset.mem_image] at hk
          obtain ⟨t, ht, rfl⟩ := hk
          rw [Finset.mem_range]
          exact Nat.lt_succ_iff.mpr (grp_le_m a μ b ν m hA hB ht)
        exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

/-- The approximation `Hmat` has rank at most 8m + 4 under the positive parameter and mass
assumptions. -/
theorem Hmat_rank_le : (Hmat μ ν f a b m).rank ≤ 8 * m + 4 := by
  rw [Hmat]
  have h1 := Hrows_rank_le (μ := μ) (ν := ν) (f := f) a b m hm hA hB
  have h2 := Hcols_rank_le (μ := μ) (ν := ν) (f := f) a b m hm hA hB
  have h3 := Lfar_rank_le (μ := μ) (ν := ν) (f := f) a b m hA hB
  have h12 := rank_add_le' (Hrows μ ν f a b m) (Hcols μ ν f a b m)
  have h123 := rank_add_le' (Hrows μ ν f a b m + Hcols μ ν f a b m) (Lfar μ ν f a b m)
  omega

end rankbounds

end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators Matrix.Norms.L2Operator

section entries

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {μ : J → ℝ} {ν : I → ℝ} {f : ℝ → ℂ} (a : J → ℂ) (b : I → ℂ) (m : ℕ)

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right eigenvalue and coefficient families leaves the light set
unchanged. -/
theorem lightSet_symm : lightSet b ν a μ m = lightSet a μ b ν m := by
  ext t
  simp only [lightSet, Finset.mem_filter, Finset.mem_union, fibα, fibβ]
  tauto

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right families leaves the combined fiber mass unchanged. -/
theorem γmass_symm (t : ℝ) : γmass b ν a μ t = γmass a μ b ν t := by
  simp only [γmass, fibα, fibβ, add_comm]

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right families leaves each group index unchanged. -/
theorem grp_symm (t : ℝ) : grp b ν a μ m t = grp a μ b ν m t := by
  simp only [grp, Γcum, lightSet_symm a b m, γmass_symm a b]

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right families leaves each group unchanged. -/
theorem groupVals_symm (k : ℕ) : groupVals b ν a μ m k = groupVals a μ b ν m k := by
  simp only [groupVals, lightSet_symm a b m, grp_symm a b m]

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right families leaves each group length unchanged. -/
theorem glen_symm (k : ℕ) : glen b ν a μ m k = glen a μ b ν m k := by
  simp only [glen, glo, ghi, groupVals_symm a b m]

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right families leaves each group midpoint unchanged. -/
theorem gctr_symm (k : ℕ) : gctr b ν a μ m k = gctr a μ b ν m k := by
  simp only [gctr, glo, ghi, groupVals_symm a b m]

omit [DecidableEq J] [DecidableEq I] in

/-- Exchanging the left and right families leaves each group radius unchanged. -/
theorem gρ_symm (k : ℕ) : gρ b ν a μ m k = gρ a μ b ν m k := by
  simp only [gρ, glen_symm a b m]

omit [DecidableEq J] [DecidableEq I] in

/-- An eigenvalue assigned to another group lies strictly outside the interval spanned by a
nonempty group. -/
theorem lt_lo_or_gt_hi_of_grp_ne {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) {t : ℝ}
    (_ht : t ∈ lightSet a μ b ν m) (htk : grp a μ b ν m t ≠ k) :
    t < glo a μ b ν m k ∨ ghi a μ b ν m k < t := by
  by_contra h
  push Not at h
  have h1 := grp_mono a μ b ν m h.1
  have h2 := grp_mono a μ b ν m h.2
  have hlo := (Finset.mem_filter.mp (glo_mem a μ b ν m hk)).2
  have hhi := (Finset.mem_filter.mp (ghi_mem a μ b ν m hk)).2
  rw [hlo] at h1
  rw [hhi] at h2
  exact htk (le_antisymm h2 h1)

omit [DecidableEq J] [DecidableEq I] in

/-- A sum supported on the unique group containing `x` reduces to the contribution at its group
index when the light-set and predicate conditions hold. -/
private theorem sum_group_piece (x : ℝ) (P : ℕ → Prop) [DecidablePred P]
    (w : ℕ → ℂ) :
    ∑ k ∈ groupIdx μ ν a b m, (if x ∈ groupVals a μ b ν m k ∧ P k then w k else 0) =
      if x ∈ lightSet a μ b ν m ∧ P (grp a μ b ν m x) then w (grp a μ b ν m x) else 0 := by
  classical
  by_cases hx : x ∈ lightSet a μ b ν m
  · have hxg : grp a μ b ν m x ∈ groupIdx μ ν a b m := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [Finset.sum_eq_single (grp a μ b ν m x)]
    · simp [groupVals, hx]
    · intro k _ hk
      have hneq : grp a μ b ν m x ≠ k := Ne.symm hk
      simp only [groupVals, Finset.mem_filter, hneq, and_false, false_and, if_false]
    · exact fun h => (h hxg).elim
  · simp only [groupVals, Finset.mem_filter, hx, false_and, if_false, Finset.sum_const_zero]

omit [DecidableEq J] [DecidableEq I] in

/-- Each entry of the far-group approximation is the sum of its two conditional contributions
with denominators measured from the relevant group midpoint. -/
theorem Lfar_apply (j : J) (i : I) :
    Lfar μ ν f a b m j i =
      (if μ j ∈ farJset μ ν a b m (grp a μ b ν m (ν i)) ∧ ν i ∈ lightSet a μ b ν m then
        (f (μ j) - f (ν i)) * a j * b i /
          ((μ j - gctr a μ b ν m (grp a μ b ν m (ν i)) : ℝ) : ℂ) else 0) +
      (if ν i ∈ farIset μ ν a b m (grp a μ b ν m (μ j)) ∧ μ j ∈ lightSet a μ b ν m then
        (f (ν i) - f (μ j)) * a j * b i /
          ((ν i - gctr a μ b ν m (grp a μ b ν m (μ j)) : ℝ) : ℂ) else 0) := by
  have hp : ∀ k, (P1 μ ν f a b m k + P2 μ ν f a b m k) j i =
      if ν i ∈ groupVals a μ b ν m k ∧ μ j ∈ farJset μ ν a b m k then
        (f (μ j) - f (ν i)) * a j * b i / ((μ j - gctr a μ b ν m k : ℝ) : ℂ) else 0 := by
    intro k
    simp only [P1, P2, Matrix.add_apply, Matrix.vecMulVec_apply]
    split_ifs <;> simp_all only [not_and, not_true_eq_false, true_implies, implies_true] <;> ring
  have hq : ∀ k, (Q1 μ ν f a b m k + Q2 μ ν f a b m k) j i =
      if μ j ∈ groupVals a μ b ν m k ∧ ν i ∈ farIset μ ν a b m k then
        (f (ν i) - f (μ j)) * a j * b i / ((ν i - gctr a μ b ν m k : ℝ) : ℂ) else 0 := by
    intro k
    simp only [Q1, Q2, Matrix.add_apply, Matrix.vecMulVec_apply]
    split_ifs <;> simp_all only [not_and, not_true_eq_false, true_implies, implies_true] <;> ring
  have hsplit : Lfar μ ν f a b m j i =
      (∑ k ∈ groupIdx μ ν a b m, (P1 μ ν f a b m k + P2 μ ν f a b m k) j i) +
      (∑ k ∈ groupIdx μ ν a b m, (Q1 μ ν f a b m k + Q2 μ ν f a b m k) j i) := by
    simp only [Lfar, Matrix.sum_apply, Matrix.add_apply, Finset.sum_add_distrib]
    ring
  rw [hsplit]
  simp_rw [hp, hq]
  rw [sum_group_piece a b m, sum_group_piece a b m]
  simp only [and_comm]

omit [DecidableEq J] [DecidableEq I] in

/-- The residual vanishes on every row whose eigenvalue is not light. -/
theorem Rmat_eq_zero_of_not_light_row {j : J} (hj : μ j ∉ lightSet a μ b ν m) (i : I) :
    Rmat μ ν f a b m j i = 0 := by
  have hn : ∀ k, μ j ∉ farJset μ ν a b m k := by
    intro k h
    exact hj (Finset.mem_filter.mp h).1
  simp only [Rmat, Hmat, Hrows, Hcols, Matrix.sub_apply, Matrix.add_apply,
    Matrix.of_apply, Lfar_apply a b m j i, hj, hn, false_and, and_false, if_false,
    ddMat_apply_eq_ddVal, Matrix.hadamard_apply, Matrix.vecMulVec_apply]
  ring

omit [DecidableEq J] [DecidableEq I] in

/-- The residual vanishes when its row eigenvalue is light and its column eigenvalue is not
light. -/
theorem Rmat_eq_zero_of_not_light_col {j : J} (hj : μ j ∈ lightSet a μ b ν m) {i : I}
    (hi : ν i ∉ lightSet a μ b ν m) : Rmat μ ν f a b m j i = 0 := by
  have hn : ∀ k, ν i ∉ farIset μ ν a b m k := by
    intro k h
    exact hi (Finset.mem_filter.mp h).1
  simp only [Rmat, Hmat, Hrows, Hcols, Matrix.sub_apply, Matrix.add_apply,
    Matrix.of_apply, Lfar_apply a b m j i, hj, hi, hn, true_and, false_and, and_false,
    if_false, if_true, not_false_eq_true, ddMat_apply_eq_ddVal, Matrix.hadamard_apply, Matrix.vecMulVec_apply]
  ring

omit [DecidableEq J] [DecidableEq I] in

/-- Within a single light group, the squared magnitude of a residual entry is at most L² times
the product of the squared coefficient magnitudes. -/
theorem Rmat_diag_bound {L : ℝ} (hL : 0 ≤ L) (hf : lipUnion μ ν f L) {j : J} {i : I}
    (hj : μ j ∈ lightSet a μ b ν m) (hi : ν i ∈ lightSet a μ b ν m)
    (h : grp a μ b ν m (μ j) = grp a μ b ν m (ν i)) :
    Complex.normSq (Rmat μ ν f a b m j i) ≤ L ^ 2 * (‖a j‖ ^ 2 * ‖b i‖ ^ 2) := by
  have hnJ : μ j ∉ farJset μ ν a b m (grp a μ b ν m (ν i)) := by
    simp [farJset, h]
  have hnI : ν i ∉ farIset μ ν a b m (grp a μ b ν m (μ j)) := by
    simp [farIset, h]
  have heq : Rmat μ ν f a b m j i = ddMat μ ν f j i * (a j * b i) := by
    simp only [Rmat, Hmat, Hrows, Hcols, Matrix.sub_apply, Matrix.add_apply,
      Matrix.of_apply, Lfar_apply a b m j i, hj, hi, hnJ, hnI, false_and,
      not_true_eq_false, and_false, if_false, if_true, Matrix.hadamard_apply, Matrix.vecMulVec_apply]
    ring
  rw [heq, Complex.normSq_eq_norm_sq, norm_mul, norm_mul, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (ddMat_entry_norm_le hL hf j i) 2)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Replacing a divided-difference denominator by the distance to a center gives a squared
residual bounded by the stated truncated inverse-square decay factor. -/
private theorem dd_residual_normSq_le {x y c ρ L : ℝ} {f : ℝ → ℂ} (a b : ℂ)
    (hxy : x ≠ y) (hxc : x ≠ c) (_hL : 0 ≤ L)
    (hf : ‖f x - f y‖ ≤ L * |x - y|)
    (hy : |y - c| ≤ ρ) (hx : ρ ≤ |x - c|) :
    Complex.normSq (ddVal f x y * a * b - (f x - f y) * a * b / ((x - c : ℝ) : ℂ)) ≤
      L ^ 2 * (‖a‖ ^ 2 * ‖b‖ ^ 2) * min 1 (ρ ^ 2 / (x - c) ^ 2) := by
  have hxyC : ((x - y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxy
  have hxcC : ((x - c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxc
  have heq : ddVal f x y * a * b - (f x - f y) * a * b / ((x - c : ℝ) : ℂ) =
      (ddVal f x y * a * b) * (((y - c : ℝ) : ℂ) / ((x - c : ℝ) : ℂ)) := by
    simp only [ddVal, if_neg hxy]
    field_simp [hxyC, hxcC]
    push_cast
    ring
  have hdd : ‖ddVal f x y‖ ≤ L := by
    simp only [ddVal, if_neg hxy, norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy))).mpr hf
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hy
  have hx2 : ρ ^ 2 ≤ (x - c) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hρ hx 2
  rw [min_eq_right (div_le_one_of_le₀ hx2 (sq_nonneg _)), heq,
    Complex.normSq_eq_norm_sq, norm_mul, norm_mul, norm_mul, norm_div,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, mul_pow, div_pow, sq_abs, sq_abs]
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hdd 2
  have hy2 : (y - c) ^ 2 ≤ ρ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hy 2
  calc ‖ddVal f x y‖ ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2 * ((y - c) ^ 2 / (x - c) ^ 2)
      ≤ (L ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2) * (ρ ^ 2 / (x - c) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd2
          (sq_nonneg _)) (sq_nonneg _)) (div_le_div_of_nonneg_right hy2 (sq_nonneg _))
          (div_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
    _ = L ^ 2 * (‖a‖ ^ 2 * ‖b‖ ^ 2) * (ρ ^ 2 / (x - c) ^ 2) := by ring

omit [DecidableEq J] [DecidableEq I] in

/-- A light eigenvalue belonging to a different group cannot equal the midpoint of a nonempty
group. -/
private theorem ne_ctr_of_grp_ne {k : ℕ} (hk : (groupVals a μ b ν m k).Nonempty) {t : ℝ}
    (ht : t ∈ lightSet a μ b ν m) (htk : grp a μ b ν m t ≠ k) :
    t ≠ gctr a μ b ν m k := by
  have hgh := glo_le_ghi a μ b ν m hk
  rcases lt_lo_or_gt_hi_of_grp_ne a b m hk ht htk with h | h
  · intro heq
    rw [heq, gctr] at h
    linarith
  · intro heq
    rw [heq, gctr] at h
    linarith

omit [DecidableEq J] [DecidableEq I] in

/-- For different light groups with the column group no longer than the row group, the squared
residual entry satisfies the inverse-square decay bound centered at the column group. -/
theorem Rmat_caseJ_bound {L : ℝ} (hL : 0 ≤ L) (hf : lipUnion μ ν f L) {j : J} {i : I}
    (hj : μ j ∈ lightSet a μ b ν m) (hi : ν i ∈ lightSet a μ b ν m)
    (h : grp a μ b ν m (μ j) ≠ grp a μ b ν m (ν i))
    (hlen : glen a μ b ν m (grp a μ b ν m (ν i)) ≤ glen a μ b ν m (grp a μ b ν m (μ j))) :
    Complex.normSq (Rmat μ ν f a b m j i) ≤
      L ^ 2 * (‖a j‖ ^ 2 * ‖b i‖ ^ 2) *
        min 1 ((gρ a μ b ν m (grp a μ b ν m (ν i))) ^ 2 /
          (μ j - gctr a μ b ν m (grp a μ b ν m (ν i))) ^ 2) := by
  have hgroup : ν i ∈ groupVals a μ b ν m (grp a μ b ν m (ν i)) := Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hk : (groupVals a μ b ν m (grp a μ b ν m (ν i))).Nonempty := ⟨ν i, hgroup⟩
  have hfar : μ j ∈ farJset μ ν a b m (grp a μ b ν m (ν i)) :=
    Finset.mem_filter.mpr ⟨hj, h, hlen⟩
  have hnfar : ν i ∉ farIset μ ν a b m (grp a μ b ν m (μ j)) := by
    intro hh
    exact (not_lt.mpr hlen) (Finset.mem_filter.mp hh).2.2
  have heq : Rmat μ ν f a b m j i = ddVal f (μ j) (ν i) * a j * b i -
      (f (μ j) - f (ν i)) * a j * b i /
        ((μ j - gctr a μ b ν m (grp a μ b ν m (ν i)) : ℝ) : ℂ) := by
    simp only [Rmat, Hmat, Hrows, Hcols, Matrix.sub_apply, Matrix.add_apply,
      Matrix.of_apply, Lfar_apply a b m j i, hj, hi, hfar, hnfar, true_and,
      not_true_eq_false, and_false, false_and, if_false, if_true,
      ddMat_apply_eq_ddVal, Matrix.hadamard_apply, Matrix.vecMulVec_apply]
    ring
  rw [heq]
  exact dd_residual_normSq_le (a j) (b i)
    (fun heq => h (congrArg (grp a μ b ν m) heq))
    (ne_ctr_of_grp_ne a b m hk hj h) hL
    (hf _ (Or.inl ⟨j, rfl⟩) _ (Or.inr ⟨i, rfl⟩))
    (abs_sub_ctr_le a μ b ν m hk hgroup)
    (ge_ρ_of_grp_ne a μ b ν m hk hj h)

omit [DecidableEq J] [DecidableEq I] in

/-- For different light groups with the row group shorter than the column group, the squared
residual entry satisfies the inverse-square decay bound centered at the row group. -/
theorem Rmat_caseI_bound {L : ℝ} (hL : 0 ≤ L) (hf : lipUnion μ ν f L) {j : J} {i : I}
    (hj : μ j ∈ lightSet a μ b ν m) (hi : ν i ∈ lightSet a μ b ν m)
    (h : grp a μ b ν m (μ j) ≠ grp a μ b ν m (ν i))
    (hlen : glen a μ b ν m (grp a μ b ν m (μ j)) < glen a μ b ν m (grp a μ b ν m (ν i))) :
    Complex.normSq (Rmat μ ν f a b m j i) ≤
      L ^ 2 * (‖a j‖ ^ 2 * ‖b i‖ ^ 2) *
        min 1 ((gρ a μ b ν m (grp a μ b ν m (μ j))) ^ 2 /
          (ν i - gctr a μ b ν m (grp a μ b ν m (μ j))) ^ 2) := by
  have hgroup : μ j ∈ groupVals a μ b ν m (grp a μ b ν m (μ j)) := Finset.mem_filter.mpr ⟨hj, rfl⟩
  have hk : (groupVals a μ b ν m (grp a μ b ν m (μ j))).Nonempty := ⟨μ j, hgroup⟩
  have hfar : ν i ∈ farIset μ ν a b m (grp a μ b ν m (μ j)) :=
    Finset.mem_filter.mpr ⟨hi, Ne.symm h, hlen⟩
  have hnfar : μ j ∉ farJset μ ν a b m (grp a μ b ν m (ν i)) := by
    intro hh
    exact (not_le.mpr hlen) (Finset.mem_filter.mp hh).2.2
  have heq : Rmat μ ν f a b m j i = ddVal f (ν i) (μ j) * a j * b i -
      (f (ν i) - f (μ j)) * a j * b i /
        ((ν i - gctr a μ b ν m (grp a μ b ν m (μ j)) : ℝ) : ℂ) := by
    have hs : ddVal f (μ j) (ν i) = ddVal f (ν i) (μ j) :=
      ddMat_apply_swap μ ν f j i
    simp only [Rmat, Hmat, Hrows, Hcols, Matrix.sub_apply, Matrix.add_apply,
      Matrix.of_apply, Lfar_apply a b m j i, hj, hi, hfar, hnfar, true_and,
      not_true_eq_false, and_false, false_and, if_false, if_true,
      ddMat_apply_eq_ddVal, Matrix.hadamard_apply, Matrix.vecMulVec_apply, hs]
    ring
  rw [heq]
  exact dd_residual_normSq_le (a j) (b i)
    (fun heq => h (congrArg (grp a μ b ν m) heq.symm))
    (ne_ctr_of_grp_ne a b m hk hi (Ne.symm h)) hL
    (hf _ (Or.inr ⟨i, rfl⟩) _ (Or.inl ⟨j, rfl⟩))
    (abs_sub_ctr_le a μ b ν m hk hgroup)
    (ge_ρ_of_grp_ne a μ b ν m hk hi (Ne.symm h))

omit [DecidableEq J] in

/-- A weighted sum over rows with eigenvalues in `F` can be regrouped by distinct eigenvalues
using the left fiber masses. -/
theorem sum_rows_weighted (F : Finset ℝ) (g : ℝ → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j => μ j ∈ F), ‖a j‖ ^ 2 * g (μ j) =
      ∑ t ∈ (Finset.univ.image μ).filter (· ∈ F), fibα a μ t * g t := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun j => μ j ∈ F))
    (t := (Finset.univ.image μ).filter (· ∈ F)) (g := μ)
    (fun j hj => Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, (Finset.mem_filter.mp hj).2⟩)
    (fun j => ‖a j‖ ^ 2 * g (μ j))
  refine h.symm.trans ?_
  apply Finset.sum_congr rfl
  intro t ht
  have htF := (Finset.mem_filter.mp ht).2
  rw [fibα, Finset.sum_mul]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hj
      exact ⟨hj ▸ htF, hj⟩
  · intro j hj
    rw [(Finset.mem_filter.mp hj).2]

omit [DecidableEq I] in

/-- A weighted sum over columns with eigenvalues in `F` can be regrouped by distinct eigenvalues
using the right fiber masses. -/
theorem sum_cols_weighted (F : Finset ℝ) (g : ℝ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => ν i ∈ F), ‖b i‖ ^ 2 * g (ν i) =
      ∑ t ∈ (Finset.univ.image ν).filter (· ∈ F), fibβ b ν t * g t := by
  exact sum_rows_weighted (μ := ν) b F g

omit [DecidableEq J] [DecidableEq I] in

/-- The right fiber mass over `farIset`, weighted by the truncated inverse-square decay factor,
is at most 80 / (3m) times the total right mass. -/
theorem decay_sum_le_β (_hm : 0 < m) (_hA : 0 < ∑ j, ‖a j‖ ^ 2) (_hB : 0 < ∑ i, ‖b i‖ ^ 2)
    (k : ℕ) (hk : (groupVals a μ b ν m k).Nonempty) (hρ : 0 < gρ a μ b ν m k) :
    ∑ t ∈ farIset μ ν a b m k,
      fibβ b ν t * min 1 ((gρ a μ b ν m k) ^ 2 / (t - gctr a μ b ν m k) ^ 2) ≤
      (80 / 3) * (∑ i, ‖b i‖ ^ 2) / m := by
  have hk' : (groupVals b ν a μ m k).Nonempty := by
    simpa only [groupVals_symm a b m] using hk
  have hρ' : 0 < gρ b ν a μ m k := by simpa only [gρ_symm a b m] using hρ
  have h := decay_sum_le b ν a μ m k hk' hρ'
  simp only [lightSet_symm a b m, grp_symm a b m, glen_symm a b m,
    gρ_symm a b m, gctr_symm a b m, fibα] at h
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_)
    (fun t _ _ => mul_nonneg (fibβ_nonneg b ν t)
      (le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _))))).trans h
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1,
    (Finset.mem_filter.mp ht).2.1, (Finset.mem_filter.mp ht).2.2.le⟩

end entries
end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators Matrix.Norms.L2Operator

section assembly
variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {μ : J → ℝ} {ν : I → ℝ} {f : ℝ → ℂ} (a : J → ℂ) (b : I → ℂ) {L : ℝ}

omit [DecidableEq J] in

/-- A bound on a nonnegative weighted sum of left fiber masses also bounds the corresponding
conditional sum over rows. -/
private theorem weighted_rows_le (F : Finset ℝ) (g : ℝ → ℝ) (hg : ∀ t ∈ F, 0 ≤ g t)
    {C : ℝ} (h : ∑ t ∈ F, fibα a μ t * g t ≤ C) :
    (∑ j, if μ j ∈ F then ‖a j‖ ^ 2 * g (μ j) else 0) ≤ C := by
  rw [← Finset.sum_filter]
  rw [sum_rows_weighted a F g]
  refine (Finset.sum_le_sum_of_subset_of_nonneg
    (fun t ht => (Finset.mem_filter.mp ht).2)
    (fun t ht _ => mul_nonneg (fibα_nonneg a μ t) (hg t ht))).trans h

omit [DecidableEq I] in

/-- A bound on a nonnegative weighted sum of right fiber masses also bounds the corresponding
conditional sum over columns. -/
private theorem weighted_cols_le (F : Finset ℝ) (g : ℝ → ℝ) (hg : ∀ t ∈ F, 0 ≤ g t)
    {C : ℝ} (h : ∑ t ∈ F, fibβ b ν t * g t ≤ C) :
    (∑ i, if ν i ∈ F then ‖b i‖ ^ 2 * g (ν i) else 0) ≤ C :=
  weighted_rows_le (μ := ν) b F g hg h

omit [DecidableEq J] [DecidableEq I] in

/-- The squared Frobenius norm of the weighted divided difference matrix is at most L² times the
product of the total coefficient masses. -/
theorem frobT_sq_le (hL : 0 ≤ L) (hf : lipUnion μ ν f L) :
    spectralFrobenius (ddMat μ ν f ⊙ Matrix.vecMulVec a b) ^ 2 ≤
      L ^ 2 * (∑ j, ‖a j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
  rw [spectralFrobenius_sq]
  calc (∑ j, ∑ i, Complex.normSq ((ddMat μ ν f ⊙ Matrix.vecMulVec a b) j i))
      ≤ ∑ j, ∑ i, L ^ 2 * ‖a j‖ ^ 2 * ‖b i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        simp only [Matrix.hadamard_apply, Matrix.vecMulVec_apply,
          Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
        nlinarith [pow_le_pow_left₀ (norm_nonneg _) (ddMat_entry_norm_le hL hf j i) 2,
          sq_nonneg ‖a j‖, sq_nonneg ‖b i‖,
          mul_nonneg (sq_nonneg ‖a j‖) (sq_nonneg ‖b i‖)]
    _ = L ^ 2 * (∑ j, ‖a j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]

omit [DecidableEq J] [DecidableEq I] in

/-- For positive `m` and total masses, the squared Frobenius norm of the residual is at most 172
/ (3m) times L² and the product of those masses. -/
theorem frobR_sq_le (hL : 0 ≤ L) (hf : lipUnion μ ν f L) (m : ℕ) (hm : 0 < m)
    (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2) :
    spectralFrobenius (Rmat μ ν f a b m) ^ 2 ≤
      (172 / 3) * L ^ 2 * (∑ j, ‖a j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) / m := by
  classical
  let d (k : ℕ) (t : ℝ) := min 1 (gρ a μ b ν m k ^ 2 / (t - gctr a μ b ν m k) ^ 2)
  have hd : ∀ k t, 0 ≤ d k t := fun k t =>
    le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _))
  let N : Matrix J I ℝ := fun j i => if μ j ∈ lightSet a μ b ν m ∧
      ν i ∈ groupVals a μ b ν m (grp a μ b ν m (μ j)) then
      L ^ 2 * ‖a j‖ ^ 2 * ‖b i‖ ^ 2 else 0
  let FJ : Matrix J I ℝ := fun j i => if ν i ∈ lightSet a μ b ν m ∧
      μ j ∈ farJset μ ν a b m (grp a μ b ν m (ν i)) then
      L ^ 2 * ‖b i‖ ^ 2 * (‖a j‖ ^ 2 * d (grp a μ b ν m (ν i)) (μ j)) else 0
  let FI : Matrix J I ℝ := fun j i => if μ j ∈ lightSet a μ b ν m ∧
      ν i ∈ farIset μ ν a b m (grp a μ b ν m (μ j)) then
      L ^ 2 * ‖a j‖ ^ 2 * (‖b i‖ ^ 2 * d (grp a μ b ν m (μ j)) (ν i)) else 0
  have hpoint : ∀ j i, Complex.normSq (Rmat μ ν f a b m j i) ≤ N j i + FJ j i + FI j i := by
    intro j i
    by_cases hj : μ j ∈ lightSet a μ b ν m
    · by_cases hi : ν i ∈ lightSet a μ b ν m
      · by_cases h : grp a μ b ν m (μ j) = grp a μ b ν m (ν i)
        · simpa [N, FJ, FI, hj, hi, groupVals, farJset, farIset, h, mul_assoc] using
            Rmat_diag_bound a b m hL hf hj hi h
        · by_cases hlen : glen a μ b ν m (grp a μ b ν m (ν i)) ≤ glen a μ b ν m (grp a μ b ν m (μ j))
          · have hh := Rmat_caseJ_bound a b m hL hf hj hi h hlen
            simpa [N, FJ, FI, d, hj, hi, groupVals, farJset, farIset, h, Ne.symm h,
              hlen, not_lt.mpr hlen, mul_assoc, mul_left_comm, mul_comm] using hh
          · have hh := Rmat_caseI_bound a b m hL hf hj hi h (lt_of_not_ge hlen)
            simpa [N, FJ, FI, d, hj, hi, groupVals, farJset, farIset, h, Ne.symm h,
              hlen, lt_of_not_ge hlen, mul_assoc] using hh
      · rw [Rmat_eq_zero_of_not_light_col a b m hj hi, Complex.normSq_zero]
        simp [N, FJ, FI, hj, hi, groupVals, farIset]
    · rw [Rmat_eq_zero_of_not_light_row a b m hj i, Complex.normSq_zero]
      simp [N, FJ, FI, hj, farJset]
  have hN : (∑ j, ∑ i, N j i) ≤ L ^ 2 * (∑ j, ‖a j‖ ^ 2) * ((4 / m) * ∑ i, ‖b i‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : μ j ∈ lightSet a μ b ν m
    · have hmass := weighted_cols_le b (groupVals a μ b ν m (grp a μ b ν m (μ j)))
        (fun _ => 1) (fun _ _ => zero_le_one)
        (by simpa using group_fibβ_le a μ b ν m hA hB (grp a μ b ν m (μ j)))
      have heq : (∑ i, N j i) = L ^ 2 * ‖a j‖ ^ 2 *
          (∑ i, if ν i ∈ groupVals a μ b ν m (grp a μ b ν m (μ j)) then ‖b i‖ ^ 2 * 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : ν i ∈ groupVals a μ b ν m (grp a μ b ν m (μ j)) <;> simp [N, hj, hi]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    · simp only [N, hj, false_and, if_false, Finset.sum_const_zero]
      positivity
  have hFJ : (∑ j, ∑ i, FJ j i) ≤ L ^ 2 * (∑ i, ‖b i‖ ^ 2) * ((80 / 3) * (∑ j, ‖a j‖ ^ 2) / m) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : ν i ∈ lightSet a μ b ν m
    · let k := grp a μ b ν m (ν i)
      have hk : (groupVals a μ b ν m k).Nonempty := ⟨ν i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
      have hdec : (∑ t ∈ farJset μ ν a b m k, fibα a μ t * d k t) ≤ (80 / 3) * (∑ j, ‖a j‖ ^ 2) / m := by
        by_cases hρ : 0 < gρ a μ b ν m k
        · exact decay_sum_le a μ b ν m k hk hρ
        · have hzero : gρ a μ b ν m k = 0 := le_antisymm (le_of_not_gt hρ) (gρ_nonneg a μ b ν m hk)
          simp only [d, hzero, zero_pow (by norm_num : 2 ≠ 0), zero_div, min_eq_right zero_le_one,
            mul_zero, Finset.sum_const_zero]
          positivity
      have hmass := weighted_rows_le a (farJset μ ν a b m k) (d k) (fun t _ => hd k t) hdec
      have heq : (∑ j, FJ j i) = L ^ 2 * ‖b i‖ ^ 2 *
          (∑ j, if μ j ∈ farJset μ ν a b m k then ‖a j‖ ^ 2 * d k (μ j) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : μ j ∈ farJset μ ν a b m k <;> simp [FJ, hi, k, hj]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    · simp only [FJ, hi, false_and, if_false, Finset.sum_const_zero]
      positivity
  have hFI : (∑ j, ∑ i, FI j i) ≤ L ^ 2 * (∑ j, ‖a j‖ ^ 2) * ((80 / 3) * (∑ i, ‖b i‖ ^ 2) / m) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : μ j ∈ lightSet a μ b ν m
    · let k := grp a μ b ν m (μ j)
      have hk : (groupVals a μ b ν m k).Nonempty := ⟨μ j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩
      have hdec : (∑ t ∈ farIset μ ν a b m k, fibβ b ν t * d k t) ≤ (80 / 3) * (∑ i, ‖b i‖ ^ 2) / m := by
        by_cases hρ : 0 < gρ a μ b ν m k
        · exact decay_sum_le_β a b m hm hA hB k hk hρ
        · have hzero : gρ a μ b ν m k = 0 := le_antisymm (le_of_not_gt hρ) (gρ_nonneg a μ b ν m hk)
          simp only [d, hzero, zero_pow (by norm_num : 2 ≠ 0), zero_div, min_eq_right zero_le_one,
            mul_zero, Finset.sum_const_zero]
          positivity
      have hmass := weighted_cols_le b (farIset μ ν a b m k) (d k) (fun t _ => hd k t) hdec
      have heq : (∑ i, FI j i) = L ^ 2 * ‖a j‖ ^ 2 *
          (∑ i, if ν i ∈ farIset μ ν a b m k then ‖b i‖ ^ 2 * d k (ν i) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : ν i ∈ farIset μ ν a b m k <;> simp [FI, hj, k, hi]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    · simp only [FI, hj, false_and, if_false, Finset.sum_const_zero]
      positivity
  rw [spectralFrobenius_sq]
  calc (∑ j, ∑ i, Complex.normSq (Rmat μ ν f a b m j i))
      ≤ ∑ j, ∑ i, (N j i + FJ j i + FI j i) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hpoint j i
    _ = (∑ j, ∑ i, N j i) + (∑ j, ∑ i, FJ j i) + (∑ j, ∑ i, FI j i) := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ L ^ 2 * (∑ j, ‖a j‖ ^ 2) * ((4 / m) * ∑ i, ‖b i‖ ^ 2) +
        L ^ 2 * (∑ i, ‖b i‖ ^ 2) * ((80 / 3) * (∑ j, ‖a j‖ ^ 2) / m) +
        L ^ 2 * (∑ j, ‖a j‖ ^ 2) * ((80 / 3) * (∑ i, ‖b i‖ ^ 2) / m) :=
      add_le_add (add_le_add hN hFJ) hFI
    _ = (172 / 3) * L ^ 2 * (∑ j, ‖a j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) / m := by ring

/-- The singular value of the weighted divided difference matrix at index 9m + 4 is at most
sqrt(172 / 3) times the Lipschitz constant and the coefficient norm product, divided by `m`. -/
theorem sv_bound_main (hL : 0 ≤ L) (hf : lipUnion μ ν f L) (m : ℕ) (hm : 0 < m)
    (hA : 0 < ∑ j, ‖a j‖ ^ 2) (hB : 0 < ∑ i, ‖b i‖ ^ 2) :
    matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) (9 * m + 4) ≤
      Real.sqrt (172 / 3) * L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) / m := by
  let T := ddMat μ ν f ⊙ Matrix.vecMulVec a b
  let H := Hmat μ ν f a b m
  let R := Rmat μ ν f a b m
  have hdecomp : T = H + R := by unfold T H R Rmat; abel
  have hrank : H.rank ≤ 8 * m + 4 := Hmat_rank_le a b m hm hA hB
  have hweyl := matrixSingularValues_add_le H R (8 * m + 4) m
  have hzero := matrixSingularValues_eq_zero_of_rank_le (X := H) hrank
  rw [hzero, zero_add, ← hdecomp, show 8 * m + 4 + m = 9 * m + 4 by omega] at hweyl
  refine hweyl.trans ?_
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hs := matrixSingularValues_sq_mul_le_spectralFrobenius_sq R m
  have hfrob := frobR_sq_le a b hL hf m hm hA hB
  have hs2 : (m : ℝ) ^ 2 * matrixSingularValues R m ^ 2 ≤
      (172 / 3) * L ^ 2 * (∑ j, ‖a j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
    calc (m : ℝ) ^ 2 * matrixSingularValues R m ^ 2
        ≤ (m : ℝ) * (((m + 1 : ℕ) : ℝ) * matrixSingularValues R m ^ 2) := by
          push_cast
          nlinarith [mul_nonneg hmR.le (sq_nonneg (matrixSingularValues R m))]
      _ ≤ (m : ℝ) * spectralFrobenius R ^ 2 := mul_le_mul_of_nonneg_left hs hmR.le
      _ ≤ (m : ℝ) * ((172 / 3) * L ^ 2 * (∑ j, ‖a j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) / m) :=
          mul_le_mul_of_nonneg_left hfrob hmR.le
      _ = _ := by field_simp
  rw [le_div_iff₀ hmR]
  apply (sq_le_sq₀ (mul_nonneg (matrixSingularValues_nonneg _ _) hmR.le)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).mp
  rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 172 / 3),
    Real.sq_sqrt hA.le, Real.sq_sqrt hB.le, mul_comm (matrixSingularValues R m ^ 2) ((m : ℝ) ^ 2)]
  simpa only [mul_assoc] using hs2

end assembly
end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Partition
open scoped Classical BigOperators Matrix.Norms.L2Operator

section finalH1

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {μ : J → ℝ} {ν : I → ℝ} {f : ℝ → ℂ} {L : ℝ}

omit [DecidableEq J] [DecidableEq I] in

/-- The expression giving the reciprocal singular value bound with constant 144 is nonnegative
when `L` is nonnegative. -/
theorem h1_rhs_nonneg (hL : 0 ≤ L) (a : J → ℂ) (b : I → ℂ) (q : ℕ) :
    0 ≤ 144 * L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) / ((q : ℝ) + 1) := by
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hq.le

/-- The singular value at index `q` of a divided difference matrix weighted by an outer product
is at most 144L times the coefficient norm product divided by q + 1. -/
theorem ddMat_hadamard_vecMulVec_sv_bound (hL : 0 ≤ L) (hf : lipUnion μ ν f L)
    (a : J → ℂ) (b : I → ℂ) (q : ℕ) :
    matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q ≤
      144 * L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) / ((q : ℝ) + 1) := by
  by_cases hA : (∑ j, ‖a j‖ ^ 2) = 0
  · have ha0 : ∀ j, a j = 0 := by
      intro j
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (‖a i‖))).mp hA
        j (Finset.mem_univ j)
      rwa [sq_eq_zero_iff, norm_eq_zero] at h
    have hT : ddMat μ ν f ⊙ Matrix.vecMulVec a b = 0 := by
      ext j i
      simp [Matrix.hadamard_apply, Matrix.vecMulVec_apply, ha0 j]
    rw [hT, show matrixSingularValues (0 : Matrix J I ℂ) q = 0 from
      matrixSingularValues_eq_zero_of_rank_le (X := (0 : Matrix J I ℂ)) (by simp [Matrix.rank_zero])]
    exact h1_rhs_nonneg hL a b q
  · by_cases hB : (∑ i, ‖b i‖ ^ 2) = 0
    · have hb0 : ∀ i, b i = 0 := by
        intro i
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (‖b k‖))).mp hB
          i (Finset.mem_univ i)
        rwa [sq_eq_zero_iff, norm_eq_zero] at h
      have hT : ddMat μ ν f ⊙ Matrix.vecMulVec a b = 0 := by
        ext j i
        simp [Matrix.hadamard_apply, Matrix.vecMulVec_apply, hb0 i]
      rw [hT, show matrixSingularValues (0 : Matrix J I ℂ) q = 0 from
        matrixSingularValues_eq_zero_of_rank_le (X := (0 : Matrix J I ℂ)) (by simp [Matrix.rank_zero])]
      exact h1_rhs_nonneg hL a b q
    · have hA' : 0 < ∑ j, ‖a j‖ ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg _) (Ne.symm hA)
      have hB' : 0 < ∑ i, ‖b i‖ ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hB)
      by_cases hq : q ≤ 26
      · have hq1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
          have h : 1 ≤ q + 1 := Nat.succ_pos q
          exact_mod_cast h
        have hsq : (matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q) ^ 2 ≤
            spectralFrobenius (ddMat μ ν f ⊙ Matrix.vecMulVec a b) ^ 2 := by
          have h := matrixSingularValues_sq_mul_le_spectralFrobenius_sq
            (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q
          have h1 : (matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q) ^ 2 ≤
              ((q + 1 : ℕ) : ℝ) *
                (matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q) ^ 2 := by
            have := mul_le_mul_of_nonneg_right hq1
              (sq_nonneg (matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q))
            rwa [one_mul] at this
          exact h1.trans h
        have hfrob : spectralFrobenius (ddMat μ ν f ⊙ Matrix.vecMulVec a b) ≤
            L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) := by
          have h2 := frobT_sq_le a b hL hf
          have h3 : spectralFrobenius (ddMat μ ν f ⊙ Matrix.vecMulVec a b) ≤
              Real.sqrt ((L ^ 2 * (∑ j, ‖a j‖ ^ 2)) * (∑ i, ‖b i‖ ^ 2)) :=
            (Real.le_sqrt (spectralFrobenius_nonneg _)
              (mul_nonneg (mul_nonneg (sq_nonneg L) hA'.le) hB'.le)).mpr h2
          rw [Real.sqrt_mul (mul_nonneg (sq_nonneg L) hA'.le), Real.sqrt_mul (sq_nonneg L),
            Real.sqrt_sq hL, mul_assoc] at h3
          exact h3
        have hmono := (sq_le_sq₀ (matrixSingularValues_nonneg _ _)
          (spectralFrobenius_nonneg _)).mp hsq
        have hbound : matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q ≤
            L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) :=
          hmono.trans hfrob
        have hq144 : ((q : ℝ) + 1) ≤ 144 := by
          have : q + 1 ≤ 144 := by omega
          exact_mod_cast this
        have hX : 0 ≤ L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) :=
          mul_nonneg hL (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        have hq0 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
        calc matrixSingularValues (ddMat μ ν f ⊙ Matrix.vecMulVec a b) q
            ≤ L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) := hbound
          _ ≤ 144 * L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) /
              ((q : ℝ) + 1) := by
              rw [le_div_iff₀ hq0]
              have hstep : L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) *
                  ((q : ℝ) + 1) ≤
                  L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) * 144 :=
                mul_le_mul_of_nonneg_left hq144 hX
              linarith [hstep]
      · push Not at hq
        set m := (q - 4) / 9 with hmdef
        have hm0 : 0 < m := by
          have h2 : 2 ≤ m := by
            rw [hmdef]
            exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 9)).mpr (by omega)
          omega
        have h9m : 9 * m + 4 ≤ q := by
          have h := Nat.div_mul_le_self (q - 4) 9
          rw [← hmdef] at h
          omega
        have hm9 : q - 12 ≤ 9 * m := by
          have h := Nat.div_add_mod (q - 4) 9
          have hmod : (q - 4) % 9 ≤ 8 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
          rw [← hmdef] at h
          omega
        have hmono := matrixSingularValues_anti (X := ddMat μ ν f ⊙ Matrix.vecMulVec a b) h9m
        refine hmono.trans ?_
        have hmain := sv_bound_main a b hL hf m hm0 hA' hB'
        refine hmain.trans ?_
        have hX : 0 ≤ L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) :=
          mul_nonneg hL (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
        have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
        rw [div_le_div_iff₀ hmR hq1]

        have hcoef : Real.sqrt (172 / 3 : ℝ) * ((q : ℝ) + 1) ≤ 144 * m := by
          have hsqrt8 : Real.sqrt (172 / 3 : ℝ) ≤ 8 := by
            rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
          have hmge : ((q : ℝ) + 1) ≤ 18 * (m : ℝ) := by
            have hcast : ((q - 12 : ℕ) : ℝ) ≤ ((9 * m : ℕ) : ℝ) := by exact_mod_cast hm9
            rw [Nat.cast_sub (by omega : 12 ≤ q), Nat.cast_mul, Nat.cast_ofNat] at hcast
            push_cast at hcast
            have hq25 : (25 : ℝ) ≤ q := by
              have h : (25 : ℕ) ≤ q := by omega
              exact_mod_cast h
            linarith [hcast]
          calc Real.sqrt (172 / 3 : ℝ) * ((q : ℝ) + 1) ≤ Real.sqrt (172 / 3 : ℝ) * (18 * (m : ℝ)) :=
                mul_le_mul_of_nonneg_left hmge (Real.sqrt_nonneg _)
            _ ≤ 8 * (18 * (m : ℝ)) :=
                mul_le_mul_of_nonneg_right hsqrt8 (by positivity)
            _ = 144 * (m : ℝ) := by ring
        calc Real.sqrt (172 / 3) * L *
                (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) * ((q : ℝ) + 1)
            = (L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2))) *
                (Real.sqrt (172 / 3 : ℝ) * ((q : ℝ) + 1)) := by ring
          _ ≤ (L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2))) * (144 * (m : ℝ)) :=
              mul_le_mul_of_nonneg_left hcoef hX
          _ = 144 * L * (Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2)) * (m : ℝ) := by
              ring

end finalH1

end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Decomposition

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Transport
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Analysis
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The Hermitian spectral Lipschitz condition implies `lipUnion` for the ordered eigenvalue
families. -/
theorem lipUnion_of_hermitianPairScalarLipschitz {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {A : Matrix I I ℂ} {hA : A.IsHermitian}
    {B : Matrix J J ℂ} {hB : B.IsHermitian} {f : ℝ → ℂ} {L : ℝ}
    (hf : hermitianPairScalarLipschitz A hA B hB f L) :
    lipUnion (orderedHermitianValues hA) (orderedHermitianValues hB) f L :=
  hf

/-- In the ordered eigenbases, the functional calculus quasicommutator is the Hadamard product
of the divided difference matrix and the original quasicommutator. -/
theorem coordinates_quasicommutator_eq_ddMat_hadamard {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
    (S : Matrix I J ℂ) (f : ℝ → ℂ) :
    (basisColumns (orderedHermitianBasis hA))ᴴ *
        (hermitianFunction A hA f*S-S*hermitianFunction B hB f) *
        basisColumns (orderedHermitianBasis hB) =
      ddMat (orderedHermitianValues hA) (orderedHermitianValues hB) f ⊙
        ((basisColumns (orderedHermitianBasis hA))ᴴ*(A*S-S*B)*
          basisColumns (orderedHermitianBasis hB)) := by
  ext i j
  simp only [Matrix.hadamard_apply, ddMat, Matrix.of_apply]
  exact hermitianFunction_quasicommutator_divided_difference A hA B hB S f i j

/-- A logarithmic Schur multiplier bound yields a universal positive constant for a
quasicommutator estimate weighted by the left matrix rank. -/
theorem clause1_of_schurBound {c : ℝ} (hc : 0 < c)
    (H2 : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (eigL : I → ℝ) (eigR : J → ℝ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
      lipUnion eigL eigR f L → ∀ K : Matrix I J ℂ,
        ‖ddMat eigL eigR f ⊙ K‖ ≤
          c * (1 + Real.log ((Finset.univ.image eigL).card : ℝ)) * L * ‖K‖) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
        (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
        (S : Matrix I J ℂ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
        hermitianPairScalarLipschitz A hA B hB f L →
        ‖hermitianFunction A hA f * S - S * hermitianFunction B hB f‖ ≤
          c₀ * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖ := by
  refine ⟨c, hc, ?_⟩
  intro I J _ _ _ _ A hA B hB S f L hL hf
  let UA := basisColumns (orderedHermitianBasis hA)
  let UB := basisColumns (orderedHermitianBasis hB)
  have hcoord := coordinates_quasicommutator_eq_ddMat_hadamard A hA B hB S f
  have hK : ‖UAᴴ*(A*S-S*B)*UB‖ = ‖A*S-S*B‖ :=
    hermitian_pair_coordinates_norm A hA B hB (A*S-S*B)
  have hX : ‖UAᴴ*(hermitianFunction A hA f*S-S*hermitianFunction B hB f)*UB‖ =
      ‖hermitianFunction A hA f*S-S*hermitianFunction B hB f‖ :=
    hermitian_pair_coordinates_norm A hA B hB _
  have hrec : UA*(UAᴴ*(hermitianFunction A hA f*S-S*hermitianFunction B hB f)*UB)*UBᴴ =
      hermitianFunction A hA f*S-S*hermitianFunction B hB f := by
    dsimp [UA, UB]
    simp only [← Matrix.mul_assoc, basisColumns_mul_adjoint, Matrix.one_mul]
    simp only [Matrix.mul_assoc, basisColumns_mul_adjoint, Matrix.mul_one]
  have hmain := H2 (Fin (Fintype.card I)) (Fin (Fintype.card J))
    (orderedHermitianValues hA) (orderedHermitianValues hB) f L hL
    (lipUnion_of_hermitianPairScalarLipschitz hf) (UAᴴ*(A*S-S*B)*UB)
  rw [← hX, hcoord]
  calc ‖ddMat (orderedHermitianValues hA) (orderedHermitianValues hB) f ⊙
          (UAᴴ*(A*S-S*B)*UB)‖
      ≤ c * (1 + Real.log ((Finset.univ.image (orderedHermitianValues hA)).card : ℝ)) * L *
          ‖UAᴴ*(A*S-S*B)*UB‖ := hmain
    _ ≤ c * hermitianRankLogWeight A.rank * L * ‖A*S-S*B‖ := by
        rw [hK]
        have hlog := orderedHermitian_log_spectrum_card_le A hA
        have h0 : 0 ≤ c * L * ‖A*S-S*B‖ :=
          mul_nonneg (mul_nonneg hc.le hL) (norm_nonneg _)
        calc c * (1 + Real.log ((Finset.univ.image (orderedHermitianValues hA)).card : ℝ)) * L *
              ‖A*S-S*B‖
            = (c * L * ‖A*S-S*B‖) * (1 + Real.log ((Finset.univ.image
              (orderedHermitianValues hA)).card : ℝ)) := by ring
          _ ≤ (c * L * ‖A*S-S*B‖) * hermitianRankLogWeight A.rank :=
              mul_le_mul_of_nonneg_left hlog h0
          _ = c * hermitianRankLogWeight A.rank * L * ‖A*S-S*B‖ := by ring

/-- A universal rectangular quasicommutator estimate yields an operator perturbation estimate
weighted by the smaller of the two ranks. -/
theorem clause2_of_clause1_square
    (hg1 : ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
        (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
        (S : Matrix I J ℂ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
        hermitianPairScalarLipschitz A hA B hB f L →
        ‖hermitianFunction A hA f * S - S * hermitianFunction B hB f‖ ≤
          c₀ * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
        (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
        hermitianPairScalarLipschitz A hA B hB f L →
        ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
          c₀ * hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ := by
  obtain ⟨c₀, hc₀, hg1'⟩ := hg1
  exact ⟨c₀, hc₀, hermitianFunction_min_rank_stability_of_quasicommutator_bound c₀
    (fun I _ _ A hA B hB S f L hL hf => hg1' I I A hA B hB S f L hL hf)⟩
end Qatlib.Concepts.SketchSpectral.MatrixFunctions.RankLogStability.Transport

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- There is a universal positive constant bounding the functional calculus quasicommutator by
the original quasicommutator norm times the spectral Lipschitz constant and the logarithmic
left-rank weight. See [ChiaEtAl2022]. -/
theorem hermitianFunction_operator_rank_quasicommutator :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
        (A : Matrix I I ℂ) (hA : A.IsHermitian) (B : Matrix J J ℂ) (hB : B.IsHermitian)
        (S : Matrix I J ℂ) (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
        hermitianPairScalarLipschitz A hA B hB f L →
        ‖hermitianFunction A hA f * S - S * hermitianFunction B hB f‖ ≤
          c₀ * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖ :=
  RankLogStability.Transport.clause1_of_schurBound (c := 144) (by norm_num)
    (RankLogStability.Analysis.schurBound_of_weakSchatten (c₁ := 144) (by norm_num)
      (fun J I _ _ _ _ μ ν f L hL hf a b q =>
        RankLogStability.Decomposition.ddMat_hadamard_vecMulVec_sv_bound hL hf a b q))

/-- There is a universal positive constant bounding the operator norm of f(A) - f(B) by the norm
of A - B times the spectral Lipschitz constant and the logarithmic weight of the smaller
rank. See [ChiaEtAl2022]. -/
theorem hermitianFunction_operator_min_rank_stability :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
        (f : ℝ → ℂ) (L : ℝ), 0 ≤ L →
        hermitianPairScalarLipschitz A hA B hB f L →
        ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
          c₀ * hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ :=
  RankLogStability.Transport.clause2_of_clause1_square hermitianFunction_operator_rank_quasicommutator

end Qatlib.Concepts.SketchSpectral.MatrixFunctions
