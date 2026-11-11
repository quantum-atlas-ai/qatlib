/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.ContinuousModulusGridSchur
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreRefined

/-!
# Spectral quantization and continuous functional calculus

This module quantizes the spectra of Hermitian contractions on a uniform grid and compares their
functional-calculus responses through divided differences. `coarseOperator` and `coarseResponse`
retain an eigenbasis while replacing eigenvalues by lower grid points.

The estimates culminate in `th20_main`, proving the logarithmic modulus-of-continuity bound
packaged as `Th20MainBound` in the setting of [GilyenSuLowWiebe2019].

## Main statements

* `coarse_response_distance`: bounds the quantized response difference by a grid harmonic
  factor.
* `hermitian_modulus_grid_bound`: bounds the original response difference using the grid size.
* `th20_main`: establishes the bound with `modulusRobustnessFactor`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord Matrix
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false
variable {I J K : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- Every ordered eigenvalue of a Hermitian contraction lies in [-1, 1]. -/
theorem contraction_spectrum {A : Matrix I I ℂ} (hA : A.IsHermitian) (hn : ‖A‖ ≤ 1)
    (i : Fin (Fintype.card I)) : orderedHermitianValues hA i ∈ Set.Icc (-1:ℝ) 1 := by
  have hv := Matrix.l2_opNorm_mulVec A (orderedHermitianBasis hA i)
  change ‖A.toEuclideanLin (orderedHermitianBasis hA i)‖ ≤
    ‖A‖*‖orderedHermitianBasis hA i‖ at hv
  rw [orderedHermitianBasis_action,norm_smul,(orderedHermitianBasis hA).norm_eq_one,
    mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs] at hv
  exact abs_le.mp (hv.trans hn)

omit [DecidableEq I] in

/-- In the row and column eigenbases, an entry of the difference of two spectral diagonal
operators is the difference of their spectral coefficients times the corresponding
basis-overlap entry. -/
theorem cross_coordinates
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (c : OrthonormalBasis K ℂ (EuclideanSpace ℂ I)) (f : J → ℂ) (g : K → ℂ)
    (i : J) (j : K) :
    ((basisColumns b)ᴴ*(spectralDiagonal b f-spectralDiagonal c g)*basisColumns c) i j =
      (f i-g j)*((basisColumns b)ᴴ*basisColumns c) i j := by
  have hm : (basisColumns b)ᴴ*(spectralDiagonal b f-spectralDiagonal c g)*basisColumns c =
      diagonal f*((basisColumns b)ᴴ*basisColumns c)-
      ((basisColumns b)ᴴ*basisColumns c)*diagonal g := by
    rw [Matrix.mul_sub,Matrix.sub_mul,basis_adjoint_mul_spectralDiagonal]
    rw [Matrix.mul_assoc (diagonal f),Matrix.mul_assoc (basisColumns b)ᴴ,
      spectralDiagonal_mul_basis,← Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  rw [hm,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

/-- Changing the row and column coordinates by orthonormal bases preserves the operator norm of
a square matrix. -/
theorem basis_coordinates_norm
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (c : OrthonormalBasis K ℂ (EuclideanSpace ℂ I)) (S : Matrix I I ℂ) :
    ‖(basisColumns b)ᴴ*S*basisColumns c‖ = ‖S‖ := by
  have bound {M N O P : Type} [Fintype M] [DecidableEq M]
      [Fintype N] [DecidableEq N] [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P]
      (X : Matrix M N ℂ) (Y : Matrix N O ℂ) (Z : Matrix O P ℂ)
      (hX : ‖X‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) : ‖X*Y*Z‖ ≤ ‖Y‖ := by
    calc
      _ ≤ (‖X‖*‖Y‖)*‖Z‖ := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1*‖Y‖)*1 := by gcongr
      _ = _ := by ring
  have hb := basisColumns_norm_le b
  have hc := basisColumns_norm_le c
  have hb' : ‖(basisColumns b)ᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have hc' : ‖(basisColumns c)ᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  apply le_antisymm (bound _ _ _ hb' hc)
  have he : basisColumns b*((basisColumns b)ᴴ*S*basisColumns c)*(basisColumns c)ᴴ = S := by
    simp only [← Matrix.mul_assoc,basisColumns_mul_adjoint,Matrix.one_mul]
    simp only [Matrix.mul_assoc,basisColumns_mul_adjoint,Matrix.mul_one]
  calc
    ‖S‖ = ‖basisColumns b*((basisColumns b)ᴴ*S*basisColumns c)*(basisColumns c)ᴴ‖ := congrArg norm he.symm
    _ ≤ ‖(basisColumns b)ᴴ*S*basisColumns c‖ := bound _ _ _ hb hc'

/-- The natural floor of 2/δ, giving the number of full grid intervals across [-1, 1] for
positive spacing δ. -/
def gridSize (δ : ℝ) : ℕ := Nat.floor (2/δ)
/-- The kth grid point -1 + δk. -/
def gridPoint (δ : ℝ) (k : ℕ) : ℝ := -1+δ*k

/-- For positive δ and x in [-1, 1], the natural floor of (x + 1)/δ is at most `gridSize δ`. -/
theorem gridIndex_le (δ : ℝ) (hδ : 0<δ) (x : ℝ) (hx : x∈Set.Icc (-1:ℝ) 1) :
    Nat.floor ((x+1)/δ)≤gridSize δ := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right (by linarith [hx.2]) hδ.le

/-- The finite grid index given by the natural floor of (x + 1)/δ for x in [-1, 1] and δ > 0. -/
def gridIndex (δ : ℝ) (hδ : 0<δ) (x : ℝ) (hx : x∈Set.Icc (-1:ℝ) 1) : Fin (gridSize δ+1) :=
  ⟨Nat.floor ((x+1)/δ),Nat.lt_succ_of_le (gridIndex_le δ hδ x hx)⟩

/-- For δ > 0 and x in [-1, 1], rounding x down to its indexed grid point produces an error in
[0, δ). -/
theorem gridIndex_error (δ : ℝ) (hδ : 0<δ) (x : ℝ) (hx : x∈Set.Icc (-1:ℝ) 1) :
    0≤x-gridPoint δ (gridIndex δ hδ x hx).val ∧
      x-gridPoint δ (gridIndex δ hδ x hx).val<δ := by
  have hq : 0≤(x+1)/δ := div_nonneg (by linarith [hx.1]) hδ.le
  have hlo := (le_div_iff₀ hδ).mp (Nat.floor_le hq)
  have hhi := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((x+1)/δ))
  dsimp [gridPoint,gridIndex]
  constructor <;> nlinarith

/-- Every grid point indexed by `Fin (gridSize δ + 1)` lies in [-1, 1] when δ > 0. -/
theorem gridPoint_mem (δ : ℝ) (hδ : 0<δ) (k : Fin (gridSize δ+1)) :
    gridPoint δ k.val∈Set.Icc (-1:ℝ) 1 := by
  have hn : (gridSize δ:ℝ)≤2/δ := Nat.floor_le (div_nonneg (by norm_num) hδ.le)
  have hk : (k.val:ℝ)≤(gridSize δ:ℝ) := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have hb : δ*(k.val:ℝ)≤2 := by
    apply (mul_le_mul_of_nonneg_left hk hδ.le).trans
    have hh := (le_div_iff₀ hδ).mp hn
    nlinarith
  have hl : 0≤δ*(k.val:ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
  dsimp [gridPoint]
  constructor <;> linarith

/-- The grid has at least one full interval when 0 < δ ≤ 2. -/
theorem gridSize_pos (δ : ℝ) (hδ : 0<δ) (hδ2 : δ≤2) : 0<gridSize δ := by
  by_contra hn
  have he : gridSize δ=0 := by omega
  have hh := Nat.lt_floor_add_one (2/δ)
  change 2/δ<(gridSize δ:ℝ)+1 at hh
  rw [he] at hh
  norm_num at hh
  have hb : 1≤2/δ := (one_le_div₀ hδ).mpr hδ2
  linarith

/-- For a response with modulus of continuity ω, the norm of an increment between consecutive
grid samples is at most ω(δ). -/
theorem grid_f_increment (δ : ℝ) (hδ : 0<δ) (f : ℝ → ℂ) (ω : ℝ → ℝ)
    (hω : ModulusOfContinuity f ω) (k : Fin (gridSize δ)) :
    ‖gridIncrement (gridSize δ) (fun q => f (gridPoint δ q)) k‖≤ω δ := by
  have hh := hω.dominates (gridPoint δ (k.val+1)) (gridPoint δ k.val)
    (gridPoint_mem δ hδ k.succ) (gridPoint_mem δ hδ k.castSucc)
  have he : gridPoint δ (k.val+1)-gridPoint δ k.val=δ := by
    simp only [gridPoint,Nat.cast_add,Nat.cast_one]; ring
  simpa only [gridIncrement,he,abs_of_pos hδ] using! hh

/-- The lower grid index of an ordered eigenvalue of a Hermitian contraction. -/
def quantizationIndex {A : Matrix I I ℂ} (hA : A.IsHermitian) (hA1 : ‖A‖≤1)
    (δ : ℝ) (hδ : 0<δ) (i : Fin (Fintype.card I)) : Fin (gridSize δ+1) :=
  gridIndex δ hδ (orderedHermitianValues hA i) (contraction_spectrum hA hA1 i)

/-- The spectral approximation obtained by replacing each eigenvalue of a Hermitian contraction
with its lower grid point. -/
def coarseOperator {A : Matrix I I ℂ} (hA : A.IsHermitian) (hA1 : ‖A‖≤1)
    (δ : ℝ) (hδ : 0<δ) : Matrix I I ℂ :=
  spectralDiagonal (orderedHermitianBasis hA)
    (fun i => (gridPoint δ (quantizationIndex hA hA1 δ hδ i).val:ℂ))

/-- The spectral operator obtained by evaluating f at the lower grid point of each eigenvalue of
a Hermitian contraction. -/
def coarseResponse {A : Matrix I I ℂ} (hA : A.IsHermitian) (hA1 : ‖A‖≤1)
    (δ : ℝ) (hδ : 0<δ) (f : ℝ → ℂ) : Matrix I I ℂ :=
  spectralDiagonal (orderedHermitianBasis hA)
    (fun i => f (gridPoint δ (quantizationIndex hA hA1 δ hδ i).val))

/-- A Hermitian contraction differs from its coarse grid operator by operator norm at most δ. -/
theorem coarse_operator_error {A : Matrix I I ℂ} (hA : A.IsHermitian) (hA1 : ‖A‖≤1)
    (δ : ℝ) (hδ : 0<δ) : ‖A-coarseOperator hA hA1 δ hδ‖≤δ := by
  calc
    _ = ‖spectralDiagonal (orderedHermitianBasis hA) (fun i => (orderedHermitianValues hA i:ℂ))-
        coarseOperator hA hA1 δ hδ‖ := by rw [← orderedHermitian_diagonal hA]
    _ ≤ _ := by
      apply spectralDiagonal_error_le _ _ _ hδ.le
      intro i
      change ‖(orderedHermitianValues hA i:ℂ)-
        (gridPoint δ (gridIndex δ hδ (orderedHermitianValues hA i) (contraction_spectrum hA hA1 i)).val:ℂ)‖≤δ
      have he := gridIndex_error δ hδ (orderedHermitianValues hA i) (contraction_spectrum hA hA1 i)
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he.1]
      exact he.2.le

/-- For a response with modulus of continuity ω, the functional calculus of a Hermitian
contraction differs from its coarse response by operator norm at most ω(δ). -/
theorem coarse_response_error {A : Matrix I I ℂ} (hA : A.IsHermitian) (hA1 : ‖A‖≤1)
    (δ : ℝ) (hδ : 0<δ) (f : ℝ → ℂ) (ω : ℝ → ℝ) (hω : ModulusOfContinuity f ω) :
    ‖hermitianFunction A hA f-coarseResponse hA hA1 δ hδ f‖≤ω δ := by
  apply spectralDiagonal_error_le _ _ _ (modulus_nonneg hω hδ.le)
  intro i
  have hs := contraction_spectrum hA hA1 i
  have he := gridIndex_error δ hδ (orderedHermitianValues hA i) hs
  apply (hω.dominates _ _ hs (gridPoint_mem δ hδ _)).trans
  apply hω.mono
  change |orderedHermitianValues hA i-gridPoint δ
      (gridIndex δ hδ (orderedHermitianValues hA i) hs).val|≤δ
  rw [abs_of_nonneg he.1]
  exact he.2.le

/-- If two Hermitian contractions are within δ in operator norm, their coarse grid operators are
within 3δ. -/
theorem coarse_pair_distance {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖≤1) (hB1 : ‖B‖≤1) (δ : ℝ) (hδ : 0<δ) (hAB : ‖A-B‖≤δ) :
    ‖coarseOperator hA hA1 δ hδ-coarseOperator hB hB1 δ hδ‖≤3*δ := by
  let QA := coarseOperator hA hA1 δ hδ
  let QB := coarseOperator hB hB1 δ hδ
  have ha : ‖QA-A‖≤δ := by simpa only [norm_sub_rev] using! coarse_operator_error hA hA1 δ hδ
  have hb : ‖B-QB‖≤δ := coarse_operator_error hB hB1 δ hδ
  have he : QA-QB=(QA-A)+(A-B)+(B-QB) := by abel
  change ‖QA-QB‖≤3*δ
  rw [he]
  calc
    _ ≤ (‖QA-A‖+‖A-B‖)+‖B-QB‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (δ+δ)+δ := add_le_add (add_le_add ha hAB) hb
    _ = _ := by ring

/-- The matrix whose (i, j) entry is the difference of the row and column grid indices times the
corresponding entry of W. -/
def indexDifference (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (W : Matrix I J ℂ) : Matrix I J ℂ := fun i j =>
  (((r i).val:ℂ)-((c j).val:ℂ))*W i j

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] in

/-- The entrywise product of the grid divided-difference matrix and `indexDifference` equals the
sampled response difference multiplied entrywise by W. -/
theorem gridDividedDifference_index (n : ℕ) (r : I → Fin (n+1)) (c : J → Fin (n+1))
    (z : ℕ → ℂ) (W : Matrix I J ℂ) :
    gridDividedDifference n r c z ⊙ indexDifference n r c W=
      fun i j => (z (r i).val-z (c j).val)*W i j := by
  ext i j
  change (if (r i).val=(c j).val then 0 else
      (z (r i).val-z (c j).val)/(((r i).val:ℂ)-((c j).val:ℂ)))*
      ((((r i).val:ℂ)-((c j).val:ℂ))*W i j)=_
  by_cases hrc : (r i).val=(c j).val
  · simp [hrc]
  · have hne : (((r i).val:ℂ)-((c j).val:ℂ))≠0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hrc
    rw [if_neg hrc,← mul_assoc,div_mul_cancel₀ _ hne]

omit [DecidableEq I] in

/-- In mixed spectral coordinates, the difference of two grid-valued spectral operators equals δ
times the index-difference matrix of the basis overlaps. -/
theorem grid_coordinates
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (c : OrthonormalBasis K ℂ (EuclideanSpace ℂ I)) (δ : ℝ) (n : ℕ)
    (r : J → Fin (n+1)) (s : K → Fin (n+1)) :
    (basisColumns b).conjTranspose*(spectralDiagonal b (fun i => (gridPoint δ (r i).val:ℂ))-
      spectralDiagonal c (fun j => (gridPoint δ (s j).val:ℂ)))*basisColumns c =
      (δ:ℂ) • indexDifference n r s ((basisColumns b).conjTranspose*basisColumns c) := by
  ext i j
  rw [cross_coordinates]
  simp only [Matrix.smul_apply,smul_eq_mul,indexDifference,gridPoint]
  push_cast
  ring

/-- If two Hermitian contractions are within δ > 0, the index-difference matrix formed from
their quantization indices and basis overlaps has operator norm at most three. -/
theorem coarse_index_norm {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖≤1) (hB1 : ‖B‖≤1) (δ : ℝ) (hδ : 0<δ) (hAB : ‖A-B‖≤δ) :
    ‖indexDifference (gridSize δ) (quantizationIndex hA hA1 δ hδ) (quantizationIndex hB hB1 δ hδ)
      ((basisColumns (orderedHermitianBasis hA)).conjTranspose*basisColumns (orderedHermitianBasis hB))‖≤3 := by
  let b := orderedHermitianBasis hA
  let c := orderedHermitianBasis hB
  let r := quantizationIndex hA hA1 δ hδ
  let s := quantizationIndex hB hB1 δ hδ
  let W := (basisColumns b).conjTranspose*basisColumns c
  have he : (basisColumns b).conjTranspose*(coarseOperator hA hA1 δ hδ-
      coarseOperator hB hB1 δ hδ)*basisColumns c=(δ:ℂ) • indexDifference (gridSize δ) r s W :=
    grid_coordinates b c δ (gridSize δ) r s
  have hn := basis_coordinates_norm b c (coarseOperator hA hA1 δ hδ-coarseOperator hB hB1 δ hδ)
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ] at hn
  change ‖indexDifference (gridSize δ) r s W‖≤3
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    _ = ‖coarseOperator hA hA1 δ hδ-coarseOperator hB hB1 δ hδ‖ := hn
    _ ≤ 3*δ := coarse_pair_distance hA hB hA1 hB1 δ hδ hAB
    _ = δ*3 := by ring

/-- Expresses the difference of two coarse responses in their mixed eigenbases as the entrywise
product of a grid divided-difference matrix and the index-difference matrix of the basis
overlaps. -/
theorem coarse_response_coordinates {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖≤1) (hB1 : ‖B‖≤1) (δ : ℝ) (hδ : 0<δ) (f : ℝ → ℂ) :
    (basisColumns (orderedHermitianBasis hA)).conjTranspose*(coarseResponse hA hA1 δ hδ f-
      coarseResponse hB hB1 δ hδ f)*basisColumns (orderedHermitianBasis hB) =
      gridDividedDifference (gridSize δ) (quantizationIndex hA hA1 δ hδ) (quantizationIndex hB hB1 δ hδ)
        (fun q => f (gridPoint δ q)) ⊙
        indexDifference (gridSize δ) (quantizationIndex hA hA1 δ hδ) (quantizationIndex hB hB1 δ hδ)
          ((basisColumns (orderedHermitianBasis hA)).conjTranspose*basisColumns (orderedHermitianBasis hB)) := by
  rw [gridDividedDifference_index]
  unfold coarseResponse
  ext i j
  exact cross_coordinates _ _ _ _ i j

/-- The finite odd harmonic sum `oddHarmonic n` is nonnegative. -/
theorem oddHarmonic_nonneg (n : ℕ) : 0≤oddHarmonic n := by
  unfold oddHarmonic
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- For Hermitian contractions within δ > 0 and a response with modulus ω, bounds the coarse
response difference by `6 * ω δ * oddHarmonic (gridSize δ)`. -/
theorem coarse_response_distance {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖≤1) (hB1 : ‖B‖≤1) (δ : ℝ) (hδ : 0<δ) (hAB : ‖A-B‖≤δ)
    (f : ℝ → ℂ) (ω : ℝ → ℝ) (hω : ModulusOfContinuity f ω) :
    ‖coarseResponse hA hA1 δ hδ f-coarseResponse hB hB1 δ hδ f‖≤6*ω δ*oddHarmonic (gridSize δ) := by
  let r := quantizationIndex hA hA1 δ hδ
  let s := quantizationIndex hB hB1 δ hδ
  let W :=
      (basisColumns (orderedHermitianBasis hA)).conjTranspose*basisColumns
      (orderedHermitianBasis hB)
  let X := indexDifference (gridSize δ) r s W
  have hn := basis_coordinates_norm (orderedHermitianBasis hA) (orderedHermitianBasis hB)
    (coarseResponse hA hA1 δ hδ f-coarseResponse hB hB1 δ hδ f)
  rw [coarse_response_coordinates] at hn
  have hD := modulus_nonneg hω hδ.le
  calc
    _ = ‖gridDividedDifference (gridSize δ) r s (fun q => f (gridPoint δ q)) ⊙ X‖ := hn.symm
    _ ≤ 2*ω δ*oddHarmonic (gridSize δ)*‖X‖ := gridSchur_bound _ _ _ _ _ hD (grid_f_increment δ hδ f ω hω) X
    _ ≤ 2*ω δ*oddHarmonic (gridSize δ)*3 := mul_le_mul_of_nonneg_left
      (coarse_index_norm hA hB hA1 hB1 δ hδ hAB)
      (mul_nonneg (mul_nonneg (by norm_num) hD) (oddHarmonic_nonneg _))
    _ = _ := by ring

/-- For Hermitian contractions within δ > 0, the functional-calculus response difference is at
most `(8 + 6 * Real.log (gridSize δ)) * ω δ` when ω is a modulus of continuity. -/
theorem hermitian_modulus_grid_bound {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖≤1) (hB1 : ‖B‖≤1) (δ : ℝ) (hδ : 0<δ) (hAB : ‖A-B‖≤δ)
    (f : ℝ → ℂ) (ω : ℝ → ℝ) (hω : ModulusOfContinuity f ω) :
    ‖hermitianFunction A hA f-hermitianFunction B hB f‖≤(8+6*Real.log (gridSize δ))*ω δ := by
  let FA := hermitianFunction A hA f
  let FB := hermitianFunction B hB f
  let QA := coarseResponse hA hA1 δ hδ f
  let QB := coarseResponse hB hB1 δ hδ f
  have ha : ‖FA-QA‖≤ω δ := coarse_response_error hA hA1 δ hδ f ω hω
  have hb : ‖QB-FB‖≤ω δ := by
    simpa only [norm_sub_rev] using! coarse_response_error hB hB1 δ hδ f ω hω
  have hm : ‖QA-QB‖≤6*ω δ*oddHarmonic (gridSize δ) :=
    coarse_response_distance hA hB hA1 hB1 δ hδ hAB f ω hω
  have he : FA-FB=(FA-QA)+(QA-QB)+(QB-FB) := by abel
  change ‖FA-FB‖≤_
  rw [he]
  calc
    _ ≤ (‖FA-QA‖+‖QA-QB‖)+‖QB-FB‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (ω δ+6*ω δ*oddHarmonic (gridSize δ))+ω δ := add_le_add (add_le_add ha hm) hb
    _ = (2+6*oddHarmonic (gridSize δ))*ω δ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by have hh := oddHarmonic_le (gridSize δ); linarith) (modulus_nonneg hω hδ.le)

/-- The natural logarithm of three is at least one. -/
private theorem log_three_ge_one : (1:ℝ)≤Real.log 3 := by
  have h8 : Real.log (8:ℝ)=3*Real.log 2 := by
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num
  have h9 : Real.log (9:ℝ)=2*Real.log 3 := by
    rw [show (9:ℝ)=3^2 by norm_num,Real.log_pow]
    norm_num
  have hm := Real.log_le_log (by norm_num : (0:ℝ)<8) (by norm_num : (8:ℝ)≤9)
  rw [h8,h9] at hm
  linarith [Real.log_two_gt_d9]

/-- For 0 < δ ≤ 2, the coefficient `8 + 6 * Real.log (gridSize δ)` is at most
`modulusRobustnessFactor δ`. -/
theorem grid_printed_coefficient (δ : ℝ) (hδ : 0<δ) (hδ2 : δ≤2) :
    8+6*Real.log (gridSize δ) ≤ modulusRobustnessFactor δ := by
  have hnpos := gridSize_pos δ hδ hδ2
  by_cases hn1 : gridSize δ=1
  · simp only [hn1,Nat.cast_one,Real.log_one,mul_zero,add_zero]
    have hh := eleven_le_modulusRobustnessFactor hδ hδ2
    linarith
  · have hn2 : 2≤gridSize δ := by omega
    have hfloor : (gridSize δ:ℝ)≤2/δ := Nat.floor_le (div_nonneg (by norm_num) hδ.le)
    have hn2R : (2:ℝ)≤gridSize δ := by exact_mod_cast hn2
    have hd1 : δ≤1 := by
      have hp := (le_div_iff₀ hδ).mp hfloor
      have hm := mul_le_mul_of_nonneg_right hn2R hδ.le
      nlinarith
    have hx : (3:ℝ)≤2/δ+1 := by
      have hb : (2:ℝ)≤2/δ := (le_div_iff₀ hδ).mpr (by linarith)
      linarith
    have ht : 1≤Real.log (2/δ+1) := log_three_ge_one.trans (Real.log_le_log (by norm_num) hx)
    have hlog : Real.log (gridSize δ)≤Real.log (2/δ+1) :=
      Real.log_le_log (by exact_mod_cast hnpos) (by linarith)
    unfold modulusRobustnessFactor
    nlinarith [sq_nonneg (Real.log (2/δ+1)-1)]

/-- Establishes `Th20MainBound`, bounding the functional-calculus difference of Hermitian
contractions at positive distance by their modulus of continuity times
`modulusRobustnessFactor` [Gilyén et al., Theorem 20][GilyenSuLowWiebe2019]. -/
theorem th20_main : Th20MainBound := by
  intro H _ _ A B hA hB f ω hA1 hB1 hω hδ
  have hg := hermitian_modulus_grid_bound hA hB hA1 hB1 ‖A-B‖ hδ (le_refl _) f ω hω
  exact hg.trans (mul_le_mul_of_nonneg_right
    (grid_printed_coefficient ‖A-B‖ hδ (norm_sub_le_two A B hA1 hB1))
    (modulus_nonneg hω (norm_nonneg _)))

end Qatlib.Concepts.QsvtCore.PhaseExistence
