/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.VectorSQRun

/-!
# Inflation bounds for PCA vector access

Relates the energy of a lifted PCA output to the small-sketch value and the cached row energies.
The resulting bound on `pcaSQInflation` ensures nonzero outputs and controls rejection overhead
for the access construction in [Tang2021].

## Main statements

* `pca_output_weighted_energy`: The weighted energy of the output coefficients equals the
  eigenvector-weighted cached row energy divided by the positive small-sketch value.
* `pca_actual_sq_inflation`: The eigenvalue lower bound and column Gram error bound imply a
  nonzero PCA output and sample-and-query inflation at most `4 * q * K` [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SqEstimation.RejectionSample

/-- For a positive small-sketch value, the squared PCA output norm is the squared adjoint-lift
norm divided by that value. -/
theorem pca_output_norm_sq {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (hmu : 0<pcaSmallValue W i) :
    ‖pcaOutput R W i‖^2=‖Rᴴ.toEuclideanLin (pcaSmallVector W i)‖^2/pcaSmallValue W i := by
  rw [pcaOutput,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow,inv_pow,Real.sq_sqrt hmu.le]
  ring

/-- The coordinate squared magnitudes of a canonical small-sketch eigenvector sum to one. -/
theorem pca_small_vector_energy {q : ℕ} (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    (∑ t,Complex.normSq (pcaSmallVector W i t))=1 := by
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [← EuclideanSpace.norm_sq_eq,pcaSmallVector_norm,one_pow]

/-- The cached row energy averaged with a unit small-sketch eigenvector's squared coordinates is
at most the input energy. -/
theorem pca_weighted_unit_rows {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hq : 0<q) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    (∑ t,Complex.normSq (pcaSmallVector W i t)*pcaCachedRowEnergy A hA q rows t)≤sketchSquared A := by
  calc
    _ ≤ ∑ t,Complex.normSq (pcaSmallVector W i t)*sketchSquared A := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
      rw [pcaCachedRowEnergy_spec]
      exact (Finset.single_le_sum (fun j _ => sketchRowSquared_nonneg (pcaRowSketch A hA q rows) j)
        (Finset.mem_univ t)).trans (pcaRowSketch_energy A hA q hq rows)
    _ = _ := by rw [← Finset.sum_mul,pca_small_vector_energy,one_mul]

/-- The weighted energy of the output coefficients equals the eigenvector-weighted cached row
energy divided by the positive small-sketch value. -/
theorem pca_output_weighted_energy {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (hmu : 0<pcaSmallValue W i) :
    pcaWeightedEnergy A hA rows (pcaOutputCoefficients W i)=
      (∑ t,Complex.normSq (pcaSmallVector W i t)*pcaCachedRowEnergy A hA q rows t)/pcaSmallValue W i := by
  simp only [pcaWeightedEnergy,pcaOutputCoefficients,Complex.normSq_mul,Complex.normSq_inv,
    Complex.normSq_ofReal,← pow_two,Real.sq_sqrt hmu.le]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The ratio of total sampling-envelope energy to the squared norm of the lifted PCA output. -/
def pcaSQInflation {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) : ℝ :=
  (∑ j,Complex.normSq (sqLinearEnvelope (pcaOutputCoefficients W i)
    (pcaConjugateRows (pcaRowSketch A hA q rows)) j))/‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2

/-- The eigenvalue lower bound and column Gram error bound imply a nonzero PCA output and
sample-and-query inflation at most `4 * q * K` [Tang2021]. -/
theorem pca_actual_sq_inflation {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hq : 0<q) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (sigma etaCol K : ℝ)
    (hsigma : 0<sigma) (hF : sketchSquared A=K*sigma^2)
    (hmu : sigma^2/2≤pcaSmallValue W i) (heta : etaCol≤sigma^2/4)
    (hcol : spectralFrobenius (W*Wᴴ-pcaRowSketch A hA q rows*(pcaRowSketch A hA q rows)ᴴ)≤etaCol) :
    0<‖pcaOutput (pcaRowSketch A hA q rows) W i‖ ∧
      pcaSQInflation A hA rows W i≤4*(q:ℝ)*K := by
  let R := pcaRowSketch A hA q rows
  have hmu0 : 0<pcaSmallValue W i := lt_of_lt_of_le (by positivity) hmu
  have hx := pca_lift_norm_lower R W (pcaSmallVector W i) (pcaSmallValue W i) etaCol sigma
    (pcaSmallVector_norm W i) (pcaSmallVector_action W i) hcol hsigma hmu heta
  have hxpos : 0<‖Rᴴ.toEuclideanLin (pcaSmallVector W i)‖ := by linarith
  have hxSq : sigma^2/4≤‖Rᴴ.toEuclideanLin (pcaSmallVector W i)‖^2 := by nlinarith
  constructor
  · rw [pcaOutput,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hmu0)) hxpos
  · unfold pcaSQInflation
    rw [pca_envelope_energy,pca_output_weighted_energy A hA rows W i hmu0,pca_output_norm_sq _ _ _ hmu0]
    have hid : (q:ℝ)*((∑ t,Complex.normSq (pcaSmallVector W i t)*pcaCachedRowEnergy A hA q rows t)/
        pcaSmallValue W i)/(‖Rᴴ.toEuclideanLin (pcaSmallVector W i)‖^2/pcaSmallValue W i)=
        (q:ℝ)*(∑ t,Complex.normSq (pcaSmallVector W i t)*pcaCachedRowEnergy A hA q rows t)/
          ‖Rᴴ.toEuclideanLin (pcaSmallVector W i)‖^2 := by field_simp
    rw [hid]
    apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
    have hK : 0<K := by nlinarith [sq_nonneg sigma]
    have hm := mul_le_mul_of_nonneg_left hxSq (by positivity : 0≤4*(q:ℝ)*K)
    have hb :=
        mul_le_mul_of_nonneg_left (pca_weighted_unit_rows A hA hq rows W i)
        (Nat.cast_nonneg (α:=ℝ) q)
    rw [hF] at hb
    nlinarith

end Qatlib.Papers.QPCAAssume18.ClassicalPca
